-- Prove2me | solution 1 for HararySachs.Hyper.trace_identity
-- status  : ACCEPTED   (prove)
-- author  : @milia
-- created : 2026-11-12T05:17:12.775348+00:00
-- url     : https://prove2.me/submissions/c76aa006-3a71-4219-bdf0-f3238d07d234

import Mathlib
import Definitions.Def_HararySachs_Hyper_CharPoly
import Definitions.Def_HararySachs_Hyper_Operators
import Theorems.Thm_HararySachs_Hyper_exp_newton
import Theorems.Thm_HararySachs_Hyper_charPoly_coeff_top
import Theorems.Thm_HararySachs_Hyper_newton_traces

open HararySachs.Hyper

theorem solution (n k d : ℕ) (hk : 2 ≤ k) (hn : 1 ≤ n)
    (E : Finset (Finset (Fin n))) (hE : ∀ e ∈ E, e.card = k)
    (hd1 : 1 ≤ d) (hdt : d ≤ n * (k - 1) ^ (n - 1))
    (res : MvPolynomial (ResVar n (fun _ => k - 1)) ℤ)
    (hres : IsResultant n (fun _ => k - 1) res) :
    codegCoeff (k := k) E res d =
      schurP d (fun j => -(Tr (k := k) E j) / (j : ℚ)) := by
  -- the codegree coefficients satisfy the exponential (Newton) recursion
  refine exp_newton (n * (k - 1) ^ (n - 1)) (fun j => -(Tr (k := k) E j) / (j : ℚ))
    (fun e => codegCoeff (k := k) E res e) ?_ ?_ d hdt
  · -- normalisation: the leading coefficient is `1`
    show codegCoeff (k := k) E res 0 = 1
    unfold codegCoeff
    rw [Nat.sub_zero]
    exact charPoly_coeff_top n k hk hn E hE res hres
  · -- Newton's identities with the Morozov–Shakirov traces
    intro e he1 heN
    show (e : ℚ) * codegCoeff (k := k) E res e =
      ∑ j ∈ Finset.Icc 1 e, (j : ℚ) * (-(Tr (k := k) E j) / (j : ℚ)) *
        codegCoeff (k := k) E res (e - j)
    rw [newton_traces n k hk hn E hE res hres e he1 heN, ← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun j hj => ?_
    have hj0 : (j : ℚ) ≠ 0 := by
      have := (Finset.mem_Icc.mp hj).1
      exact_mod_cast (by omega : j ≠ 0)
    field_simp
