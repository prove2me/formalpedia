-- Prove2me | solution 1 for GlobalTheory.multiDiff_polynomial_eval
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T10:16:52.191605+00:00
-- url     : https://prove2.me/submissions/0a286b4c-7545-49d5-8ffa-200e014191ec

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_ExistsMvPolynomialOfIteratedBackwardDifferenceVa
import Theorems.Thm_P2M_GlobalTheory_multiDiff_cons__e9b475c9a4ea

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory
open Finset
namespace GlobalTheory
theorem _root_.solution {R : Type*} [CommRing R] {d : ℕ} (z : Fin d → R)
    (p : Polynomial R) (hp : p.natDegree ≤ d) (y : R) :
    multiDiff z (fun t ↦ p.eval t) y = d.factorial * p.coeff d * ∏ i, z i := by
  induction d generalizing p with
  | zero =>
    rw [Polynomial.eq_C_of_natDegree_le_zero hp]; simp
  | succ d ih =>
    rw [← Fin.cons_self_tail z, multiDiff_cons']
    set a := z 0
    have e : bwdDiff a (fun t ↦ p.eval t) =
        fun t ↦ (p - Polynomial.taylor (-a) p).eval t := by
      ext t; simp [bwdDiff, Polynomial.taylor_eval, sub_eq_add_neg]
    have hc : ∀ m, d + 1 ≤ m → (Polynomial.taylor (-a) p).coeff m = p.coeff m := fun m hm ↦ by
      have h0 : (Polynomial.hasseDeriv m p).natDegree ≤ 0 :=
        (Polynomial.natDegree_hasseDeriv_le p m).trans (by omega)
      rw [Polynomial.taylor_coeff, Polynomial.eq_C_of_natDegree_le_zero h0]
      simp [Polynomial.hasseDeriv_coeff]
    have hd : (Polynomial.taylor (-a) p).coeff d = p.coeff d - (d + 1) * p.coeff (d + 1) * a := by
      have h1 : (Polynomial.hasseDeriv d p).natDegree ≤ 1 :=
        (Polynomial.natDegree_hasseDeriv_le p d).trans (by omega)
      rw [Polynomial.taylor_coeff, Polynomial.eq_X_add_C_of_natDegree_le_one h1]
      simp [Polynomial.hasseDeriv_coeff, add_comm 1 d]
      ring
    rw [e, ih]
    · simp only [Polynomial.coeff_sub, hd, Fin.prod_univ_succ, Fin.cons_zero, Fin.cons_succ,
        Nat.factorial_succ]
      push_cast; ring
    · rw [Polynomial.natDegree_le_iff_coeff_eq_zero]
      intro m hm
      rw [Polynomial.coeff_sub, hc m hm, sub_self]
end GlobalTheory
