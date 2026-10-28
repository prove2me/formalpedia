-- Prove2me | solution 1 for OAI.PiExponent.FormalInterpolation.weighted_finite_power_certificate_to_rational_initial_power_certificate
-- status  : ACCEPTED   (disprove)
-- author  : @Eyal1990
-- created : 2026-10-24T14:41:54.646385+00:00
-- url     : https://prove2.me/submissions/f4e74009-b365-413c-b24b-8d38101f14ed

import Definitions.Def_OAI_PiExponent_WeightedIdealCurveCriterion
import Mathlib.Data.Complex.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Data.Rat.Defs
import Mathlib.RingTheory.Ideal.Operations
import Mathlib.RingTheory.MvPolynomial.WeightedHomogeneous

open scoped BigOperators
open OAI.PiExponent.FormalInterpolation

theorem solution : ¬ (∀ {d : Nat} (I : Ideal (MvPolynomial (Fin d) Complex))
    (w : Fin d → Rat) (rho : Rat) (eps : Real) (heps : 0 < eps)
    (s : Nat) (hs : 0 < s) (D : Real) (hD : 0 < D)
    (hDtarget : D < (s : Real) * ((rho : Real) + eps))
    (n : Nat) (f : Fin n → MvPolynomial (Fin d) Complex)
    (hf : ∀ j, f j ∈ I ^ s)
    (hweight : ∀ j, ∀ a ∈ (f j).support,
      ∑ k, (w k : Real) * (a k : Real) ≤ D)
    (hgen : ∀ i : Fin d, ∃ e : Nat, 0 < e ∧
      MvPolynomial.X i ^ e ∈
        Ideal.span (Set.range (fun j =>
          MvPolynomial.weightedHomogeneousComponent
            (fun k => (w k : Real)) D (f j)))) ,
    ∃ q : Rat, 0 < q ∧ (q : Real) + 1 <
      (s : Real) * ((rho : Real) + eps) ∧
      ∃ n' : Nat, ∃ g : Fin n' → MvPolynomial (Fin d) Complex,
        (∀ j, g j ∈ I ^ s) ∧
        (∀ j, ∀ a ∈ (g j).support,
          ∑ k, (w k : Real) * (a k : Real) ≤ (q : Real)) ∧
        ∀ i : Fin d, ∃ e : Nat,
          MvPolynomial.X i ^ e ∈
            Ideal.span (Set.range (fun j =>
              MvPolynomial.weightedHomogeneousComponent
                (fun k => (w k : Real)) q (g j)))) := by
  intro H
  have hresult := H (d := 0) (I := (⊥ : Ideal (MvPolynomial (Fin 0) Complex)))
    (w := fun i : Fin 0 => (0 : Rat)) (rho := (0 : Rat))
    (eps := (1 : Real) / 2) (by norm_num)
    (s := 1) (by norm_num) (D := (1 : Real) / 4) (by norm_num)
    (by norm_num) (n := 0)
    (f := fun j : Fin 0 => Fin.elim0 j)
    (by intro j; exact Fin.elim0 j)
    (by intro j; exact Fin.elim0 j)
    (by intro i; exact Fin.elim0 i)
  rcases hresult with ⟨q, hq, hbound, _⟩
  have hqreal : (0 : Real) < (q : Real) := by exact_mod_cast hq
  linarith