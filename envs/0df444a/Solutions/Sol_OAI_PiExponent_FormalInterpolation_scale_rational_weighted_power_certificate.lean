-- Prove2me | solution 1 for OAI.PiExponent.FormalInterpolation.scale_rational_weighted_power_certificate
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-24T14:59:17.416337+00:00
-- url     : https://prove2.me/submissions/5eca9279-869f-4f11-b6ac-cac98e5a5c35

import Definitions.Def_OAI_PiExponent_WeightedIdealCurveCriterion
import Mathlib.Data.Complex.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Data.Rat.Defs
import Mathlib.RingTheory.Ideal.Operations
import Mathlib.RingTheory.MvPolynomial.WeightedHomogeneous
import Theorems.Thm_OAI_PiExponent_FormalInterpolation_scale_integer_bound
import Theorems.Thm_OAI_PiExponent_FormalInterpolation_scaled_product_algebraic_certificate
import Theorems.Thm_OAI_PiExponent_FormalInterpolation_weightedHomogeneousComponent_rat_eq_real

open scoped BigOperators
open OAI.PiExponent.FormalInterpolation

theorem solution
    {d : Nat} (I : Ideal (MvPolynomial (Fin d) Complex))
    (w : Fin d → Rat) (R : Real)
    (s : Nat) (hs : 0 < s) (D : Real) (hD : 0 < D)
    (hDR : D < (s : Real) * R) (r : Rat) (hr : (r : Real) = D)
    (n : Nat) (f : Fin n → MvPolynomial (Fin d) Complex)
    (hf : ∀ j, f j ∈ I ^ s)
    (hweight : ∀ j, ∀ a ∈ (f j).support,
      ∑ k, (w k : Real) * (a k : Real) ≤ D)
    (hgen : ∀ i : Fin d, ∃ e : Nat, 0 < e ∧
      MvPolynomial.X i ^ e ∈ Ideal.span (Set.range (fun j =>
        MvPolynomial.weightedHomogeneousComponent
          (fun k => (w k : Real)) D (f j)))) :
    ∃ s' : Nat, 0 < s' ∧ ∃ q : Rat, 0 < q ∧
      (q : Real) + 1 < (s' : Real) * R ∧
      ∃ n' : Nat, ∃ g : Fin n' → MvPolynomial (Fin d) Complex,
        (∀ j, g j ∈ I ^ s') ∧
        (∀ j, ∀ a ∈ (g j).support,
          ∑ k, (w k : Real) * (a k : Real) ≤ (q : Real)) ∧
        ∀ i : Fin d, ∃ e : Nat,
          MvPolynomial.X i ^ e ∈ Ideal.span (Set.range (fun j =>
            MvPolynomial.weightedHomogeneousComponent w q (g j))) := by
  obtain ⟨k, hk, hscale⟩ :=
    OAI.PiExponent.FormalInterpolation.scale_integer_bound hs hD hDR
  obtain ⟨hq, n', g, hgI, hgweight, hggenerates⟩ :=
    OAI.PiExponent.FormalInterpolation.scaled_product_algebraic_certificate
      I w s hs D hD r hr k hk n f hf hweight hgen
  refine ⟨k * s, Nat.mul_pos hk hs, k * r, hq, ?_, n', g, hgI, hgweight, hggenerates⟩
  simpa [Rat.cast_mul, hr, Nat.cast_mul, mul_comm, mul_left_comm, mul_assoc] using hscale
