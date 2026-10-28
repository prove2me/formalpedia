-- Prove2me | solution 1 for OAI.PiExponent.FormalInterpolation.weighted_curve_bound_finite_initial_power_certificate
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-24T14:34:51.234133+00:00
-- url     : https://prove2.me/submissions/aabd72de-ffa5-4565-a6c4-990abb16fa55
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_OAI_PiExponent_WeightedIdealCurveCriterion
import Theorems.Thm_OAI_PiExponent_FormalInterpolation_weighted_curve_bound_gives_finite_weighted_power_certificate
import Theorems.Thm_OAI_PiExponent_FormalInterpolation_weighted_finite_power_certificate_to_rational_initial_power_certificate
import Theorems.Thm_OAI_PiExponent_FormalInterpolation_weightedHomogeneousComponent_rat_eq_real
import Mathlib.Data.Complex.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Data.Rat.Defs
import Mathlib.RingTheory.Finiteness.Defs
import Mathlib.RingTheory.MvPolynomial.WeightedHomogeneous

open scoped BigOperators
open OAI.PiExponent.FormalInterpolation

theorem solution
    {d : Nat} (I : Ideal (MvPolynomial (Fin d) Complex))
    (hfinite : Module.Finite Complex (MvPolynomial (Fin d) Complex ⧸ I))
    (w : Fin d → Rat) (hw : ∀ i, 0 < (w i : Real))
    (rho : Rat) (hrho : 0 ≤ rho)
    (hcurve : WeightedIdealCurveBound I w rho)
    (eps : Real) (heps : 0 < eps) :
    ∃ s : Nat, 0 < s ∧ ∃ q : Rat, 0 < q ∧
      (q : Real) + 1 < (s : Real) * ((rho : Real) + eps) ∧
      ∃ n : Nat, ∃ f : Fin n → MvPolynomial (Fin d) Complex,
        (∀ j, f j ∈ I ^ s) ∧
        (∀ j, ∀ a ∈ (f j).support,
          ∑ k, (w k : Real) * (a k : Real) ≤ (q : Real)) ∧
        ∀ i : Fin d, ∃ e : Nat,
          MvPolynomial.X i ^ e ∈
            Ideal.span (Set.range (fun j =>
              MvPolynomial.weightedHomogeneousComponent w q (f j))) := by
  obtain ⟨s, hs, D, hD, hDR, n, f, hf, hweight, hgen⟩ :=
    weighted_curve_bound_gives_finite_weighted_power_certificate
      I hfinite w hw rho hrho hcurve ((rho : Real) + eps / 2) (by linarith)
  have hsR : 0 < (s : Real) := by exact_mod_cast hs
  have he : 0 < eps / 2 := by linarith
  have hgap : 0 < (s : Real) * (eps / 2) := mul_pos hsR he
  have hDtarget : D < (s : Real) * ((rho : Real) + eps) := by
    calc
      D < (s : Real) * ((rho : Real) + eps / 2) := hDR
      _ < (s : Real) * ((rho : Real) + eps) := by nlinarith
  obtain ⟨q, hq, hqbound, n', g, hg, hweightg, hgenq⟩ :=
    weighted_finite_power_certificate_to_rational_initial_power_certificate
      I w rho eps heps s hs D hD hDtarget n f hf hweight hgen
  refine ⟨s, hs, q, hq, hqbound, n', g, hg, hweightg, ?_⟩
  intro i
  obtain ⟨e, hmem⟩ := hgenq i
  refine ⟨e, ?_⟩
  simpa only [weightedHomogeneousComponent_rat_eq_real] using hmem