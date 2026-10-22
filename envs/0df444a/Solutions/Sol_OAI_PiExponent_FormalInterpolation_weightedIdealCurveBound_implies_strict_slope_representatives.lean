-- Prove2me | solution 1 for OAI.PiExponent.FormalInterpolation.weightedIdealCurveBound_implies_strict_slope_representatives
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-21T09:20:00.063979+00:00
-- url     : https://prove2.me/submissions/cb486e91-0bd0-4849-930c-351af28dac1a
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_OAI_PiExponent_WeightedIdealCurveCriterion
import Theorems.Thm_OAI_PiExponent_FormalInterpolation_weighted_curve_bound_gives_power_sections_at_infinity
import Theorems.Thm_OAI_PiExponent_FormalInterpolation_finite_adjoin_of_common_weight_initial_forms
import Theorems.Thm_OAI_PiExponent_FormalInterpolation_power_representatives_of_finite_adjoin
import Mathlib.Data.Real.Archimedean
import Mathlib.Tactic.Linarith

open scoped BigOperators
open OAI.PiExponent.FormalInterpolation

theorem solution
    {d : Nat} (I : Ideal (MvPolynomial (Fin d) Complex))
    (hfinite : Module.Finite Complex (MvPolynomial (Fin d) Complex ⧸ I))
    (w : Fin d → Rat) (hw : ∀ i, 0 < (w i : Real))
    (rho : Rat) (hrho : 0 ≤ rho)
    (hcurve : WeightedIdealCurveBound I w rho)
    (eps : Real) (heps : 0 < eps) :
    ∃ delta : Real, 0 ≤ delta ∧ delta < (rho : Real) + eps ∧
      ∃ N : Nat, ∀ n : Nat, N ≤ n →
        ∀ z : MvPolynomial (Fin d) Complex ⧸ I ^ n,
          ∃ q : MvPolynomial (Fin d) Complex,
            Ideal.Quotient.mk (I ^ n) q = z ∧
              ∀ a ∈ q.support,
                ∑ i, (w i : Real) * (a i : Real) ≤ (n : Real) * delta := by
  have hrhoReal : 0 ≤ (rho : Real) := by exact_mod_cast hrho
  obtain ⟨s, hs, D, hD, hDs, k, f, hmem, hweight, htop⟩ :=
    weighted_curve_bound_gives_power_sections_at_infinity
      I hfinite w hw rho hrho hcurve ((rho : Real) + eps / 2) (by linarith)
  have hfiniteF : Module.Finite (Algebra.adjoin Complex (Set.range f))
      (MvPolynomial (Fin d) Complex) :=
    finite_adjoin_of_common_weight_initial_forms w hw D hD f hweight htop
  obtain ⟨B, hB, hrep⟩ :=
    power_representatives_of_finite_adjoin
      (fun i => (w i : Real)) I s hs D hD.le f hmem hweight hfiniteF
  have hsReal : 0 < (s : Real) := by exact_mod_cast hs
  have hrate : D / (s : Real) < (rho : Real) + eps / 2 := by
    apply (div_lt_iff₀ hsReal).2
    simpa only [mul_comm] using hDs
  have hgap : 0 < ((rho : Real) + eps / 2) - D / (s : Real) := by
    linarith
  obtain ⟨N, hN⟩ := exists_nat_gt
    (B / (((rho : Real) + eps / 2) - D / (s : Real)))
  refine ⟨(rho : Real) + eps / 2, by linarith, by linarith, N, ?_⟩
  intro n hn z
  have hNn : (N : Real) ≤ (n : Real) := by exact_mod_cast hn
  have hratio : B / (((rho : Real) + eps / 2) - D / (s : Real)) ≤
      (n : Real) := le_trans hN.le hNn
  have hBbound : B ≤ (n : Real) *
      (((rho : Real) + eps / 2) - D / (s : Real)) :=
    (div_le_iff₀ hgap).1 hratio
  obtain ⟨P, hP⟩ := Ideal.Quotient.mk_surjective z
  obtain ⟨Q, hPQ, hQ⟩ := hrep n P
  refine ⟨Q, ?_, ?_⟩
  · calc
      Ideal.Quotient.mk (I ^ n) Q = Ideal.Quotient.mk (I ^ n) P :=
        ((Ideal.Quotient.eq).2 hPQ).symm
      _ = z := hP
  · intro a ha
    have hQa := hQ a ha
    nlinarith
