-- Prove2me | solution 1 for OAI.PiExponent.FormalInterpolation.eventual_packet_degree_reduction
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-08T06:13:48.027978+00:00
-- url     : https://prove2.me/submissions/1f4963fa-8e8c-4b84-ae64-b362f8075efc
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Theorems.Thm_OAI_PiExponent_FormalInterpolation_logarithmic_ideal_power_annihilates_strict_jets
import Theorems.Thm_OAI_PiExponent_FormalInterpolation_eventual_weighted_representatives_mod_logarithmic_ideal

open Filter Topology
open OAI.PiExponent OAI.PiExponent.DeterminantContradiction

theorem solution
    (nu : ℝ) (hnu : 2 < nu) (d : FixedData nu) :
    ∃ R : ℚ, 0 < R ∧ ∀ᶠ n : ℕ in atTop,
      ∀ P : MvPolynomial (Fin (d.m + 1)) ℂ,
        ∃ Q : FormalInterpolation.WeightedPolynomial d.w0
          (MatrixArithmetic.logWeights (finiteDenominators d)) ((n : ℝ) * (R : ℝ)),
          ∀ ρ : Row d ((n : ℝ) * (R : ℝ)),
            FormalInterpolation.packetMap d ((n : ℝ) * (R : ℝ)) Q ρ =
              MvPowerSeries.coeff (InterpolationMatrix.exponentVector ρ.2.val)
                (FormalInterpolation.formalJet
                  (fun i => (ρ.1.val : ℂ) * MatrixArithmetic.rationalCenters
                    (finiteNumerators d) (finiteDenominators d) i) P) := by
  obtain ⟨R, T, e, hR, _hepos, hT, he, hrepresent⟩ :=
    FormalInterpolation.eventual_weighted_representatives_mod_logarithmic_ideal nu hnu d
  refine ⟨R, hR, ?_⟩
  filter_upwards [hrepresent] with n hn
  intro P
  obtain ⟨Q, hQ⟩ := hn P
  refine ⟨Q, ?_⟩
  intro ρ
  have hv : ∀ i, 0 ≤ InterpolationMatrix.rowWeights d.v0 d.base.theta
      (MatrixArithmetic.logWeights (finiteDenominators d)) i := by
    intro i
    refine Fin.cases ?_ (fun j => ?_) i
    · exact d.v0_pos.le
    · exact div_nonneg (Nat.cast_nonneg _) d.base.theta_pos.le
  have hz := FormalInterpolation.logarithmic_ideal_power_annihilates_strict_jets
    (fun j : Fin d.K => fun i => (j.val : ℂ) *
      MatrixArithmetic.rationalCenters (finiteNumerators d) (finiteDenominators d) i)
    T e (InterpolationMatrix.rowWeights d.v0 d.base.theta
      (MatrixArithmetic.logWeights (finiteDenominators d))) hv hT (R : ℝ)
    (fun i => (he i).le) n (P - Q.val) hQ ρ.1 ρ.2
  change MvPowerSeries.coeff (InterpolationMatrix.exponentVector ρ.2.val)
      (FormalInterpolation.formalJet
        (fun i => (ρ.1.val : ℂ) * MatrixArithmetic.rationalCenters
          (finiteNumerators d) (finiteDenominators d) i) Q.val) = _
  have heq := sub_eq_zero.mp (by simpa only [map_sub] using hz)
  exact heq.symm
