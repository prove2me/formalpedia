-- Prove2me | solution 1 for GlobalTheory.HCXi.ConeOne.cone_ne_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T04:11:53.712078+00:00
-- url     : https://prove2.me/submissions/f1dc5c35-0e28-4621-8b32-1e6633c362b1

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ThetaMetrics_IsKMeas
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CmHalfIntegralGeneratorMemAlgebraicClosure
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_ExistsConeMeasurePosRank
import Theorems.Thm_GlobalTheory_HCXi_ConeOne_par_meas
import Theorems.Thm_GlobalTheory_HCXi_ConeOne_cone_def

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix MeasureTheory Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.B2 GlobalTheory.HCXi
open scoped ENNReal ComplexOrder ComplexConjugate
noncomputable section
open GlobalTheory GlobalTheory.HCXi GlobalTheory.HCXi.ConeOne
open Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.B2x8
namespace GlobalTheory.HCXi.ConeOne
theorem _root_.solution (k r' : ℕ) : coneMeas k r' ≠ 0 := by
  intro h
  have h1 : coneMeas k r' Set.univ = 0 := by rw [h]; rfl
  rw [cone_def, Measure.map_apply (par_meas k r') MeasurableSet.univ, Set.preimage_univ, ← Set.univ_prod_univ,
    Measure.prod_prod, mul_eq_zero] at h1
  rcases h1 with h1 | h1
  · unfold radMeas at h1
    rw [withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ, lintegral_eq_zero_iff (by fun_prop)] at h1
    have h2 : ∀ᵐ c : ℂ, c ≠ 0 := by rw [ae_iff]; simp
    have h3 : ∀ᵐ _c : ℂ, False := by
      filter_upwards [h1, h2] with c hc hc0
      have : 0 < ‖c‖ ^ (2 * (2 * r' + k + 1)) := pow_pos (norm_pos_iff.2 hc0) _
      simp only [Pi.zero_apply, ENNReal.ofReal_eq_zero] at hc
      linarith
    rw [Filter.eventually_false_iff_eq_bot, ae_eq_bot] at h3
    exact NeZero.ne _ h3
  · rw [Measure.volume_eq_prod, ← Set.univ_prod_univ, Measure.prod_prod, mul_eq_zero] at h1
    rcases h1 with h1 | h1
    · exact (isOpen_univ.measure_pos (volume : Measure (Fin (2 * r' + k + 1) → ℂ)) Set.univ_nonempty).ne' h1
    · simp at h1
end GlobalTheory.HCXi.ConeOne
