-- Prove2me | solution 1 for GlobalTheory.HCXi.ConeOne.cone_ae
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T04:53:18.437636+00:00
-- url     : https://prove2.me/submissions/0d73a0b1-5225-4c7c-8df3-1d92d8643f6d

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ThetaMetrics_IsKMeas
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CmHalfIntegralGeneratorMemAlgebraicClosure
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_ExistsConeMeasurePosRank
import Theorems.Thm_GlobalTheory_HCXi_ConeOne_par_meas
import Theorems.Thm_GlobalTheory_HCXi_ConeOne_cone_def
import Theorems.Thm_GlobalTheory_HCXi_ConeOne_par_eq
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x8_hb_add_conj
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x8_herm_smul_left
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x8_herm_smul_right
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x8_hermitian_quadratic_continuous
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x8_hermitian_three_block
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x8_three_block_last


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
theorem _root_.solution (k r' : ℕ) : ∀ᵐ v ∂(coneMeas k r'), v ≠ 0 ∧ herm (Hpk k (1 + r')) v v = 0 := by
  rw [cone_def]
  have hc : Continuous fun v : Fin (2 * (1 + r') + k + 1) → ℂ => herm (Hpk k (1 + r')) v v :=
    hermitian_quadratic_continuous (k := k) (r' := 1 + r')
  have hS : MeasurableSet {v : Fin (2 * (1 + r') + k + 1) → ℂ | v ≠ 0 ∧ herm (Hpk k (1 + r')) v v = 0} :=
    (MeasurableSet.singleton 0).compl.inter (isClosed_eq hc continuous_const).measurableSet
  rw [ae_map_iff (par_meas k r').aemeasurable hS]
  have h0 : ∀ᵐ p : ℂ × HPar k r' ∂((radMeas (2 * r' + k + 1)).prod (volume : Measure (HPar k r'))), p.1 ≠ 0 := by
    rw [ae_iff]
    have : {p : ℂ × HPar k r' | ¬ p.1 ≠ 0} = {(0 : ℂ)} ×ˢ Set.univ := by
      ext p; simp
    rw [this, Measure.prod_prod]
    have h0 : radMeas (2 * r' + k + 1) {(0 : ℂ)} = 0 := by
      unfold radMeas
      exact withDensity_absolutelyContinuous _ _ (by simp)
    rw [h0, zero_mul]
  filter_upwards [h0] with p hp
  rw [par_eq]
  constructor
  · intro h
    apply hp
    have := congrArg cL h
    rw [three_block_smul, three_block_last, mul_one] at this
    exact this
  · rw [herm_smul_left, herm_smul_right, hermitian_three_block]
    have := hb_add_conj (k := k) (r' := r') p.2.1 p.2.2
    simp only [map_one, mul_one, one_mul]
    rw [this]
    simp
end GlobalTheory.HCXi.ConeOne
