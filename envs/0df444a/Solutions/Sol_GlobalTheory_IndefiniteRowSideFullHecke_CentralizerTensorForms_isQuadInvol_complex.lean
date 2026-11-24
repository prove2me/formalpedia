-- Prove2me | solution 1 for GlobalTheory.IndefiniteRowSideFullHecke.CentralizerTensorForms.isQuadInvol_complex
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T17:38:32.239157+00:00
-- url     : https://prove2.me/submissions/29ca2392-55a4-4602-98a0-53f42351eb95

import Mathlib
import Definitions.Def_Formalism_SatakeDualWeyl_Statement
import Definitions.Def_Formalism_LocalRingCardinality_DataLevel
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_TwistedDiscreteSeries_CentralizerTensorForms
import Theorems.Thm_Formalism_HC_Frame_iotaInv_iota
import Theorems.Thm_Formalism_HC_Frame_iota_iotaInv
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.HC.Frame.iotaInv_iota
attribute [local simp] Formalism.HC.Frame.iota_iotaInv



set_option autoImplicit false
noncomputable section
open Matrix Formalism.UG NumberField
open scoped TensorProduct
open GlobalTheory GlobalTheory.IndefiniteRowSideFullHecke GlobalTheory.IndefiniteRowSideFullHecke.CentralizerTensorForms
namespace GlobalTheory.IndefiniteRowSideFullHecke.CentralizerTensorForms
theorem _root_.solution : IsQuadInvol ℝ ℂ (Complex.conjAe : ℂ →ₐ[ℝ] ℂ) where
  etale := ⟨Algebra.FormallyEtale.of_isSeparable ℝ ℂ,
    Algebra.FinitePresentation.of_finiteType.1 inferInstance⟩
  finrank_eq := Complex.finrank_real_complex
  invol := by intro e; simp
  ne_id := ⟨Complex.I, by simp [Complex.ext_iff]; norm_num⟩
end GlobalTheory.IndefiniteRowSideFullHecke.CentralizerTensorForms
