-- Prove2me | solution 1 for GlobalTheory.JR.LinDesc.eta_inv_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T18:01:17.485217+00:00
-- url     : https://prove2.me/submissions/e915f1c3-15a9-49e8-b5bb-8d00945b1463

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_LeftMulTau
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_JacquetRallisTransferFactorKrylovDetStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_UnramifiedValuationParitySignCharacterKernelNormStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_EtaleHermitianPairStructureFactsStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_JacquetRallisTransferFactorLinearDescentPointOne

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.JR Matrix MeasureTheory Filter Topology
noncomputable section
open GlobalTheory GlobalTheory.JR GlobalTheory.JR.LinDesc
namespace GlobalTheory.JR.LinDesc
theorem _root_.solution {F : Type} [NormedField F] (x : F) : eta x⁻¹ = eta x := by
  have key : (∃ y : F, ‖x⁻¹‖ = ‖y‖ ^ 2) ↔ ∃ y : F, ‖x‖ = ‖y‖ ^ 2 := by
    constructor
    · rintro ⟨y, hy⟩
      refine ⟨y⁻¹, ?_⟩
      rw [norm_inv] at hy
      rw [norm_inv, inv_pow, ← hy, inv_inv]
    · rintro ⟨y, hy⟩
      exact ⟨y⁻¹, by rw [norm_inv, norm_inv, inv_pow, hy]⟩
  unfold eta
  by_cases h : ∃ y : F, ‖x‖ = ‖y‖ ^ 2
  · rw [if_pos (key.mpr h), if_pos h]
  · rw [if_neg (fun h' => h (key.mp h')), if_neg h]
end GlobalTheory.JR.LinDesc
