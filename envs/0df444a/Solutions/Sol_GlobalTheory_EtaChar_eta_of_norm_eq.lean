-- Prove2me | solution 1 for GlobalTheory.EtaChar.eta_of_norm_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T14:27:33.859138+00:00
-- url     : https://prove2.me/submissions/60d5c11f-e704-49d3-9ad6-8350a73c0a0f

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_FourierMatch
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ExistsMulStarEqOfNormOneUnramifiedQuadraticStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_UnramifiedValuationParitySignCharacterKernelNorm
import Theorems.Thm_GlobalTheory_EtaChar_eta_eq_one_iff
import Theorems.Thm_GlobalTheory_EtaChar_eta_eq_neg_one_iff

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.JR Matrix MeasureTheory Filter Topology
open GlobalTheory GlobalTheory.EtaChar
namespace GlobalTheory.EtaChar
theorem _root_.solution {F : Type} [NormedField F] {x y : F} (h : ‖x‖ = ‖y‖) : eta x = eta y := by
  have e : (∃ z : F, ‖x‖ = ‖z‖ ^ 2) ↔ (∃ z : F, ‖y‖ = ‖z‖ ^ 2) := by rw [h]
  by_cases hh : ∃ z : F, ‖x‖ = ‖z‖ ^ 2
  · rw [(eta_eq_one_iff x).2 hh, (eta_eq_one_iff y).2 (e.1 hh)]
  · rw [(eta_eq_neg_one_iff x).2 hh, (eta_eq_neg_one_iff y).2 (fun h' => hh (e.2 h'))]
end GlobalTheory.EtaChar
