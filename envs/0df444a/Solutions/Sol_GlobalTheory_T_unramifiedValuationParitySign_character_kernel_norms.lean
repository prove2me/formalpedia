-- Prove2me | solution 1 for GlobalTheory.T.unramifiedValuationParitySign_character_kernel_norms
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T20:35:49.68931+00:00
-- url     : https://prove2.me/submissions/37f3abe4-7657-482e-8711-1353d4ae6c79

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_UnramifiedValuationParitySignCharacterKernelNorm
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_FourierMatch
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_UnramifiedValuationParitySignCharacterKernelNormStatement
import Theorems.Thm_GlobalTheory_EtaChar_main


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.JR Matrix MeasureTheory Filter Topology
set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E] [Unram F E], (∀ x y : F, x ≠ 0 → y ≠ 0 → eta (x * y) = eta x * eta y) ∧ (∀ x : F, ‖x‖ = 1 → eta x = 1) ∧ (∀ x : F, x ≠ 0 → (eta x = 1 ↔ ∃ v : E, v * star v = algebraMap F E x)) ∧ IsLocallyConstant (fun x : {x : F // x ≠ 0} => eta x.1) := by
  first | exact @GlobalTheory.EtaChar.main | exact GlobalTheory.EtaChar.main | (intros; apply GlobalTheory.EtaChar.main <;> assumption)
end _root_.GlobalTheory.T
