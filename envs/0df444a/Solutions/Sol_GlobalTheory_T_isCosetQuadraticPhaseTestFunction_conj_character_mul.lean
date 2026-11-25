-- Prove2me | solution 1 for GlobalTheory.T.isCosetQuadraticPhaseTestFunction_conj_character_mul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T18:20:31.509569+00:00
-- url     : https://prove2.me/submissions/cdc92e8e-c004-4e73-b996-cddb695b9961

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_IsCosetQuadraticPhaseTestFunctionConjCharacterMu
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SpanningFamilies_IntMIffInt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_IsCosetQuadraticPhaseTestFunctionConjCharacterMuStatement
import Theorems.Thm_GlobalTheory_Phase_shape_conj_chr_mul


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Complex GlobalTheory.SW GlobalTheory.Phase
open scoped ComplexConjugate Real
set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ (κ ι : Type) [Fintype κ] [Fintype ι] [DecidableEq ι], ∀ φ : Matrix κ ι ℚ → ℂ, Shape φ → Shape (fun x => conj (φ x)) ∧ (∀ y, Shape (fun x => φ x * chr y x)) ∧ ∀ ψ, Shape ψ → Shape (fun x => φ x * ψ x) := by
  first | exact @GlobalTheory.Phase.shape_conj_chr_mul | exact GlobalTheory.Phase.shape_conj_chr_mul | (intros; apply GlobalTheory.Phase.shape_conj_chr_mul <;> assumption)
end _root_.GlobalTheory.T
