-- Prove2me | solution 1 for GlobalTheory.T.siegelTheta_transformation_siegelParabolic
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T03:46:18.382389+00:00
-- url     : https://prove2.me/submissions/74bf77a0-2cf0-4aa7-8ec3-2cd58e0e9f22

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_SiegelThetaTransformationSiegelParabolic
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SpanningFamilies_IMemSiegel
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_SiegelThetaTransformationSiegelParabolicStatement
import Theorems.Thm_GlobalTheory_SW_Parab_trans_parabolic


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Complex GlobalTheory.SW
open scoped ComplexConjugate Real
set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ (κ ι : Type) [Fintype κ] [Fintype ι] [DecidableEq ι] (σ : Matrix (ι ⊕ ι) (ι ⊕ ι) ℚ), Even (Fintype.card κ) → σ ∈ Matrix.symplecticGroup ι ℚ → σ.toBlocks₂₁ = 0 → ∃ ω : (Matrix κ ι ℚ → ℂ) → (Matrix κ ι ℚ → ℂ), ∀ φ, IsSB φ → IsSB (ω φ) ∧ TransS σ φ (ω φ) ∧ ∀ φ', IsSB φ' → ip (ω φ) (ω φ') = ip φ φ' := by
  first | exact @GlobalTheory.SW.Parab.trans_parabolic | exact GlobalTheory.SW.Parab.trans_parabolic | (intros; apply GlobalTheory.SW.Parab.trans_parabolic <;> assumption)
end _root_.GlobalTheory.T
