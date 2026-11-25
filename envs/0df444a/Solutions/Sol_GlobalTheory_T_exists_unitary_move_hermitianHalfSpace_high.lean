-- Prove2me | solution 1 for GlobalTheory.T.exists_unitary_move_hermitianHalfSpace_high
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T08:00:56.724144+00:00
-- url     : https://prove2.me/submissions/592a4e16-2016-437e-aa9a-ce88762b6098

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_ExistsUnitaryMoveHermitianHalfSpaceHigh
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SpanningFamilies_IsHeatZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_ExistsUnitaryMoveHermitianHalfSpaceHighStatement
import Theorems.Thm_GlobalTheory_SW_exists_move_high


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Complex NumberField GlobalTheory.SW Filter Topology
open ReciprocityTheory.ChartRestriction.G.FD (cc herm)
open scoped ComplexConjugate ComplexOrder Real
set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (Ψ : Finset (E →+* ℂ)), IsType Ψ → ∀ N : ℕ, ∃ (c : ℕ) (δ : ℝ), 0 < c ∧ 0 < δ ∧ ∀ Z ∈ Hn Ψ N, ∃ γ ∈ UU E N, Den c γ ∧ hAct Ψ γ Z ∈ HnGe Ψ N δ := by
  first | exact @GlobalTheory.SW.exists_move_high | exact GlobalTheory.SW.exists_move_high | (intros; apply GlobalTheory.SW.exists_move_high <;> assumption)
end _root_.GlobalTheory.T
