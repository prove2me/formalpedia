-- Prove2me | solution 1 for GlobalTheory.SplitFlip.exists_isUnif
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T00:42:36.158064+00:00
-- url     : https://prove2.me/submissions/dd59afd6-a143-4e46-b1ce-a1eb64cadec1

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_T2SpaceGeneralLinearGroup
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_RankEqCardIffExistsFrameMatrixFirstColumnBlock

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory ValuativeRel Matrix
open scoped NNReal ENNReal Pointwise
noncomputable section
open GlobalTheory GlobalTheory.SplitFlip
open GlobalTheory.SplitWeil GlobalTheory.SplitWeil.Model
variable {k : Type*} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
namespace GlobalTheory.SplitFlip
theorem _root_.solution : ∃ ϖ : kˣ, IsUnif ϖ := by
  obtain ⟨t, ht⟩ := ValuativeRel.valuation_surjective (uniformizer k)
  exact ⟨Units.mk0 t (by rintro rfl; exact ValuativeRel.uniformizer_ne_zero (R := k) (by simpa using ht.symm)), ht⟩
end GlobalTheory.SplitFlip
