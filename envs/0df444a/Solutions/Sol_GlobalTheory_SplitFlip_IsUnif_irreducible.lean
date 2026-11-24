-- Prove2me | solution 1 for GlobalTheory.SplitFlip.IsUnif.irreducible
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T04:08:32.905098+00:00
-- url     : https://prove2.me/submissions/26cefd70-9ee4-4b8a-a01d-c7dbb41a9517

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_T2SpaceGeneralLinearGroup
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_RankEqCardIffExistsFrameMatrixFirstColumnBlock
import Theorems.Thm_GlobalTheory_SplitFlip_IsUnif_maximalIdeal_eq

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
namespace IsUnif
theorem _root_.solution {ϖ : kˣ} (hϖ : IsUnif ϖ) : Irreducible (⟨ϖ, hϖ.mem⟩ : 𝒪[k]) :=
  IsDiscreteValuationRing.irreducible_of_span_eq_maximalIdeal _ (fun h => ϖ.ne_zero (congrArg Subtype.val h))
    hϖ.maximalIdeal_eq
end IsUnif
end GlobalTheory.SplitFlip
