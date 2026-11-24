-- Prove2me | solution 1 for GlobalTheory.SplitFlip.liftRes_mem
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T04:10:15.079408+00:00
-- url     : https://prove2.me/submissions/0f47a6ff-3a96-4133-b2cf-3c2ac4c2c591

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
variable {A D : Type*}
namespace GlobalTheory.SplitFlip
theorem _root_.solution {B : Type*} {e : ℕ} (T : A → B → Res k e) (i : A) (j : B) : liftRes T i j ∈ 𝒪[k] :=
  (Quotient.out (T i j) : 𝒪[k]).2
end GlobalTheory.SplitFlip
