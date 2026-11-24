-- Prove2me | solution 1 for GlobalTheory.SplitFlip.mem_shellSet
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T04:10:15.257867+00:00
-- url     : https://prove2.me/submissions/2ea82e4e-1539-4884-9240-eace51bb722e

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
variable {A A' D : Type*} [Fintype A] [DecidableEq A] [Fintype A'] [DecidableEq A'] [Fintype D] [DecidableEq D]
namespace GlobalTheory.SplitFlip
theorem _root_.solution {ϖ : kˣ} {n : A → ℤ} {g : GL A k} :
    g ∈ shellSet ϖ n ↔ ∃ x ∈ KO k A, ∃ y ∈ KO k A, g = x * (diagGL fun i => ϖ ^ n i) * y :=
  DoubleCoset.mem_doubleCoset
end GlobalTheory.SplitFlip
