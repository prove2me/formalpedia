-- Prove2me | solution 1 for GlobalTheory.LevelUnfold.mul_inv_q
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T05:32:11.717746+00:00
-- url     : https://prove2.me/submissions/c1785f96-07ce-427a-a9ed-d907c1381d92

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_TwistedDiscreteSeries_FlagVolumeFiltration
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_UnipotentRadicalBasic
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_MemSmulOfMemFlagSubOne
import Theorems.Thm_GlobalTheory_RootEx_Radical_Uni_inv


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory ValuativeRel Matrix IsLocalRing
open scoped Pointwise ENNReal
noncomputable section
open GlobalTheory GlobalTheory.LevelUnfold
open GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.LatPair GlobalTheory.IndefiniteRowSideFullHecke.FlagVolumeFiltration
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  {n n' : Type} {c : ℕ} {q : Unif k}
open MeasureTheory ValuativeRel Matrix IsLocalRing
open scoped Pointwise ENNReal
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  {n n' : Type} {c : ℕ} {q : _root_.GlobalTheory.LatPair.Unif k}
namespace GlobalTheory.LevelUnfold
namespace _root_.GlobalTheory.LevelUnfold
theorem _root_.solution (q : _root_.GlobalTheory.LatPair.Unif k) :
    (q.1 : k) * q.inv = 1 :=
  mul_inv_cancel₀ q.ne_zero
end _root_.GlobalTheory.LevelUnfold
end GlobalTheory.LevelUnfold
