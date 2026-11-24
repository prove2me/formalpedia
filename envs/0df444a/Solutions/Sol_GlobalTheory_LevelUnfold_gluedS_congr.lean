-- Prove2me | solution 1 for GlobalTheory.LevelUnfold.gluedS_congr
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T18:55:41.59141+00:00
-- url     : https://prove2.me/submissions/2a83faf3-8b04-45bc-9d65-78cea231306b

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_TwistedDiscreteSeries_FlagVolumeFiltration
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_UnipotentRadicalBasic
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_MemSmulOfMemFlagSubOne
import Theorems.Thm_GlobalTheory_LatPair_gluedLat_congr


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
theorem _root_.solution {L : Submodule 𝒪[k] (n → k)} {f f' : n → k}
    (h : f - f' ∈ L) : _root_.GlobalTheory.LatPair.gluedS q c L f = _root_.GlobalTheory.LatPair.gluedS q c L f' := by
  rw [← _root_.GlobalTheory.LatPair.gluedLat_one, ← _root_.GlobalTheory.LatPair.gluedLat_one,
    _root_.GlobalTheory.LatPair.gluedLat_congr q c 1 h]
end _root_.GlobalTheory.LevelUnfold
end GlobalTheory.LevelUnfold
