-- Prove2me | solution 1 for GlobalTheory.LevelUnfold.embX_smul_gluedS
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T18:54:37.46186+00:00
-- url     : https://prove2.me/submissions/5f16e589-f2ac-4653-9a35-325b24e22b73

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_TwistedDiscreteSeries_FlagVolumeFiltration
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_UnipotentRadicalBasic
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_MemSmulOfMemFlagSubOne
import Theorems.Thm_GlobalTheory_LatPair_embX_smul_gluedLat


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
variable [Fintype n] [DecidableEq n]
open MeasureTheory ValuativeRel Matrix IsLocalRing
open scoped Pointwise ENNReal
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  {n n' : Type} {c : ℕ} {q : _root_.GlobalTheory.LatPair.Unif k}
variable [Fintype n] [DecidableEq n]
namespace GlobalTheory.LevelUnfold
namespace _root_.GlobalTheory.LevelUnfold
theorem _root_.solution (g : GL n k) (L : Submodule 𝒪[k] (n → k))
    (f : n → k) :
    _root_.GlobalTheory.RootEx.embX c g • _root_.GlobalTheory.LatPair.gluedS q c L f =
      _root_.GlobalTheory.LatPair.gluedS q c (g • L) (g • f) := by
  rw [← _root_.GlobalTheory.LatPair.gluedLat_one, ← _root_.GlobalTheory.LatPair.gluedLat_one,
    _root_.GlobalTheory.LatPair.embX_smul_gluedLat]
end _root_.GlobalTheory.LevelUnfold
end GlobalTheory.LevelUnfold
