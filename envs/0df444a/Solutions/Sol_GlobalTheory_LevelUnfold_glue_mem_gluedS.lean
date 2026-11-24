-- Prove2me | solution 1 for GlobalTheory.LevelUnfold.glue_mem_gluedS
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T05:40:07.342681+00:00
-- url     : https://prove2.me/submissions/280e5b3c-03be-4f37-bcad-e47511698adf

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
theorem _root_.solution (L : Submodule 𝒪[k] (n → k)) (f : n → k) :
    q.inv • _root_.GlobalTheory.LatPair.avec k n c 1 +
      _root_.GlobalTheory.LatPair.inX k n c f ∈ _root_.GlobalTheory.LatPair.gluedS q c L f := by
  unfold _root_.GlobalTheory.LatPair.gluedS
  exact Submodule.mem_sup_left (Submodule.mem_sup_right (Submodule.mem_span_singleton_self _))
end _root_.GlobalTheory.LevelUnfold
end GlobalTheory.LevelUnfold
