-- Prove2me | solution 1 for GlobalTheory.UnfoldLoss.LatVol.varLat_eq_pi
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T22:36:05.635901+00:00
-- url     : https://prove2.me/submissions/1d9c0358-fbf4-4df4-a7f6-7aa6c7cf9189

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_MemVarLat
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_PadicIsNonarchimedeanLocalField
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_VariablesUniformizerPowerLatticeBasisOpenVolume

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory ValuativeRel GlobalTheory.FunObj GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.UnfoldLoss
open GlobalTheory GlobalTheory.UnfoldLoss GlobalTheory.UnfoldLoss.LatVol
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
namespace GlobalTheory.UnfoldLoss.LatVol
theorem _root_.solution (G : Grid k) (ϖ : kˣ) (n : ℕ) :
    (varLat G ϖ n : Set (Vars G)) = Set.univ.pi fun _ => Set.univ.pi fun _ => cball (ϖ ^ n) := by
  ext e
  exact ⟨fun h j _ r _ => h j r, fun h j r => h j trivial r trivial⟩
end GlobalTheory.UnfoldLoss.LatVol
