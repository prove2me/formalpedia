-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.SW.TailConst.tail_pos
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T14:09:21.734699+00:00
-- url     : https://prove2.me/submissions/748563f2-d54e-4dca-9a14-981dceb98818

import Mathlib
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_InfiniteProductMultipliableStatement
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_InfiniteProductRenormalization
import Theorems.Thm_GlobalTheory_T_infinite_product_multipliable


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Topology
open scoped ENNReal NNReal Matrix
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.SW GlobalTheory.CompanionTheory.SW.TailConst
namespace GlobalTheory.CompanionTheory.SW.TailConst
theorem _root_.solution {ι : Type} (a : ι → ℝ) (hs : Summable (fun v => |a v - 1|)) (S : Finset ι)
    (hpos : ∀ v, v ∉ S → 0 < a v) : 0 < ∏' w : {w // w ∉ S}, a w.1 :=
  (GlobalTheory.T.infinite_product_multipliable {w // w ∉ S} (fun w => a w.1)
    (hs.comp_injective Subtype.val_injective)).2.2.1 (fun w => hpos w.1 w.2)
end GlobalTheory.CompanionTheory.SW.TailConst
