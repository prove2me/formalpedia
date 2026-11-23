-- Prove2me | solution 1 for GlobalTheory.LocFlat.CFac.mulLC_apply
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T20:39:46.680802+00:00
-- url     : https://prove2.me/submissions/bf94bfdf-ecfe-4b35-a003-f6a28f2e86a8

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_MatrixMeasurableSpace
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_ProdFnMemSB

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.SplitWeil
noncomputable section
open GlobalTheory GlobalTheory.LocFlat GlobalTheory.LocFlat.CFac
namespace GlobalTheory.LocFlat.CFac
theorem _root_.solution {X : Type} [TopologicalSpace X] (φ : X → ℂ) (hφ : IsLocallyConstant φ) (F : SB X) (x : X) :
    (mulLC φ hφ F).1 x = φ x * F.1 x := rfl
end GlobalTheory.LocFlat.CFac
