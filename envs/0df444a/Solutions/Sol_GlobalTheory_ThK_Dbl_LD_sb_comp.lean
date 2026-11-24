-- Prove2me | solution 1 for GlobalTheory.ThK.Dbl.LD.sb_comp
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T04:30:51.152802+00:00
-- url     : https://prove2.me/submissions/aa5a6f63-af17-4db9-9394-5716b47fd69f

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsCompactOpenAddSubgroup
import Definitions.Def_Development_WeilBound_ThetaLifts_LatticeBasics_LocDistA
import Theorems.Thm_GlobalTheory_ThK_Dbl_LD_sb_chart

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Filter Topology GlobalTheory.WeilM
open GlobalTheory GlobalTheory.ThK GlobalTheory.ThK.Dbl GlobalTheory.ThK.Dbl.LD
namespace GlobalTheory.ThK.Dbl.LD
theorem _root_.solution {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y] [T2Space X] (e : X → Y) (r : Y → X)
    (ce : Continuous e) (cr : Continuous r) (hre : ∀ x, r (e x) = x) {F : Y → ℂ} (hF : F ∈ SB Y) :
    (fun x => F (e x)) ∈ SB X :=
  sb_chart (U := Set.univ) (T := Set.univ) isOpen_univ ce.continuousOn cr.continuousOn (fun x _ => hre x)
    (fun _ _ => trivial) hF (fun _ h => absurd trivial h) (fun _ _ => rfl) (fun _ h => absurd trivial h)
end GlobalTheory.ThK.Dbl.LD
