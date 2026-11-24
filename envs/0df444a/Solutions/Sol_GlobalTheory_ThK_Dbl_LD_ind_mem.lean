-- Prove2me | solution 1 for GlobalTheory.ThK.Dbl.LD.ind_mem
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T04:30:11.168712+00:00
-- url     : https://prove2.me/submissions/92f13f35-66f7-4136-b701-4137f9271f4b

import Mathlib
import Definitions.Def_Development_WeilBound_ThetaLifts_LatticeBasics_LocDistA
import Definitions.Def_Development_WeilBound_ThetaLifts_LatticeBasics_LocDistB

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Filter Topology GlobalTheory.WeilM
open GlobalTheory GlobalTheory.ThK GlobalTheory.ThK.Dbl GlobalTheory.ThK.Dbl.LD
variable {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [T2Space G]
namespace GlobalTheory.ThK.Dbl.LD
theorem _root_.solution {K : Subgroup G} (ho : IsOpen (K : Set G)) (hc : IsCompact (K : Set G)) : ind K ∈ SB G :=
  ⟨(LocallyConstant.charFn ℂ ⟨K.isClosed_of_isOpen ho, ho⟩).isLocallyConstant,
    HasCompactSupport.intro hc fun _ hx => Set.indicator_of_notMem hx _⟩
end GlobalTheory.ThK.Dbl.LD
