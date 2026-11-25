-- Prove2me | solution 1 for GroundTheory.GroupCoh.function_exact_of_shortExact
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T01:35:32.931107+00:00
-- url     : https://prove2.me/submissions/500f6d1f-b256-40f2-baaa-3a7fae01b970

import Mathlib
import Definitions.Def_GroundTheory_TateCohomology_InducedNorm
import Definitions.Def_GroundTheory_TateCohomology_DimensionShift
import Definitions.Def_GroundTheory_TateCohomology_TateConnecting
import Definitions.Def_GroundTheory_TateCohomology_AugmentationSES

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open CategoryTheory MonoidalCategory
open GroundTheory GroundTheory.GroupCoh
universe u
variable {k G : Type u} [CommRing k] [Group G]
variable (k G)
variable {k G}
variable (k G)
variable {k G}
variable {A B : Rep.{u} k G}
namespace GroundTheory.GroupCoh
theorem _root_.solution {S : ShortComplex (Rep.{u} k G)} (hS : S.ShortExact) :
    Function.Exact S.f.hom.toLinearMap S.g.hom.toLinearMap := by
  have h := hS.exact.map (forget₂ (Rep.{u} k G) (ModuleCat.{u} k))
  rw [ShortComplex.moduleCat_exact_iff_range_eq_ker] at h
  exact LinearMap.exact_iff.mpr h.symm
end GroundTheory.GroupCoh
