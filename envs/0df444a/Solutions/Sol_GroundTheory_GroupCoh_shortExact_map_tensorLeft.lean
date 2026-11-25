-- Prove2me | solution 1 for GroundTheory.GroupCoh.shortExact_map_tensorLeft
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T01:47:37.82481+00:00
-- url     : https://prove2.me/submissions/466c569b-8cd2-45ae-9170-dc1c732f4f88

import Mathlib
import Definitions.Def_GroundTheory_TateCohomology_InducedNorm
import Definitions.Def_GroundTheory_TateCohomology_DimensionShift
import Definitions.Def_GroundTheory_TateCohomology_TateConnecting
import Definitions.Def_GroundTheory_TateCohomology_AugmentationSES
import Theorems.Thm_GroundTheory_GroupCoh_shortExact_of_linear
import Theorems.Thm_GroundTheory_GroupCoh_whiskerLeft_hom_eq_lTensor
import Theorems.Thm_GroundTheory_GroupCoh_function_exact_of_shortExact

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
theorem _root_.solution {S : ShortComplex (Rep.{u} k G)} (hS : S.ShortExact)
    (Y : Rep.{u} k G) (hinj : Function.Injective (Y ◁ S.f).hom) :
    (S.map (tensorLeft Y)).ShortExact := by
  have hg : Function.Surjective S.g.hom := (Rep.epi_iff_surjective _).1 hS.epi_g
  have hex := lTensor_exact Y.V (function_exact_of_shortExact hS) hg
  refine shortExact_of_linear hinj (fun t => ?_) (fun t ht => ?_)
  · obtain ⟨s, hs⟩ := LinearMap.lTensor_surjective Y.V hg t
    exact ⟨s, (whiskerLeft_hom_eq_lTensor _ _ s).trans hs⟩
  · have ht' : LinearMap.lTensor Y.V S.g.hom.toLinearMap t = 0 :=
      (whiskerLeft_hom_eq_lTensor _ _ t).symm.trans ht
    obtain ⟨s, hs⟩ := (hex t).1 ht'
    exact ⟨s, (whiskerLeft_hom_eq_lTensor _ _ s).trans hs⟩
end GroundTheory.GroupCoh
