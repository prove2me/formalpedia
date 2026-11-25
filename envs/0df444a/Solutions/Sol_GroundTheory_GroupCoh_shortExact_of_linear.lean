-- Prove2me | solution 1 for GroundTheory.GroupCoh.shortExact_of_linear
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T01:35:38.716485+00:00
-- url     : https://prove2.me/submissions/66bfdb43-8081-4abe-b429-46ac5026d321

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
namespace GroundTheory.GroupCoh
theorem _root_.solution {S : ShortComplex (Rep.{u} k G)} (hf : Function.Injective S.f.hom)
    (hg : Function.Surjective S.g.hom) (h : ∀ y : S.X₂, S.g.hom y = 0 → ∃ x, S.f.hom x = y) :
    S.ShortExact := by
  have : Mono S.f := (Rep.mono_iff_injective _).2 hf
  have : Epi S.g := (Rep.epi_iff_surjective _).2 hg
  refine ShortComplex.ShortExact.mk' ?_ inferInstance inferInstance
  rw [← ShortComplex.exact_map_iff_of_faithful _ (forget₂ (Rep.{u} k G) (ModuleCat.{u} k)),
    ShortComplex.moduleCat_exact_iff]
  exact h
end GroundTheory.GroupCoh
