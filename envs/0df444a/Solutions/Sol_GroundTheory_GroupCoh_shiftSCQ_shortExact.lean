-- Prove2me | solution 1 for GroundTheory.GroupCoh.shiftSCQ_shortExact
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T00:18:11.048882+00:00
-- url     : https://prove2.me/submissions/c07bbbaa-cdb9-4f05-abbd-cc5da988969d

import Mathlib
import Definitions.Def_GroundTheory_TateCohomology_DeltaMap
import Definitions.Def_GroundTheory_TateCohomology_CoindOne
import Definitions.Def_GroundTheory_TateCohomology_InfRes
import Theorems.Thm_GroundTheory_GroupCoh_invariants_map_surjective
import Theorems.Thm_GroundTheory_GroupCoh_shiftSC_shortExact

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.GroupCoh
open CategoryTheory Limits groupCohomology Rep
universe u
variable {k G : Type u} [CommRing k] [Group G]
variable (A : Rep k G) (S : Subgroup G) [S.Normal]
namespace GroundTheory.GroupCoh
theorem _root_.solution (h1 : IsZero (groupCohomology (res S.subtype A) 1)) :
    (shiftSCQ A S).ShortExact where
  mono_f := (Rep.mono_iff_injective _).2 fun x y h =>
    Subtype.ext (toCoindOne_injective A (congrArg Subtype.val h))
  epi_g := (Rep.epi_iff_surjective _).2
    (invariants_map_surjective ((shortExact_res S.subtype).2 (shiftSC_shortExact A)) h1)
  exact := by
    rw [← ShortComplex.exact_map_iff_of_faithful _ (forget₂ (Rep k (G ⧸ S)) (ModuleCat k)),
      ShortComplex.moduleCat_exact_iff_ker_sub_range]
    intro x hx
    have hrk := ((shiftSC_shortExact A).exact.map
      (forget₂ (Rep k G) (ModuleCat k))).moduleCat_range_eq_ker
    have hx' : x.1 ∈ LinearMap.ker ((shiftSC A).map (forget₂ (Rep k G) (ModuleCat k))).g.hom :=
      congrArg Subtype.val hx
    rw [← hrk] at hx'
    obtain ⟨a, ha⟩ := hx'
    have ha' : (toCoindOne A).hom a = x.1 := ha
    refine ⟨⟨a, fun s => toCoindOne_injective A ?_⟩, Subtype.ext ha'⟩
    refine (hom_comm_apply (toCoindOne A) (s : G) a).trans ?_
    rw [ha']
    exact x.2 s
end GroundTheory.GroupCoh
