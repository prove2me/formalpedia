-- Prove2me | solution 1 for GlobalTheory.bijective_lbSecPull
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T01:15:18.681571+00:00
-- url     : https://prove2.me/submissions/0f5e3499-6647-4fef-b853-6977bb9d1fad

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_MemRangeOfForallHeightEqOneOfIsReflexive
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ShimuraVarieties_IsOpenOfMemIrreducibleComponentsOfFinite
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsGrpPullback
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SemiabelianSchemes_PrecompleteBases_PsbLb
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_ProdIso
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_ExistsUniqueLbIsoPullEqOfCoheightLeOne
import Theorems.Thm_GlobalTheory_existsUnique_sec_of_charts
import Theorems.Thm_GlobalTheory_lbSec_ext
import Theorems.Thm_P2M_GlobalTheory_normal_domain_height_one__5612c3bf64ed


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
universe u
open CategoryTheory AlgebraicGeometry TopologicalSpace Opposite
open GlobalTheory
open ReciprocityTheory.ChartRestriction.G.Semi
variable {X Y : Scheme.{u}}
namespace GlobalTheory
theorem _root_.solution (f : Y ⟶ X) (hf : ∀ V, Function.Bijective (f.app V).hom) (L : LB X) :
    Function.Bijective fun s : L.Sec ↦ lbSecPull L s f := by
  refine (Function.bijective_iff_existsUnique _).mpr fun s ↦ ?_
  refine (existsUnique_congr fun t ↦ ?_).mp (existsUnique_sec_of_charts f hf (L := L)
    (L' := L.pull f) (Equiv.funUnique PUnit L.ι) (lb_pull_U L f) (lb_pull_g L f) s)
  exact ⟨fun h ↦ lbSec_ext h, fun h j ↦ congrArg (fun z : (L.pull f).Sec ↦ z.f j) h⟩
end GlobalTheory
