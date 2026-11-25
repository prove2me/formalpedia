-- Prove2me | solution 1 for GlobalTheory.existsUnique_genPull_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T01:21:14.463371+00:00
-- url     : https://prove2.me/submissions/3bd399de-51f6-47a3-b338-3c1ef4fdd23f

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_MemRangeOfForallHeightEqOneOfIsReflexive
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ShimuraVarieties_IsOpenOfMemIrreducibleComponentsOfFinite
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsGrpPullback
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SemiabelianSchemes_PrecompleteBases_PsbLb
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_ProdIso
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_ExistsUniqueLbIsoPullEqOfCoheightLeOne
import Theorems.Thm_GlobalTheory_existsUnique_gen_of_charts
import Theorems.Thm_GlobalTheory_lbGen_ext
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
theorem _root_.solution (f : Y ⟶ X) (hf : ∀ V, Function.Bijective (f.app V).hom)
    (L : LB X) (r : (L.pull f).Gen) (hr : r.IsGen) :
    ∃! t : L.Gen, t.IsGen ∧ L.genPull t f = r := by
  refine (existsUnique_congr fun t ↦ and_congr_right fun _ ↦ ?_).mp
    (existsUnique_gen_of_charts f hf (L := L)
      (L' := L.pull f) (Equiv.funUnique PUnit L.ι) (lb_pull_U L f) (lb_pull_g L f) r hr)
  exact ⟨fun h ↦ lbGen_ext h, fun h j ↦ congrArg (fun z : (L.pull f).Gen ↦ (z.s j).val) h⟩
end GlobalTheory
