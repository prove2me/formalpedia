-- Prove2me | solution 1 for GlobalTheory.existsUnique_lbIsoPull_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T01:21:29.237801+00:00
-- url     : https://prove2.me/submissions/0333db87-b551-4fca-8a82-811aacfbdee4

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_MemRangeOfForallHeightEqOneOfIsReflexive
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ShimuraVarieties_IsOpenOfMemIrreducibleComponentsOfFinite
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsGrpPullback
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SemiabelianSchemes_PrecompleteBases_PsbLb
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_ProdIso
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_ExistsUniqueLbIsoPullEqOfCoheightLeOne
import Theorems.Thm_GlobalTheory_existsUnique_gen_of_charts
import Theorems.Thm_GlobalTheory_lbGen_ext
import Theorems.Thm_GlobalTheory_lb_div_pull_g
import Theorems.Thm_GlobalTheory_lbIsoPull_s_val
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
    (L M : LB X) (w : LB.Iso (L.pull f) (M.pull f)) (hw : w.IsGen) :
    ∃! v : LB.Iso L M, v.IsGen ∧ lbIsoPull v f = w := by
  refine (existsUnique_congr fun t ↦ and_congr_right fun _ ↦ ?_).mp
    (existsUnique_gen_of_charts f hf (L := M.div L) (L' := (M.pull f).div (L.pull f))
      ((Equiv.funUnique PUnit M.ι).prodCongr (Equiv.funUnique PUnit L.ι)) (lb_div_pull_U L M f)
      (fun p q ↦ congrArg Units.val (lb_div_pull_g L M f p q)) w hw)
  exact ⟨fun h ↦ lbGen_ext fun p ↦ (lbIsoPull_s_val t f p).trans (h p),
    fun h p ↦ (lbIsoPull_s_val t f p).symm.trans
      (congrArg (fun z : LB.Iso (L.pull f) (M.pull f) ↦ (z.s p).val) h)⟩
end GlobalTheory
