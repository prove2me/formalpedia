-- Prove2me | solution 1 for GlobalTheory.lbIsoPull_s_val
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T00:52:22.555882+00:00
-- url     : https://prove2.me/submissions/871deab9-a8b6-4a4b-8d3a-afe00cea3a49

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_MemRangeOfForallHeightEqOneOfIsReflexive
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ShimuraVarieties_IsOpenOfMemIrreducibleComponentsOfFinite
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsGrpPullback
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SemiabelianSchemes_PrecompleteBases_PsbLb
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_ProdIso
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_ExistsUniqueLbIsoPullEqOfCoheightLeOne
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
theorem _root_.solution {L M : LB X} (w : LB.Iso L M) (f : Y ⟶ X)
    (p : (PUnit.{u + 1} → M.ι) × (PUnit.{u + 1} → L.ι)) :
    ((lbIsoPull w f).s p).val =
      (f.appLE ((M.div L).U (p.1 PUnit.unit, p.2 PUnit.unit)) (((M.pull f).div (L.pull f)).U p)
        (lb_div_pull_U L M f p).le).hom (w.s (p.1 PUnit.unit, p.2 PUnit.unit)).val := by
  simp only [lbIsoPull, LB.linCombIso, zpow_one]
  exact congrArg Units.val (Fintype.prod_unique _)
end GlobalTheory
