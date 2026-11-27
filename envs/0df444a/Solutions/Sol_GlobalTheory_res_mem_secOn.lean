-- Prove2me | solution 1 for GlobalTheory.res_mem_secOn
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-27T04:44:11.950242+00:00
-- url     : https://prove2.me/submissions/0d5fb267-66bc-4d93-b6db-039e24819b2b

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_MemRangeOfForallHeightEqOneOfIsReflexive
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ShimuraVarieties_IsOpenOfMemIrreducibleComponentsOfFinite
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsGrpPullback
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SemiabelianSchemes_PrecompleteBases_PsbLb
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_ProdIso
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_ExistsUniqueLbIsoPullEqOfCoheightLeOne
import Theorems.Thm_GlobalTheory_resG_resG
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
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
variable {X Y : Scheme.{0}}
namespace GlobalTheory
theorem _root_.solution {L : LB X} {V W : X.Opens} (h : W ≤ V) {s : ∀ i, Γ(X, V ⊓ L.U i)}
    (hs : s ∈ secOn L V) : (fun i ↦ resG X (inf_le_inf_right _ h) (s i)) ∈ secOn L W := by
  intro i j
  have := congrArg (resG X (inf_le_inf_right _ (inf_le_inf_right _ h) :
    W ⊓ L.U i ⊓ L.U j ≤ V ⊓ L.U i ⊓ L.U j)) (hs i j)
  simpa only [map_mul, resG_resG] using this
end GlobalTheory
