-- Prove2me | solution 1 for GlobalTheory.bijective_res_of_coheight_eq_one
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T01:05:20.207799+00:00
-- url     : https://prove2.me/submissions/842ec5c2-de93-4d3f-b5fb-e6f14cc6cab7

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_MemRangeOfForallHeightEqOneOfIsReflexive
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ShimuraVarieties_IsOpenOfMemIrreducibleComponentsOfFinite
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsGrpPullback
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SemiabelianSchemes_PrecompleteBases_PsbLb
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_ProdIso
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_ExistsUniqueLbIsoPullEqOfCoheightLeOne
import Theorems.Thm_GlobalTheory_genericPoint_mem_opens
import Theorems.Thm_GlobalTheory_germToFunctionField_mem_range_stalk
import Theorems.Thm_GlobalTheory_germToFunctionField_res
import Theorems.Thm_GlobalTheory_exists_germToFunctionField_eq_of_coheight_eq_one
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
variable {X Y : Scheme.{u}}
namespace GlobalTheory
theorem _root_.solution [IsIntegral X] [IsLocallyNoetherian X]
    [IsNormalScheme X] {V W : X.Opens} (h : W ≤ V) [Nonempty W]
    (hW : ∀ x ∈ V, Order.coheight x = 1 → x ∈ W) :
    Function.Bijective (X.presheaf.map (homOfLE h).op).hom := by
  have : Nonempty V := ⟨⟨_, h (genericPoint_mem_opens W)⟩⟩
  refine ⟨map_injective_of_isIntegral X (homOfLE h), fun s ↦ ?_⟩
  obtain ⟨t, ht⟩ := exists_germToFunctionField_eq_of_coheight_eq_one V
    (X.germToFunctionField W s) fun x hx h1 ↦ germToFunctionField_mem_range_stalk W s (hW x hx h1)
  exact ⟨t, X.germToFunctionField_injective W ((germToFunctionField_res h t).trans ht)⟩
end GlobalTheory
