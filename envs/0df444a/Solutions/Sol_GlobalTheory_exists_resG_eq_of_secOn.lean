-- Prove2me | solution 1 for GlobalTheory.exists_resG_eq_of_secOn
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T01:18:46.291976+00:00
-- url     : https://prove2.me/submissions/c726591d-6585-4578-96ea-a87280f22af8

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
import Theorems.Thm_GlobalTheory_bijective_res_of_eq_bot
import Theorems.Thm_GlobalTheory_germToFunctionField_mem_range_stalk_of_secOn
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
variable [IsIntegral X]
variable [IsLocallyNoetherian X] [GlobalTheory.IsNormalScheme X]
namespace GlobalTheory
theorem _root_.solution {L : LB X} {W : X.Opens} [Nonempty W]
    {s : ∀ i, Γ(X, W ⊓ L.U i)} (hs : s ∈ secOn L W) (i : L.ι) {O : X.Opens} (h : W ⊓ L.U i ≤ O)
    (hO : O ≤ L.U i)
    (H : ∀ x ∈ O, Order.coheight x = 1 → x ∉ W → ∃ (j : L.ι) (_ : Nonempty (W ⊓ L.U j : X.Opens)),
      x ∈ L.U j ∧ X.germToFunctionField (W ⊓ L.U j) (s j) ∈
        (algebraMap (X.presheaf.stalk x) X.functionField).range) :
    ∃ t : Γ(X, O), resG X h t = s i := by
  by_cases hT : O = ⊥
  · exact (bijective_res_of_eq_bot h hT).2 _
  have : Nonempty O := ((Opens.ne_bot_iff_nonempty _).mp hT).to_subtype
  have : Nonempty (W ⊓ L.U i : X.Opens) :=
    ⟨⟨_, genericPoint_mem_opens W, hO (genericPoint_mem_opens O)⟩⟩
  obtain ⟨t, ht⟩ := exists_germToFunctionField_eq_of_coheight_eq_one O
    (X.germToFunctionField _ (s i)) fun x hx h1 ↦ by
      by_cases hxW : x ∈ W
      · exact germToFunctionField_mem_range_stalk _ _ ⟨hxW, hO hx⟩
      · obtain ⟨j, _, hj, h⟩ := H x hx h1 hxW
        exact germToFunctionField_mem_range_stalk_of_secOn hs (hO hx) hj h
  exact ⟨t, X.germToFunctionField_injective _ ((germToFunctionField_res h t).trans ht)⟩
end GlobalTheory
