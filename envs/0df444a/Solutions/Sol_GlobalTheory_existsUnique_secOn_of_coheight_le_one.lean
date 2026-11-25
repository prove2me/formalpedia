-- Prove2me | solution 1 for GlobalTheory.existsUnique_secOn_of_coheight_le_one
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T01:59:49.044614+00:00
-- url     : https://prove2.me/submissions/eb5af633-1313-4e1d-aa5a-4bf26f7cd9d7

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_MemRangeOfForallHeightEqOneOfIsReflexive
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ShimuraVarieties_IsOpenOfMemIrreducibleComponentsOfFinite
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsGrpPullback
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SemiabelianSchemes_PrecompleteBases_PsbLb
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_ProdIso
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_ExistsUniqueLbIsoPullEqOfCoheightLeOne
import Theorems.Thm_GlobalTheory_resG_eq_mul_of_injective
import Theorems.Thm_GlobalTheory_bijective_resG_of_coheight_le_one
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
theorem _root_.solution [IsLocallyNoetherian X] [GlobalTheory.IsNormalScheme X]
    (L : LB X) {V W : X.Opens} (h : W ≤ V) (hW : ∀ x ∈ V, Order.coheight x ≤ 1 → x ∈ W)
    {s : ∀ i, Γ(X, W ⊓ L.U i)} (hs : s ∈ secOn L W) :
    ∃! t : ∀ i, Γ(X, V ⊓ L.U i),
      t ∈ secOn L V ∧ ∀ i, resG X (inf_le_inf_right _ h) (t i) = s i := by
  have hb (i) : Function.Bijective (resG X (inf_le_inf_right (L.U i) h)) :=
    bijective_resG_of_coheight_le_one _ fun x hx h1 ↦ ⟨hW x hx.1 h1, hx.2⟩
  choose t ht using fun i ↦ (hb i).2 (s i)
  refine ⟨t, ⟨fun i j ↦ ?_, ht⟩, fun t' ht' ↦ funext fun i ↦ (hb i).1 ((ht'.2 i).trans (ht i).symm)⟩
  refine resG_eq_mul_of_injective _ _ _ (inf_le_inf_right _ h) (inf_le_inf_right _ h)
    (inf_le_inf_right _ (inf_le_inf_right _ h) : W ⊓ L.U i ⊓ L.U j ≤ _) inf_le_left
    (le_inf (inf_le_left.trans inf_le_left) inf_le_right)
    (bijective_resG_of_coheight_le_one _ fun x hx h1 ↦ ?_).1 ?_
  · exact ⟨⟨hW x hx.1.1 h1, hx.1.2⟩, hx.2⟩
  · rw [ht, ht]
    exact hs i j
end GlobalTheory
