-- Prove2me | solution 1 for GlobalTheory.existsUnique_sec_res_eq_of_coheight_le_one
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-27T04:38:17.205489+00:00
-- url     : https://prove2.me/submissions/5e8f5fd5-b0f0-482c-9b50-735ddbe5aab3

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_MemRangeOfForallHeightEqOneOfIsReflexive
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ShimuraVarieties_IsOpenOfMemIrreducibleComponentsOfFinite
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsGrpPullback
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SemiabelianSchemes_PrecompleteBases_PsbLb
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_ProdIso
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_ExistsUniqueLbIsoPullEqOfCoheightLeOne
import Theorems.Thm_GlobalTheory_lbSec_ext
import Theorems.Thm_GlobalTheory_resG_refl
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
    (L : LB X) {U : X.Opens} (hU : ∀ x : X, Order.coheight x ≤ 1 → x ∈ U)
    {s : ∀ i, Γ(X, U ⊓ L.U i)} (hs : s ∈ secOn L U) :
    ∃! t : L.Sec, ∀ i, resG X inf_le_right (t.f i) = s i := by
  have hb (i) : Function.Bijective (resG X (inf_le_right : U ⊓ L.U i ≤ L.U i)) :=
    bijective_resG_of_coheight_le_one _ fun x hx h1 ↦ ⟨hU x h1, hx⟩
  choose t ht using fun i ↦ (hb i).2 (s i)
  refine ⟨⟨t, fun i j ↦ ?_⟩, ht, fun t' ht' ↦ lbSec_ext fun i ↦
    (hb i).1 ((ht' i).trans (ht i).symm)⟩
  refine Eq.trans ?_ (congrArg (· * _) (resG_refl _))
  refine resG_eq_mul_of_injective _ _ _ inf_le_right inf_le_right
    (le_inf (inf_le_left.trans inf_le_right) inf_le_right : U ⊓ L.U i ⊓ L.U j ≤ _) inf_le_left
    (le_inf (inf_le_left.trans inf_le_left) inf_le_right)
    (bijective_resG_of_coheight_le_one _ fun x hx h1 ↦ ?_).1 ?_
  · exact ⟨⟨hU x h1, hx.1⟩, hx.2⟩
  · rw [ht, ht]
    exact hs i j
end GlobalTheory
