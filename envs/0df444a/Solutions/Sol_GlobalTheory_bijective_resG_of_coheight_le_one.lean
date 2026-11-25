-- Prove2me | solution 1 for GlobalTheory.bijective_resG_of_coheight_le_one
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T01:50:24.109406+00:00
-- url     : https://prove2.me/submissions/aca25887-6f8f-4074-a663-0699272ec3fe

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_MemRangeOfForallHeightEqOneOfIsReflexive
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ShimuraVarieties_IsOpenOfMemIrreducibleComponentsOfFinite
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsGrpPullback
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SemiabelianSchemes_PrecompleteBases_PsbLb
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_ProdIso
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_ExistsUniqueLbIsoPullEqOfCoheightLeOne
import Theorems.Thm_GlobalTheory_coheight_apply_of_isOpenImmersion
import Theorems.Thm_GlobalTheory_bijective_res_inf_of_coheight_le_one
import Theorems.Thm_GlobalTheory_bijective_appLE_of_eq
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
    {V W : X.Opens} (h : W ≤ V) (hW : ∀ x ∈ V, Order.coheight x ≤ 1 → x ∈ W) :
    Function.Bijective (resG X h) := by
  have hb := bijective_res_inf_of_coheight_le_one (X := V) (U := V.ι ⁻¹ᵁ W)
    (fun x hx ↦ hW _ x.2 (by rwa [← coheight_apply_of_isOpenImmersion V.ι] at hx)) (V.ι ⁻¹ᵁ V)
  have h1 : Function.Bijective (V.ι.app V).hom :=
    have := V.ι.isIso_app V (by simp)
    ConcreteCategory.bijective_of_isIso _
  have h2 : Function.Bijective (V.ι.appLE W (V.ι ⁻¹ᵁ V ⊓ V.ι ⁻¹ᵁ W) inf_le_right).hom :=
    have := V.ι.isIso_app W (by simpa)
    bijective_appLE_of_eq V.ι (inf_eq_right.mpr (V.ι.preimage_mono h))
      (ConcreteCategory.bijective_of_isIso _)
  rw [← h2.of_comp_iff']
  convert hb.comp h1 using 1
  funext s
  exact appLE_res_apply V.ι h _ s
end GlobalTheory
