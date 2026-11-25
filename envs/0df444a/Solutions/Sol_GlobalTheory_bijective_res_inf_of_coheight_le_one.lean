-- Prove2me | solution 1 for GlobalTheory.bijective_res_inf_of_coheight_le_one
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T01:41:35.351958+00:00
-- url     : https://prove2.me/submissions/60d477e0-7ce5-4e93-9543-f7a228981c9a

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_MemRangeOfForallHeightEqOneOfIsReflexive
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ShimuraVarieties_IsOpenOfMemIrreducibleComponentsOfFinite
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsGrpPullback
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SemiabelianSchemes_PrecompleteBases_PsbLb
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_ProdIso
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_ExistsUniqueLbIsoPullEqOfCoheightLeOne
import Theorems.Thm_GlobalTheory_bijective_app_iff_of_isOpenImmersion
import Theorems.Thm_GlobalTheory_bijective_app_of_coheight_le_one
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
theorem _root_.solution [IsLocallyNoetherian X] [IsNormalScheme X]
    {U : X.Opens} (hU : ∀ x : X, Order.coheight x ≤ 1 → x ∈ U) (V : X.Opens) :
    Function.Bijective (X.presheaf.map (homOfLE (inf_le_left : V ⊓ U ≤ V)).op).hom := by
  have := (bijective_app_iff_of_isOpenImmersion U.ι V).mp
    (bijective_app_of_coheight_le_one U.ι (fun x hx ↦ by simpa using hU x hx) V)
  have key : ∀ U' : X.Opens, U' = U → Function.Bijective
      (X.presheaf.map (homOfLE (inf_le_left : V ⊓ U' ≤ V)).op).hom → Function.Bijective
      (X.presheaf.map (homOfLE (inf_le_left : V ⊓ U ≤ V)).op).hom := by
    rintro _ rfl h
    exact h
  exact key _ U.opensRange_ι this
end GlobalTheory
