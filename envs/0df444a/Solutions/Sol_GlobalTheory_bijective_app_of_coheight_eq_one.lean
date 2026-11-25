-- Prove2me | solution 1 for GlobalTheory.bijective_app_of_coheight_eq_one
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T01:22:42.101458+00:00
-- url     : https://prove2.me/submissions/2ddc136e-f3ba-4733-a77c-1929214f6d0a

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_MemRangeOfForallHeightEqOneOfIsReflexive
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ShimuraVarieties_IsOpenOfMemIrreducibleComponentsOfFinite
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsGrpPullback
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SemiabelianSchemes_PrecompleteBases_PsbLb
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_ProdIso
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_ExistsUniqueLbIsoPullEqOfCoheightLeOne
import Theorems.Thm_GlobalTheory_genericPoint_mem_opens
import Theorems.Thm_GlobalTheory_bijective_res_of_eq_bot
import Theorems.Thm_GlobalTheory_bijective_res_of_coheight_eq_one
import Theorems.Thm_GlobalTheory_bijective_app_iff_of_isOpenImmersion
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
theorem _root_.solution [IsIntegral X] [IsLocallyNoetherian X] [IsNormalScheme X]
    (f : Y ⟶ X) [IsOpenImmersion f] [Nonempty Y]
    (hf : ∀ x : X, Order.coheight x = 1 → x ∈ Set.range f) (V : X.Opens) :
    Function.Bijective (f.app V).hom := by
  rw [bijective_app_iff_of_isOpenImmersion]
  by_cases hV : V = ⊥
  · exact bijective_res_of_eq_bot _ hV
  have : Nonempty V := ((Opens.ne_bot_iff_nonempty _).mp hV).to_subtype
  have : Nonempty f.opensRange := ⟨⟨f (Nonempty.some inferInstance), _, rfl⟩⟩
  have : Nonempty (V ⊓ f.opensRange : X.Opens) :=
    ⟨⟨_, genericPoint_mem_opens V, genericPoint_mem_opens f.opensRange⟩⟩
  exact bijective_res_of_coheight_eq_one _ fun x hx h1 ↦ ⟨hx, hf x h1⟩
end GlobalTheory
