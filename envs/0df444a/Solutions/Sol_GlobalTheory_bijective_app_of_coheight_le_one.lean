-- Prove2me | solution 1 for GlobalTheory.bijective_app_of_coheight_le_one
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T01:32:38.042934+00:00
-- url     : https://prove2.me/submissions/d69b95e3-03a3-43ff-8737-829dd4f7ea98

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_MemRangeOfForallHeightEqOneOfIsReflexive
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ShimuraVarieties_IsOpenOfMemIrreducibleComponentsOfFinite
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsGrpPullback
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SemiabelianSchemes_PrecompleteBases_PsbLb
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_ProdIso
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_ExistsUniqueLbIsoPullEqOfCoheightLeOne
import Theorems.Thm_GlobalTheory_coheight_apply_of_isOpenImmersion
import Theorems.Thm_GlobalTheory_coheight_genericPoint
import Theorems.Thm_GlobalTheory_bijective_app_of_coheight_eq_one
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
    (f : Y ⟶ X) [IsOpenImmersion f]
    (hf : ∀ x : X, Order.coheight x ≤ 1 → x ∈ Set.range f) (V : X.Opens) :
    Function.Bijective (f.app V).hom := by
  let B : (Σ Z : irreducibleComponents X, (IsNormalScheme.component Z).toScheme.Opens) → X.Opens :=
    fun p ↦ (IsNormalScheme.component p.1).ι ''ᵁ p.2
  have hB : Opens.IsBasis (Set.range B) := by
    rw [Opens.isBasis_iff_nbhd]
    intro O x hx
    let Z : irreducibleComponents X := ⟨_, irreducibleComponent_mem_irreducibleComponents x⟩
    refine ⟨_, ⟨⟨Z, (IsNormalScheme.component Z).ι ⁻¹ᵁ O⟩, rfl⟩,
      ⟨⟨x, mem_irreducibleComponent⟩, hx, rfl⟩, Scheme.Hom.image_preimage_le _ _⟩
  let φ : X.sheaf ⟶ (TopCat.Sheaf.pushforward CommRingCat f.base).obj Y.sheaf := ⟨f.c⟩
  have hφ : IsIso φ := by
    refine TopCat.Sheaf.isIso_iff_isIso_basis hB fun ⟨Z, O⟩ ↦ ?_
    have hf' : ∀ x : (IsNormalScheme.component Z).toScheme, Order.coheight x ≤ 1 →
        x ∈ Set.range (f ∣_ IsNormalScheme.component Z) := fun x hx ↦ by
      obtain ⟨y, hy⟩ := hf ((IsNormalScheme.component Z).ι x)
        (by rwa [coheight_apply_of_isOpenImmersion])
      refine ⟨⟨y, ?_⟩, Subtype.ext ?_⟩
      · change f y ∈ IsNormalScheme.component Z
        rw [hy]
        exact x.2
      · exact (morphismRestrict_base_coe f _ _).trans hy
    have : Nonempty (f ⁻¹ᵁ IsNormalScheme.component Z).toScheme := by
      obtain ⟨y, -⟩ := hf' (genericPoint _) (by simp [coheight_genericPoint])
      exact ⟨y⟩
    have hb := bijective_app_of_coheight_eq_one (f ∣_ IsNormalScheme.component Z)
      (fun x hx ↦ hf' x hx.le) O
    have : IsIso ((f ∣_ IsNormalScheme.component Z).app O) :=
      (ConcreteCategory.isIso_iff_bijective _).mpr hb
    rw [morphismRestrict_app] at this
    exact (@isIso_comp_right_iff _ _ _ _ _ (f.app _) _ (Functor.map_isIso Y.presheaf _)).mp this
  have : IsIso f.c := @Functor.map_isIso _ _ _ _ _ _ (sheafToPresheaf _ _) φ hφ
  exact ConcreteCategory.bijective_of_isIso (f.c.app (op V))
end GlobalTheory
