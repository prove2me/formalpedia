-- Prove2me | solution 1 for GlobalTheory.BaseChangeFns.app_surjective
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T12:16:09.0928+00:00
-- url     : https://prove2.me/submissions/c898883b-97ca-4743-a12a-fcd3435a5786

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_HeckeKer
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_AppTopSurjective
import Theorems.Thm_GlobalTheory_BaseChangeFns_appTop_surjective
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
noncomputable section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
namespace GlobalTheory.BaseChangeFns
private theorem surjective_of_comp_surjective_of_injective {A B C : CommRingCat} (g : A ⟶ B) (m : B ⟶ C)
    (hm : Function.Injective m.hom) (h : Function.Surjective (g ≫ m).hom) : Function.Surjective g.hom := by
  intro y
  obtain ⟨x, hx⟩ := h (m.hom y)
  exact ⟨x, hm hx⟩
private theorem injective_presheaf_map_eqToHom {X : Scheme.{0}} {V W : X.Opens} (p : V = W) :
    Function.Injective (X.presheaf.map (eqToHom p).op).hom := by
  subst p
  first
  | (intro a b hab; simpa using hab)
  | (simp only [eqToHom_refl, op_id, Functor.map_id, CommRingCat.hom_id]; exact Function.injective_id)
end GlobalTheory.BaseChangeFns
end
end

set_option autoImplicit false
noncomputable section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory GlobalTheory.BaseChangeFns
namespace GlobalTheory.BaseChangeFns
theorem _root_.solution : Out.GlobalFnsSt → ∀ (S₀ : Scheme.{0}) (B : Over S₀) [GrpObj B], IsAbelianScheme B → ∀ (S X : Scheme.{0}) (t : S ⟶ S₀) (π : X ⟶ B.left) (f : X ⟶ S), IsPullback π f B.hom t → ∀ U : S.Opens, Function.Surjective (f.app U).hom := by
  intro hG S₀ B _ hB S X t π f h U
  have hP : IsPullback ((f ⁻¹ᵁ U).ι ≫ π) (f ∣_ U) B.hom (U.ι ≫ t) :=
    (isPullback_morphismRestrict f U).flip.paste_horiz h
  have hres := appTop_surjective hG hB hP
  rw [morphismRestrict_appTop] at hres
  have hV := surjective_of_comp_surjective_of_injective _ _ (injective_presheaf_map_eqToHom _) hres
  change Function.Surjective (f.app (U.ι ''ᵁ ⊤)).hom at hV
  rwa [Scheme.Opens.ι_image_top] at hV
end GlobalTheory.BaseChangeFns
