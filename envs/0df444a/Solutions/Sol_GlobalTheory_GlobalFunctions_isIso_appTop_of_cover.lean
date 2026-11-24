-- Prove2me | solution 1 for GlobalTheory.GlobalFunctions.isIso_appTop_of_cover
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T20:45:37.799526+00:00
-- url     : https://prove2.me/submissions/247a4166-3b70-4799-8878-38fe0e92f589

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_SecBaseChangeAnySt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_ExistsFiniteProjectiveComplexQuasiIso
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_IsIsoAppTopOfIsPullbackOfSurjective
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_ExistsAppTopEqOfEffectiveEpi
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_IsIsoAppTopOfIsAffine
import Theorems.Thm_GlobalTheory_GlobalFunctions_eq_zero_of_fibres
import Theorems.Thm_GlobalTheory_GlobalFunctions_appTop_comp_eq
import Theorems.Thm_GlobalTheory_GlobalFunctions_eq_zero_fibre
import Theorems.Thm_GlobalTheory_FlatDescent_injective_appTop_of_epi


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi
open TensorProduct
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory
open GlobalTheory.GlobalFunctions
variable {R B C : Type} [CommRing R] [CommRing B] [CommRing C] [Algebra R B] [Algebra R C]
  {X : Scheme.{0}}
namespace GlobalTheory.GlobalFunctions
theorem _root_.solution (hI : FibreInjective) (hD : SmoothDescent)
    [Algebra.Smooth R B] [Algebra.Smooth R C]
    (p : X ⟶ Spec (.of R)) [UniversallyClosed p] [GeometricallyIntegral p]
    (i : Spec (.of B) ⟶ X) [Flat i] [Surjective i] [QuasiCompact i] (f g : B →ₐ[R] C)
    (H : IsPullback (Spec.map (CommRingCat.ofHom f.toRingHom))
      (Spec.map (CommRingCat.ofHom g.toRingHom)) i i)
    (hφ : i ≫ p = Spec.map (CommRingCat.ofHom (algebraMap R B))) (r : B →ₐ[R] R) :
    IsIso p.appTop := by
  let u := i.appTop ≫ (Scheme.ΓSpecIso (.of B)).hom
  have h1 : ∀ c, u (p.appTop c) = algebraMap R B ((Scheme.ΓSpecIso (.of R)).hom c) :=
    fun c ↦ congr($(appTop_comp_eq hφ) c)
  have hu : Function.Injective u := by
    have h := FlatDescent.injective_appTop_of_epi i
    exact (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (.of B)).hom).1.comp h
  refine (ConcreteCategory.isIso_iff_bijective _).mpr ⟨fun a b hab ↦ ?_, fun a ↦ ?_⟩
  · have h2 := (h1 a).symm.trans ((congrArg u hab).trans (h1 b))
    have h3 := congrArg r h2
    rw [r.commutes, r.commutes] at h3
    exact (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (.of R)).hom).1 h3
  · have hfg : u ≫ CommRingCat.ofHom f.toRingHom = u ≫ CommRingCat.ofHom g.toRingHom := by
      simp only [u, Category.assoc]
      rw [← Scheme.ΓSpecIso_naturality, ← Scheme.ΓSpecIso_naturality, ← Category.assoc,
        ← Category.assoc, ← Scheme.Hom.comp_appTop, ← Scheme.Hom.comp_appTop, H.w]
    have hfg' : f (u a) = g (u a) := congr($hfg a)
    have h2 := eq_zero_of_fibres hI hD f g r (eq_zero_fibre p i f g H hφ r)
      (u a - algebraMap R B (r (u a)))
      (by rw [map_sub, map_sub, hfg', f.commutes, g.commutes])
      (by rw [map_sub, r.commutes]; exact sub_self _)
    refine ⟨(Scheme.ΓSpecIso (.of R)).inv (r (u a)), hu ?_⟩
    rw [h1, Iso.inv_hom_id_apply]
    exact (sub_eq_zero.mp h2).symm
end GlobalTheory.GlobalFunctions
