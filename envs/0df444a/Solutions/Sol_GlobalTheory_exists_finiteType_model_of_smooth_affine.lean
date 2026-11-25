-- Prove2me | solution 1 for GlobalTheory.exists_finiteType_model_of_smooth_affine
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T15:05:54.410903+00:00
-- url     : https://prove2.me/submissions/fe912fa4-9578-4160-92ae-a85eef44d122

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CubicalLineBundles_MorphismsSpreadOutToFgSubalgebra
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_ExistsFiniteTypeModelOfSmoothAffine
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_LBIso_symm
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_LBIso_trans


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
namespace GlobalTheory
theorem _root_.solution :
    ∀ (V : Type) [CommRing V] (X : Scheme.{0}) (p : X ⟶ Sp V), IsAffine X → Smooth p → ∃ (R : Type) (_ : CommRing R) (f : R →+* V) (X₀ : Scheme.{0}) (p₀ : X₀ ⟶ Sp R) (φ : X ⟶ X₀), Algebra.FiniteType ℤ R ∧ Smooth p₀ ∧ IsAffine X₀ ∧ IsPullback φ p p₀ (spMap f) := by
  intro V _ X p _ _
  let B : CommRingCat.{0} := Γ(X, ⊤)
  let g : CommRingCat.of V ⟶ B := (Scheme.Spec.preimage (X.isoSpec.inv ≫ p)).unop
  have hg : Spec.map g = X.isoSpec.inv ≫ p := Scheme.Spec.map_preimage _
  have hpg : p = X.isoSpec.hom ≫ Spec.map g := by rw [hg, Iso.hom_inv_id_assoc]
  have hsg : Smooth (Spec.map g) := by rw [hg]; infer_instance
  have hgs : g.hom.Smooth := (HasRingHomProperty.Spec_iff (P := @Smooth)).mp hsg
  let _ : Algebra V B := g.hom.toAlgebra
  have : Algebra.Smooth V B := hgs
  obtain ⟨A₀, B₀, _, _, hA₀, hsm, ⟨ψe⟩⟩ := Algebra.Smooth.exists_subalgebra_fg ℤ V B
  let T : CommRingCat.{0} := CommRingCat.of (TensorProduct A₀ V B₀)
  let inl : CommRingCat.of V ⟶ T := CommRingCat.ofHom Algebra.TensorProduct.includeLeftRingHom
  let inr : CommRingCat.of B₀ ⟶ T :=
    CommRingCat.ofHom (Algebra.TensorProduct.includeRight (R := A₀) (A := V)).toRingHom
  let jIso : T ≅ B :=
    { hom := CommRingCat.ofHom ψe.symm.toRingHom
      inv := CommRingCat.ofHom ψe.toRingHom
      hom_inv_id := CommRingCat.hom_ext (RingHom.ext fun x => ψe.apply_symm_apply x)
      inv_hom_id := CommRingCat.hom_ext (RingHom.ext fun x => ψe.symm_apply_apply x) }
  have hj : inl ≫ jIso.hom = g := by
    ext v
    exact ψe.symm.commutes v
  have hpb := (isPullback_SpecMap_of_isPushout _ _ _ _
    (CommRingCat.isPushout_tensorProduct A₀ V B₀)).flip
  let e : X ≅ Spec T := X.isoSpec ≪≫ Scheme.Spec.mapIso jIso.op
  refine ⟨A₀, inferInstance, algebraMap A₀ V, Spec (CommRingCat.of B₀),
    Spec.map (CommRingCat.ofHom (algebraMap A₀ B₀)), e.hom ≫ Spec.map inr, ?_, ?_,
    inferInstance, ?_⟩
  · convert (Subalgebra.fg_iff_finiteType A₀).mp hA₀
  · exact (HasRingHomProperty.Spec_iff (P := @Smooth)).mpr (RingHom.smooth_algebraMap.mpr hsm)
  · refine IsPullback.of_iso hpb e.symm (Iso.refl _) (Iso.refl _) (Iso.refl _) ?_ ?_ ?_ ?_
    · rw [Iso.refl_hom, Category.comp_id, Iso.symm_hom, Iso.inv_hom_id_assoc]
    · rw [Iso.refl_hom, Category.comp_id, Iso.symm_hom, Iso.eq_inv_comp, hpg]
      change (X.isoSpec.hom ≫ Spec.map jIso.hom) ≫ Spec.map inl = _
      rw [Category.assoc, ← Spec.map_comp, hj]
    · exact (Category.comp_id _).trans (Category.id_comp _).symm
    · exact (Category.comp_id _).trans (Category.id_comp _).symm
end GlobalTheory
