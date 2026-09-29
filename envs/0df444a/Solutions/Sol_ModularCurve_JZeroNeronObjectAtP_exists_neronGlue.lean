-- Prove2me | solution 1 for ModularCurve.JZeroNeronObjectAtP.exists_neronGlue
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:10.583295+00:00
-- url     : https://prove2.me/submissions/21b5c039-dfdd-5616-8f28-55ba627ef4dd

import Mathlib
import Definitions.Def_ModularCurve_JZeroNeronObjectAtP_NeronExtension
import Definitions.Def_AlgebraicGeometry_RelativeGroupLaw
import Definitions.Def_AlgebraicGeometry_NeronModelEndomorphismExtension
import Definitions.Def_AlgebraicGeometry_MazurRapoportAppendixGenericFibreOpenImmersionDVR
import Theorems.Thm_GoodReductionJacobian_RelativeGroupLaw_exists_iso_hom_comp_eq_and_comp_hom_eq_mul
import Theorems.Thm_AlgebraicGeometry_Scheme_exists_specMap_fixedField_comp_eq_of_forall_comp_eq
import Theorems.Thm_ValuationSubring_isDiscreteValuationRing_comap_fixedField_inertiaSubgroupIn
import Theorems.Thm_ModularCurve_finite_componentGroup_of_pos
import Theorems.Thm_NeronModelInfra_genericFibreRestrict_injective_of_flat_of_isSeparated
import Theorems.Thm_AlgebraicGeometry_locallyOfFiniteType_and_quasiCompact_of_finite_openCover
import Theorems.Thm_ModularCurve_JZeroNeronObjectAtP_comp_eq_zero_iff_exists_schemeHomOver_shGenLift_eq
import Theorems.Thm_AlgebraicGeometry_Scheme_exists_isOpenImmersion_isPullback_of_glue_cocycle
import Theorems.Thm_AlgebraicGeometry_IsSeparated_of_isClosedImmersion_mapDesc_openCover
import Theorems.Thm_GoodReductionJacobian_RelativeGroupLaw_isClosedImmersion_lift_fst_mul_of_not_exists_section
import Theorems.Thm_GoodReductionJacobian_RelativeGroupLaw_exists_relativeGroupLaw_glued_charts_mul_eq
import Theorems.Thm_ModularCurve_JZeroNeronObjectAtP_exists_inertiaInvariants_to_schemeHomOver_specGenericFibreInclusion_bijective
import Theorems.Thm_GoodReductionJacobian_RelativeGroupLaw_exists_spec_glued_charts
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_JZeroNeronObjectAtP_exists_neronGlue
p2m_attr_erase "simp" "ModularCurve.coordOf_apply ModularCurve.coordOfEquiv_apply ModularCurve.diffChar_coe_apply ModularCurve.gramRangeBasisOf_coe ModularCurve.gramMatrixOf_apply"

set_option autoImplicit false

universe u v

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian ModularCurve IsLocalRing AlgebraicCurve ModularCurve.JZeroNeronObjectAtP

namespace NeronGlueAux

theorem reps_aux {M Φ : Type*} [AddCommGroup M] [AddCommGroup Φ] (f : M →+ Φ) (hf : Function.Surjective f) :
    ∃ y' : Φ → M, (∀ φ, f (y' φ) = φ) ∧ y' 0 = 0 := by
  refine ⟨fun φ => Function.surjInv hf φ - Function.surjInv hf 0, fun φ => ?_, sub_self _⟩
  rw [map_sub, Function.surjInv_eq hf, Function.surjInv_eq hf, sub_zero]

theorem cocycle_aux {M Φ : Type*} [AddCommGroup M] [AddCommGroup Φ] (f : M →+ Φ) (y' : Φ → M)
    (hy : ∀ φ, f (y' φ) = φ) (φ ψ : Φ) : f (y' φ + y' ψ - y' (φ + ψ)) = 0 := by
  rw [map_sub, map_add, hy, hy, hy]; exact sub_self _

end NeronGlueAux

namespace NeronGlueAux
open CategoryTheory AlgebraicGeometry NeronModelInfra
universe w

theorem chart_congr {S X N : Scheme.{w}} {f : X ⟶ S} {gN : N ⟶ S} {ι : Type*} (e : ι → (X ⟶ N))
    (hef : ∀ i, e i ≫ gN = f) {i j : ι} (h : i = j) {T : Scheme.{w}} {s : T ⟶ S} (a : SchemeHomOver s f) :
    NeronModelInfra.schemeHomOverComp a ⟨e i, hef i⟩ = NeronModelInfra.schemeHomOverComp a ⟨e j, hef j⟩ := by
  subst h; rfl
end NeronGlueAux

namespace NeronGlueAux
private theorem _root_.NeronGlueAux.sub_aux {M Φ : Type*} [AddCommGroup M] [AddCommGroup Φ] (f : M →+ Φ) (y' : Φ → M)
    (hy : ∀ φ, f (y' φ) = φ) (φ ψ : Φ) : f (y' φ - y' ψ) = φ - ψ := by
  rw [map_sub, hy, hy]
p2m_export "NeronGlueAux" "sub_aux"
theorem eq_add_of_sub_eq_aux {M Φ : Type*} [AddCommGroup M] [AddCommGroup Φ] (f : M →+ Φ) (y' : Φ → M)
    (hy : ∀ φ, f (y' φ) = φ) (x : M) (φ : Φ) (h : f (x - y' φ) = 0) : f x = φ := by
  rwa [map_sub, hy, sub_eq_zero] at h
end NeronGlueAux

namespace NeronGlueAux
namespace SepTransport

theorem isClosedImmersion_mapDesc_of_isOpenImmersion {S X N : Scheme.{u}} (f : X ⟶ S) [IsSeparated f]
    (gN : N ⟶ S) (e : X ⟶ N) [IsOpenImmersion e] (hef : e ≫ gN = f) :
    IsClosedImmersion (pullback.mapDesc e e gN) := by
  haveI : IsSeparated (e ≫ gN) := by rw [hef]; infer_instance
  haveI : IsClosedImmersion (pullback.diagonal (e ≫ gN)) := IsSeparated.isClosedImmersion_diagonal
  have heq : pullback.mapDesc e e gN = pullback.fst e e ≫ pullback.diagonal (e ≫ gN) := by
    delta pullback.mapDesc pullback.map
    apply pullback.hom_ext
    · simp only [pullback.lift_fst, Category.comp_id, Category.assoc, pullback.diagonal_fst]
    · simp only [pullback.lift_snd, Category.comp_id, Category.assoc, pullback.diagonal_snd, fst_eq_snd_of_mono_eq]
  rw [heq]
  infer_instance

theorem isClosedImmersion_mapDesc_of_isPullback {S X N U : Scheme.{u}} (f : X ⟶ S) (gN : N ⟶ S)
    (e₁ e₂ : X ⟶ N) (hef₁ : e₁ ≫ gN = f) (hef₂ : e₂ ≫ gN = f) (j : U ⟶ X) (τ : U ⟶ U)
    (sq : IsPullback j (τ ≫ j) e₁ e₂)
    (h : IsClosedImmersion (pullback.lift j (τ ≫ j)
      (by simpa only [Category.assoc, hef₁, hef₂] using congrArg (· ≫ gN) sq.w : j ≫ f = (τ ≫ j) ≫ f) :
        U ⟶ pullback f f)) :
    IsClosedImmersion (pullback.mapDesc e₁ e₂ gN) := by
  have hw : j ≫ f = (τ ≫ j) ≫ f := by simpa only [Category.assoc, hef₁, hef₂] using congrArg (· ≫ gN) sq.w
  have heq : sq.isoPullback.hom ≫ pullback.mapDesc e₁ e₂ gN ≫ (pullback.congrHom hef₁ hef₂).hom =
      pullback.lift j (τ ≫ j) hw := by
    delta pullback.mapDesc pullback.map pullback.congrHom
    apply pullback.hom_ext
    · simp only [asIso_hom, Category.assoc, pullback.lift_fst, Category.comp_id,
        IsPullback.isoPullback_hom_fst]
    · simp only [asIso_hom, Category.assoc, pullback.lift_snd, Category.comp_id,
        IsPullback.isoPullback_hom_snd]
  have h' : IsClosedImmersion (sq.isoPullback.hom ≫ pullback.mapDesc e₁ e₂ gN ≫ (pullback.congrHom hef₁ hef₂).hom) := by
    rw [heq]; exact h
  exact (MorphismProperty.cancel_right_of_respectsIso @IsClosedImmersion _ _).mp
    ((MorphismProperty.cancel_left_of_respectsIso @IsClosedImmersion _ _).mp h')

theorem exists_eq_of_mem_range_of_isPullback {X N U : Scheme.{u}} (e₁ e₂ : X ⟶ N) (j : U ⟶ X) (τ : U ⟶ U)
    (sq : IsPullback j (τ ≫ j) e₁ e₂) (n : N) (h₁ : n ∈ Set.range e₁.base) (h₂ : n ∈ Set.range e₂.base) :
    ∃ u : U, e₁.base (j.base u) = n := by
  obtain ⟨x₁, hx₁⟩ := h₁
  obtain ⟨x₂, hx₂⟩ := h₂
  obtain ⟨z, hz₁, -⟩ := Scheme.Pullback.exists_preimage_pullback (f := e₁) (g := e₂) x₁ x₂ (hx₁.trans hx₂.symm)
  refine ⟨sq.isoPullback.inv.base z, ?_⟩
  have hj : j.base (sq.isoPullback.inv.base z) = (pullback.fst e₁ e₂).base z := by
    rw [← Scheme.Hom.comp_apply, sq.isoPullback_inv_fst]
  rw [hj]
  change e₁.base ((pullback.fst e₁ e₂).base z) = n
  rw [hz₁, hx₁]

end NeronGlueAux.SepTransport

namespace NeronGlueAux
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra

theorem exists_pt_eq_comp_chart
    {R : Type u} [CommRing R] {K : Type u} [Field K] [Algebra R K]
    {G : Scheme.{u}} {f : G ⟶ Spec (CommRingCat.of R)} {Φ : Type u} {N : Scheme.{u}}
    (e : Φ → (G ⟶ N))
    (t : Φ → Φ → (pullback f (Spec.map (CommRingCat.ofHom (algebraMap R K))) ≅
      pullback f (Spec.map (CommRingCat.ofHom (algebraMap R K)))))
    (gN : N ⟶ Spec (CommRingCat.of R)) (hef : ∀ φ, e φ ≫ gN = f)
    (hpb : ∀ φ ψ, φ ≠ ψ →
      IsPullback (pullback.fst f (Spec.map (CommRingCat.ofHom (algebraMap R K))))
        ((t φ ψ).hom ≫ pullback.fst f (Spec.map (CommRingCat.ofHom (algebraMap R K)))) (e φ) (e ψ))
    [∀ φ, IsOpenImmersion (e φ)] (hecov : (⋃ φ, Set.range (e φ).base) = Set.univ) (χ : Φ)
    {T : Scheme.{u}} (σ : T ⟶ Spec (CommRingCat.of K))
    (u : SchemeHomOver (σ ≫ Spec.map (CommRingCat.ofHom (algebraMap R K))) gN) :
    ∃ a : SchemeHomOver (σ ≫ Spec.map (CommRingCat.ofHom (algebraMap R K))) f,
      u = NeronModelInfra.schemeHomOverComp a ⟨e χ, hef χ⟩ := by
  have hrange : Set.range u.1.base ⊆ Set.range (e χ).base := by
    rintro _ ⟨x, rfl⟩
    have hgx : gN (u.1 x) = (Spec.map (CommRingCat.ofHom (algebraMap R K))) (σ x) := by
      rw [← Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply, u.2]
    have hx : u.1 x ∈ ⋃ φ, Set.range (e φ).base := by rw [hecov]; trivial
    obtain ⟨ψ, g, hg⟩ := Set.mem_iUnion.mp hx
    have hfg : g ∈ Set.range (pullback.fst f (Spec.map (CommRingCat.ofHom (algebraMap R K)))).base := by
      rw [Scheme.Pullback.range_fst]
      refine ⟨σ x, ?_⟩
      change _ = f g
      rw [← hef ψ, Scheme.Hom.comp_apply, hg, hgx]
    obtain ⟨z, hz⟩ := hfg
    by_cases hψχ : ψ = χ
    · subst hψχ; exact ⟨g, hg⟩
    · refine ⟨((t ψ χ).hom ≫ pullback.fst f (Spec.map (CommRingCat.ofHom (algebraMap R K)))) z, ?_⟩
      change ((t ψ χ).hom ≫ pullback.fst f _ ≫ e χ) z = u.1 x
      rw [← Category.assoc, ← (hpb ψ χ hψχ).w, Scheme.Hom.comp_apply, hz, hg]
  refine ⟨⟨IsOpenImmersion.lift (e χ) u.1 hrange, ?_⟩, Subtype.ext (IsOpenImmersion.lift_fac _ _ _).symm⟩
  rw [← hef χ, ← Category.assoc, IsOpenImmersion.lift_fac]
  exact u.2

end NeronGlueAux

namespace NeronGlueAux
theorem cocycle_aux2 {M Φ : Type*} [AddCommGroup M] [AddCommGroup Φ] (f : M →+ Φ) (y' : Φ → M)
    (hy : ∀ φ, f (y' φ) = φ) :
    ∃ v : Φ → Φ → M, (∀ φ ψ, f (v φ ψ) = 0) ∧ ∀ φ ψ, v φ ψ = y' φ + y' ψ - y' (φ + ψ) :=
  ⟨fun φ ψ => y' φ + y' ψ - y' (φ + ψ), fun φ ψ => cocycle_aux f y' hy φ ψ, fun _ _ => rfl⟩
end NeronGlueAux

namespace NeronGlueAux
theorem hom_aux {M P : Type*} [AddCommGroup M] [Group P] (g : M → P) (hg : ∀ u v, g (u + v) = g u * g v)
    (v a b c : M) (hv : v = a + b - c) : g v = g a * g b * (g c)⁻¹ := by
  subst hv
  have h1 : g (a + b - c) * g c = g a * g b := by rw [← hg, sub_add_cancel, hg]
  exact eq_mul_inv_of_mul_eq h1
private theorem _root_.NeronGlueAux.hom_sub_aux {M P : Type*} [AddCommGroup M] [Group P] (g : M → P) (hg : ∀ u v, g (u + v) = g u * g v)
    (a b : M) : g (a - b) = g a * (g b)⁻¹ := by
  have h1 : g (a - b) * g b = g a := by rw [← hg, sub_add_cancel]
  exact eq_mul_inv_of_mul_eq h1
p2m_export "NeronGlueAux" "hom_sub_aux"
private theorem _root_.NeronGlueAux.hom_zero_aux {M P : Type*} [AddCommGroup M] [Group P] (g : M → P) (hg : ∀ u v, g (u + v) = g u * g v) :
    g 0 = 1 := by
  have h00 : g (0 + 0) = g 0 * g 0 := hg 0 0
  rw [add_zero] at h00
  exact mul_eq_left.mp h00.symm
p2m_export "NeronGlueAux" "hom_zero_aux"
end NeronGlueAux

namespace NeronGlueAux

namespace Hext
private theorem _root_.NeronGlueAux.Hext.sub_aux {M Φ : Type*} [AddCommGroup M] [AddCommGroup Φ] (f : M →+ Φ) (y' : Φ → M)
    (hy : ∀ φ, f (y' φ) = φ) (z w : M) (hw : w = z - y' (f z)) : f w = 0 := by
  subst hw; rw [map_sub, hy, sub_self]

end Hext
p2m_export "NeronGlueAux" "Hext.sub_aux"
namespace Hext
private theorem _root_.NeronGlueAux.Hext.hom_sub_aux {M P : Type*} [AddCommGroup M] [Group P] (g : M → P) (hg : ∀ u v, g (u + v) = g u * g v)
    (a b w : M) (hw : w = a - b) : g w = g a * (g b)⁻¹ := by
  subst hw
  have h1 : g (a - b) * g b = g a := by rw [← hg, sub_add_cancel]
  exact eq_mul_inv_of_mul_eq h1

end Hext
p2m_export "NeronGlueAux" "Hext.hom_sub_aux"

theorem Hext.eq_one_mul {R : Type} [CommRing R] {X T : Scheme.{0}} {f : X ⟶ Spec (CommRingCat.of R)}
    (G : RelativeGroupLaw R f) {t : T ⟶ Spec (CommRingCat.of R)} (o q : SchemeHomOver t f) (ho : o = G.one t) :
    q = G.mul t o q := by
  subst ho; exact (G.one_mul t q).symm

namespace Hext
private theorem _root_.NeronGlueAux.Hext.hom_zero_aux {M P : Type*} [AddCommGroup M] [Group P] (g : M → P) (hg : ∀ u v, g (u + v) = g u * g v) :
    g 0 = 1 := by
  have h00 : g (0 + 0) = g 0 * g 0 := hg 0 0
  rw [add_zero] at h00
  exact mul_eq_left.mp h00.symm

end Hext
p2m_export "NeronGlueAux" "Hext.hom_zero_aux"
theorem hext_aux
    (N₀ p : ℕ) [NeZero N₀] [Fact p.Prime] [NeZero p] (hpN₀ : ¬ p ∣ N₀)
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime p)
    (Λ : JZeroNeronObjectAtP.LevelData N₀ p A)
    (O : JZeroNeronObjectAtP N₀ p hpN₀ A hA Λ)
    {N : Scheme.{0}} (gN : N ⟶ shBase A)
    (e : componentGroup O.width → (RelativeGroupLaw.baseChangeScheme Λ.shStr O.g ⟶ N))
    (hef : ∀ φ, e φ ≫ gN = RelativeGroupLaw.baseChangeStr Λ.shStr O.g)
    (yK : ↥(inertiaInvariants A (N₀ * p)) →
      SchemeHomOver (specGenericFibreInclusion ↥(shRing A) ↥(invField A)) (RelativeGroupLaw.baseChangeStr Λ.shStr O.g))
    (hyK_add : ∀ x x', yK (x + x') =
      (O.L.baseChange Λ.shStr).mul (specGenericFibreInclusion ↥(shRing A) ↥(invField A)) (yK x) (yK x'))
    (hyK_bij : Function.Bijective yK)
    (y' : componentGroup O.width → ↥(inertiaInvariants A (N₀ * p))) (hy'comp : ∀ φ, O.comp (y' φ) = φ) (hy'0 : y' 0 = 0)
    (y : componentGroup O.width →
      SchemeHomOver (specGenericFibreInclusion ↥(shRing A) ↥(invField A)) (RelativeGroupLaw.baseChangeStr Λ.shStr O.g))
    (hy : ∀ φ, y φ = yK (y' φ))
    (hbar : Spec.map (CommRingCat.ofHom (algebraMap ↥(invField A) (AlgebraicClosure ℚ))) ≫
        specGenericFibreInclusion ↥(shRing A) ↥(invField A) = barPt A ≫ shPt A)
    (key : ∀ (P : SchemeHomOver (specGenericFibreInclusion ↥(shRing A) ↥(invField A))
        (RelativeGroupLaw.baseChangeStr Λ.shStr O.g)) (v : ↥(inertiaInvariants A (N₀ * p))),
      Spec.map (CommRingCat.ofHom (algebraMap ↥(invField A) (AlgebraicClosure ℚ))) ≫ P.1 =
        (Λ.shGenLift (O.pts (v : JZero (N₀ * p)))).1 → P = yK v)
    (chart_rel : ∀ (φ ψ : componentGroup O.width) {T : Scheme.{0}} (σ : T ⟶ Spec (CommRingCat.of ↥(invField A)))
        (P : SchemeHomOver (σ ≫ specGenericFibreInclusion ↥(shRing A) ↥(invField A))
          (RelativeGroupLaw.baseChangeStr Λ.shStr O.g)),
      P.1 ≫ e φ =
        ((O.L.baseChange Λ.shStr).mul (σ ≫ specGenericFibreInclusion ↥(shRing A) ↥(invField A)) P
          (GoodReductionJacobian.schemeHomOverComp σ rfl
            ((O.L.baseChange Λ.shStr).mul (specGenericFibreInclusion ↥(shRing A) ↥(invField A)) (y φ)
              ((O.L.baseChange Λ.shStr).inv (specGenericFibreInclusion ↥(shRing A) ↥(invField A)) (y ψ))))).1 ≫ e ψ)
    (hchart0 : ∀ {T : Scheme.{0}} (σ : T ⟶ Spec (CommRingCat.of ↥(invField A)))
        (u : SchemeHomOver (σ ≫ specGenericFibreInclusion ↥(shRing A) ↥(invField A)) gN),
      ∃ a : SchemeHomOver (σ ≫ specGenericFibreInclusion ↥(shRing A) ↥(invField A))
          (RelativeGroupLaw.baseChangeStr Λ.shStr O.g),
        u = NeronModelInfra.schemeHomOverComp a ⟨e 0, hef 0⟩) :
    Function.Surjective (genericFibreRestrict ↥(shRing A) ↥(invField A) gN (𝟙 (shBase A))) := by
  intro uK

  have hfst : pullback.fst (𝟙 (shBase A)) (specGenericFibreInclusion ↥(shRing A) ↥(invField A)) =
      pullback.snd (𝟙 (shBase A)) (specGenericFibreInclusion ↥(shRing A) ↥(invField A)) ≫
        specGenericFibreInclusion ↥(shRing A) ↥(invField A) := by
    have h := pullback.condition (f := 𝟙 (shBase A)) (g := specGenericFibreInclusion ↥(shRing A) ↥(invField A))
    simpa only [Category.comp_id] using h

  have hu : (uK.1 ≫ pullback.fst gN (specGenericFibreInclusion ↥(shRing A) ↥(invField A))) ≫ gN =
      pullback.snd (𝟙 (shBase A)) (specGenericFibreInclusion ↥(shRing A) ↥(invField A)) ≫
        specGenericFibreInclusion ↥(shRing A) ↥(invField A) := by
    rw [Category.assoc, pullback.condition, ← Category.assoc, uK.2]
  have ha_ex := hchart0 _ ⟨uK.1 ≫ pullback.fst gN (specGenericFibreInclusion ↥(shRing A) ↥(invField A)), hu⟩
  obtain ⟨a, ha⟩ := ha_ex
  have ha1 : uK.1 ≫ pullback.fst gN (specGenericFibreInclusion ↥(shRing A) ↥(invField A)) = a.1 ≫ e 0 :=
    congrArg Subtype.val ha

  have ha' : (inv (pullback.snd (𝟙 (shBase A)) (specGenericFibreInclusion ↥(shRing A) ↥(invField A))) ≫ a.1) ≫
      RelativeGroupLaw.baseChangeStr Λ.shStr O.g = specGenericFibreInclusion ↥(shRing A) ↥(invField A) := by
    rw [Category.assoc, a.2, IsIso.inv_hom_id_assoc]
  have hz_ex := hyK_bij.2 ⟨_, ha'⟩
  obtain ⟨z, hz⟩ := hz_ex

  have hw_ex : ∃ w : ↥(inertiaInvariants A (N₀ * p)), w = z - y' (O.comp z) := ⟨_, rfl⟩
  obtain ⟨w, hw⟩ := hw_ex
  have hcomp0 : O.comp w = 0 := Hext.sub_aux O.comp y' hy'comp z w hw
  have hC3 := (ModularCurve.JZeroNeronObjectAtP.comp_eq_zero_iff_exists_schemeHomOver_shGenLift_eq
    N₀ p hpN₀ A hA Λ O w).1 hcomp0
  obtain ⟨s₀, hs₀⟩ := hC3

  have hs₀K : (specGenericFibreInclusion ↥(shRing A) ↥(invField A) ≫ s₀.1) ≫ RelativeGroupLaw.baseChangeStr Λ.shStr O.g =
      specGenericFibreInclusion ↥(shRing A) ↥(invField A) := by
    rw [Category.assoc, s₀.2, Category.comp_id]
  have hP : (⟨_, hs₀K⟩ : SchemeHomOver (specGenericFibreInclusion ↥(shRing A) ↥(invField A))
      (RelativeGroupLaw.baseChangeStr Λ.shStr O.g)) = yK w :=
    key _ w ((Category.assoc _ _ _).symm.trans ((congrArg (· ≫ s₀.1) hbar).trans hs₀.symm))
  have hsub : yK w =
      (O.L.baseChange Λ.shStr).mul (specGenericFibreInclusion ↥(shRing A) ↥(invField A)) ⟨_, ha'⟩
        ((O.L.baseChange Λ.shStr).inv (specGenericFibreInclusion ↥(shRing A) ↥(invField A)) (y (O.comp z))) := by
    letI : Group (SchemeHomOver (specGenericFibreInclusion ↥(shRing A) ↥(invField A))
        (RelativeGroupLaw.baseChangeStr Λ.shStr O.g)) :=
      (O.L.baseChange Λ.shStr).pointGroup (specGenericFibreInclusion ↥(shRing A) ↥(invField A))
    have h := Hext.hom_sub_aux yK (fun u w => hyK_add u w) z (y' (O.comp z)) w hw
    simp only [hz, ← hy] at h
    exact h
  have hy0 : y 0 = (O.L.baseChange Λ.shStr).one (specGenericFibreInclusion ↥(shRing A) ↥(invField A)) := by
    letI : Group (SchemeHomOver (specGenericFibreInclusion ↥(shRing A) ↥(invField A))
        (RelativeGroupLaw.baseChangeStr Λ.shStr O.g)) :=
      (O.L.baseChange Λ.shStr).pointGroup (specGenericFibreInclusion ↥(shRing A) ↥(invField A))
    rw [hy, hy'0]
    exact Hext.hom_zero_aux yK (fun u w => hyK_add u w)

  refine ⟨NeronModelInfra.schemeHomOverComp s₀ ⟨e (O.comp z), hef _⟩, ?_⟩
  have e1 : specGenericFibreInclusion ↥(shRing A) ↥(invField A) ≫ s₀.1 =
      ((O.L.baseChange Λ.shStr).mul (specGenericFibreInclusion ↥(shRing A) ↥(invField A)) ⟨_, ha'⟩
        ((O.L.baseChange Λ.shStr).inv (specGenericFibreInclusion ↥(shRing A) ↥(invField A)) (y (O.comp z)))).1 :=
    (congrArg Subtype.val hP).trans (congrArg Subtype.val hsub)
  have e2 := congrArg Subtype.val ((O.L.baseChange Λ.shStr).mul_natural
    (specGenericFibreInclusion ↥(shRing A) ↥(invField A))
    (pullback.snd (𝟙 (shBase A)) (specGenericFibreInclusion ↥(shRing A) ↥(invField A)) ≫
      specGenericFibreInclusion ↥(shRing A) ↥(invField A))
    (pullback.snd (𝟙 (shBase A)) (specGenericFibreInclusion ↥(shRing A) ↥(invField A))) rfl ⟨_, ha'⟩
    ((O.L.baseChange Λ.shStr).inv (specGenericFibreInclusion ↥(shRing A) ↥(invField A)) (y (O.comp z))))
  have e3 : GoodReductionJacobian.schemeHomOverComp
      (pullback.snd (𝟙 (shBase A)) (specGenericFibreInclusion ↥(shRing A) ↥(invField A))) rfl
        (⟨_, ha'⟩ : SchemeHomOver (specGenericFibreInclusion ↥(shRing A) ↥(invField A))
          (RelativeGroupLaw.baseChangeStr Λ.shStr O.g)) = a :=
    Subtype.ext (IsIso.hom_inv_id_assoc _ _)
  simp only [e3, GoodReductionJacobian.schemeHomOverComp_coe] at e2

  have hq : (O.L.baseChange Λ.shStr).inv (specGenericFibreInclusion ↥(shRing A) ↥(invField A)) (y (O.comp z)) =
      (O.L.baseChange Λ.shStr).mul (specGenericFibreInclusion ↥(shRing A) ↥(invField A)) (y 0)
        ((O.L.baseChange Λ.shStr).inv (specGenericFibreInclusion ↥(shRing A) ↥(invField A)) (y (O.comp z))) :=
    Hext.eq_one_mul (O.L.baseChange Λ.shStr) (y 0) _ hy0
  apply Subtype.ext
  apply pullback.hom_ext
  · calc (genericFibreRestrict ↥(shRing A) ↥(invField A) gN (𝟙 (shBase A))
            (NeronModelInfra.schemeHomOverComp s₀ ⟨e (O.comp z), hef _⟩)).1 ≫
            pullback.fst gN (specGenericFibreInclusion ↥(shRing A) ↥(invField A))
          = pullback.fst (𝟙 (shBase A)) (specGenericFibreInclusion ↥(shRing A) ↥(invField A)) ≫ s₀.1 ≫ e (O.comp z) :=
            NeronModelInfra.genericFibreRestrict_coe_comp_fst _ _ _
      _ = (pullback.snd (𝟙 (shBase A)) (specGenericFibreInclusion ↥(shRing A) ↥(invField A)) ≫
            specGenericFibreInclusion ↥(shRing A) ↥(invField A)) ≫ s₀.1 ≫ e (O.comp z) :=
            congrArg (· ≫ s₀.1 ≫ e (O.comp z)) hfst
      _ = pullback.snd (𝟙 (shBase A)) (specGenericFibreInclusion ↥(shRing A) ↥(invField A)) ≫
            (specGenericFibreInclusion ↥(shRing A) ↥(invField A) ≫ s₀.1) ≫ e (O.comp z) := by
            simp only [Category.assoc]
      _ = pullback.snd (𝟙 (shBase A)) (specGenericFibreInclusion ↥(shRing A) ↥(invField A)) ≫
            ((O.L.baseChange Λ.shStr).mul (specGenericFibreInclusion ↥(shRing A) ↥(invField A)) ⟨_, ha'⟩
              ((O.L.baseChange Λ.shStr).inv (specGenericFibreInclusion ↥(shRing A) ↥(invField A)) (y (O.comp z)))).1 ≫
            e (O.comp z) :=
            congrArg (fun t => pullback.snd (𝟙 (shBase A)) (specGenericFibreInclusion ↥(shRing A) ↥(invField A)) ≫
              t ≫ e (O.comp z)) e1
      _ = ((O.L.baseChange Λ.shStr).mul
              (pullback.snd (𝟙 (shBase A)) (specGenericFibreInclusion ↥(shRing A) ↥(invField A)) ≫
                specGenericFibreInclusion ↥(shRing A) ↥(invField A)) a
              (GoodReductionJacobian.schemeHomOverComp
                (pullback.snd (𝟙 (shBase A)) (specGenericFibreInclusion ↥(shRing A) ↥(invField A))) rfl
                ((O.L.baseChange Λ.shStr).inv (specGenericFibreInclusion ↥(shRing A) ↥(invField A)) (y (O.comp z))))).1 ≫
            e (O.comp z) := (Category.assoc _ _ _).symm.trans (congrArg (· ≫ e (O.comp z)) e2)
      _ = a.1 ≫ e 0 :=
            (congrArg (fun q => ((O.L.baseChange Λ.shStr).mul
              (pullback.snd (𝟙 (shBase A)) (specGenericFibreInclusion ↥(shRing A) ↥(invField A)) ≫
                specGenericFibreInclusion ↥(shRing A) ↥(invField A)) a
              (GoodReductionJacobian.schemeHomOverComp
                (pullback.snd (𝟙 (shBase A)) (specGenericFibreInclusion ↥(shRing A) ↥(invField A))) rfl q)).1 ≫
              e (O.comp z)) hq).trans
            (chart_rel 0 (O.comp z) _ a).symm
      _ = uK.1 ≫ pullback.fst gN (specGenericFibreInclusion ↥(shRing A) ↥(invField A)) := ha1.symm
  · exact (NeronModelInfra.genericFibreRestrict_coe_comp_snd _ _ _).trans uK.2.symm

end NeronGlueAux

namespace NeronGlueAux
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian ModularCurve ModularCurve.JZeroNeronObjectAtP

attribute [local instance] ModularCurve.instDecidableEqResidueFieldSemistable
  ModularCurve.instAlgebraResidueFieldModularFunctionFieldCSemistable

theorem exists_shGenLift_pts_coe_eq
    (N₀ p : ℕ) [NeZero N₀] [Fact p.Prime] [NeZero p] (hpN₀ : ¬ p ∣ N₀)
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime p)
    (Λ : JZeroNeronObjectAtP.LevelData N₀ p A) (O : JZeroNeronObjectAtP N₀ p hpN₀ A hA Λ)
    {ι : Spec (CommRingCat.of (AlgebraicClosure ℚ)) ⟶ shBase A} (hι : ι = barPt A ≫ shPt A)
    (P : SchemeHomOver ι (RelativeGroupLaw.baseChangeStr Λ.shStr O.g)) :
    ∃ x : JZero (N₀ * p), (Λ.shGenLift (O.pts x)).1 = P.1 := by
  subst hι
  let Pg : SchemeHomOver (genPt p) O.g :=
    castOver Λ.barPt_shPt_shStr (RelativeGroupLaw.baseChangePointToBase Λ.shStr P)
  refine ⟨O.pts.symm Pg, ?_⟩
  have hu : O.pts (O.pts.symm Pg) = Pg := O.pts.apply_symm_apply Pg
  rw [hu]
  apply pullback.hom_ext
  · simp only [LevelData.shGenLift, RelativeGroupLaw.baseChangePointOfBase_coe, pullback.lift_fst]
    rfl
  · simp only [LevelData.shGenLift, RelativeGroupLaw.baseChangePointOfBase_coe, pullback.lift_snd]
    exact P.2.symm
end NeronGlueAux

namespace NeronGlueAux
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian ModularCurve ModularCurve.JZeroNeronObjectAtP

attribute [local instance] ModularCurve.instDecidableEqResidueFieldSemistable
  ModularCurve.instAlgebraResidueFieldModularFunctionFieldCSemistable

theorem pts_surj_aux
    (N₀ p : ℕ) [NeZero N₀] [Fact p.Prime] [NeZero p] (hpN₀ : ¬ p ∣ N₀)
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime p)
    (Λ : JZeroNeronObjectAtP.LevelData N₀ p A) (O : JZeroNeronObjectAtP N₀ p hpN₀ A hA Λ)
    {N : Scheme.{0}} (gN : N ⟶ shBase A)
    (e : componentGroup O.width → (RelativeGroupLaw.baseChangeScheme Λ.shStr O.g ⟶ N))
    (hef : ∀ φ, e φ ≫ gN = RelativeGroupLaw.baseChangeStr Λ.shStr O.g)
    {ιK : Spec (CommRingCat.of ↥(invField A)) ⟶ shBase A}
    {σb : Spec (CommRingCat.of (AlgebraicClosure ℚ)) ⟶ Spec (CommRingCat.of ↥(invField A))}
    (hbar : σb ≫ ιK = barPt A ≫ shPt A)
    (hchart0 : ∀ (u : SchemeHomOver (σb ≫ ιK) gN),
      ∃ a : SchemeHomOver (σb ≫ ιK) (RelativeGroupLaw.baseChangeStr Λ.shStr O.g),
        u = NeronModelInfra.schemeHomOverComp a ⟨e 0, hef 0⟩)
    (y0 : SchemeHomOver (barPt A ≫ shPt A) gN) :
    ∃ x : JZero (N₀ * p),
      NeronModelInfra.schemeHomOverComp (Λ.shGenLift (O.pts x)) (⟨e 0, hef 0⟩ : SchemeHomOver _ gN) = y0 := by
  have hch := hchart0 (castOver hbar.symm y0)
  obtain ⟨P, hP⟩ := hch
  have hP1 : y0.1 = P.1 ≫ e 0 := congrArg Subtype.val hP
  have hxe := NeronGlueAux.exists_shGenLift_pts_coe_eq N₀ p hpN₀ A hA Λ O hbar P
  obtain ⟨x, hx⟩ := hxe
  refine ⟨x, Subtype.ext ?_⟩
  exact (congrArg (fun w => w ≫ e 0) hx).trans hP1.symm
end NeronGlueAux

namespace NeronGlueAux
namespace P2

theorem inv_natural {R : Type u} [CommRing R] {G : Scheme.{u}} {f : G ⟶ Spec (CommRingCat.of R)}
    (L : RelativeGroupLaw R f) {T T' : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R))
    (t' : T' ⟶ Spec (CommRingCat.of R)) (ψ : T' ⟶ T) (hψ : ψ ≫ t = t') (x : SchemeHomOver t f) :
    GoodReductionJacobian.schemeHomOverComp ψ hψ (L.inv t x) =
      L.inv t' (GoodReductionJacobian.schemeHomOverComp ψ hψ x) := by
  letI := L.pointGroup t'
  symm
  apply inv_eq_of_mul_eq_one_left
  show L.mul t' (GoodReductionJacobian.schemeHomOverComp ψ hψ (L.inv t x))
    (GoodReductionJacobian.schemeHomOverComp ψ hψ x) = L.one t'
  rw [← L.mul_natural, L.inv_mul_cancel, L.one_natural]

theorem mul_inv_one {R : Type u} [CommRing R] {G : Scheme.{u}} {f : G ⟶ Spec (CommRingCat.of R)}
    (L : RelativeGroupLaw R f) {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) (x : SchemeHomOver t f) :
    L.mul t x (L.inv t (L.one t)) = x := by
  letI := L.pointGroup t
  show x * (1 : SchemeHomOver t f)⁻¹ = x
  rw [inv_one, _root_.mul_one]

theorem mul_mul_inv_cancel {R : Type u} [CommRing R] {G : Scheme.{u}} {f : G ⟶ Spec (CommRingCat.of R)}
    (L : RelativeGroupLaw R f) {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) (a b : SchemeHomOver t f) :
    L.mul t (L.mul t a b) (L.inv t b) = a := by
  letI := L.pointGroup t
  exact mul_inv_cancel_right a b

theorem eq_of_sub_rep_eq_zero {M Φ : Type*} [AddCommGroup M] [AddCommGroup Φ] (f : M →+ Φ) (y' : Φ → M)
    (hy' : ∀ φ, f (y' φ) = φ) (z : M) (φ : Φ) (h : f (z - y' φ) = 0) : f z = φ := by
  rw [map_sub, hy', sub_eq_zero] at h
  exact h

theorem comp_pin_aux
    (N₀ p : ℕ) [NeZero N₀] [Fact p.Prime] [NeZero p] (hpN₀ : ¬ p ∣ N₀)
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime p)
    (Λ : JZeroNeronObjectAtP.LevelData N₀ p A)
    (O : JZeroNeronObjectAtP N₀ p hpN₀ A hA Λ)
    (LX : RelativeGroupLaw ↥(shRing A) (RelativeGroupLaw.baseChangeStr Λ.shStr O.g))
    {N : Scheme.{0}} (gN : N ⟶ shBase A)
    (e : componentGroup O.width → (RelativeGroupLaw.baseChangeScheme Λ.shStr O.g ⟶ N))
    (hef : ∀ φ, e φ ≫ gN = RelativeGroupLaw.baseChangeStr Λ.shStr O.g) [∀ φ, IsOpenImmersion (e φ)]
    (σb : Spec (CommRingCat.of (AlgebraicClosure ℚ)) ⟶ Spec (CommRingCat.of ↥(invField A)))
    (ιK : Spec (CommRingCat.of ↥(invField A)) ⟶ shBase A)
    (hbar : σb ≫ ιK = barPt A ≫ shPt A)
    (prX : RelativeGroupLaw.baseChangeScheme Λ.shStr O.g ⟶ O.G)
    (shGenLift_fst : ∀ u : SchemeHomOver (genPt p) O.g, (Λ.shGenLift u).1 ≫ prX = u.1)
    (toPlace : ∀ a : SchemeHomOver (shPt A) (RelativeGroupLaw.baseChangeStr Λ.shStr O.g),
      ∃ s' : SchemeHomOver Λ.σA O.g, s'.1 = a.1 ≫ prX)
    (yK : ↥(inertiaInvariants A (N₀ * p)) → SchemeHomOver ιK (RelativeGroupLaw.baseChangeStr Λ.shStr O.g))
    (hyK_bar : ∀ z, σb ≫ (yK z).1 = (Λ.shGenLift (O.pts (z : JZero (N₀ * p)))).1)
    (yK_sub : ∀ a b, yK (a - b) = LX.mul ιK (yK a) (LX.inv ιK (yK b)))
    (y' : componentGroup O.width → ↥(inertiaInvariants A (N₀ * p))) (hy'comp : ∀ φ, O.comp (y' φ) = φ)
    (y : componentGroup O.width → SchemeHomOver ιK (RelativeGroupLaw.baseChangeStr Λ.shStr O.g))
    (hy : ∀ φ, y φ = yK (y' φ)) (hy0 : y 0 = LX.one ιK)
    (chart_rel : ∀ (φ ψ : componentGroup O.width) {T : Scheme.{0}} (σ : T ⟶ Spec (CommRingCat.of ↥(invField A)))
        (P : SchemeHomOver (σ ≫ ιK) (RelativeGroupLaw.baseChangeStr Λ.shStr O.g)),
      P.1 ≫ e φ = (LX.mul (σ ≫ ιK) P (GoodReductionJacobian.schemeHomOverComp σ rfl
          (LX.mul ιK (y φ) (LX.inv ιK (y ψ))))).1 ≫ e ψ)
    (specN : SchemeHomOver (shPt A) gN → componentGroup O.width)
    (hspecN : ∀ (s : SchemeHomOver (shPt A) gN) (φ : componentGroup O.width),
      specN s = φ ↔ ∃ a : SchemeHomOver (shPt A) (RelativeGroupLaw.baseChangeStr Λ.shStr O.g),
        NeronModelInfra.schemeHomOverComp a ⟨e φ, hef φ⟩ = s)
    (x : ↥(inertiaInvariants A (N₀ * p))) (s : SchemeHomOver (shPt A) gN)
    (H : (NeronModelInfra.schemeHomOverComp (Λ.shGenLift (O.pts (x : JZero (N₀ * p)))) ⟨e 0, hef 0⟩).1 = barPt A ≫ s.1) :
    O.comp x = specN s := by

  suffices key : ∀ φ : componentGroup O.width, specN s = φ → O.comp x = φ from key _ rfl
  intro φ hφ
  have hex := (hspecN s φ).1 hφ
  obtain ⟨a, ha⟩ := hex
  have hs : s.1 = a.1 ≫ e φ := (congrArg Subtype.val ha).symm
  have H0 : (Λ.shGenLift (O.pts (x : JZero (N₀ * p)))).1 ≫ e 0 = barPt A ≫ s.1 :=
    (NeronModelInfra.schemeHomOverComp_coe (Λ.shGenLift (O.pts (x : JZero (N₀ * p)))) ⟨e 0, hef 0⟩).symm.trans H
  have H1 : (Λ.shGenLift (O.pts (x : JZero (N₀ * p)))).1 ≫ e 0 = (barPt A ≫ a.1) ≫ e φ :=
    H0.trans (by rw [hs, Category.assoc])

  have hPb : (barPt A ≫ a.1) ≫ RelativeGroupLaw.baseChangeStr Λ.shStr O.g = σb ≫ ιK := by
    rw [Category.assoc, a.2]; exact hbar.symm
  have hd : LX.mul ιK (y φ) (LX.inv ιK (y 0)) = y φ := by rw [hy0]; exact mul_inv_one LX ιK _
  have hrel := chart_rel φ 0 σb ⟨barPt A ≫ a.1, hPb⟩
  simp only [hd] at hrel
  have H2 := (cancel_mono (e 0)).mp (H1.trans hrel)

  have H4 : GoodReductionJacobian.schemeHomOverComp σb rfl (yK x) =
      LX.mul (σb ≫ ιK) ⟨barPt A ≫ a.1, hPb⟩ (GoodReductionJacobian.schemeHomOverComp σb rfl (y φ)) :=
    Subtype.ext ((hyK_bar x).trans H2)

  have H5 : GoodReductionJacobian.schemeHomOverComp σb rfl (yK (x - y' φ)) = ⟨barPt A ≫ a.1, hPb⟩ := by
    rw [yK_sub, LX.mul_natural, inv_natural, ← hy, H4]
    exact mul_mul_inv_cancel LX _ _ _
  have H6 : σb ≫ (yK (x - y' φ)).1 = barPt A ≫ a.1 := congrArg Subtype.val H5

  have hts := toPlace a
  obtain ⟨s', hs'⟩ := hts
  have hext : ExtendsToPlace A Λ.σA (O.pts ((x - y' φ : ↥(inertiaInvariants A (N₀ * p))) : JZero (N₀ * p))) := by
    refine ⟨s', ?_⟩
    calc (O.pts ((x - y' φ : ↥(inertiaInvariants A (N₀ * p))) : JZero (N₀ * p))).1
        = (Λ.shGenLift (O.pts ((x - y' φ : ↥(inertiaInvariants A (N₀ * p))) : JZero (N₀ * p)))).1 ≫ prX :=
          (shGenLift_fst _).symm
      _ = (σb ≫ (yK (x - y' φ)).1) ≫ prX := congrArg (· ≫ prX) (hyK_bar _).symm
      _ = (barPt A ≫ a.1) ≫ prX := congrArg (· ≫ prX) H6
      _ = barPt A ≫ s'.1 := by rw [hs', Category.assoc]
  have h0 : O.comp (x - y' φ) = 0 := (O.comp_eq_zero_iff (x - y' φ)).2 hext
  exact eq_of_sub_rep_eq_zero O.comp y' hy'comp x φ h0

end NeronGlueAux.P2

attribute [local instance] ModularCurve.instDecidableEqResidueFieldSemistable
  ModularCurve.instAlgebraResidueFieldModularFunctionFieldCSemistable

set_option maxHeartbeats 1600000 in

theorem solution
    (N₀ p : ℕ) [NeZero N₀] [Fact p.Prime] [NeZero p] (hpN₀ : ¬ p ∣ N₀)
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime p)
    (Λ : JZeroNeronObjectAtP.LevelData N₀ p A) (hΛ : Λ.IsJacobian)
    (O : JZeroNeronObjectAtP N₀ p hpN₀ A hA Λ) :
    ∃ (Nfull : Scheme.{0}) (gN : Nfull ⟶ shBase A) (LN : RelativeGroupLaw ↥(shRing A) gN),
      LN.IsCommutative ∧
      (Smooth gN ∧ IsSeparated gN ∧ LocallyOfFiniteType gN ∧ QuasiCompact gN) ∧
      Function.Surjective (genericFibreRestrict ↥(shRing A) ↥(invField A) gN (𝟙 (shBase A))) ∧
      ∃ (openImm : SchemeHomOver (RelativeGroupLaw.baseChangeStr Λ.shStr O.g) gN)
        (specN : SchemeHomOver (shPt A) gN → componentGroup O.width),
        IsOpenImmersion openImm.1 ∧
        (∀ {T : Scheme.{0}} (s : T ⟶ shBase A)
          (x y : SchemeHomOver s (RelativeGroupLaw.baseChangeStr Λ.shStr O.g)),
          NeronModelInfra.schemeHomOverComp ((O.L.baseChange Λ.shStr).mul s x y) openImm =
            LN.mul s (NeronModelInfra.schemeHomOverComp x openImm) (NeronModelInfra.schemeHomOverComp y openImm)) ∧
        (∀ y : SchemeHomOver (barPt A ≫ shPt A) gN,
          ∃ x : JZero (N₀ * p), NeronModelInfra.schemeHomOverComp (Λ.shGenLift (O.pts x)) openImm = y) ∧
        (∀ s s' : SchemeHomOver (shPt A) gN, specN (LN.mul (shPt A) s s') = specN s + specN s') ∧
        Function.Surjective specN ∧
        (∀ s : SchemeHomOver (shPt A) gN,
          specN s = 0 ↔ ∃ s₀ : SchemeHomOver Λ.σA O.g, NeronModelInfra.schemeHomOverComp (Λ.shLift s₀) openImm = s) ∧
        (∀ (x : ↥(inertiaInvariants A (N₀ * p))) (s : SchemeHomOver (shPt A) gN),
          (NeronModelInfra.schemeHomOverComp (Λ.shGenLift (O.pts (x : JZero (N₀ * p)))) openImm).1 = barPt A ≫ s.1 →
            O.comp x = specN s) := by
  classical

  haveI hDVR : IsDiscreteValuationRing ↥(shRing A) :=
    (ValuationSubring.isDiscreteValuationRing_comap_fixedField_inertiaSubgroupIn A p hA).1
  let ιK : Spec (CommRingCat.of ↥(invField A)) ⟶ shBase A := specGenericFibreInclusion ↥(shRing A) ↥(invField A)
  have hιK : ιK = Spec.map (CommRingCat.ofHom (algebraMap ↥(shRing A) ↥(invField A))) := rfl

  let X : Scheme.{0} := RelativeGroupLaw.baseChangeScheme Λ.shStr O.g
  let fX : X ⟶ shBase A := RelativeGroupLaw.baseChangeStr Λ.shStr O.g
  let LX : RelativeGroupLaw ↥(shRing A) fX := O.L.baseChange Λ.shStr
  have hLX : LX.IsCommutative := RelativeGroupLaw.IsCommutative.baseChange Λ.shStr O.comm
  haveI : Smooth fX := by
    haveI := O.smooth; exact MorphismProperty.pullback_snd (P := @Smooth) _ _ inferInstance
  haveI : IsSeparated fX := by
    haveI := O.separated; exact MorphismProperty.pullback_snd (P := @IsSeparated) _ _ inferInstance
  haveI : LocallyOfFiniteType fX := by
    haveI := O.locallyOfFiniteType; exact MorphismProperty.pullback_snd (P := @LocallyOfFiniteType) _ _ inferInstance
  haveI : QuasiCompact fX := by
    haveI := O.quasiCompact; exact MorphismProperty.pullback_snd (P := @QuasiCompact) _ _ inferInstance
  haveI : Flat fX := inferInstance

  haveI hιKopen : IsOpenImmersion ιK := inferInstance
  let GK : Scheme.{0} := pullback fX ιK
  let jK : GK ⟶ X := pullback.fst fX ιK
  haveI : IsOpenImmersion jK := MorphismProperty.pullback_fst (P := @IsOpenImmersion) _ _ hιKopen

  haveI : Finite (componentGroup O.width) := ModularCurve.finite_componentGroup_of_pos O.width O.width_pos
  haveI : Fintype (componentGroup O.width) := Fintype.ofFinite (componentGroup O.width)
  have hy'ex : ∃ y' : (componentGroup O.width) → ↥(inertiaInvariants A (N₀ * p)), (∀ φ, O.comp (y' φ) = φ) ∧ y' 0 = 0 :=
    NeronGlueAux.reps_aux O.comp O.comp_surjective
  obtain ⟨y', hy'comp, hy'0⟩ := hy'ex

  have hC11 := ModularCurve.JZeroNeronObjectAtP.exists_inertiaInvariants_to_schemeHomOver_specGenericFibreInclusion_bijective
    N₀ p hpN₀ A hA Λ O
  obtain ⟨yK, hyK_bar, hyK_add, hyK_bij⟩ := hC11

  let σb : Spec (CommRingCat.of (AlgebraicClosure ℚ)) ⟶ Spec (CommRingCat.of ↥(invField A)) :=
    Spec.map (CommRingCat.ofHom (algebraMap ↥(invField A) (AlgebraicClosure ℚ)))
  have hbar : σb ≫ ιK = barPt A ≫ shPt A := by
    change Spec.map _ ≫ Spec.map _ = Spec.map _ ≫ Spec.map _
    rw [← Spec.map_comp, ← Spec.map_comp]
    rfl
  have yK_sub : ∀ a b, yK (a - b) = LX.mul ιK (yK a) (LX.inv ιK (yK b)) := fun a b => by
    letI : Group (SchemeHomOver ιK fX) := LX.pointGroup ιK
    exact NeronGlueAux.hom_sub_aux yK (fun u w => hyK_add u w) a b
  have yK_zero : yK 0 = LX.one ιK := by
    letI : Group (SchemeHomOver ιK fX) := LX.pointGroup ιK
    exact NeronGlueAux.hom_zero_aux yK (fun u w => hyK_add u w)
  have shGenLift_fst : ∀ u : SchemeHomOver (genPt p) O.g, (Λ.shGenLift u).1 ≫ pullback.fst O.g Λ.shStr = u.1 := by
    intro u; simp only [LevelData.shGenLift, RelativeGroupLaw.baseChangePointOfBase_coe, pullback.lift_fst]; rfl
  have key : ∀ (P : SchemeHomOver ιK fX) (v : ↥(inertiaInvariants A (N₀ * p))),
      σb ≫ P.1 = (Λ.shGenLift (O.pts (v : JZero (N₀ * p)))).1 → P = yK v := by
    intro P v hP
    obtain ⟨w, rfl⟩ := hyK_bij.2 P
    have h1 : (Λ.shGenLift (O.pts (w : JZero (N₀ * p)))).1 = (Λ.shGenLift (O.pts (v : JZero (N₀ * p)))).1 := by
      rw [← hyK_bar, hP]
    have h2 : (O.pts (w : JZero (N₀ * p))).1 = (O.pts (v : JZero (N₀ * p))).1 := by
      rw [← shGenLift_fst, ← shGenLift_fst, h1]
    have h3 : (w : JZero (N₀ * p)) = v := O.pts.injective (Subtype.ext h2)
    rw [Subtype.ext h3]
  have hy_ex : ∃ y : (componentGroup O.width) → SchemeHomOver ιK fX, ∀ φ, y φ = yK (y' φ) := ⟨_, fun _ => rfl⟩
  obtain ⟨y, hy⟩ := hy_ex
  have hy0 : y 0 = LX.one ιK := by rw [hy, hy'0, yK_zero]

  have hv_ex := NeronGlueAux.cocycle_aux2 O.comp y' hy'comp
  obtain ⟨v, hv0, hv⟩ := hv_ex
  have hc_ex : ∀ φ ψ : (componentGroup O.width), ∃ s : SchemeHomOver (𝟙 (shBase A)) (RelativeGroupLaw.baseChangeStr Λ.shStr O.g),
      (Λ.shGenLift (O.pts (v φ ψ : JZero (N₀ * p)))).1 = (barPt A ≫ shPt A) ≫ s.1 := fun φ ψ =>
    (ModularCurve.JZeroNeronObjectAtP.comp_eq_zero_iff_exists_schemeHomOver_shGenLift_eq N₀ p hpN₀ A hA Λ O _).1
      (hv0 φ ψ)
  choose c hc using hc_ex
  have hcK : ∀ φ ψ, ιK ≫ (c φ ψ).1 = (LX.mul _ (LX.mul _ (y φ) (y ψ)) (LX.inv _ (y (φ + ψ)))).1 := by
    intro φ ψ
    have hP : (⟨ιK ≫ (c φ ψ).1, by rw [Category.assoc, (c φ ψ).2, Category.comp_id]⟩ : SchemeHomOver ιK fX) =
        yK (v φ ψ) := by
      apply key
      change σb ≫ ιK ≫ (c φ ψ).1 = _
      rw [← Category.assoc, hbar]
      exact (hc φ ψ).symm
    have hP1 : ιK ≫ (c φ ψ).1 = (yK (v φ ψ)).1 := congrArg Subtype.val hP
    have hP2 : yK (v φ ψ) = LX.mul ιK (LX.mul ιK (y φ) (y ψ)) (LX.inv ιK (y (φ + ψ))) := by
      letI : Group (SchemeHomOver ιK fX) := LX.pointGroup ιK
      have h := NeronGlueAux.hom_aux yK (fun u w => hyK_add u w) (v φ ψ) (y' φ) (y' ψ) (y' (φ + ψ)) (hv φ ψ)
      simp only [hy]
      exact h
    exact hP1.trans (congrArg Subtype.val hP2)
  have hc0 : c 0 0 = LX.one _ := by
    apply NeronModelInfra.genericFibreRestrict_injective_of_flat_of_isSeparated ↥(shRing A) ↥(invField A) fX (𝟙 _)
    apply Subtype.ext
    apply pullback.hom_ext
    · have hfst : pullback.fst (𝟙 (shBase A)) ιK = pullback.snd (𝟙 (shBase A)) ιK ≫ ιK := by
        have := pullback.condition (f := 𝟙 (shBase A)) (g := ιK)
        simp only [Category.comp_id] at this; exact this
      simp only [NeronModelInfra.genericFibreRestrict_coe_comp_fst]
      change pullback.fst (𝟙 (shBase A)) ιK ≫ (c 0 0).1 = pullback.fst (𝟙 (shBase A)) ιK ≫ (LX.one (𝟙 (shBase A))).1
      have hinv1 : LX.inv ιK (LX.one ιK) = LX.one ιK := by
        letI : Group (SchemeHomOver ιK fX) := LX.pointGroup ιK
        exact inv_one
      simp only [hfst, Category.assoc, hcK 0 0, add_zero, hy0, LX.one_mul, hinv1]
      exact congrArg (fun w => pullback.snd (𝟙 (shBase A)) ιK ≫ w)
        (congrArg Subtype.val (RelativeGroupLaw.one_natural LX (𝟙 (shBase A)) ιK ιK (Category.comp_id ιK))).symm
    · simp only [NeronModelInfra.genericFibreRestrict_coe_comp_snd]

  let LK : RelativeGroupLaw ↥(invField A) (pullback.snd fX ιK) := LX.baseChange ιK
  let dK : (componentGroup O.width) → (componentGroup O.width) → SchemeHomOver (𝟙 (Spec (CommRingCat.of ↥(invField A)))) (pullback.snd fX ιK) := fun φ ψ =>
    RelativeGroupLaw.baseChangePointOfBase ιK
      ⟨(LX.mul _ (y φ) (LX.inv _ (y ψ))).1, by rw [Category.id_comp]; exact (LX.mul _ (y φ) (LX.inv _ (y ψ))).2⟩
  have hτ : ∀ φ ψ : (componentGroup O.width), ∃ τ : GK ≅ GK, τ.hom ≫ pullback.snd fX ιK = pullback.snd fX ιK ∧
      τ.inv ≫ pullback.snd fX ιK = pullback.snd fX ιK ∧
      (∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of ↥(invField A))) (x : SchemeHomOver t (pullback.snd fX ιK)),
        x.1 ≫ τ.hom = (LK.mul t x (GoodReductionJacobian.schemeHomOverComp t (Category.comp_id t) (dK φ ψ))).1) ∧
      (∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of ↥(invField A))) (x : SchemeHomOver t (pullback.snd fX ιK)),
        x.1 ≫ τ.inv = (LK.mul t x (LK.inv t (GoodReductionJacobian.schemeHomOverComp t (Category.comp_id t) (dK φ ψ)))).1) :=
    fun φ ψ => GoodReductionJacobian.RelativeGroupLaw.exists_iso_hom_comp_eq_and_comp_hom_eq_mul _ LK (dK φ ψ)
  choose t ht_snd ht_inv_snd ht_hom ht_inv using hτ
  have ht_over : ∀ φ ψ, (t φ ψ).hom ≫ jK ≫ fX = jK ≫ fX := by
    intro φ ψ
    simp only [jK, pullback.condition]; rw [← Category.assoc, ht_snd]

  let d : (componentGroup O.width) → (componentGroup O.width) → SchemeHomOver ιK fX := fun φ ψ => LX.mul _ (y φ) (LX.inv _ (y ψ))
  have hdK_toBase : ∀ (φ ψ : (componentGroup O.width)) {T : Scheme.{0}} (σ : T ⟶ Spec (CommRingCat.of ↥(invField A))),
      RelativeGroupLaw.baseChangePointToBase ιK
          (GoodReductionJacobian.schemeHomOverComp σ (Category.comp_id σ) (dK φ ψ)) =
        GoodReductionJacobian.schemeHomOverComp σ rfl (d φ ψ) := by
    intro φ ψ T σ; apply Subtype.ext
    simp only [RelativeGroupLaw.baseChangePointToBase_coe, GoodReductionJacobian.schemeHomOverComp_coe, dK,
      RelativeGroupLaw.baseChangePointOfBase_coe, Category.assoc, pullback.lift_fst]
    rfl
  have ht_pt : ∀ (φ ψ : (componentGroup O.width)) {T : Scheme.{0}} (σ : T ⟶ Spec (CommRingCat.of ↥(invField A)))
      (q : SchemeHomOver σ (pullback.snd fX ιK)),
      q.1 ≫ (t φ ψ).hom ≫ pullback.fst fX ιK = (LX.mul (σ ≫ ιK) (RelativeGroupLaw.baseChangePointToBase ιK q)
        (GoodReductionJacobian.schemeHomOverComp σ rfl (d φ ψ))).1 := by
    intro φ ψ T σ q
    rw [← Category.assoc, ht_hom φ ψ σ q]
    change (RelativeGroupLaw.baseChangePointToBase ιK (LK.mul σ q _)).1 = _
    rw [RelativeGroupLaw.baseChangePointToBase_mul, hdK_toBase]
  have hone_pt : RelativeGroupLaw.baseChangePointToBase ιK (⟨𝟙 GK, Category.id_comp _⟩ : SchemeHomOver (pullback.snd fX ιK) (pullback.snd fX ιK)) =
      (⟨pullback.fst fX ιK, pullback.condition⟩ : SchemeHomOver (pullback.snd fX ιK ≫ ιK) fX) :=
    Subtype.ext (Category.id_comp _)
  have ht_fst : ∀ φ ψ, (t φ ψ).hom ≫ pullback.fst fX ιK =
      (LX.mul (pullback.snd fX ιK ≫ ιK) ⟨pullback.fst fX ιK, pullback.condition⟩
        (GoodReductionJacobian.schemeHomOverComp (pullback.snd fX ιK) rfl (LX.mul _ (y φ) (LX.inv _ (y ψ))))).1 := by
    intro φ ψ
    have h := ht_pt φ ψ (pullback.snd fX ιK) ⟨𝟙 GK, Category.id_comp _⟩
    rw [Category.id_comp, hone_pt] at h
    exact h

  have hd_refl : ∀ φ, d φ φ = LX.one ιK := fun φ => RelativeGroupLaw.mul_inv_cancel LX ιK (y φ)
  have hd_trans : ∀ φ ψ χ, LX.mul ιK (d φ ψ) (d ψ χ) = d φ χ := by
    intro φ ψ χ
    change LX.mul ιK (LX.mul ιK (y φ) (LX.inv ιK (y ψ))) (LX.mul ιK (y ψ) (LX.inv ιK (y χ))) =
      LX.mul ιK (y φ) (LX.inv ιK (y χ))
    rw [LX.mul_assoc, ← LX.mul_assoc ιK (LX.inv ιK (y ψ)), LX.inv_mul_cancel, LX.one_mul]
  have hd_noext : ∀ φ ψ, φ ≠ ψ → ¬ ∃ s : SchemeHomOver (𝟙 (Spec (CommRingCat.of ↥(shRing A)))) fX,
      Spec.map (CommRingCat.ofHom (algebraMap ↥(shRing A) ↥(invField A))) ≫ s.1 = (d φ ψ).1 := by
    intro φ ψ hne hs
    obtain ⟨s, hs⟩ := hs
    apply hne
    have hdφψ : d φ ψ = yK (y' φ - y' ψ) := by
      change LX.mul ιK (y φ) (LX.inv ιK (y ψ)) = _
      simp only [hy, yK_sub]
    have hzero : O.comp (y' φ - y' ψ) = 0 := by
      refine (ModularCurve.JZeroNeronObjectAtP.comp_eq_zero_iff_exists_schemeHomOver_shGenLift_eq
        N₀ p hpN₀ A hA Λ O _).2 ⟨s, ?_⟩
      have e1 : (Λ.shGenLift (O.pts ((y' φ - y' ψ : ↥(inertiaInvariants A (N₀ * p))) : JZero (N₀ * p)))).1 =
          σb ≫ (yK (y' φ - y' ψ)).1 := (hyK_bar _).symm
      have e2 : σb ≫ (yK (y' φ - y' ψ)).1 = σb ≫ (d φ ψ).1 := congrArg (fun w => σb ≫ w.1) hdφψ.symm
      have e3 : σb ≫ (d φ ψ).1 = σb ≫ (ιK ≫ s.1) := congrArg (fun w => σb ≫ w) hs.symm
      have e4 : σb ≫ (ιK ≫ s.1) = (barPt A ≫ shPt A) ≫ s.1 := by
        rw [← Category.assoc]; exact congrArg (fun w => w ≫ s.1) hbar
      exact e1.trans (e2.trans (e3.trans e4))
    have h2 := NeronGlueAux.sub_aux O.comp y' hy'comp φ ψ
    exact sub_eq_zero.mp (h2.symm.trans hzero)
  have ht_refl : ∀ φ, t φ φ = Iso.refl GK := by
    intro φ; apply Iso.ext
    apply pullback.hom_ext
    · have h := ht_pt φ φ (pullback.snd fX ιK) ⟨𝟙 GK, Category.id_comp _⟩
      rw [Category.id_comp, hone_pt] at h
      rw [h, hd_refl, RelativeGroupLaw.one_natural LX _ _ (pullback.snd fX ιK) rfl, LX.mul_one, Iso.refl_hom,
        Category.id_comp]
    · rw [ht_snd, Iso.refl_hom, Category.id_comp]
  have ht_trans : ∀ φ ψ χ, (t φ ψ).hom ≫ (t ψ χ).hom = (t φ χ).hom := by
    intro φ ψ χ
    apply pullback.hom_ext
    · have h1 := ht_pt ψ χ (pullback.snd fX ιK) ⟨(t φ ψ).hom, ht_snd φ ψ⟩
      have h2 := ht_pt φ ψ (pullback.snd fX ιK) ⟨𝟙 GK, Category.id_comp _⟩
      have h3 := ht_pt φ χ (pullback.snd fX ιK) ⟨𝟙 GK, Category.id_comp _⟩
      rw [Category.id_comp, hone_pt] at h2 h3
      have hq : RelativeGroupLaw.baseChangePointToBase ιK
          (⟨(t φ ψ).hom, ht_snd φ ψ⟩ : SchemeHomOver (pullback.snd fX ιK) (pullback.snd fX ιK)) =
          LX.mul (pullback.snd fX ιK ≫ ιK) ⟨pullback.fst fX ιK, pullback.condition⟩
            (GoodReductionJacobian.schemeHomOverComp (pullback.snd fX ιK) rfl (d φ ψ)) :=
        Subtype.ext h2
      calc ((t φ ψ).hom ≫ (t ψ χ).hom) ≫ pullback.fst fX ιK
          = (t φ ψ).hom ≫ (t ψ χ).hom ≫ pullback.fst fX ιK := Category.assoc _ _ _
        _ = _ := h1
        _ = (LX.mul (pullback.snd fX ιK ≫ ιK) (LX.mul (pullback.snd fX ιK ≫ ιK) ⟨pullback.fst fX ιK, pullback.condition⟩
              (GoodReductionJacobian.schemeHomOverComp (pullback.snd fX ιK) rfl (d φ ψ)))
              (GoodReductionJacobian.schemeHomOverComp (pullback.snd fX ιK) rfl (d ψ χ))).1 := by rw [hq]
        _ = (LX.mul (pullback.snd fX ιK ≫ ιK) ⟨pullback.fst fX ιK, pullback.condition⟩
              (GoodReductionJacobian.schemeHomOverComp (pullback.snd fX ιK) rfl (d φ χ))).1 := by
            rw [LX.mul_assoc, ← LX.mul_natural ιK (pullback.snd fX ιK ≫ ιK) (pullback.snd fX ιK) rfl (d φ ψ) (d ψ χ),
              hd_trans]
        _ = (t φ χ).hom ≫ pullback.fst fX ιK := h3.symm
    · rw [Category.assoc, ht_snd, ht_snd, ht_snd]

  have hC4 := AlgebraicGeometry.Scheme.exists_isOpenImmersion_isPullback_of_glue_cocycle fX jK t ht_over ht_refl ht_trans
  obtain ⟨N, gN, e, he, hef, hecov, hpb⟩ := hC4
  haveI := he

  have chart_rel : ∀ (φ ψ : (componentGroup O.width)) {T : Scheme.{0}}
      (σ : T ⟶ Spec (CommRingCat.of ↥(invField A))) (P : SchemeHomOver (σ ≫ ιK) fX),
      P.1 ≫ e φ = (LX.mul (σ ≫ ιK) P (GoodReductionJacobian.schemeHomOverComp σ rfl (d φ ψ))).1 ≫ e ψ := by
    intro φ ψ T σ P
    by_cases hφψ : φ = ψ
    · subst hφψ
      have h1 : GoodReductionJacobian.schemeHomOverComp σ rfl (d φ φ) = LX.one (σ ≫ ιK) := by
        simp only [hd_refl]; exact RelativeGroupLaw.one_natural LX _ _ σ rfl
      simp only [h1, LX.mul_one]
    · let q : SchemeHomOver σ (pullback.snd fX ιK) := RelativeGroupLaw.baseChangePointOfBase ιK P
      have hq1 : q.1 ≫ pullback.fst fX ιK = P.1 := by
        simp only [q, RelativeGroupLaw.baseChangePointOfBase_coe, pullback.lift_fst]
      have hqP : RelativeGroupLaw.baseChangePointToBase ιK q = P := RelativeGroupLaw.baseChangePointToBase_ofBase ιK P
      have hw := (hpb φ ψ hφψ).w
      calc P.1 ≫ e φ = q.1 ≫ (jK ≫ e φ) := by rw [← hq1, Category.assoc]
        _ = q.1 ≫ (((t φ ψ).hom ≫ jK) ≫ e ψ) := by rw [hw]
        _ = (q.1 ≫ (t φ ψ).hom ≫ pullback.fst fX ιK) ≫ e ψ := by simp only [Category.assoc]; rfl
        _ = _ := by rw [ht_pt φ ψ σ q, hqP]

  let 𝒰 : Scheme.OpenCover.{0} N := Scheme.Cover.mkOfCovers (componentGroup O.width) (fun _ => X) e (by
    intro n
    have : n ∈ ⋃ φ, Set.range (e φ).base := by rw [hecov]; trivial
    obtain ⟨_, ⟨φ, rfl⟩, ⟨x, rfl⟩⟩ := this
    exact ⟨φ, x, rfl⟩)

  haveI hsep : IsSeparated gN := by
    refine AlgebraicGeometry.IsSeparated.of_isClosedImmersion_mapDesc_openCover gN 𝒰 fun φ ψ => ?_
    change IsClosedImmersion (pullback.mapDesc (e φ) (e ψ) gN)
    by_cases hφψ : φ = ψ
    · subst hφψ
      exact NeronGlueAux.SepTransport.isClosedImmersion_mapDesc_of_isOpenImmersion fX gN (e φ) (hef φ)
    · have hC6 := GoodReductionJacobian.RelativeGroupLaw.isClosedImmersion_lift_fst_mul_of_not_exists_section
        ↥(shRing A) ↥(invField A) LX (d φ ψ) (hd_noext φ ψ hφψ)
      refine NeronGlueAux.SepTransport.isClosedImmersion_mapDesc_of_isPullback fX gN (e φ) (e ψ) (hef φ) (hef ψ)
        (pullback.fst fX ιK) (t φ ψ).hom (hpb φ ψ hφψ) ?_
      have heq : (pullback.lift (pullback.fst fX ιK) ((t φ ψ).hom ≫ pullback.fst fX ιK)
          (by rw [Category.assoc]; exact (ht_over φ ψ).symm) : GK ⟶ pullback fX fX) =
          pullback.lift (pullback.fst fX ιK)
            (LX.mul (pullback.snd fX ιK ≫ ιK) ⟨pullback.fst fX ιK, pullback.condition⟩
              (GoodReductionJacobian.schemeHomOverComp (pullback.snd fX ιK) rfl (d φ ψ))).1
            (pullback.condition.trans (LX.mul (pullback.snd fX ιK ≫ ιK) ⟨pullback.fst fX ιK, pullback.condition⟩
              (GoodReductionJacobian.schemeHomOverComp (pullback.snd fX ιK) rfl (d φ ψ))).2.symm) := by
        apply pullback.hom_ext
        · simp only [pullback.lift_fst]
        · simp only [pullback.lift_snd, ht_fst]
          rfl
      rw [heq]
      exact hC6

  have hC8 := GoodReductionJacobian.RelativeGroupLaw.exists_relativeGroupLaw_glued_charts_mul_eq ↥(shRing A) ↥(invField A)
      LX hLX y c hcK hc0 gN e he hef hecov t ht_fst hpb
  obtain ⟨LN, hLNcomm, hchart⟩ := hC8

  let openImm : SchemeHomOver (RelativeGroupLaw.baseChangeStr Λ.shStr O.g) gN := ⟨e 0, hef 0⟩

  haveI : IsLocalHom (shToPlace A) := by
    refine ⟨fun x hx => ?_⟩
    obtain ⟨b, hb⟩ := hx.exists_right_inv
    have hx0 : ((x : ↥(invField A)) : AlgebraicClosure ℚ) ≠ 0 := by
      intro h0
      have : ((shToPlace A x : ↥A) : AlgebraicClosure ℚ) * (b : AlgebraicClosure ℚ) = 1 := by
        exact congrArg (fun z : ↥A => (z : AlgebraicClosure ℚ)) hb
      rw [coe_shToPlace, h0, zero_mul] at this
      exact zero_ne_one this
    have hxK0 : (x : ↥(invField A)) ≠ 0 := fun h => hx0 (by rw [h]; rfl)
    have hbinv : (b : AlgebraicClosure ℚ) = ((x : ↥(invField A)) : AlgebraicClosure ℚ)⁻¹ := by
      have : ((shToPlace A x : ↥A) : AlgebraicClosure ℚ) * (b : AlgebraicClosure ℚ) = 1 :=
        congrArg (fun z : ↥A => (z : AlgebraicClosure ℚ)) hb
      rw [coe_shToPlace] at this
      exact (eq_inv_of_mul_eq_one_right this)
    have hmem : (x : ↥(invField A))⁻¹ ∈ shRing A := by
      rw [ValuationSubring.mem_comap, map_inv₀]
      change (((x : ↥(invField A)) : AlgebraicClosure ℚ))⁻¹ ∈ A
      rw [← hbinv]; exact b.2
    refine ⟨⟨x, ⟨(x : ↥(invField A))⁻¹, hmem⟩, ?_, ?_⟩, rfl⟩
    · apply Subtype.ext; exact mul_inv_cancel₀ hxK0
    · apply Subtype.ext; exact inv_mul_cancel₀ hxK0
  have hne : ∀ φ ψ : (componentGroup O.width), φ ≠ ψ → ∀ n ∈ Set.range (e φ).base ∩ Set.range (e ψ).base,
      gN.base n ≠ IsLocalRing.closedPoint ↥(shRing A) := by
    intro φ ψ hφψ n hn hclosed
    obtain ⟨u, hu⟩ := NeronGlueAux.SepTransport.exists_eq_of_mem_range_of_isPullback (e φ) (e ψ)
      (pullback.fst fX ιK) (t φ ψ).hom (hpb φ ψ hφψ) n hn.1 hn.2

    have h1 : gN.base n = ιK.base ((pullback.snd fX ιK).base u) := by
      rw [← hu, ← Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply, hef,
        pullback.condition]
    rw [h1] at hclosed

    have hgen : ιK.base ((pullback.snd fX ιK).base u) = ⟨⊥, Ideal.isPrime_bot⟩ := by
      apply PrimeSpectrum.ext
      change Ideal.comap (algebraMap ↥(shRing A) ↥(invField A)) _ = ⊥
      rw [Ideal.eq_bot_of_prime ((pullback.snd fX ιK).base u).asIdeal,
        Ideal.comap_bot_of_injective _ (IsFractionRing.injective ↥(shRing A) ↥(invField A))]
    rw [hgen] at hclosed
    have hmax : (⊥ : Ideal ↥(shRing A)) = IsLocalRing.maximalIdeal ↥(shRing A) :=
      congrArg PrimeSpectrum.asIdeal hclosed
    exact (IsDiscreteValuationRing.not_isField ↥(shRing A))
      (IsLocalRing.isField_iff_maximalIdeal_eq.mpr hmax.symm)
  have hC12 := GoodReductionJacobian.RelativeGroupLaw.exists_spec_glued_charts (shToPlace A) LX LN e he hef hecov hne c hchart
  obtain ⟨specN, hspecN, hspecN_mul, hspecN_surj⟩ := hC12

  refine ⟨N, gN, LN, hLNcomm, ⟨?smooth, hsep, ?loft, ?qc⟩, ?hext, openImm, specN, he 0, ?openImm_mul, ?pts_surj,
    hspecN_mul, hspecN_surj, ?specN_zero, ?comp_pin⟩
  · exact IsZariskiLocalAtSource.of_openCover (P := @Smooth) 𝒰 fun φ => by
      change Smooth (e φ ≫ gN); rw [hef]; infer_instance
  · exact IsZariskiLocalAtSource.of_openCover (P := @LocallyOfFiniteType) 𝒰 fun φ => by
      change LocallyOfFiniteType (e φ ≫ gN); rw [hef]; infer_instance
  ·
    have hfin := Fintype.equivFin (componentGroup O.width)
    have hcov' : (⋃ i : Fin (Fintype.card (componentGroup O.width)), Set.range (e (hfin.symm i)).base) = Set.univ := by
      rw [← hecov]; ext n; simp only [Set.mem_iUnion, Set.mem_range]
      constructor
      · rintro ⟨i, x, rfl⟩; exact ⟨hfin.symm i, x, rfl⟩
      · rintro ⟨φ, x, rfl⟩; exact ⟨hfin φ, x, by rw [Equiv.symm_apply_apply]⟩
    have hq := AlgebraicGeometry.locallyOfFiniteType_and_quasiCompact_of_finite_openCover (f := fX) (σ := gN)
      (fun i => e (hfin.symm i)) (fun i => he _) (fun i => hef _) hcov'
    exact hq.2
  · exact NeronGlueAux.hext_aux N₀ p hpN₀ A hA Λ O gN e hef yK hyK_add hyK_bij y' hy'comp hy'0 y hy hbar key chart_rel
      (fun σ u => NeronGlueAux.exists_pt_eq_comp_chart e t gN hef hpb hecov 0 σ u)
  ·
    intro T s x z
    have hch := hchart s 0 0 x z
    have hc00 : GoodReductionJacobian.schemeHomOverComp s (Category.comp_id s) (c 0 0) = LX.one s := by
      rw [hc0]; exact RelativeGroupLaw.one_natural LX _ _ s (Category.comp_id s)
    have h2 : LX.mul s (LX.mul s x z) (GoodReductionJacobian.schemeHomOverComp s (Category.comp_id s) (c 0 0)) =
        LX.mul s x z := by
      rw [hc00]; exact LX.mul_one s _
    refine (hch.trans ?_).symm
    exact (congrArg (fun w => NeronModelInfra.schemeHomOverComp w (⟨e (0 + 0), hef (0 + 0)⟩ : SchemeHomOver fX gN)) h2).trans
      (NeronGlueAux.chart_congr e hef (add_zero 0) _)
  · exact NeronGlueAux.pts_surj_aux N₀ p hpN₀ A hA Λ O gN e hef hbar
      (fun u => NeronGlueAux.exists_pt_eq_comp_chart e t gN hef hpb hecov 0 σb u)
  ·
    intro s
    refine (hspecN s 0).trans ⟨?_, ?_⟩
    · rintro ⟨a, ha⟩
      refine ⟨castOver Λ.shPt_comp_shStr (RelativeGroupLaw.baseChangePointToBase Λ.shStr a), ?_⟩
      have hsh : Λ.shLift (castOver Λ.shPt_comp_shStr (RelativeGroupLaw.baseChangePointToBase Λ.shStr a)) = a := by
        change RelativeGroupLaw.baseChangePointOfBase Λ.shStr
          (castOver Λ.shPt_comp_shStr.symm (castOver Λ.shPt_comp_shStr (RelativeGroupLaw.baseChangePointToBase Λ.shStr a))) = a
        have hcc : castOver Λ.shPt_comp_shStr.symm
            (castOver Λ.shPt_comp_shStr (RelativeGroupLaw.baseChangePointToBase Λ.shStr a)) =
            RelativeGroupLaw.baseChangePointToBase Λ.shStr a := Subtype.ext rfl
        rw [hcc]; exact RelativeGroupLaw.baseChangePointOfBase_toBase Λ.shStr a
      rw [hsh]; exact ha
    · rintro ⟨s₀, hs₀⟩; exact ⟨Λ.shLift s₀, hs₀⟩
  · intro x s H
    exact NeronGlueAux.P2.comp_pin_aux N₀ p hpN₀ A hA Λ O LX gN e hef σb ιK hbar (pullback.fst O.g Λ.shStr)
      shGenLift_fst (fun a => ⟨castOver Λ.shPt_comp_shStr (RelativeGroupLaw.baseChangePointToBase Λ.shStr a), rfl⟩)
      yK hyK_bar yK_sub y' hy'comp y hy hy0 chart_rel specN hspecN x s H

end S_ModularCurve_JZeroNeronObjectAtP_exists_neronGlue
end P2MW
export P2MW.S_ModularCurve_JZeroNeronObjectAtP_exists_neronGlue (solution)
