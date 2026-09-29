-- Prove2me | solution 1 for ModularCurve.JZeroNeronObjectAtP.isFinite_schemeKerStr_special_and_finrank_eq_mul_sq
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:10.583295+00:00
-- url     : https://prove2.me/submissions/624814d1-40e5-59c5-96d5-5af7b025db6c

import Mathlib
import Definitions.Def_ModularCurve_JZeroNeronObjectAtP
import Definitions.Def_ModularCurve_JZeroNeronAtPData
import Definitions.Def_AlgebraicCurve_Repartitions
import Definitions.Def_AlgebraicGeometry_TwoAffineOpenCover

import Definitions.Def_GoodReductionJacobian_RelativeGroupLawKerPair
import Definitions.Def_AlgebraicGeometry_SplitTorusMu
import Theorems.Thm_ModularCurve_JZeroNeronObjectAtP_exists_iso_torus_kerPair_abqFibre
import Theorems.Thm_AlgebraicGeometry_SplitTorus_isFinite_schemeKerStr_and_finrank_eq_of_iso_torusScheme
import Theorems.Thm_ModularCurve_JZeroNeronObjectAtP_exists_iso_pullback_schemeKer_torus_of_abqFibre
import Theorems.Thm_AlgebraicGeometry_isFinite_pullback_and_finrank_sections_eq_mul
import Theorems.Thm_AlgebraicGeometry_flat_of_isPullback_of_flat_of_surjective
import Theorems.Thm_AlgebraicGeometry_isFinite_of_finite_setOf_exists_section_of_isAlgClosed
import Theorems.Thm_ValuationSubring_isAlgClosed_residueField_algebraicClosure_rat
import Theorems.Thm_AlgebraicGeometry_exists_algEquiv_globalSections_pullback_spec_tensorProduct
import Theorems.Thm_Module_finrank_eq_mul_of_tensorProduct_linearEquiv_baseChange
import Theorems.Thm_ModularCurve_JZeroNeronObjectAtP_exists_fppfCover_section_schemeKer_of_abqFibre
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_JZeroNeronObjectAtP_isFinite_schemeKerStr_special_and_finrank_eq_mul_sq

set_option autoImplicit false

attribute [local instance] ModularCurve.instDecidableEqResidueFieldSemistable
  ModularCurve.instAlgebraResidueFieldModularFunctionFieldCSemistable

p2m_open "CategoryTheory CategoryTheory.Limits AlgebraicGeometry P2MW.S_ModularCurve_JZeroNeronObjectAtP_isFinite_schemeKerStr_special_and_finrank_eq_mul_sq.AlgebraicGeometry NeronModelInfra GoodReductionJacobian ModularCurve IsLocalRing AlgebraicCurve ModularCurve.JZeroNeronObjectAtP"

open scoped TensorProduct

universe u

namespace TorsorRankScheme

theorem finrank_eq_of_ringEquiv {κ : Type*} [CommSemiring κ] {T₁ T₂ : Type*} [Semiring T₁] [Semiring T₂]
    (i₁ : Algebra κ T₁) (i₂ : Algebra κ T₂) (h : T₁ ≃+* T₂)
    (hc : ∀ r, h (@algebraMap κ T₁ _ _ i₁ r) = @algebraMap κ T₂ _ _ i₂ r) :
    @Module.finrank κ T₁ _ _ i₁.toModule = @Module.finrank κ T₂ _ _ i₂.toModule := by
  letI := i₁; letI := i₂
  exact (AlgEquiv.ofRingEquiv (f := h) hc).toLinearEquiv.finrank_eq

theorem finrank_eq_of_algebraMap_eq {κ : Type*} [CommSemiring κ] {T : Type*} [Semiring T]
    (i₁ i₂ : Algebra κ T) (hc : ∀ r, @algebraMap κ T _ _ i₁ r = @algebraMap κ T _ _ i₂ r) :
    @Module.finrank κ T _ _ i₁.toModule = @Module.finrank κ T _ _ i₂.toModule :=
  finrank_eq_of_ringEquiv i₁ i₂ (RingEquiv.refl T) hc

theorem appLE_top_top {κ : Type u} [Field κ] {X : Scheme.{u}} (q : X ⟶ Spec (.of κ)) :
    q.appLE ⊤ ⊤ le_top = q.appTop := by
  rw [Scheme.Hom.appTop, ← Scheme.Hom.appLE_eq_app]
  rfl

theorem moduleFinite_of_isFinite {κ : Type u} [Field κ] {W : Scheme.{u}} (q : W ⟶ Spec (.of κ)) [IsFinite q] :
    @Module.Finite κ Γ(W, ⊤) _ _ (((Scheme.ΓSpecIso (.of κ)).inv ≫ q.appTop).hom.toAlgebra).toModule := by
  haveI : IsAffine W := isAffine_of_isAffineHom q
  obtain ⟨_, hfin⟩ := (HasAffineProperty.iff_of_isAffine (P := @IsFinite) (f := q)).mp inferInstance
  have h2 : (q.appTop.hom.comp (Scheme.ΓSpecIso (.of κ)).inv.hom).Finite :=
    RingHom.Finite.comp hfin
      (RingHom.Finite.of_surjective _ (Scheme.ΓSpecIso (.of κ)).commRingCatIsoToRingEquiv.symm.surjective)
  exact h2

theorem isoSpec_hom_comp_spec_algebraMap {κ : Type u} [CommRing κ] {X : Scheme.{u}} [IsAffine X]
    (q : X ⟶ Spec (.of κ)) :
    X.isoSpec.hom ≫ Spec.map ((Scheme.ΓSpecIso (.of κ)).inv ≫ q.appTop) = q := by
  rw [Spec.map_comp, Scheme.isoSpec_hom, ← Category.assoc, ← Scheme.toSpecΓ_naturality, Category.assoc,
    ← SpecMap_ΓSpecIso_hom, ← Spec.map_comp, Iso.inv_hom_id, Spec.map_id, Category.comp_id]

end TorsorRankScheme

namespace AlgebraicGeometry p2m_export "AlgebraicGeometry" "Spec.map_comp HasRingHomProperty.iff_of_isAffine Scheme.Hom.finite_preimage_singleton Surjective HasAffineProperty IsProper Scheme.Hom Scheme.Γ Scheme.isoSpec_hom IsFinite isAffine_of_isAffineHom IsAffine LocallyOfFiniteType Spec Spec.map Scheme.toSpecΓ_naturality Scheme Scheme.Hom.appTop Scheme.toSpecΓ_appTop HasAffineProperty.iff_of_isAffine Scheme.Hom.comp_appTop Flat IsClosedImmersion locallyOfFiniteType_of_comp IsSeparated ext_of_apply_closedPoint_eq IsFinite.of_comp SpecMap_ΓSpecIso_hom Spec.map_id HasRingHomProperty Scheme.Hom.comp_apply Scheme.ΓSpecIso Scheme.Hom.appLE_eq_app Scheme.TwoAffineOpenCover Scheme.TwoAffineOpenCover.algebraOfHom SplitTorus.torusStr SplitTorus.isFinite_schemeKerStr_and_finrank_eq_of_iso_torusScheme isFinite_pullback_and_finrank_sections_eq_mul flat_of_isPullback_of_flat_of_surjective isFinite_of_finite_setOf_exists_section_of_isAlgClosed exists_algEquiv_globalSections_pullback_spec_tensorProduct" end AlgebraicGeometry
p2m_open_scoped "AlgebraicGeometry" in
open TorsorRankScheme in

theorem AlgebraicGeometry.finrank_sections_eq_mul_of_iso_pullback_of_finite_flat_surjective
    {κ : Type u} [Field κ] {X Y K : Scheme.{u}}
    (qX : X ⟶ Spec (.of κ)) (qY : Y ⟶ Spec (.of κ)) (qK : K ⟶ Spec (.of κ))
    [IsFinite qX] [IsFinite qY] [IsFinite qK]
    (ψ : X ⟶ Y) (hψ : ψ ≫ qY = qX) [IsFinite ψ] [Flat ψ] [Surjective ψ]
    (φ : pullback qK qX ≅ pullback ψ ψ) (hφ : φ.hom ≫ pullback.snd ψ ψ = pullback.snd qK qX) :
    letI := Scheme.TwoAffineOpenCover.algebraOfHom qX ⊤
    letI := Scheme.TwoAffineOpenCover.algebraOfHom qY ⊤
    letI := Scheme.TwoAffineOpenCover.algebraOfHom qK ⊤
    Module.finrank κ Γ(X, ⊤) = Module.finrank κ Γ(K, ⊤) * Module.finrank κ Γ(Y, ⊤) := by

  let iX' : Algebra κ Γ(X, ⊤) := ((Scheme.ΓSpecIso (.of κ)).inv ≫ qX.appTop).hom.toAlgebra
  let iY' : Algebra κ Γ(Y, ⊤) := ((Scheme.ΓSpecIso (.of κ)).inv ≫ qY.appTop).hom.toAlgebra
  let iK' : Algebra κ Γ(K, ⊤) := ((Scheme.ΓSpecIso (.of κ)).inv ≫ qK.appTop).hom.toAlgebra
  have hX : @Module.finrank κ Γ(X, ⊤) _ _ (Scheme.TwoAffineOpenCover.algebraOfHom qX ⊤).toModule =
      @Module.finrank κ Γ(X, ⊤) _ _ iX'.toModule :=
    finrank_eq_of_algebraMap_eq _ _ fun r => by
      show ((Scheme.ΓSpecIso (.of κ)).inv ≫ qX.appLE ⊤ ⊤ le_top).hom r = ((Scheme.ΓSpecIso (.of κ)).inv ≫ qX.appTop).hom r
      rw [appLE_top_top]
  have hY : @Module.finrank κ Γ(Y, ⊤) _ _ (Scheme.TwoAffineOpenCover.algebraOfHom qY ⊤).toModule =
      @Module.finrank κ Γ(Y, ⊤) _ _ iY'.toModule :=
    finrank_eq_of_algebraMap_eq _ _ fun r => by
      show ((Scheme.ΓSpecIso (.of κ)).inv ≫ qY.appLE ⊤ ⊤ le_top).hom r = ((Scheme.ΓSpecIso (.of κ)).inv ≫ qY.appTop).hom r
      rw [appLE_top_top]
  have hK : @Module.finrank κ Γ(K, ⊤) _ _ (Scheme.TwoAffineOpenCover.algebraOfHom qK ⊤).toModule =
      @Module.finrank κ Γ(K, ⊤) _ _ iK'.toModule :=
    finrank_eq_of_algebraMap_eq _ _ fun r => by
      show ((Scheme.ΓSpecIso (.of κ)).inv ≫ qK.appLE ⊤ ⊤ le_top).hom r = ((Scheme.ΓSpecIso (.of κ)).inv ≫ qK.appTop).hom r
      rw [appLE_top_top]
  rw [hX, hY, hK]
  haveI : IsAffine X := isAffine_of_isAffineHom qX
  haveI : IsAffine Y := isAffine_of_isAffineHom qY
  haveI : IsAffine K := isAffine_of_isAffineHom qK

  letI := iX'; letI := iY'; letI := iK'
  haveI : Module.Finite κ Γ(X, ⊤) := moduleFinite_of_isFinite qX
  haveI : Module.Finite κ Γ(Y, ⊤) := moduleFinite_of_isFinite qY
  haveI : Module.Finite κ Γ(K, ⊤) := moduleFinite_of_isFinite qK

  let f : X ⟶ Spec (CommRingCat.of ↑Γ(Y, ⊤)) := ψ ≫ Y.isoSpec.hom
  letI iBC : Algebra ↑Γ(Y, ⊤) ↑Γ(X, ⊤) := ((Scheme.ΓSpecIso (.of ↑Γ(Y, ⊤))).inv ≫ f.appTop).hom.toAlgebra
  have hBC : ∀ b, algebraMap ↑Γ(Y, ⊤) ↑Γ(X, ⊤) b = ψ.appTop.hom b := fun b => by
    show ((Scheme.ΓSpecIso (.of ↑Γ(Y, ⊤))).inv ≫ (ψ ≫ Y.isoSpec.hom).appTop).hom b = _
    rw [Scheme.Hom.comp_appTop, Scheme.isoSpec_hom, Scheme.toSpecΓ_appTop]
    erw [Iso.inv_hom_id_assoc]
  have hBC' : ((Scheme.ΓSpecIso (.of ↑Γ(Y, ⊤))).inv ≫ f.appTop).hom = ψ.appTop.hom := RingHom.ext hBC
  haveI : IsScalarTower κ ↑Γ(Y, ⊤) ↑Γ(X, ⊤) := IsScalarTower.of_algebraMap_eq fun r => by
    show ((Scheme.ΓSpecIso (.of κ)).inv ≫ qX.appTop).hom r =
      algebraMap ↑Γ(Y, ⊤) ↑Γ(X, ⊤) (((Scheme.ΓSpecIso (.of κ)).inv ≫ qY.appTop).hom r)
    rw [hBC, ← hψ, Scheme.Hom.comp_appTop]
    rfl

  have hflat : ψ.appTop.hom.Flat := (HasRingHomProperty.iff_of_isAffine (P := @Flat)).mp inferInstance
  have hsurjS : Function.Surjective (PrimeSpectrum.comap ψ.appTop.hom) := by
    have hnat : Spec.map ψ.appTop = X.isoSpec.inv ≫ ψ ≫ Y.isoSpec.hom := by
      rw [Scheme.isoSpec_hom, Scheme.toSpecΓ_naturality, ← Scheme.isoSpec_hom, Iso.inv_hom_id_assoc]
    have : Surjective (Spec.map ψ.appTop) := by rw [hnat]; infer_instance
    exact (Spec.map ψ.appTop).surjective
  haveI : Module.FaithfullyFlat ↑Γ(Y, ⊤) ↑Γ(X, ⊤) := by
    have h : (algebraMap ↑Γ(Y, ⊤) ↑Γ(X, ⊤)).FaithfullyFlat := by
      rw [RingHom.FaithfullyFlat.iff_flat_and_comap_surjective]
      show ((Scheme.ΓSpecIso (.of ↑Γ(Y, ⊤))).inv ≫ f.appTop).hom.Flat ∧
        Function.Surjective (PrimeSpectrum.comap ((Scheme.ΓSpecIso (.of ↑Γ(Y, ⊤))).inv ≫ f.appTop).hom)
      rw [hBC']
      exact ⟨hflat, hsurjS⟩
    exact h

  let gψ : Spec (CommRingCat.of ↑Γ(X, ⊤)) ⟶ Spec (CommRingCat.of ↑Γ(Y, ⊤)) :=
    Spec.map (CommRingCat.ofHom (algebraMap ↑Γ(Y, ⊤) ↑Γ(X, ⊤)))
  have hgψ : X.isoSpec.hom ≫ gψ = f := isoSpec_hom_comp_spec_algebraMap f
  obtain ⟨e9ψ, -⟩ := exists_algEquiv_globalSections_pullback_spec_tensorProduct f ↑Γ(X, ⊤)
  let πψ : pullback ψ ψ ⟶ pullback f gψ :=
    pullback.map ψ ψ f gψ (𝟙 X) X.isoSpec.hom Y.isoSpec.hom (by rw [Category.id_comp]) (by rw [hgψ])
  haveI : IsIso πψ := inferInstance
  have hπψ : πψ ≫ pullback.snd f gψ = pullback.snd ψ ψ ≫ X.isoSpec.hom := pullback.lift_snd _ _ _
  letI jψ' : Algebra ↑Γ(X, ⊤) Γ(pullback f gψ, ⊤) :=
    ((Scheme.ΓSpecIso (.of ↑Γ(X, ⊤))).inv ≫ (pullback.snd f gψ).appTop).hom.toAlgebra
  letI jψ : Algebra ↑Γ(X, ⊤) Γ(pullback ψ ψ, ⊤) := (pullback.snd ψ ψ).appTop.hom.toAlgebra
  let E2 : Γ(pullback f gψ, ⊤) ≃ₐ[↑Γ(X, ⊤)] Γ(pullback ψ ψ, ⊤) :=
    AlgEquiv.ofRingEquiv (f := (Scheme.Γ.mapIso (asIso πψ).op).commRingCatIsoToRingEquiv) fun c => by
      show πψ.appTop.hom (((Scheme.ΓSpecIso (.of ↑Γ(X, ⊤))).inv ≫ (pullback.snd f gψ).appTop).hom c) =
        (pullback.snd ψ ψ).appTop.hom c
      rw [← CommRingCat.comp_apply, Category.assoc, ← Scheme.Hom.comp_appTop, hπψ, Scheme.Hom.comp_appTop,
        Scheme.isoSpec_hom, Scheme.toSpecΓ_appTop]
      erw [Iso.inv_hom_id_assoc]

  letI jK : Algebra ↑Γ(X, ⊤) Γ(pullback qK qX, ⊤) := (pullback.snd qK qX).appTop.hom.toAlgebra
  let E3 : Γ(pullback ψ ψ, ⊤) ≃ₐ[↑Γ(X, ⊤)] Γ(pullback qK qX, ⊤) :=
    AlgEquiv.ofRingEquiv (f := (Scheme.Γ.mapIso φ.op).commRingCatIsoToRingEquiv) fun c => by
      show φ.hom.appTop.hom ((pullback.snd ψ ψ).appTop.hom c) = (pullback.snd qK qX).appTop.hom c
      rw [← CommRingCat.comp_apply, ← Scheme.Hom.comp_appTop, hφ]

  let gK : Spec (CommRingCat.of ↑Γ(X, ⊤)) ⟶ Spec (CommRingCat.of κ) :=
    Spec.map (CommRingCat.ofHom (algebraMap κ ↑Γ(X, ⊤)))
  have hgK : X.isoSpec.hom ≫ gK = qX := isoSpec_hom_comp_spec_algebraMap qX
  obtain ⟨e9K, -⟩ := exists_algEquiv_globalSections_pullback_spec_tensorProduct qK ↑Γ(X, ⊤)
  let πK : pullback qK qX ⟶ pullback qK gK :=
    pullback.map qK qX qK gK (𝟙 K) X.isoSpec.hom (𝟙 _) (by simp) (by rw [Category.comp_id, hgK])
  haveI : IsIso πK := inferInstance
  have hπK : πK ≫ pullback.snd qK gK = pullback.snd qK qX ≫ X.isoSpec.hom := pullback.lift_snd _ _ _
  letI jK' : Algebra ↑Γ(X, ⊤) Γ(pullback qK gK, ⊤) :=
    ((Scheme.ΓSpecIso (.of ↑Γ(X, ⊤))).inv ≫ (pullback.snd qK gK).appTop).hom.toAlgebra
  let E4 : Γ(pullback qK gK, ⊤) ≃ₐ[↑Γ(X, ⊤)] Γ(pullback qK qX, ⊤) :=
    AlgEquiv.ofRingEquiv (f := (Scheme.Γ.mapIso (asIso πK).op).commRingCatIsoToRingEquiv) fun c => by
      show πK.appTop.hom (((Scheme.ΓSpecIso (.of ↑Γ(X, ⊤))).inv ≫ (pullback.snd qK gK).appTop).hom c) =
        (pullback.snd qK qX).appTop.hom c
      rw [← CommRingCat.comp_apply, Category.assoc, ← Scheme.Hom.comp_appTop, hπK, Scheme.Hom.comp_appTop,
        Scheme.isoSpec_hom, Scheme.toSpecΓ_appTop]
      erw [Iso.inv_hom_id_assoc]

  let e : ↑Γ(X, ⊤) ⊗[↑Γ(Y, ⊤)] ↑Γ(X, ⊤) ≃ₗ[↑Γ(X, ⊤)] ↑Γ(X, ⊤) ⊗[κ] ↑Γ(K, ⊤) :=
    (e9ψ.trans (E2.trans (E3.trans (E4.symm.trans e9K.symm)))).toLinearEquiv
  exact Module.finrank_eq_mul_of_tensorProduct_linearEquiv_baseChange e

noncomputable section

namespace S2A

section KerPts

variable {S : Type u} [CommRing S] {Y : Scheme.{u}} {h : Y ⟶ Spec (CommRingCat.of S)}
  (H : RelativeGroupLaw S h) (n : ℕ)

theorem comp_schemeNsmul {T : Scheme.{u}} {t : T ⟶ Spec (CommRingCat.of S)} (z : SchemeHomOver t h) :
    z.1 ≫ H.schemeNsmul n = (H.nsmul t n z).1 := by
  have e : GoodReductionJacobian.schemeHomOverComp z.1 z.2 (RelativeGroupLaw.idPoint (f := h)) = z :=
    Subtype.ext (Category.comp_id _)
  have key := congrArg Subtype.val (H.nsmul_natural h t z.1 z.2 n RelativeGroupLaw.idPoint)
  rw [e, GoodReductionJacobian.schemeHomOverComp_coe] at key
  exact key

theorem schemeKer_fst_comp {T : Scheme.{u}} (a : T ⟶ H.schemeKer n) :
    (a ≫ pullback.fst _ _) ≫ h = a ≫ H.schemeKerStr n := by
  calc (a ≫ pullback.fst _ _) ≫ h
      = a ≫ pullback.fst _ _ ≫ (H.schemeNsmul n ≫ h) := by rw [H.schemeNsmul_over, Category.assoc]
    _ = a ≫ (pullback.fst _ _ ≫ H.schemeNsmul n) ≫ h := by simp only [Category.assoc]
    _ = a ≫ (pullback.snd _ _ ≫ (H.one (𝟙 _)).1) ≫ h := by rw [pullback.condition]
    _ = a ≫ H.schemeKerStr n := by rw [Category.assoc, (H.one (𝟙 _)).2, Category.comp_id]

def kerPtOut {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of S)) (a : T ⟶ H.schemeKer n)
    (ha : a ≫ H.schemeKerStr n = t) : SchemeHomOver t h :=
  ⟨a ≫ pullback.fst _ _, (schemeKer_fst_comp H n a).trans ha⟩

@[scoped simp]
theorem kerPtOut_coe {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of S)) (a : T ⟶ H.schemeKer n)
    (ha : a ≫ H.schemeKerStr n = t) : (kerPtOut H n t a ha).1 = a ≫ pullback.fst _ _ :=
  rfl

theorem nsmul_kerPtOut {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of S)) (a : T ⟶ H.schemeKer n)
    (ha : a ≫ H.schemeKerStr n = t) : H.nsmul t n (kerPtOut H n t a ha) = H.one t := by
  apply Subtype.ext
  rw [← comp_schemeNsmul, RelativeGroupLaw.one_coe_eq, kerPtOut_coe, ← ha]
  simp only [Category.assoc, pullback.condition]

def kerPtIn {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of S)) (z : SchemeHomOver t h)
    (hz : H.nsmul t n z = H.one t) : T ⟶ H.schemeKer n :=
  pullback.lift z.1 t (by rw [comp_schemeNsmul, hz, RelativeGroupLaw.one_coe_eq])

@[scoped simp]
theorem kerPtIn_fst {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of S)) (z : SchemeHomOver t h)
    (hz : H.nsmul t n z = H.one t) : kerPtIn H n t z hz ≫ pullback.fst _ _ = z.1 :=
  pullback.lift_fst _ _ _

@[scoped simp]
theorem kerPtIn_str {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of S)) (z : SchemeHomOver t h)
    (hz : H.nsmul t n z = H.one t) : kerPtIn H n t z hz ≫ H.schemeKerStr n = t :=
  pullback.lift_snd _ _ _

end KerPts

section Hom

variable {S : Type u} [CommRing S] {Y Y' : Scheme.{u}} {h : Y ⟶ Spec (CommRingCat.of S)} {h' : Y' ⟶ Spec (CommRingCat.of S)}

namespace IsHom

private theorem _root_.S2A.IsHom.nsmul {H : RelativeGroupLaw S h} {H' : RelativeGroupLaw S h'} {φ : SchemeHomOver h h'}
    (hφ : RelativeGroupLaw.IsHom H H' φ) {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of S)) (n : ℕ)
    (x : SchemeHomOver t h) :
    NeronModelInfra.schemeHomOverComp (H.nsmul t n x) φ = H'.nsmul t n (NeronModelInfra.schemeHomOverComp x φ) := by
  induction n with
  | zero => rw [RelativeGroupLaw.nsmul_zero, RelativeGroupLaw.nsmul_zero, RelativeGroupLaw.IsHom.one hφ]
  | succ n ih => rw [RelativeGroupLaw.nsmul_succ, RelativeGroupLaw.nsmul_succ, hφ t, ih]

end IsHom
p2m_export "S2A" "IsHom.nsmul"
end Hom

end S2A
p2m_reactivate "P2MW.S_ModularCurve_JZeroNeronObjectAtP_isFinite_schemeKerStr_special_and_finrank_eq_mul_sq.S2A"

end
p2m_reactivate "P2MW.S_ModularCurve_JZeroNeronObjectAtP_isFinite_schemeKerStr_special_and_finrank_eq_mul_sq.S2A"

open S2A in
set_option maxHeartbeats 6400000 in
theorem solution
    (N₀ p : ℕ) [NeZero N₀] [Fact p.Prime] [NeZero p] (hpN₀ : ¬ p ∣ N₀)
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime p)
    (Λ : JZeroNeronObjectAtP.LevelData N₀ p A) (hΛ : Λ.IsJacobian)
    (O : JZeroNeronObjectAtP N₀ p hpN₀ A hA Λ) (m : ℕ) (hm : 0 < m)
    (hB : IsFinite ((Λ.L.baseChange (resPt A ≫ Λ.σA)).schemeKerStr m)) :
    IsFinite ((O.L.baseChange (resPt A ≫ Λ.σA)).schemeKerStr m) ∧
    (letI := Scheme.TwoAffineOpenCover.algebraOfHom ((O.L.baseChange (resPt A ≫ Λ.σA)).schemeKerStr m) ⊤
     letI := Scheme.TwoAffineOpenCover.algebraOfHom ((Λ.L.baseChange (resPt A ≫ Λ.σA)).schemeKerStr m) ⊤
     Module.finrank (ResidueField ↥A) Γ((O.L.baseChange (resPt A ≫ Λ.σA)).schemeKer m, ⊤) =
       m ^ O.toricRank *
         Module.finrank (ResidueField ↥A) Γ((Λ.L.baseChange (resPt A ≫ Λ.σA)).schemeKer m, ⊤) ^ 2) := by
  classical
  haveI : IsAlgClosed (ResidueField ↥A) := ValuationSubring.isAlgClosed_residueField_algebraicClosure_rat A
  haveI := O.locallyOfFiniteType
  haveI := O.quasiCompact
  haveI := O.separated
  haveI : IsSeparated Λ.f := hΛ.1.proper.toIsSeparated
  haveI : IsProper Λ.f := hΛ.1.proper
  haveI : LocallyOfFiniteType Λ.f := inferInstance
  haveI : IsClosedImmersion ((Λ.L.baseChange (resPt A ≫ Λ.σA)).one (𝟙 (Spec (CommRingCat.of (ResidueField ↥A))))).1 :=
    RelativeGroupLaw.isClosedImmersion_one (Λ.L.baseChange (resPt A ≫ Λ.σA))
  haveI : IsClosedImmersion ((O.L.baseChange (resPt A ≫ Λ.σA)).one (𝟙 (Spec (CommRingCat.of (ResidueField ↥A))))).1 :=
    RelativeGroupLaw.isClosedImmersion_one (O.L.baseChange (resPt A ≫ Λ.σA))
  haveI : IsFinite ((Λ.L.baseChange (resPt A ≫ Λ.σA)).schemeKerStr m) := hB
  have habq : ∀ i, RelativeGroupLaw.IsHom (O.L.baseChange (resPt A ≫ Λ.σA)) (Λ.L.baseChange (resPt A ≫ Λ.σA)) (O.abqFibre i) := fun i => O.abqFibre_mul i

  let gm := (O.L.baseChange (resPt A ≫ Λ.σA)).schemeKerStr m
  let am := (Λ.L.baseChange (resPt A ≫ Λ.σA)).schemeKerStr m
  let jG := pullback.fst ((O.L.baseChange (resPt A ≫ Λ.σA)).schemeNsmul m) ((O.L.baseChange (resPt A ≫ Λ.σA)).one (𝟙 _)).1
  let jA := pullback.fst ((Λ.L.baseChange (resPt A ≫ Λ.σA)).schemeNsmul m) ((Λ.L.baseChange (resPt A ≫ Λ.σA)).one (𝟙 _)).1
  let xG : SchemeHomOver gm (RelativeGroupLaw.baseChangeStr (resPt A ≫ Λ.σA) O.g) := kerPtOut (O.L.baseChange (resPt A ≫ Λ.σA)) m gm (𝟙 _) (Category.id_comp _)
  have hxG : xG.1 = jG := Category.id_comp _
  let z : Fin 2 → SchemeHomOver gm (RelativeGroupLaw.baseChangeStr (resPt A ≫ Λ.σA) Λ.f) :=
    fun i => NeronModelInfra.schemeHomOverComp xG (O.abqFibre i)
  have hz : ∀ i, (Λ.L.baseChange (resPt A ≫ Λ.σA)).nsmul gm m (z i) = (Λ.L.baseChange (resPt A ≫ Λ.σA)).one gm := by
    intro i
    show (Λ.L.baseChange (resPt A ≫ Λ.σA)).nsmul gm m (NeronModelInfra.schemeHomOverComp xG (O.abqFibre i)) = _
    rw [← IsHom.nsmul (habq i), nsmul_kerPtOut, RelativeGroupLaw.IsHom.one (habq i)]
  let ψi : Fin 2 → ((O.L.baseChange (resPt A ≫ Λ.σA)).schemeKer m ⟶ (Λ.L.baseChange (resPt A ≫ Λ.σA)).schemeKer m) := fun i => kerPtIn (Λ.L.baseChange (resPt A ≫ Λ.σA)) m gm (z i) (hz i)
  have hψi_str : ∀ i, ψi i ≫ am = gm := fun i => kerPtIn_str _ _ _ _ _
  have hψi_j : ∀ i, ψi i ≫ jA = jG ≫ (O.abqFibre i).1 := by
    intro i
    show kerPtIn (Λ.L.baseChange (resPt A ≫ Λ.σA)) m gm (z i) (hz i) ≫ pullback.fst _ _ = _
    rw [kerPtIn_fst, NeronModelInfra.schemeHomOverComp_coe, hxG]
  let ψ : (O.L.baseChange (resPt A ≫ Λ.σA)).schemeKer m ⟶ pullback am am := pullback.lift (ψi 0) (ψi 1) (by rw [hψi_str, hψi_str])
  have hψ₀ : ψ ≫ pullback.fst _ _ ≫ jA = jG ≫ (O.abqFibre 0).1 := by
    rw [← Category.assoc, pullback.lift_fst, hψi_j]
  have hψ₁ : ψ ≫ pullback.snd _ _ ≫ jA = jG ≫ (O.abqFibre 1).1 := by
    rw [← Category.assoc, pullback.lift_snd, hψi_j]
  have hψq : ψ ≫ (pullback.fst am am ≫ am) = gm := by
    rw [← Category.assoc, pullback.lift_fst, hψi_str]

  let km := (RelativeGroupLaw.kerPairLaw (O.L.baseChange (resPt A ≫ Λ.σA)) (Λ.L.baseChange (resPt A ≫ Λ.σA)) O.abqFibre (fun i => O.abqFibre_mul i)).schemeKerStr m

  obtain ⟨eT, heT, henT⟩ := ModularCurve.JZeroNeronObjectAtP.exists_iso_torus_kerPair_abqFibre N₀ p hpN₀ A hA Λ hΛ O
  have hefT : eT.hom ≫ RelativeGroupLaw.kerPairStr (Λ.L.baseChange (resPt A ≫ Λ.σA)) O.abqFibre = SplitTorus.torusStr (ResidueField ↥A) O.toricRank := by
    show eT.hom ≫ (RelativeGroupLaw.kerPairι (Λ.L.baseChange (resPt A ≫ Λ.σA)) O.abqFibre ≫ _) = _
    rw [← Category.assoc, heT]
    exact O.torusFibre.2
  obtain ⟨hKfin, ⟨eK, heK⟩, hKrank⟩ :=
    AlgebraicGeometry.SplitTorus.isFinite_schemeKerStr_and_finrank_eq_of_iso_torusScheme O.toricRank
      (RelativeGroupLaw.kerPairStr (Λ.L.baseChange (resPt A ≫ Λ.σA)) O.abqFibre) (RelativeGroupLaw.kerPairLaw (O.L.baseChange (resPt A ≫ Λ.σA)) (Λ.L.baseChange (resPt A ≫ Λ.σA)) O.abqFibre (fun i => O.abqFibre_mul i)) eT hefT henT m hm

  obtain ⟨U, u, hu_flat, hu_surj, hu_lfp, s, hs⟩ :=
    ModularCurve.JZeroNeronObjectAtP.exists_fppfCover_section_schemeKer_of_abqFibre N₀ p hpN₀ A hA Λ hΛ O m hm ψ hψ₀ hψ₁
  obtain ⟨φ, hφ⟩ :=
    ModularCurve.JZeroNeronObjectAtP.exists_iso_pullback_schemeKer_torus_of_abqFibre N₀ p hpN₀ A hA Λ hΛ O m hm ψ hψ₀ hψ₁

  have hbc : Flat (pullback.snd ψ u) ∧ Surjective (pullback.snd ψ u) := by

    subst hs

    haveI : Flat km := inferInstance
    haveI : Surjective km :=
      ⟨fun q => ⟨(kerPtIn (RelativeGroupLaw.kerPairLaw (O.L.baseChange (resPt A ≫ Λ.σA)) (Λ.L.baseChange (resPt A ≫ Λ.σA)) O.abqFibre (fun i => O.abqFibre_mul i)) m (𝟙 _) ((RelativeGroupLaw.kerPairLaw (O.L.baseChange (resPt A ≫ Λ.σA)) (Λ.L.baseChange (resPt A ≫ Λ.σA)) O.abqFibre (fun i => O.abqFibre_mul i)).one (𝟙 _)) (RelativeGroupLaw.nsmul_unit _ _ _)) q,
        Subsingleton.elim _ _⟩⟩
    let φ' : pullback km gm ≅ pullback ψ ψ := φ ≪≫ pullbackSymmetry ψ ψ
    have hφ' : φ'.hom ≫ pullback.fst ψ ψ = pullback.snd km gm := by
      show (φ.hom ≫ (pullbackSymmetry ψ ψ).hom) ≫ _ = _
      rw [Category.assoc, pullbackSymmetry_hom_comp_fst, hφ]
    let i1 := pullbackSymmetry ψ (s ≫ ψ)
    let i2 := (pullbackRightPullbackFstIso ψ ψ s).symm
    haveI : IsIso φ'.inv := inferInstance
    let i4 : pullback s (pullback.fst ψ ψ) ⟶ pullback s (pullback.snd km gm) :=
      pullback.map s (pullback.fst ψ ψ) s (pullback.snd km gm) (𝟙 U) φ'.inv (𝟙 _)
        (by rw [Category.comp_id, Category.id_comp]) (by rw [Category.comp_id, ← hφ', Iso.inv_hom_id_assoc])
    haveI : IsIso i4 := inferInstance
    let i5a := pullbackSymmetry s (pullback.snd km gm)
    let i5 := pullbackLeftPullbackSndIso km gm s
    have hchain : pullback.snd ψ (s ≫ ψ) =
        (i1.hom ≫ i2.hom ≫ i4 ≫ i5a.hom ≫ i5.hom) ≫ pullback.snd km (s ≫ gm) := by
      simp only [Category.assoc]
      rw [pullbackLeftPullbackSndIso_hom_snd, pullbackSymmetry_hom_comp_snd, pullback.lift_fst, Category.comp_id]
      show _ = i1.hom ≫ (pullbackRightPullbackFstIso ψ ψ s).inv ≫ pullback.fst s (pullback.fst ψ ψ)
      rw [pullbackRightPullbackFstIso_inv_fst, pullbackSymmetry_hom_comp_fst]
    rw [hchain]
    exact ⟨inferInstance, inferInstance⟩
  haveI := hu_flat
  haveI := hu_surj
  haveI := hu_lfp
  haveI : Flat (pullback.snd ψ u) := hbc.1
  haveI hflat : Flat ψ :=
    AlgebraicGeometry.flat_of_isPullback_of_flat_of_surjective ψ u (pullback.snd ψ u) (pullback.fst ψ u)
      (IsPullback.of_hasPullback ψ u)

  haveI : Surjective (pullback.snd ψ u) := hbc.2
  haveI hsurj : Surjective ψ := by
    refine ⟨fun y => ?_⟩
    obtain ⟨y', hy'⟩ := hu_surj.1 y
    obtain ⟨x', hx'⟩ := (inferInstance : Surjective (pullback.snd ψ u)).1 y'
    refine ⟨pullback.fst ψ u x', ?_⟩
    rw [← Scheme.Hom.comp_apply, pullback.condition, Scheme.Hom.comp_apply, hx', hy']

  obtain ⟨hPAfin, hPArank⟩ := AlgebraicGeometry.isFinite_pullback_and_finrank_sections_eq_mul am am

  have hGfin : IsFinite gm := by

    haveI : LocallyOfFiniteType ((O.L.baseChange (resPt A ≫ Λ.σA)).schemeNsmul m) := by
      haveI : LocallyOfFiniteType ((O.L.baseChange (resPt A ≫ Λ.σA)).schemeNsmul m ≫ RelativeGroupLaw.baseChangeStr (resPt A ≫ Λ.σA) O.g) := by
        rw [RelativeGroupLaw.schemeNsmul_over]; infer_instance
      exact locallyOfFiniteType_of_comp _ (RelativeGroupLaw.baseChangeStr (resPt A ≫ Λ.σA) O.g)
    haveI hlft : LocallyOfFiniteType gm := inferInstance
    haveI : LocallyOfFiniteType km := inferInstance
    haveI : LocallyOfFiniteType (pullback.fst am am ≫ am) := inferInstance

    have hfinPA : Finite ↥(pullback am am) := by
      have h := Scheme.Hom.finite_preimage_singleton (pullback.fst am am ≫ am) (IsLocalRing.closedPoint (ResidueField ↥A))
      exact Set.finite_univ_iff.mp (h.subset fun x _ => Subsingleton.elim _ _)
    have hfinK : Finite ↥((RelativeGroupLaw.kerPairLaw (O.L.baseChange (resPt A ≫ Λ.σA)) (Λ.L.baseChange (resPt A ≫ Λ.σA)) O.abqFibre (fun i => O.abqFibre_mul i)).schemeKer m) := by
      have h := Scheme.Hom.finite_preimage_singleton km (IsLocalRing.closedPoint (ResidueField ↥A))
      exact Set.finite_univ_iff.mp (h.subset fun x _ => Subsingleton.elim _ _)

    have hφinv : φ.inv ≫ pullback.snd km gm = pullback.snd ψ ψ := by
      rw [Iso.inv_comp_eq, hφ]
    apply AlgebraicGeometry.isFinite_of_finite_setOf_exists_section_of_isAlgClosed gm

    let pt := IsLocalRing.closedPoint (ResidueField ↥A)
    let Sy : ↥(pullback am am) → Set ↥((O.L.baseChange (resPt A ≫ Λ.σA)).schemeKer m) := fun y =>
      {x | ∃ s : Spec (.of (ResidueField ↥A)) ⟶ (O.L.baseChange (resPt A ≫ Λ.σA)).schemeKer m, s ≫ gm = 𝟙 _ ∧ s pt = x ∧ ψ x = y}
    have hcover : {x : ↥((O.L.baseChange (resPt A ≫ Λ.σA)).schemeKer m) | ∃ s : Spec (.of (ResidueField ↥A)) ⟶ (O.L.baseChange (resPt A ≫ Λ.σA)).schemeKer m,
        s ≫ gm = 𝟙 _ ∧ s (IsLocalRing.closedPoint (ResidueField ↥A)) = x} ⊆ ⋃ y, Sy y := by
      rintro x ⟨s, hs, hsx⟩
      exact Set.mem_iUnion.mpr ⟨ψ x, s, hs, hsx, rfl⟩
    refine (Set.finite_iUnion fun y => ?_).subset hcover

    by_cases hy : ∃ s₀ : Spec (.of (ResidueField ↥A)) ⟶ (O.L.baseChange (resPt A ≫ Λ.σA)).schemeKer m, s₀ ≫ gm = 𝟙 _ ∧ ψ (s₀ pt) = y
    · obtain ⟨s₀, hs₀, hy₀⟩ := hy
      let Sec := {s : Spec (.of (ResidueField ↥A)) ⟶ (O.L.baseChange (resPt A ≫ Λ.σA)).schemeKer m // s ≫ gm = 𝟙 _ ∧ ψ (s pt) = y}

      have hψs : ∀ s : Sec, s.1 ≫ ψ = s₀ ≫ ψ := by
        intro s
        refine ext_of_apply_closedPoint_eq (pullback.fst am am ≫ am) ?_ ?_ ?_
        · rw [Category.assoc, hψq, s.2.1]
        · rw [Category.assoc, hψq, hs₀]
        · rw [Scheme.Hom.comp_apply, Scheme.Hom.comp_apply, s.2.2, hy₀]
      let F : Sec → ↥((RelativeGroupLaw.kerPairLaw (O.L.baseChange (resPt A ≫ Λ.σA)) (Λ.L.baseChange (resPt A ≫ Λ.σA)) O.abqFibre (fun i => O.abqFibre_mul i)).schemeKer m) := fun s =>
        (pullback.lift s.1 s₀ (hψs s) ≫ φ.inv ≫ pullback.fst km gm) pt
      have hF : Function.Injective F := by
        intro s s' hss'

        have hk : pullback.lift s.1 s₀ (hψs s) ≫ φ.inv ≫ pullback.fst km gm =
            pullback.lift s'.1 s₀ (hψs s') ≫ φ.inv ≫ pullback.fst km gm := by
          refine ext_of_apply_closedPoint_eq km ?_ ?_ hss'
          · simp only [Category.assoc, pullback.condition]
            rw [reassoc_of% hφinv, pullback.lift_snd_assoc, hs₀]
          · simp only [Category.assoc, pullback.condition]
            rw [reassoc_of% hφinv, pullback.lift_snd_assoc, hs₀]
        have hw : pullback.lift s.1 s₀ (hψs s) ≫ φ.inv = pullback.lift s'.1 s₀ (hψs s') ≫ φ.inv := by
          apply pullback.hom_ext
          · simpa only [Category.assoc] using hk
          · rw [Category.assoc, Category.assoc, hφinv, pullback.lift_snd, pullback.lift_snd]
        apply Subtype.ext
        have := congrArg (· ≫ φ.hom ≫ pullback.fst ψ ψ) hw
        simpa only [Category.assoc, Iso.inv_hom_id_assoc, pullback.lift_fst] using this
      haveI : Finite Sec := Finite.of_injective F hF
      refine (Set.finite_range fun s : Sec => s.1 pt).subset ?_
      rintro x ⟨s, hs, hsx, hxy⟩
      exact ⟨⟨s, hs, by rw [hsx]; exact hxy⟩, hsx⟩
    · refine Set.finite_empty.subset ?_
      rintro x ⟨s, hs, hsx, hxy⟩
      exact (hy ⟨s, hs, by rw [hsx]; exact hxy⟩).elim

  haveI : IsFinite gm := hGfin
  haveI : IsFinite (pullback.fst am am ≫ am) := hPAfin
  haveI : IsFinite km := hKfin

  haveI : IsFinite ψ := by
    haveI : IsFinite (ψ ≫ (pullback.fst am am ≫ am)) := by rw [hψq]; exact hGfin
    exact IsFinite.of_comp ψ (pullback.fst am am ≫ am)
  have hrankC := AlgebraicGeometry.finrank_sections_eq_mul_of_iso_pullback_of_finite_flat_surjective
    gm (pullback.fst am am ≫ am) km ψ hψq φ hφ

  refine ⟨hGfin, ?_⟩
  rw [hrankC, hKrank, hPArank, pow_two]

end S_ModularCurve_JZeroNeronObjectAtP_isFinite_schemeKerStr_special_and_finrank_eq_mul_sq
end P2MW
export P2MW.S_ModularCurve_JZeroNeronObjectAtP_isFinite_schemeKerStr_special_and_finrank_eq_mul_sq (solution)
