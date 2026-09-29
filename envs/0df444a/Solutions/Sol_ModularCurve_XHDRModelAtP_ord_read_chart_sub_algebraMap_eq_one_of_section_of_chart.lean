-- Prove2me | solution 1 for ModularCurve.XHDRModelAtP.ord_read_chart_sub_algebraMap_eq_one_of_section_of_chart
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:11.002793+00:00
-- url     : https://prove2.me/submissions/88434162-7c12-5230-9ef1-742a1db67714

import Mathlib
import Definitions.Def_ModularCurve_XHDRModelAtPCrossingFrame
import Definitions.Def_MvPolynomial_CrossingResolutionScheme
import Definitions.Def_AlgebraicCurve_PlaceEvaluation
import Definitions.Def_ModularCurve_ArithmeticGalois
import Definitions.Def_ModularCurve_JZeroNeronObjectAtP
import Definitions.Def_FLTPrelim_Ramification
import Definitions.Def_AlgebraicCurve_SemistableCharts
import Theorems.Thm_AlgebraicCurve_CurveModel_ord_placeOfPoint_ffEquiv_symm_algebraMap_eq_one_of_maximalIdeal_eq_span
import Theorems.Thm_AlgebraicGeometry_Scheme_Hom_map_stalkMap_maximalIdeal_eq_of_etale_restrict
import Theorems.Thm_MvPolynomial_CrossingQuotient_maximalIdeal_stalk_eq_span_germ_V_sub
import Theorems.Thm_AlgebraicGeometry_exists_baseChange_chart_isPullback_of_isPullback
import Theorems.Thm_MvPolynomial_CrossingQuotient_exists_algEquiv_tensorProduct_apply_U_and_apply_V
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_XHDRModelAtP_ord_read_chart_sub_algebraMap_eq_one_of_section_of_chart

set_option autoImplicit false

p2m_open "CategoryTheory CategoryTheory.Limits AlgebraicGeometry IsLocalRing AlgebraicCurve ModularCurve P2MW.S_ModularCurve_XHDRModelAtP_ord_read_chart_sub_algebraMap_eq_one_of_section_of_chart.ModularCurve ModularCurve.XHDRLevel ModularCurve.JZeroNeronObjectAtP MvPolynomial"

open scoped MatrixGroups TensorProduct

universe u

theorem aux_comp_app_apply {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) (U : Z.Opens) (s : Γ(Z, U)) :
    ((f ≫ g).app U).hom s = (f.app (g ⁻¹ᵁ U)).hom ((g.app U).hom s) := by
  rw [Scheme.Hom.comp_app]; rfl

theorem aux_morphismRestrict_appTop_apply {X Y : Scheme.{u}} (f : X ⟶ Y) (U : Y.Opens) (s : Γ(U, ⊤)) :
    (f ∣_ U).appTop.hom s =
      (X.presheaf.map (eqToHom (image_morphismRestrict_preimage f U ⊤)).op).hom ((f.app (U.ι ''ᵁ ⊤)).hom s) := by
  rw [morphismRestrict_appTop]; rfl

theorem aux_specMap_appTop_ΓSpecIso_inv'' {R S : CommRingCat.{u}} (f : R ⟶ S) (r : R) :
    (Spec.map f).appTop.hom ((Scheme.ΓSpecIso R).inv.hom r) = (Scheme.ΓSpecIso S).inv.hom (f.hom r) := by
  rw [← CommRingCat.comp_apply, ← Scheme.ΓSpecIso_inv_naturality, CommRingCat.comp_apply]

theorem aux_comp_appTop_apply'' {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) (s : Γ(Z, ⊤)) :
    (f ≫ g).appTop.hom s = f.appTop.hom (g.appTop.hom s) := by
  rw [Scheme.Hom.comp_appTop, CommRingCat.comp_apply]

theorem aux_B1_appTop_algebraMap {X : Scheme.{u}} {K S : Type u} [CommRing K] [CommRing S] [Algebra K S]
    (h : X ⟶ Spec (CommRingCat.of S)) (t : X ⟶ Spec (CommRingCat.of K))
    (hh : h ≫ Spec.map (CommRingCat.ofHom (algebraMap K S)) = t) (c : K) :
    h.appTop.hom ((Scheme.ΓSpecIso (CommRingCat.of S)).inv.hom (algebraMap K S c)) =
      t.appTop.hom ((Scheme.ΓSpecIso (CommRingCat.of K)).inv.hom c) := by
  rw [← hh, aux_comp_appTop_apply'', aux_specMap_appTop_ΓSpecIso_inv'', CommRingCat.hom_ofHom]

theorem aux_B1_compare_germ
    {X Y Z S₁ S₂ B : Scheme.{u}} (eeta : X ⟶ Y) (prJ : Y ⟶ Z) (U : Z.Opens)
    (f : (U : Scheme.{u}) ⟶ S₁) (g : (eeta ⁻¹ᵁ (prJ ⁻¹ᵁ U) : Scheme.{u}) ⟶ (prJ ⁻¹ᵁ U : Scheme.{u}))
    (hg : g = eeta ∣_ (prJ ⁻¹ᵁ U)) (fK' : (prJ ⁻¹ᵁ U : Scheme.{u}) ⟶ S₂) (toB : X ⟶ B)
    (v₂ c₂ : Γ(S₂, ⊤)) (v₁ : Γ(S₁, ⊤)) (cB : Γ(B, ⊤))
    (hV : fK'.appTop.hom v₂ = ((prJ ∣_ U) ≫ f).appTop.hom v₁)
    (hC : (g ≫ fK').appTop.hom c₂ = ((eeta ⁻¹ᵁ (prJ ⁻¹ᵁ U)).ι ≫ toB).appTop.hom cB)
    (r : Γ(S₂, ⊤)) (hr : r = v₂ - c₂)
    (x : ↥(eeta ⁻¹ᵁ (prJ ⁻¹ᵁ U))) (hx' : x.1 ∈ eeta ⁻¹ᵁ (prJ ⁻¹ᵁ (U.ι ''ᵁ ⊤))) :
    (X.presheaf.germ ((eeta ⁻¹ᵁ (prJ ⁻¹ᵁ U)).ι ''ᵁ (g ⁻¹ᵁ (fK' ⁻¹ᵁ ⊤))) x.1 ⟨x, trivial, rfl⟩).hom
        ((g.app (fK' ⁻¹ᵁ ⊤)).hom ((fK'.app ⊤).hom r)) =
      (X.presheaf.germ (eeta ⁻¹ᵁ (prJ ⁻¹ᵁ (U.ι ''ᵁ ⊤))) x.1 hx').hom
        ((eeta.app (prJ ⁻¹ᵁ (U.ι ''ᵁ ⊤))).hom ((prJ.app (U.ι ''ᵁ ⊤)).hom ((U.ι.appIso ⊤).inv (f.appTop v₁))) -
          X.presheaf.map (homOfLE le_top).op (toB.appTop cB)) := by

  have hca : ∀ s, (g.app (fK' ⁻¹ᵁ ⊤)).hom ((fK'.app ⊤).hom s) = (g ≫ fK').appTop.hom s := fun s => by
    show _ = ((g ≫ fK').app ⊤).hom s
    rw [Scheme.Hom.comp_app]
    rfl
  rw [hr, hca, map_sub ((g ≫ fK').appTop).hom]

  have hgcomp : g ≫ (prJ ∣_ U) = (eeta ≫ prJ) ∣_ U := by rw [hg, ← morphismRestrict_comp]
  have hVpart : (g ≫ fK').appTop.hom v₂ =
      (X.presheaf.map (eqToHom (image_morphismRestrict_preimage (eeta ≫ prJ) U ⊤)).op).hom
        (((eeta ≫ prJ).app (U.ι ''ᵁ ⊤)).hom (f.appTop.hom v₁)) := by
    rw [aux_comp_appTop_apply'', hV, ← aux_comp_appTop_apply'', ← Category.assoc, hgcomp, aux_comp_appTop_apply'',
      morphismRestrict_appTop]
    rfl
  rw [hVpart, hC, aux_comp_appTop_apply'', Scheme.Opens.ι_appTop, Scheme.Opens.ι_appIso, Iso.refl_inv, Scheme.Hom.comp_app]
  change (X.presheaf.germ _ x.1 _).hom (_ - _) = (X.presheaf.germ _ x.1 _).hom (_ - _)
  rw [map_sub, map_sub]
  congr 1
  · exact (TopCat.Presheaf.germ_res_apply X.presheaf _ x.1 _ _)
  · exact (TopCat.Presheaf.germ_res_apply X.presheaf _ x.1 _ _).trans (TopCat.Presheaf.germ_res_apply X.presheaf _ x.1 _ _).symm

theorem aux_maximalIdeal_stalk_eq_span_germ_of_iso_restrict
    {X P Y : Scheme.{u}} (O : X.Opens) (g : (O : Scheme.{u}) ⟶ P) [IsIso g] (fK : P ⟶ Y) (x : O) (r : Γ(Y, ⊤))
    (hunr : Ideal.map (fK.stalkMap (g.base x)).hom (IsLocalRing.maximalIdeal (Y.presheaf.stalk (fK.base (g.base x)))) =
      IsLocalRing.maximalIdeal (P.presheaf.stalk (g.base x)))
    (hY : IsLocalRing.maximalIdeal (Y.presheaf.stalk (fK.base (g.base x))) =
      Ideal.span {(Y.presheaf.germ ⊤ (fK.base (g.base x)) trivial).hom r}) :
    IsLocalRing.maximalIdeal (X.presheaf.stalk x.1) =
      Ideal.span {(X.presheaf.germ (O.ι ''ᵁ (g ⁻¹ᵁ (fK ⁻¹ᵁ ⊤))) x.1 ⟨x, trivial, rfl⟩).hom
        ((g.app (fK ⁻¹ᵁ ⊤)).hom ((fK.app ⊤).hom r))} := by

  have hP : IsLocalRing.maximalIdeal (P.presheaf.stalk (g.base x)) =
      Ideal.span {(P.presheaf.germ (fK ⁻¹ᵁ ⊤) (g.base x) trivial).hom ((fK.app ⊤).hom r)} := by
    rw [← hunr, hY, Ideal.map_span, Set.image_singleton, Scheme.Hom.germ_stalkMap_apply]

  have hT1 := Scheme.Hom.germ_stalkMap_apply g (fK ⁻¹ᵁ ⊤) x trivial ((fK.app ⊤).hom r)
  have hO : IsLocalRing.maximalIdeal ((O : Scheme.{u}).presheaf.stalk x) =
      Ideal.span {((O : Scheme.{u}).presheaf.germ (g ⁻¹ᵁ (fK ⁻¹ᵁ ⊤)) x trivial).hom ((g.app (fK ⁻¹ᵁ ⊤)).hom ((fK.app ⊤).hom r))} := by
    have h1 : Ideal.map (asIso (g.stalkMap x)).commRingCatIsoToRingEquiv
        (IsLocalRing.maximalIdeal (P.presheaf.stalk (g.base x))) = IsLocalRing.maximalIdeal _ :=
      IsLocalRing.eq_maximalIdeal (Ideal.map_isMaximal_of_equiv _)
    rw [← h1, hP, Ideal.map_span, Set.image_singleton, ← hT1]
    rfl

  have hT2 := Scheme.Opens.germ_stalkIso_hom O (V := g ⁻¹ᵁ (fK ⁻¹ᵁ ⊤)) x trivial
  have hT2' : (O.stalkIso x).hom.hom (((O : Scheme.{u}).presheaf.germ (g ⁻¹ᵁ (fK ⁻¹ᵁ ⊤)) x trivial).hom
        ((g.app (fK ⁻¹ᵁ ⊤)).hom ((fK.app ⊤).hom r))) =
      (X.presheaf.germ (O.ι ''ᵁ (g ⁻¹ᵁ (fK ⁻¹ᵁ ⊤))) x.1 ⟨x, trivial, rfl⟩).hom ((g.app (fK ⁻¹ᵁ ⊤)).hom ((fK.app ⊤).hom r)) := by
    rw [← CommRingCat.comp_apply, hT2]
    rfl
  have h1 : Ideal.map (O.stalkIso x).commRingCatIsoToRingEquiv
      (IsLocalRing.maximalIdeal ((O : Scheme.{u}).presheaf.stalk x)) = IsLocalRing.maximalIdeal _ :=
    IsLocalRing.eq_maximalIdeal (Ideal.map_isMaximal_of_equiv _)
  rw [← h1, hO, Ideal.map_span, Set.image_singleton, ← hT2']
  rfl

theorem aux_B1_iso_tensor {O K : Type} [CommRing O] [Field K] [Algebra O K] (t : O) :
    ∃ iC : CommRingCat.of (CrossingQuotient K (algebraMap O K t)) ≅ CommRingCat.of (K ⊗[O] CrossingQuotient O t),
      iC.hom.hom (CrossingQuotient.U (algebraMap O K t)) =
        (@CommRingCat.ofHom (CrossingQuotient O t) (K ⊗[O] CrossingQuotient O t) _ _ (Algebra.TensorProduct.includeRight (R := O) (A := K) (B := CrossingQuotient O t)).toRingHom).hom (CrossingQuotient.U t) ∧
      iC.hom.hom (CrossingQuotient.V (algebraMap O K t)) =
        (@CommRingCat.ofHom (CrossingQuotient O t) (K ⊗[O] CrossingQuotient O t) _ _ (Algebra.TensorProduct.includeRight (R := O) (A := K) (B := CrossingQuotient O t)).toRingHom).hom (CrossingQuotient.V t) ∧
      ∀ c : K, iC.hom.hom (algebraMap K (CrossingQuotient K (algebraMap O K t)) c) =
        (@CommRingCat.ofHom K (K ⊗[O] CrossingQuotient O t) _ _ (algebraMap K (K ⊗[O] CrossingQuotient O t))).hom c := by
  obtain ⟨eT, heU, heV⟩ := MvPolynomial.CrossingQuotient.exists_algEquiv_tensorProduct_apply_U_and_apply_V O t K (algebraMap O K t) rfl
  refine ⟨eT.toRingEquiv.toCommRingCatIso, ?_, ?_, fun c => ?_⟩
  · show eT.toRingEquiv _ = _
    rw [AlgEquiv.coe_ringEquiv, heU, CommRingCat.hom_ofHom, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, Algebra.TensorProduct.includeRight_apply]
  · show eT.toRingEquiv _ = _
    rw [AlgEquiv.coe_ringEquiv, heV, CommRingCat.hom_ofHom, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, Algebra.TensorProduct.includeRight_apply]
  · show eT.toRingEquiv _ = _
    rw [AlgEquiv.coe_ringEquiv, AlgEquiv.commutes, CommRingCat.hom_ofHom]

theorem aux_specMap_appTop_ΓSpecIso_inv' {R S : CommRingCat.{0}} (f : R ⟶ S) (r : R) :
    (Spec.map f).appTop.hom ((Scheme.ΓSpecIso R).inv.hom r) = (Scheme.ΓSpecIso S).inv.hom (f.hom r) := by
  rw [← CommRingCat.comp_apply, ← Scheme.ΓSpecIso_inv_naturality, CommRingCat.comp_apply]

theorem aux_comp_appTop_apply' {X Y Z : Scheme.{0}} (f : X ⟶ Y) (g : Y ⟶ Z) (s : Γ(Z, ⊤)) :
    (f ≫ g).appTop.hom s = f.appTop.hom (g.appTop.hom s) := by
  rw [Scheme.Hom.comp_appTop, CommRingCat.comp_apply]

theorem aux_B1_model_base
    {O K T : Type} [CommRing O] [Field K] [Algebra O K] [CommRing T] (t : O) (ht : algebraMap O K t ≠ 0)
    (iR : CommRingCat.of (CrossingQuotient O t) ⟶ CommRingCat.of T) (aKT : CommRingCat.of K ⟶ CommRingCat.of T)
    (iC : CommRingCat.of (CrossingQuotient K (algebraMap O K t)) ≅ CommRingCat.of T)
    (heRU : iC.hom.hom (CrossingQuotient.U (algebraMap O K t)) = iR.hom (CrossingQuotient.U t))
    (heRV : iC.hom.hom (CrossingQuotient.V (algebraMap O K t)) = iR.hom (CrossingQuotient.V t))
    (heRalg : ∀ c : K, iC.hom.hom (algebraMap K _ c) = aKT.hom c)
    {Usch PU : Scheme.{0}} (f : Usch ⟶ Spec (CommRingCat.of (CrossingQuotient O t))) (g₁ : PU ⟶ Usch)
    (toK : PU ⟶ Spec (CommRingCat.of K))
    (fK : PU ⟶ Spec (CommRingCat.of T))
    (hfK₁ : fK ≫ Spec.map iR = g₁ ≫ f)
    (hfK₂ : fK ≫ Spec.map aKT = toK)
:
      (∀ V' : PU.Opens, Etale (V'.ι ≫ fK) → Etale (V'.ι ≫ (fK ≫ Spec.map iC.hom))) ∧
      (fK ≫ Spec.map iC.hom) ≫ Spec.map (CommRingCat.ofHom (algebraMap K (CrossingQuotient K (algebraMap O K t)))) = toK ∧
      ((fK ≫ Spec.map iC.hom).appTop).hom ((Scheme.ΓSpecIso (CommRingCat.of (CrossingQuotient K (algebraMap O K t)))).inv.hom (CrossingQuotient.V (algebraMap O K t))) =
        ((g₁ ≫ f).appTop).hom ((Scheme.ΓSpecIso (CommRingCat.of (CrossingQuotient O t))).inv.hom (CrossingQuotient.V t)) := by
  have halgT : CommRingCat.ofHom (algebraMap K (CrossingQuotient K (algebraMap O K t))) ≫ iC.hom =
      aKT := by
    apply CommRingCat.hom_ext; apply RingHom.ext; intro c
    rw [CommRingCat.hom_comp, RingHom.comp_apply, CommRingCat.hom_ofHom, heRalg]
  refine ⟨fun V' hV' => ?_, ?_, ?_⟩
  · rw [← Category.assoc]
    exact (MorphismProperty.cancel_right_of_respectsIso @Etale _ (Spec.map iC.hom)).mpr hV'
  · rw [Category.assoc, ← Spec.map_comp, halgT, hfK₂]
  · rw [aux_comp_appTop_apply', aux_specMap_appTop_ΓSpecIso_inv', heRV, ← hfK₁, aux_comp_appTop_apply',
      aux_specMap_appTop_ΓSpecIso_inv']

theorem aux_B1_model_point
    {O K T : Type} [CommRing O] [Field K] [Algebra O K] [CommRing T] (t : O) (ht : algebraMap O K t ≠ 0)
    (iR : CommRingCat.of (CrossingQuotient O t) ⟶ CommRingCat.of T) (aKT : CommRingCat.of K ⟶ CommRingCat.of T)
    (iC : CommRingCat.of (CrossingQuotient K (algebraMap O K t)) ≅ CommRingCat.of T)
    (heRU : iC.hom.hom (CrossingQuotient.U (algebraMap O K t)) = iR.hom (CrossingQuotient.U t))
    (heRV : iC.hom.hom (CrossingQuotient.V (algebraMap O K t)) = iR.hom (CrossingQuotient.V t))
    (heRalg : ∀ c : K, iC.hom.hom (algebraMap K _ c) = aKT.hom c)
    {Usch PU : Scheme.{0}} (f : Usch ⟶ Spec (CommRingCat.of (CrossingQuotient O t))) (g₁ : PU ⟶ Usch)
    (toK : PU ⟶ Spec (CommRingCat.of K))
    (fK : PU ⟶ Spec (CommRingCat.of T))
    (hfK₁ : fK ≫ Spec.map iR = g₁ ≫ f)
    (hfK₂ : fK ≫ Spec.map aKT = toK)
    (χK : CrossingQuotient O t →+* K) (hχK : χK.comp (algebraMap O (CrossingQuotient O t)) = algebraMap O K)
    (pt : PU) (zQ : Spec (CommRingCat.of K) ⟶ PU) (hzQpt : zQ.base (IsLocalRing.closedPoint K) = pt)
    (hzQ₁ : zQ ≫ g₁ ≫ f = Spec.map (CommRingCat.ofHom χK)) (hzQ₂ : zQ ≫ toK = 𝟙 _) :
      IsLocalRing.maximalIdeal ((Spec (CommRingCat.of (CrossingQuotient K (algebraMap O K t)))).presheaf.stalk ((fK ≫ Spec.map iC.hom).base pt)) =
        Ideal.span {((Spec (CommRingCat.of (CrossingQuotient K (algebraMap O K t)))).presheaf.germ ⊤ ((fK ≫ Spec.map iC.hom).base pt) trivial).hom
          ((Scheme.ΓSpecIso (CommRingCat.of (CrossingQuotient K (algebraMap O K t)))).inv.hom
            (CrossingQuotient.V (algebraMap O K t) - algebraMap K _ (χK (CrossingQuotient.V t))))} := by

  obtain ⟨x₀, hx₀⟩ : ∃ x₀ : K, x₀ = χK (CrossingQuotient.U t) := ⟨_, rfl⟩
  obtain ⟨y₀, hy₀⟩ : ∃ y₀ : K, y₀ = χK (CrossingQuotient.V t) := ⟨_, rfl⟩
  rw [← hy₀]
  have hxy : x₀ * y₀ = algebraMap O K t := by
    rw [hx₀, hy₀, ← map_mul, CrossingQuotient.U_mul_V]
    show (χK.comp (algebraMap O (CrossingQuotient O t))) t = _
    rw [hχK]
  have hy0 : y₀ ≠ 0 := by
    intro h0
    rw [h0, mul_zero] at hxy
    exact ht hxy.symm
  obtain ⟨θ, hθ⟩ := Spec.map_surjective (zQ ≫ fK)
  have hθR : iR ≫ θ =
      CommRingCat.ofHom χK := by
    apply Spec.map_injective
    rw [Spec.map_comp, hθ, Category.assoc, hfK₁, hzQ₁]
  have hθL : aKT ≫ θ = 𝟙 _ := by
    apply Spec.map_injective
    rw [Spec.map_comp, hθ, Category.assoc, hfK₂, hzQ₂, Spec.map_id]
  obtain ⟨ψ, hψ⟩ : ∃ ψ : CommRingCat.of (CrossingQuotient K (algebraMap O K t)) ⟶ CommRingCat.of K, ψ = iC.hom ≫ θ := ⟨_, rfl⟩
  have hzfK' : zQ ≫ fK ≫ Spec.map iC.hom = Spec.map ψ := by
    rw [← Category.assoc, ← hθ, hψ, Spec.map_comp]
  have hψalg : ∀ c : K, ψ.hom (algebraMap K _ c) = c := by
    intro c
    have h1 := congrArg (fun φ => (CommRingCat.Hom.hom φ) c) hθL
    simp only [CommRingCat.hom_comp, RingHom.coe_comp, Function.comp_apply, CommRingCat.hom_id, RingHom.id_apply] at h1
    rw [hψ, CommRingCat.hom_comp, RingHom.coe_comp, Function.comp_apply, heRalg]
    exact h1
  have hψU : ψ.hom (CrossingQuotient.U (algebraMap O K t)) = x₀ := by
    have h1 := congrArg (fun φ => (CommRingCat.Hom.hom φ) (CrossingQuotient.U t)) hθR
    simp only [CommRingCat.hom_comp, CommRingCat.hom_ofHom, RingHom.coe_comp, Function.comp_apply] at h1
    rw [hψ, CommRingCat.hom_comp, RingHom.coe_comp, Function.comp_apply, heRU, hx₀]
    exact h1
  have hψV : ψ.hom (CrossingQuotient.V (algebraMap O K t)) = y₀ := by
    have h1 := congrArg (fun φ => (CommRingCat.Hom.hom φ) (CrossingQuotient.V t)) hθR
    simp only [CommRingCat.hom_comp, CommRingCat.hom_ofHom, RingHom.coe_comp, Function.comp_apply] at h1
    rw [hψ, CommRingCat.hom_comp, RingHom.coe_comp, Function.comp_apply, heRV, hy₀]
    exact h1
  obtain ⟨L, hLdef⟩ : ∃ L : CrossingQuotient K (algebraMap O K t) →+* K,
      L = (CrossingQuotient.lift (t := algebraMap O K t) x₀ y₀ (by rw [Algebra.algebraMap_self, RingHom.id_apply, hxy])).toRingHom := ⟨_, rfl⟩
  have hψL : ψ.hom = L := by
    apply Ideal.Quotient.ringHom_ext
    apply MvPolynomial.ringHom_ext
    · intro c
      change ψ.hom (algebraMap K _ c) = L (algebraMap K _ c)
      rw [hψalg, hLdef, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, AlgHom.commutes, Algebra.algebraMap_self, RingHom.id_apply]
    · intro i
      fin_cases i
      · change ψ.hom (CrossingQuotient.U _) = L (CrossingQuotient.U _)
        rw [hψU, hLdef, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, CrossingQuotient.lift_U]
      · change ψ.hom (CrossingQuotient.V _) = L (CrossingQuotient.V _)
        rw [hψV, hLdef, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, CrossingQuotient.lift_V]
  have hprime : (RingHom.ker L).IsPrime := RingHom.ker_isPrime L
  have hpt : (fK ≫ Spec.map iC.hom).base pt = (⟨RingHom.ker L, hprime⟩ : PrimeSpectrum _) := by
    rw [← hzQpt]
    show (zQ ≫ fK ≫ Spec.map iC.hom).base (IsLocalRing.closedPoint K) = _
    rw [hzfK']
    apply PrimeSpectrum.ext
    show (PrimeSpectrum.comap ψ.hom (IsLocalRing.closedPoint K)).asIdeal = RingHom.ker L
    rw [PrimeSpectrum.comap_asIdeal, ← hψL]
    show Ideal.comap ψ.hom (IsLocalRing.maximalIdeal K) = _
    rw [IsLocalRing.maximalIdeal_eq_bot, ← RingHom.ker_eq_comap_bot]
  have hK2 : ∀ (pt' : ↥(Spec (CommRingCat.of (CrossingQuotient K (algebraMap O K t))))) (hpt' : pt' = (⟨RingHom.ker L, hprime⟩ : PrimeSpectrum _)),
      IsLocalRing.maximalIdeal ((Spec (CommRingCat.of (CrossingQuotient K (algebraMap O K t)))).presheaf.stalk pt') =
        Ideal.span {((Spec (CommRingCat.of (CrossingQuotient K (algebraMap O K t)))).presheaf.germ ⊤ pt' trivial).hom
          ((Scheme.ΓSpecIso (CommRingCat.of (CrossingQuotient K (algebraMap O K t)))).inv.hom
            (CrossingQuotient.V (algebraMap O K t) - algebraMap K _ y₀))} := by
    rintro pt' rfl
    subst hLdef
    exact MvPolynomial.CrossingQuotient.maximalIdeal_stalk_eq_span_germ_V_sub K (algebraMap O K t) x₀ y₀ hxy hy0 hprime
  exact hK2 ((fK ≫ Spec.map iC.hom).base pt) hpt

namespace ModularCurve p2m_export "ModularCurve" "XHDRModelAtP xHFunctionFieldBar qExpFunctionFieldC jqModC JZeroNeronObjectAtP" namespace XHDRModelAtP p2m_export "ModularCurve.XHDRModelAtP" "eeta Meta heeta comp" end ModularCurve.XHDRModelAtP
p2m_open_scoped "ModularCurve ModularCurve.XHDRModelAtP" in

theorem ModularCurve.XHDRModelAtP.aux_B1_baseChange_chart
    (p M : ℕ) [Fact p.Prime] [NeZero M] (H : Subgroup (ZMod M)ˣ) (hpM : p ∣ M) (hpM2 : ¬ p ^ 2 ∣ M)
    (hHp : ∀ u : (ZMod M)ˣ, ZMod.unitsMap (Nat.div_dvd_of_dvd hpM) u = 1 → u ∈ H) [NeZero (M / p)]
    (hj : jqModC ℚ ∈ qExpFunctionFieldC ℚ (⊤ : Subgroup SL(2, ℤ)))
    (𝔛 : XHDRModelAtP p M H hpM hj)
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime p)
    [CharP (IsLocalRing.ResidueField ↥A) p] [IsAlgClosed (IsLocalRing.ResidueField ↥A)]
    (ρ : R p →+* ↥A) (hρ : A.subtype.comp ρ = algebraMap (R p) (AlgebraicClosure ℚ))
    (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (ρO : R p →+* O)
    (hϖ : IsLocalRing.maximalIdeal O = Ideal.span {((p : ℕ) : O)})
    (toκ : O →+* ResidueField ↥A) (htoκ : toκ.comp ρO = (IsLocalRing.residue ↥A).comp ρ)

    (jO : O →+* AlgebraicClosure ℚ) (hjO : jO.comp ρO = algebraMap (R p) (AlgebraicClosure ℚ))
    (ιA : O →+* ↥A) (hιA : A.subtype.comp ιA = jO) (hιAκ : (IsLocalRing.residue ↥A).comp ιA = toκ)

    (n : ↥(pullback (𝔛.comp A hA ρ hρ 0) (𝔛.comp A hA ρ hρ 1)))
    (e : ℕ) (he : 1 ≤ e) (U : (XO (ΓM M H) hj ρO).Opens) (hxU : (pullback.fst (𝔛.comp A hA ρ hρ 0) (𝔛.comp A hA ρ hρ 1) ≫ 𝔛.comp A hA ρ hρ 0 ≫ bcMap (ΓM M H) hj ρO toκ htoκ).base n ∈ U)
    (f : (U : Scheme.{0}) ⟶ CrossingQuotient.crossingScheme (((p : ℕ) : O) ^ e))
    (hover : f ≫ Spec.map (CommRingCat.ofHom (algebraMap O (CrossingQuotient O (((p : ℕ) : O) ^ e)))) = U.ι ≫ pullback.snd _ _)
    (hfib : ∀ y : ↥(U : Scheme.{0}),
      (CrossingQuotient.U (((p : ℕ) : O) ^ e) ∈ (f.base y).asIdeal ∧ CrossingQuotient.V (((p : ℕ) : O) ^ e) ∈ (f.base y).asIdeal) ↔ U.ι.base y = (pullback.fst (𝔛.comp A hA ρ hρ 0) (𝔛.comp A hA ρ hρ 1) ≫ 𝔛.comp A hA ρ hρ 0 ≫ bcMap (ΓM M H) hj ρO toκ htoκ).base n)
    (hpt : ∀ y : ↥(U : Scheme.{0}), U.ι.base y = (pullback.fst (𝔛.comp A hA ρ hρ 0) (𝔛.comp A hA ρ hρ 1) ≫ 𝔛.comp A hA ρ hρ 0 ≫ bcMap (ΓM M H) hj ρO toκ htoκ).base n →
      (f.stalkMap y).hom.Flat ∧ Ideal.map (f.stalkMap y).hom (IsLocalRing.maximalIdeal _) = IsLocalRing.maximalIdeal _ ∧ IsIso (f.residueFieldMap y))
    (het : ∀ y : ↥(U : Scheme.{0}), U.ι.base y = (pullback.fst (𝔛.comp A hA ρ hρ 0) (𝔛.comp A hA ρ hρ 1) ≫ 𝔛.comp A hA ρ hρ 0 ≫ bcMap (ΓM M H) hj ρO toκ htoκ).base n → ∃ V : (U : Scheme.{0}).Opens, y ∈ V ∧ Etale (V.ι ≫ f))
    (hor₁ : ∀ y : ↥(U : Scheme.{0}), CrossingQuotient.V (((p : ℕ) : O) ^ e) ∈ (f.base y).asIdeal → U.ι.base y ∈ Set.range (𝔛.comp A hA ρ hρ 0 ≫ bcMap (ΓM M H) hj ρO toκ htoκ).base)
    (hor₂ : ∀ y : ↥(U : Scheme.{0}), CrossingQuotient.U (((p : ℕ) : O) ^ e) ∈ (f.base y).asIdeal → U.ι.base y ∈ Set.range (𝔛.comp A hA ρ hρ 1 ≫ bcMap (ΓM M H) hj ρO toκ htoκ).base)
    (hor₃ : ∀ y : ↥(U : Scheme.{0}), U.ι.base y ∈ Set.range (𝔛.comp A hA ρ hρ 0 ≫ bcMap (ΓM M H) hj ρO toκ htoκ).base → CrossingQuotient.V (((p : ℕ) : O) ^ e) ∈ (f.base y).asIdeal)
    (hor₄ : ∀ y : ↥(U : Scheme.{0}), U.ι.base y ∈ Set.range (𝔛.comp A hA ρ hρ 1 ≫ bcMap (ΓM M H) hj ρO toκ htoκ).base → CrossingQuotient.U (((p : ℕ) : O) ^ e) ∈ (f.base y).asIdeal)
    (prJ : pullback (toBase p (ΓM M H) hj) (Spec.map (CommRingCat.ofHom (algebraMap (R p) (AlgebraicClosure ℚ)))) ⟶ XO (ΓM M H) hj ρO)
    (hprJ : prJ = pullback.map _ _ _ _ (𝟙 _) (Spec.map (CommRingCat.ofHom jO)) (𝟙 _)
        (by rw [Category.comp_id, Category.id_comp]) (by rw [Category.comp_id, ← Spec.map_comp, ← CommRingCat.ofHom_comp, hjO]))
    [Algebra O (AlgebraicClosure ℚ)] (halg : algebraMap O (AlgebraicClosure ℚ) = jO) :
    ∃ fK : ((prJ ⁻¹ᵁ U : _) : Scheme.{0}) ⟶ Spec (CommRingCat.of (TensorProduct O (AlgebraicClosure ℚ) (CrossingQuotient O (((p : ℕ) : O) ^ e)))),
      fK ≫ Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.includeRight (R := O) (A := AlgebraicClosure ℚ)
        (B := CrossingQuotient O (((p : ℕ) : O) ^ e))).toRingHom) = (prJ ∣_ U) ≫ f ∧
      fK ≫ Spec.map (CommRingCat.ofHom (algebraMap (AlgebraicClosure ℚ) (TensorProduct O (AlgebraicClosure ℚ) (CrossingQuotient O (((p : ℕ) : O) ^ e))))) =
        (prJ ⁻¹ᵁ U).ι ≫ pullback.snd _ _ ∧
      ∀ V : (U : Scheme.{0}).Opens, Etale (V.ι ≫ f) → Etale (((prJ ∣_ U) ⁻¹ᵁ V).ι ≫ fK) := by

  have hfst : prJ ≫ pullback.fst (toBase p (ΓM M H) hj) (Spec.map (CommRingCat.ofHom ρO)) =
      pullback.fst (toBase p (ΓM M H) hj) (Spec.map (CommRingCat.ofHom (algebraMap (R p) (AlgebraicClosure ℚ)))) := by
    rw [hprJ, pullback.lift_fst, Category.comp_id]
  have hsnd : prJ ≫ pullback.snd (toBase p (ΓM M H) hj) (Spec.map (CommRingCat.ofHom ρO)) =
      pullback.snd (toBase p (ΓM M H) hj) (Spec.map (CommRingCat.ofHom (algebraMap (R p) (AlgebraicClosure ℚ)))) ≫
        Spec.map (CommRingCat.ofHom (algebraMap O (AlgebraicClosure ℚ))) := by
    rw [hprJ, pullback.lift_snd, halg]
  have hbot : Spec.map (CommRingCat.ofHom (algebraMap O (AlgebraicClosure ℚ))) ≫ Spec.map (CommRingCat.ofHom ρO) =
      Spec.map (CommRingCat.ofHom (algebraMap (R p) (AlgebraicClosure ℚ))) := by
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp, halg, hjO]
  have hpr : IsPullback prJ (pullback.snd (toBase p (ΓM M H) hj) (Spec.map (CommRingCat.ofHom (algebraMap (R p) (AlgebraicClosure ℚ)))))
      (pullback.snd (toBase p (ΓM M H) hj) (Spec.map (CommRingCat.ofHom ρO))) (Spec.map (CommRingCat.ofHom (algebraMap O (AlgebraicClosure ℚ)))) := by
    have right := IsPullback.of_hasPullback (toBase p (ΓM M H) hj) (Spec.map (CommRingCat.ofHom ρO))
    have big : IsPullback (prJ ≫ pullback.fst (toBase p (ΓM M H) hj) (Spec.map (CommRingCat.ofHom ρO)))
        (pullback.snd (toBase p (ΓM M H) hj) (Spec.map (CommRingCat.ofHom (algebraMap (R p) (AlgebraicClosure ℚ)))))
        (toBase p (ΓM M H) hj) (Spec.map (CommRingCat.ofHom (algebraMap O (AlgebraicClosure ℚ))) ≫ Spec.map (CommRingCat.ofHom ρO)) := by
      rw [hbot, hfst]
      exact IsPullback.of_hasPullback _ _
    exact IsPullback.of_right big hsnd right

  obtain ⟨fK, hfK₁, hfK₂, hfK₃⟩ := AlgebraicGeometry.exists_baseChange_chart_isPullback_of_isPullback
    (pullback.snd (toBase p (ΓM M H) hj) (Spec.map (CommRingCat.ofHom ρO)))
    (pullback.snd (toBase p (ΓM M H) hj) (Spec.map (CommRingCat.ofHom (algebraMap (R p) (AlgebraicClosure ℚ)))))
    prJ hpr U f hover
  refine ⟨fK, hfK₁, hfK₂, fun V hV => ?_⟩
  have hsq : IsPullback (((prJ ∣_ U) ⁻¹ᵁ V).ι ≫ fK) ((prJ ∣_ U) ∣_ V)
      (Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.includeRight (R := O) (A := AlgebraicClosure ℚ)
        (B := CrossingQuotient O (((p : ℕ) : O) ^ e))).toRingHom)) (V.ι ≫ f) :=
    (isPullback_morphismRestrict (prJ ∣_ U) V).flip.paste_horiz hfK₃
  exact MorphismProperty.of_isPullback (P := @Etale) hsq.flip hV

p2m_open_scoped "ModularCurve ModularCurve.XHDRModelAtP" in

theorem ModularCurve.XHDRModelAtP.aux_B1_chart_barQ
    (p M : ℕ) [Fact p.Prime] [NeZero M] (H : Subgroup (ZMod M)ˣ) (hpM : p ∣ M) (hpM2 : ¬ p ^ 2 ∣ M)
    (hHp : ∀ u : (ZMod M)ˣ, ZMod.unitsMap (Nat.div_dvd_of_dvd hpM) u = 1 → u ∈ H) [NeZero (M / p)]
    (hj : jqModC ℚ ∈ qExpFunctionFieldC ℚ (⊤ : Subgroup SL(2, ℤ)))
    (𝔛 : XHDRModelAtP p M H hpM hj)
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime p)
    [CharP (IsLocalRing.ResidueField ↥A) p] [IsAlgClosed (IsLocalRing.ResidueField ↥A)]
    (ρ : R p →+* ↥A) (hρ : A.subtype.comp ρ = algebraMap (R p) (AlgebraicClosure ℚ))
    (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (ρO : R p →+* O)
    (hϖ : IsLocalRing.maximalIdeal O = Ideal.span {((p : ℕ) : O)})
    (toκ : O →+* ResidueField ↥A) (htoκ : toκ.comp ρO = (IsLocalRing.residue ↥A).comp ρ)

    (jO : O →+* AlgebraicClosure ℚ) (hjO : jO.comp ρO = algebraMap (R p) (AlgebraicClosure ℚ))
    (ιA : O →+* ↥A) (hιA : A.subtype.comp ιA = jO) (hιAκ : (IsLocalRing.residue ↥A).comp ιA = toκ)

    (n : ↥(pullback (𝔛.comp A hA ρ hρ 0) (𝔛.comp A hA ρ hρ 1)))
    (e : ℕ) (he : 1 ≤ e) (U : (XO (ΓM M H) hj ρO).Opens) (hxU : (pullback.fst (𝔛.comp A hA ρ hρ 0) (𝔛.comp A hA ρ hρ 1) ≫ 𝔛.comp A hA ρ hρ 0 ≫ bcMap (ΓM M H) hj ρO toκ htoκ).base n ∈ U)
    (f : (U : Scheme.{0}) ⟶ CrossingQuotient.crossingScheme (((p : ℕ) : O) ^ e))
    (hover : f ≫ Spec.map (CommRingCat.ofHom (algebraMap O (CrossingQuotient O (((p : ℕ) : O) ^ e)))) = U.ι ≫ pullback.snd _ _)
    (hfib : ∀ y : ↥(U : Scheme.{0}),
      (CrossingQuotient.U (((p : ℕ) : O) ^ e) ∈ (f.base y).asIdeal ∧ CrossingQuotient.V (((p : ℕ) : O) ^ e) ∈ (f.base y).asIdeal) ↔ U.ι.base y = (pullback.fst (𝔛.comp A hA ρ hρ 0) (𝔛.comp A hA ρ hρ 1) ≫ 𝔛.comp A hA ρ hρ 0 ≫ bcMap (ΓM M H) hj ρO toκ htoκ).base n)
    (hpt : ∀ y : ↥(U : Scheme.{0}), U.ι.base y = (pullback.fst (𝔛.comp A hA ρ hρ 0) (𝔛.comp A hA ρ hρ 1) ≫ 𝔛.comp A hA ρ hρ 0 ≫ bcMap (ΓM M H) hj ρO toκ htoκ).base n →
      (f.stalkMap y).hom.Flat ∧ Ideal.map (f.stalkMap y).hom (IsLocalRing.maximalIdeal _) = IsLocalRing.maximalIdeal _ ∧ IsIso (f.residueFieldMap y))
    (het : ∀ y : ↥(U : Scheme.{0}), U.ι.base y = (pullback.fst (𝔛.comp A hA ρ hρ 0) (𝔛.comp A hA ρ hρ 1) ≫ 𝔛.comp A hA ρ hρ 0 ≫ bcMap (ΓM M H) hj ρO toκ htoκ).base n → ∃ V : (U : Scheme.{0}).Opens, y ∈ V ∧ Etale (V.ι ≫ f))
    (hor₁ : ∀ y : ↥(U : Scheme.{0}), CrossingQuotient.V (((p : ℕ) : O) ^ e) ∈ (f.base y).asIdeal → U.ι.base y ∈ Set.range (𝔛.comp A hA ρ hρ 0 ≫ bcMap (ΓM M H) hj ρO toκ htoκ).base)
    (hor₂ : ∀ y : ↥(U : Scheme.{0}), CrossingQuotient.U (((p : ℕ) : O) ^ e) ∈ (f.base y).asIdeal → U.ι.base y ∈ Set.range (𝔛.comp A hA ρ hρ 1 ≫ bcMap (ΓM M H) hj ρO toκ htoκ).base)
    (hor₃ : ∀ y : ↥(U : Scheme.{0}), U.ι.base y ∈ Set.range (𝔛.comp A hA ρ hρ 0 ≫ bcMap (ΓM M H) hj ρO toκ htoκ).base → CrossingQuotient.V (((p : ℕ) : O) ^ e) ∈ (f.base y).asIdeal)
    (hor₄ : ∀ y : ↥(U : Scheme.{0}), U.ι.base y ∈ Set.range (𝔛.comp A hA ρ hρ 1 ≫ bcMap (ΓM M H) hj ρO toκ htoκ).base → CrossingQuotient.U (((p : ℕ) : O) ^ e) ∈ (f.base y).asIdeal)
    (prJ : pullback (toBase p (ΓM M H) hj) (Spec.map (CommRingCat.ofHom (algebraMap (R p) (AlgebraicClosure ℚ)))) ⟶ XO (ΓM M H) hj ρO)
    (hprJ : prJ = pullback.map _ _ _ _ (𝟙 _) (Spec.map (CommRingCat.ofHom jO)) (𝟙 _)
        (by rw [Category.comp_id, Category.id_comp]) (by rw [Category.comp_id, ← Spec.map_comp, ← CommRingCat.ofHom_comp, hjO])) :
    ∃ fK' : ((prJ ⁻¹ᵁ U : _) : Scheme.{0}) ⟶ Spec (CommRingCat.of (CrossingQuotient (AlgebraicClosure ℚ) (jO (((p : ℕ) : O) ^ e)))),
      (∀ V : (U : Scheme.{0}).Opens, Etale (V.ι ≫ f) → Etale (((prJ ∣_ U) ⁻¹ᵁ V).ι ≫ fK')) ∧
      fK' ≫ Spec.map (CommRingCat.ofHom (algebraMap (AlgebraicClosure ℚ) (CrossingQuotient (AlgebraicClosure ℚ) (jO (((p : ℕ) : O) ^ e))))) = (prJ ⁻¹ᵁ U).ι ≫ pullback.snd _ _ ∧
      (fK'.appTop).hom ((Scheme.ΓSpecIso (CommRingCat.of (CrossingQuotient (AlgebraicClosure ℚ) (jO (((p : ℕ) : O) ^ e))))).inv.hom (CrossingQuotient.V (jO (((p : ℕ) : O) ^ e)))) =
        (((prJ ∣_ U) ≫ f).appTop).hom ((Scheme.ΓSpecIso (CommRingCat.of (CrossingQuotient O (((p : ℕ) : O) ^ e)))).inv.hom (CrossingQuotient.V (((p : ℕ) : O) ^ e))) ∧
      ∀ (χK : CrossingQuotient O (((p : ℕ) : O) ^ e) →+* AlgebraicClosure ℚ) (hχK : χK.comp (algebraMap O (CrossingQuotient O (((p : ℕ) : O) ^ e))) = jO)
        (pt : ↥(prJ ⁻¹ᵁ U : Scheme.{0})) (zQ : Spec (CommRingCat.of (AlgebraicClosure ℚ)) ⟶ (prJ ⁻¹ᵁ U : Scheme.{0}))
        (hzQpt : zQ.base (IsLocalRing.closedPoint (AlgebraicClosure ℚ)) = pt)
        (hzQ₁ : zQ ≫ (prJ ∣_ U) ≫ f = Spec.map (CommRingCat.ofHom χK)) (hzQ₂ : zQ ≫ (prJ ⁻¹ᵁ U).ι ≫ pullback.snd _ _ = 𝟙 _),
        IsLocalRing.maximalIdeal ((Spec (CommRingCat.of (CrossingQuotient (AlgebraicClosure ℚ) (jO (((p : ℕ) : O) ^ e))))).presheaf.stalk (fK'.base pt)) =
          Ideal.span {((Spec (CommRingCat.of (CrossingQuotient (AlgebraicClosure ℚ) (jO (((p : ℕ) : O) ^ e))))).presheaf.germ ⊤ (fK'.base pt) trivial).hom
            ((Scheme.ΓSpecIso (CommRingCat.of (CrossingQuotient (AlgebraicClosure ℚ) (jO (((p : ℕ) : O) ^ e))))).inv.hom
              (CrossingQuotient.V (jO (((p : ℕ) : O) ^ e)) - algebraMap (AlgebraicClosure ℚ) _ (χK (CrossingQuotient.V (((p : ℕ) : O) ^ e)))))} := by
  letI instOQ : Algebra O (AlgebraicClosure ℚ) := jO.toAlgebra
  obtain ⟨fK, hfK₁, hfK₂, hfKet⟩ := ModularCurve.XHDRModelAtP.aux_B1_baseChange_chart p M H hpM hpM2 hHp hj 𝔛 A hA ρ hρ O ρO hϖ
    toκ htoκ jO hjO ιA hιA hιAκ n e he U hxU f hover hfib hpt het hor₁ hor₂ hor₃ hor₄ prJ hprJ rfl
  obtain ⟨iC, heRU, heRV, heRalg⟩ := aux_B1_iso_tensor (O := O) (K := AlgebraicClosure ℚ) (((p : ℕ) : O) ^ e)
  have ht : algebraMap O (AlgebraicClosure ℚ) (((p : ℕ) : O) ^ e) ≠ 0 := by
    rw [map_pow, map_natCast]
    exact pow_ne_zero e (Nat.cast_ne_zero.mpr (Fact.out : p.Prime).ne_zero)
  obtain ⟨hB₁, hB₂, hB₃⟩ := aux_B1_model_base (((p : ℕ) : O) ^ e) ht _ _ iC heRU heRV heRalg f (prJ ∣_ U)
    ((prJ ⁻¹ᵁ U).ι ≫ pullback.snd _ _) fK hfK₁ hfK₂
  refine ⟨fK ≫ Spec.map iC.hom, fun V hV => hB₁ _ (hfKet V hV), hB₂, hB₃, fun χK hχK pt zQ hzQpt hzQ₁ hzQ₂ => ?_⟩
  exact aux_B1_model_point (((p : ℕ) : O) ^ e) ht _ _ iC heRU heRV heRalg f (prJ ∣_ U) ((prJ ⁻¹ᵁ U).ι ≫ pullback.snd _ _)
    fK hfK₁ hfK₂ χK hχK pt zQ hzQpt hzQ₁ hzQ₂

set_option maxHeartbeats 1600000 in

theorem solution
    (p M : ℕ) [Fact p.Prime] [NeZero M] (H : Subgroup (ZMod M)ˣ) (hpM : p ∣ M) (hpM2 : ¬ p ^ 2 ∣ M)
    (hHp : ∀ u : (ZMod M)ˣ, ZMod.unitsMap (Nat.div_dvd_of_dvd hpM) u = 1 → u ∈ H) [NeZero (M / p)]
    (hj : jqModC ℚ ∈ qExpFunctionFieldC ℚ (⊤ : Subgroup SL(2, ℤ)))
    (𝔛 : XHDRModelAtP p M H hpM hj)
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime p)
    [CharP (IsLocalRing.ResidueField ↥A) p] [IsAlgClosed (IsLocalRing.ResidueField ↥A)]
    (ρ : R p →+* ↥A) (hρ : A.subtype.comp ρ = algebraMap (R p) (AlgebraicClosure ℚ))
    (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (ρO : R p →+* O)
    (hϖ : IsLocalRing.maximalIdeal O = Ideal.span {((p : ℕ) : O)})
    (toκ : O →+* ResidueField ↥A) (htoκ : toκ.comp ρO = (IsLocalRing.residue ↥A).comp ρ)

    (jO : O →+* AlgebraicClosure ℚ) (hjO : jO.comp ρO = algebraMap (R p) (AlgebraicClosure ℚ))
    (ιA : O →+* ↥A) (hιA : A.subtype.comp ιA = jO) (hιAκ : (IsLocalRing.residue ↥A).comp ιA = toκ)

    (n : ↥(pullback (𝔛.comp A hA ρ hρ 0) (𝔛.comp A hA ρ hρ 1)))
    (e : ℕ) (he : 1 ≤ e) (U : (XO (ΓM M H) hj ρO).Opens) (hxU : (pullback.fst (𝔛.comp A hA ρ hρ 0) (𝔛.comp A hA ρ hρ 1) ≫ 𝔛.comp A hA ρ hρ 0 ≫ bcMap (ΓM M H) hj ρO toκ htoκ).base n ∈ U)
    (f : (U : Scheme.{0}) ⟶ CrossingQuotient.crossingScheme (((p : ℕ) : O) ^ e))
    (hover : f ≫ Spec.map (CommRingCat.ofHom (algebraMap O (CrossingQuotient O (((p : ℕ) : O) ^ e)))) = U.ι ≫ pullback.snd _ _)
    (hfib : ∀ y : ↥(U : Scheme.{0}),
      (CrossingQuotient.U (((p : ℕ) : O) ^ e) ∈ (f.base y).asIdeal ∧ CrossingQuotient.V (((p : ℕ) : O) ^ e) ∈ (f.base y).asIdeal) ↔ U.ι.base y = (pullback.fst (𝔛.comp A hA ρ hρ 0) (𝔛.comp A hA ρ hρ 1) ≫ 𝔛.comp A hA ρ hρ 0 ≫ bcMap (ΓM M H) hj ρO toκ htoκ).base n)
    (hpt : ∀ y : ↥(U : Scheme.{0}), U.ι.base y = (pullback.fst (𝔛.comp A hA ρ hρ 0) (𝔛.comp A hA ρ hρ 1) ≫ 𝔛.comp A hA ρ hρ 0 ≫ bcMap (ΓM M H) hj ρO toκ htoκ).base n →
      (f.stalkMap y).hom.Flat ∧ Ideal.map (f.stalkMap y).hom (IsLocalRing.maximalIdeal _) = IsLocalRing.maximalIdeal _ ∧ IsIso (f.residueFieldMap y))
    (het : ∀ y : ↥(U : Scheme.{0}), U.ι.base y = (pullback.fst (𝔛.comp A hA ρ hρ 0) (𝔛.comp A hA ρ hρ 1) ≫ 𝔛.comp A hA ρ hρ 0 ≫ bcMap (ΓM M H) hj ρO toκ htoκ).base n → ∃ V : (U : Scheme.{0}).Opens, y ∈ V ∧ Etale (V.ι ≫ f))
    (hor₁ : ∀ y : ↥(U : Scheme.{0}), CrossingQuotient.V (((p : ℕ) : O) ^ e) ∈ (f.base y).asIdeal → U.ι.base y ∈ Set.range (𝔛.comp A hA ρ hρ 0 ≫ bcMap (ΓM M H) hj ρO toκ htoκ).base)
    (hor₂ : ∀ y : ↥(U : Scheme.{0}), CrossingQuotient.U (((p : ℕ) : O) ^ e) ∈ (f.base y).asIdeal → U.ι.base y ∈ Set.range (𝔛.comp A hA ρ hρ 1 ≫ bcMap (ΓM M H) hj ρO toκ htoκ).base)
    (hor₃ : ∀ y : ↥(U : Scheme.{0}), U.ι.base y ∈ Set.range (𝔛.comp A hA ρ hρ 0 ≫ bcMap (ΓM M H) hj ρO toκ htoκ).base → CrossingQuotient.V (((p : ℕ) : O) ^ e) ∈ (f.base y).asIdeal)
    (hor₄ : ∀ y : ↥(U : Scheme.{0}), U.ι.base y ∈ Set.range (𝔛.comp A hA ρ hρ 1 ≫ bcMap (ΓM M H) hj ρO toκ htoκ).base → CrossingQuotient.U (((p : ℕ) : O) ^ e) ∈ (f.base y).asIdeal) :
    letI XQ : Scheme.{0} := pullback (toBase p (ΓM M H) hj) (Spec.map (CommRingCat.ofHom (algebraMap (R p) (AlgebraicClosure ℚ))))
    letI prJ : XQ ⟶ XO (ΓM M H) hj ρO :=
      pullback.map _ _ _ _ (𝟙 _) (Spec.map (CommRingCat.ofHom jO)) (𝟙 _)
        (by rw [Category.comp_id, Category.id_comp]) (by rw [Category.comp_id, ← Spec.map_comp, ← CommRingCat.ofHom_comp, hjO])
    letI VM : (𝔛.Meta).C.Opens := 𝔛.eeta ⁻¹ᵁ (prJ ⁻¹ᵁ U)
    letI Q := CrossingQuotient O (((p : ℕ) : O) ^ e)
    letI φ : Q →+* Γ(CrossingQuotient.crossingScheme (((p : ℕ) : O) ^ e), ⊤) := (Scheme.ΓSpecIso (CommRingCat.of Q)).inv.hom
    letI gv : Γ(XO (ΓM M H) hj ρO, U.ι ''ᵁ ⊤) := (U.ι.appIso ⊤).inv (f.appTop (φ (CrossingQuotient.V (((p : ℕ) : O) ^ e))))
    letI gu : Γ(XO (ΓM M H) hj ρO, U.ι ''ᵁ ⊤) := (U.ι.appIso ⊤).inv (f.appTop (φ (CrossingQuotient.U (((p : ℕ) : O) ^ e))))
    ∀ hgen : genericPoint (𝔛.Meta).C ∈ 𝔛.eeta ⁻¹ᵁ (prJ ⁻¹ᵁ (U.ι ''ᵁ ⊤)),
    letI read : Γ(XO (ΓM M H) hj ρO, U.ι ''ᵁ ⊤) →+* ↥(xHFunctionFieldBar M H) :=
      (𝔛.Meta).ffEquiv.symm.toRingHom.comp
        (((𝔛.Meta).C.presheaf.germ (𝔛.eeta ⁻¹ᵁ (prJ ⁻¹ᵁ (U.ι ''ᵁ ⊤))) (genericPoint (𝔛.Meta).C) hgen).hom.comp
          ((𝔛.eeta.app (prJ ⁻¹ᵁ (U.ι ''ᵁ ⊤))).hom.comp (prJ.app (U.ι ''ᵁ ⊤)).hom))
    letI param : ↥(xHFunctionFieldBar M H) := read gv
    ∀ (W : Place (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H)), W.IsRational →
      ∀ (s : Spec (CommRingCat.of ↥A) ⟶ (U : Scheme.{0})),
        s ≫ U.ι ≫ pullback.snd _ _ = Spec.map (CommRingCat.ofHom ιA) →
        barPt A ≫ s ≫ U.ι = ((𝔛.Meta).pointEquivPlace.symm W).1 ≫ 𝔛.eeta ≫ prJ →
        U.ι.base (s.base (IsLocalRing.closedPoint ↥A)) = (pullback.fst (𝔛.comp A hA ρ hρ 0) (𝔛.comp A hA ρ hρ 1) ≫ 𝔛.comp A hA ρ hρ 0 ≫ bcMap (ΓM M H) hj ρO toκ htoκ).base n →
      ∀ (χ : CrossingQuotient O (((p : ℕ) : O) ^ e) →+* ↥A), s ≫ f = Spec.map (CommRingCat.ofHom χ) →
        W.ord (param - algebraMap (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H)
          ((χ (CrossingQuotient.V (((p : ℕ) : O) ^ e)) : ↥A) : AlgebraicClosure ℚ)) = 1 := by
  intro hgen W hW s hs₁ hs₂ hs₃ χ hχ

  set Mc := 𝔛.Meta with hMc
  set z := Mc.pointEquivPlace.symm W with hz
  haveI : LocallyOfFiniteType Mc.toBase := inferInstance
  set xW : closedPoints Mc.C := pointEquivClosedPoint Mc.toBase z with hxW
  have hxWz : (xW : Mc.C) = z.1.base (IsLocalRing.closedPoint (AlgebraicClosure ℚ)) := pointEquivClosedPoint_apply_coe _ _

  have hE2 : Mc.placeOfPoint xW = W := by
    rw [hxW, ← AlgebraicCurve.CurveModel.pointEquivPlace_apply, hz, Equiv.apply_symm_apply]

  set y₀ : AlgebraicClosure ℚ := ((χ (CrossingQuotient.V (((p : ℕ) : O) ^ e)) : ↥A) : AlgebraicClosure ℚ) with hy₀

  set prJ : pullback (toBase p (ΓM M H) hj) (Spec.map (CommRingCat.ofHom (algebraMap (R p) (AlgebraicClosure ℚ)))) ⟶ XO (ΓM M H) hj ρO :=
    pullback.map _ _ _ _ (𝟙 _) (Spec.map (CommRingCat.ofHom jO)) (𝟙 _)
      (by rw [Category.comp_id, Category.id_comp]) (by rw [Category.comp_id, ← Spec.map_comp, ← CommRingCat.ofHom_comp, hjO]) with hprJ
  set Ug : (XO (ΓM M H) hj ρO).Opens := U.ι ''ᵁ ⊤ with hUg
  set VU : Mc.C.Opens := 𝔛.eeta ⁻¹ᵁ (prJ ⁻¹ᵁ Ug) with hVU
  set gv : Γ(XO (ΓM M H) hj ρO, Ug) := (U.ι.appIso ⊤).inv (f.appTop ((Scheme.ΓSpecIso (CommRingCat.of (CrossingQuotient O (((p : ℕ) : O) ^ e)))).inv.hom
            (CrossingQuotient.V (((p : ℕ) : O) ^ e)))) with hgv
  set gvQ : Γ(Mc.C, VU) := (𝔛.eeta.app (prJ ⁻¹ᵁ Ug)).hom ((prJ.app Ug).hom gv) with hgvQ
  set cst : Γ(Mc.C, VU) := Mc.C.presheaf.map (homOfLE le_top).op (Mc.toBase.appTop ((Scheme.ΓSpecIso (CommRingCat.of (AlgebraicClosure ℚ))).inv y₀)) with hcst
  set τ : Γ(Mc.C, VU) := gvQ - cst with hτ

  have hxVU : (xW : Mc.C) ∈ VU := by
    rw [hxWz]
    show (z.1 ≫ 𝔛.eeta ≫ prJ).base (IsLocalRing.closedPoint (AlgebraicClosure ℚ)) ∈ (Ug : Set _)
    rw [hz, ← hs₂]
    exact ⟨(s.base ((barPt A).base (IsLocalRing.closedPoint (AlgebraicClosure ℚ)))), trivial, rfl⟩
  haveI hVUne : Nonempty (VU : Scheme.{0}) := ⟨⟨genericPoint Mc.C, hgen⟩⟩
  set γ : Mc.C.presheaf.stalk xW.1 := (Mc.C.presheaf.germ VU xW.1 hxVU).hom τ with hγ

  have hE1a : algebraMap (Mc.C.presheaf.stalk xW.1) Mc.C.functionField γ =
      (Mc.C.presheaf.germ VU (genericPoint Mc.C) hgen).hom τ :=
    (IsScalarTower.algebraMap_apply Γ(Mc.C, VU) (Mc.C.presheaf.stalk ((⟨xW.1, hxVU⟩ : VU) : Mc.C)) Mc.C.functionField τ).symm
  have hcstgen : (Mc.C.presheaf.germ VU (genericPoint Mc.C) hgen).hom cst =
      (Mc.C.presheaf.germ ⊤ (genericPoint Mc.C) trivial).hom ((Mc.toBase.appTop).hom ((Scheme.ΓSpecIso (CommRingCat.of (AlgebraicClosure ℚ))).inv.hom y₀)) := by
    rw [hcst, TopCat.Presheaf.germ_res_apply]
  have hE1c : Mc.ffEquiv.symm ((Mc.C.presheaf.germ VU (genericPoint Mc.C) hgen).hom cst) =
      algebraMap (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H) y₀ := by
    rw [hcstgen, RingEquiv.symm_apply_eq]
    exact (Mc.ffEquiv_algebraMap y₀).symm
  have hE1 : Mc.ffEquiv.symm (algebraMap (Mc.C.presheaf.stalk xW.1) Mc.C.functionField γ) =
      Mc.ffEquiv.symm ((Mc.C.presheaf.germ VU (genericPoint Mc.C) hgen).hom gvQ) -
        algebraMap (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H) y₀ := by
    rw [hE1a, hτ, map_sub, map_sub, hE1c]

  have hKEY : IsLocalRing.maximalIdeal (Mc.C.presheaf.stalk xW.1) = Ideal.span {γ} := by

    obtain ⟨fK', hfK'et, hfK'₂, hfK'V, hK2⟩ := ModularCurve.XHDRModelAtP.aux_B1_chart_barQ p M H hpM hpM2 hHp hj 𝔛 A hA ρ hρ O ρO hϖ
      toκ htoκ jO hjO ιA hιA hιAκ n e he U hxU f hover hfib hpt het hor₁ hor₂ hor₃ hor₄ prJ hprJ

    obtain ⟨xn, hxn⟩ : ∃ xn, xn = (pullback.fst (𝔛.comp A hA ρ hρ 0) (𝔛.comp A hA ρ hρ 1) ≫ 𝔛.comp A hA ρ hρ 0 ≫ bcMap (ΓM M H) hj ρO toκ htoκ).base n :=
      ⟨_, rfl⟩
    have hxnU : xn ∈ U := by rw [hxn]; exact hxU
    have hyn : U.ι.base ⟨xn, hxnU⟩ = (pullback.fst (𝔛.comp A hA ρ hρ 0) (𝔛.comp A hA ρ hρ 1) ≫ 𝔛.comp A hA ρ hρ 0 ≫ bcMap (ΓM M H) hj ρO toκ htoκ).base n := by
      rw [← hxn]; rfl
    obtain ⟨V, hyV, hVet⟩ := het ⟨xn, hxnU⟩ hyn
    haveI hetK' : Etale (((prJ ∣_ U) ⁻¹ᵁ V).ι ≫ fK') := hfK'et V hVet

    have hUg' : Ug = U := by rw [hUg, Scheme.Opens.ι_image_top]
    have hxVU' : (xW : Mc.C) ∈ 𝔛.eeta ⁻¹ᵁ (prJ ⁻¹ᵁ U) := by
      have h := hxVU
      rw [hVU, hUg'] at h
      exact h
    obtain ⟨g, hgdef⟩ : ∃ g : (𝔛.eeta ⁻¹ᵁ (prJ ⁻¹ᵁ U) : Scheme.{0}) ⟶ (prJ ⁻¹ᵁ U : Scheme.{0}), g = 𝔛.eeta ∣_ (prJ ⁻¹ᵁ U) :=
      ⟨_, rfl⟩
    haveI hgiso : IsIso g := by rw [hgdef]; infer_instance
    have hgx : (g.base ⟨xW.1, hxVU'⟩).1 = 𝔛.eeta.base xW.1 := by rw [hgdef, morphismRestrict_base_coe]
    have hq_prJ : prJ.base (𝔛.eeta.base xW.1) = U.ι.base (s.base ((barPt A).base (IsLocalRing.closedPoint (AlgebraicClosure ℚ)))) := by
      rw [hxWz]
      show (z.1 ≫ 𝔛.eeta ≫ prJ).base (IsLocalRing.closedPoint (AlgebraicClosure ℚ)) = _
      rw [hz, ← hs₂]
      rfl

    have hgxQ : (prJ ∣_ U).base (g.base ⟨xW.1, hxVU'⟩) = s.base ((barPt A).base (IsLocalRing.closedPoint (AlgebraicClosure ℚ))) := by
      apply Subtype.ext
      rw [morphismRestrict_base_coe, hgx]
      exact hq_prJ
    have hsclosed : s.base (IsLocalRing.closedPoint ↥A) = ⟨xn, hxnU⟩ := by
      apply U.ι.isOpenEmbedding.injective
      rw [hs₃, hyn]
    have hxQV : g.base ⟨xW.1, hxVU'⟩ ∈ (prJ ∣_ U) ⁻¹ᵁ V := by
      show (prJ ∣_ U).base (g.base ⟨xW.1, hxVU'⟩) ∈ V
      rw [hgxQ]
      have hspec : s.base ((barPt A).base (IsLocalRing.closedPoint (AlgebraicClosure ℚ))) ⤳ s.base (IsLocalRing.closedPoint ↥A) :=
        (IsLocalRing.specializes_closedPoint _).map s.base.hom.continuous
      rw [hsclosed] at hspec
      exact hspec.mem_open V.2 hyV

    obtain ⟨zQ, hzQι⟩ : ∃ zQ : Spec (CommRingCat.of (AlgebraicClosure ℚ)) ⟶ (prJ ⁻¹ᵁ U : Scheme.{0}), zQ ≫ (prJ ⁻¹ᵁ U).ι = z.1 ≫ 𝔛.eeta := by
      refine ⟨IsOpenImmersion.lift (prJ ⁻¹ᵁ U).ι (z.1 ≫ 𝔛.eeta) ?_, IsOpenImmersion.lift_fac _ _ _⟩
      rintro _ ⟨pt, rfl⟩
      obtain rfl : pt = IsLocalRing.closedPoint (AlgebraicClosure ℚ) := Subsingleton.elim _ _
      refine ⟨g.base ⟨xW.1, hxVU'⟩, ?_⟩
      show (g.base ⟨xW.1, hxVU'⟩).1 = _
      rw [hgx, hxWz]
      rfl
    have hzQg : zQ ≫ (prJ ∣_ U) = barPt A ≫ s := by
      rw [← cancel_mono U.ι, Category.assoc, Category.assoc, morphismRestrict_ι, ← Category.assoc, hzQι, hs₂, hz,
        Category.assoc]
    have hzQ₁ : zQ ≫ (prJ ∣_ U) ≫ f = Spec.map (CommRingCat.ofHom (A.subtype.comp χ)) := by
      rw [← Category.assoc, hzQg, Category.assoc, hχ, CommRingCat.ofHom_comp, Spec.map_comp]
    have hzQ₂ : zQ ≫ (prJ ⁻¹ᵁ U).ι ≫ pullback.snd _ _ = 𝟙 _ := by
      rw [← Category.assoc, hzQι, Category.assoc, 𝔛.heeta]
      exact z.2
    have hzQpt : zQ.base (IsLocalRing.closedPoint (AlgebraicClosure ℚ)) = g.base ⟨xW.1, hxVU'⟩ := by
      apply (prJ ⁻¹ᵁ U).ι.isOpenEmbedding.injective
      show ((zQ ≫ (prJ ⁻¹ᵁ U).ι).base (IsLocalRing.closedPoint (AlgebraicClosure ℚ))) = (g.base ⟨xW.1, hxVU'⟩).1
      rw [hzQι, hgx, hxWz]
      rfl

    have hχO : χ.comp (algebraMap O (CrossingQuotient O (((p : ℕ) : O) ^ e))) = ιA := by
      have h1 : Spec.map (CommRingCat.ofHom (χ.comp (algebraMap O (CrossingQuotient O (((p : ℕ) : O) ^ e))))) =
          Spec.map (CommRingCat.ofHom ιA) := by
        rw [CommRingCat.ofHom_comp, Spec.map_comp, ← hχ, Category.assoc, hover]
        exact hs₁
      have h2 := congrArg CommRingCat.Hom.hom (Spec.map_injective h1)
      simpa using h2
    have hχK : (A.subtype.comp χ).comp (algebraMap O (CrossingQuotient O (((p : ℕ) : O) ^ e))) = jO := by
      rw [RingHom.comp_assoc, hχO, hιA]
    have hK2pt := hK2 (A.subtype.comp χ) hχK (g.base ⟨xW.1, hxVU'⟩) zQ hzQpt hzQ₁ hzQ₂
    have hunr := AlgebraicGeometry.Scheme.Hom.map_stalkMap_maximalIdeal_eq_of_etale_restrict fK' ((prJ ∣_ U) ⁻¹ᵁ V)
      (g.base ⟨xW.1, hxVU'⟩) hxQV

    have hmaxMc := aux_maximalIdeal_stalk_eq_span_germ_of_iso_restrict (𝔛.eeta ⁻¹ᵁ (prJ ⁻¹ᵁ U)) g fK' ⟨xW.1, hxVU'⟩ _ hunr hK2pt

    have HC : (g ≫ fK') ≫ Spec.map (CommRingCat.ofHom (algebraMap (AlgebraicClosure ℚ) (CrossingQuotient (AlgebraicClosure ℚ) (jO (((p : ℕ) : O) ^ e))))) =
        (𝔛.eeta ⁻¹ᵁ (prJ ⁻¹ᵁ U)).ι ≫ Mc.toBase := by
      rw [Category.assoc, hfK'₂, ← Category.assoc, hgdef, morphismRestrict_ι, Category.assoc, 𝔛.heeta]
    have hCsec := aux_B1_appTop_algebraMap (g ≫ fK') ((𝔛.eeta ⁻¹ᵁ (prJ ⁻¹ᵁ U)).ι ≫ Mc.toBase) HC
      ((A.subtype.comp χ) (CrossingQuotient.V (((p : ℕ) : O) ^ e)))
    refine hmaxMc.trans (congrArg (fun a => Ideal.span {a}) ?_)
    exact aux_B1_compare_germ 𝔛.eeta prJ U f g hgdef fK' Mc.toBase _ _ _ _ hfK'V hCsec _ (map_sub _ _ _) ⟨xW.1, hxVU'⟩ hxVU
  have h1 := AlgebraicCurve.CurveModel.ord_placeOfPoint_ffEquiv_symm_algebraMap_eq_one_of_maximalIdeal_eq_span Mc xW γ hKEY
  rw [hE2, hE1] at h1
  exact h1

end S_ModularCurve_XHDRModelAtP_ord_read_chart_sub_algebraMap_eq_one_of_section_of_chart
end P2MW
export P2MW.S_ModularCurve_XHDRModelAtP_ord_read_chart_sub_algebraMap_eq_one_of_section_of_chart (solution)
