-- Prove2me | solution 1 for ModularCurve.XHDRModelAtP.exists_chart_baseChange_mem_and_flat_and_map_maximalIdeal_eq_and_isIso_residueFieldMap_and_germ_eq_of_chart
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:11.002793+00:00
-- url     : https://prove2.me/submissions/7c6f8cdd-cac1-5e1c-b61c-4187be6a25c9

import Mathlib
import Definitions.Def_ModularCurve_XHDRModelAtPCrossingFrame
import Definitions.Def_MvPolynomial_CrossingResolutionScheme
import Definitions.Def_AlgebraicCurve_PlaceEvaluation
import Definitions.Def_ModularCurve_ArithmeticGalois
import Definitions.Def_ModularCurve_JZeroNeronObjectAtP
import Definitions.Def_FLTPrelim_Ramification
import Definitions.Def_AlgebraicCurve_SemistableCharts
import Definitions.Def_ModularCurve_UVCrossingModel

import Theorems.Thm_ModularCurve_XHDRModelAtP_exists_chart_baseChange_comp_spec_eq_morphismRestrict_comp_and_etale_of_chart
import Theorems.Thm_AlgebraicGeometry_stalkMap_germ_app_appIso_inv_appTop_eq_germ_appTop_of_comp_spec_map_eq_isoOfEq_hom_comp_morphismRestrict_comp
import Theorems.Thm_AlgebraicGeometry_IsPullback_surjective_residueFieldMap_of_isIso_residueFieldMap
import Theorems.Thm_MvPolynomial_CrossingQuotient_surjective_residueFieldMap_specMap_algebraMap_of_U_mem_of_V_mem
import Theorems.Thm_AlgebraicGeometry_Scheme_Hom_map_stalkMap_maximalIdeal_eq_of_etale_restrict
import Theorems.Thm_AlgebraicGeometry_Scheme_Pullback_eq_of_fst_eq_of_snd_eq_of_isIso_residueFieldMap
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_XHDRModelAtP_exists_chart_baseChange_mem_and_flat_and_map_maximalIdeal_eq_and_isIso_residueFieldMap_and_germ_eq_of_chart

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry IsLocalRing AlgebraicCurve ModularCurve ModularCurve.XHDRLevel ModularCurve.JZeroNeronObjectAtP MvPolynomial

open scoped MatrixGroups

universe u

namespace N2aAsm

theorem flat_stalkMap_of_etale_restrict {X Y : Scheme.{u}} (g : X ⟶ Y) (V : X.Opens) [Etale (V.ι ≫ g)]
    (x : ↥X) (hx : x ∈ V) : (g.stalkMap x).hom.Flat := by
  have hF : Flat (V.ι ≫ g) := inferInstance
  have h := (Flat.iff_flat_stalkMap (V.ι ≫ g)).mp hF ⟨x, hx⟩
  rw [Scheme.Hom.stalkMap_comp] at h

  have hb : Function.Bijective (inv (V.ι.stalkMap ⟨x, hx⟩)).hom :=
    ConcreteCategory.bijective_of_isIso (inv (V.ι.stalkMap ⟨x, hx⟩))
  have hi : (inv (V.ι.stalkMap ⟨x, hx⟩)).hom.Flat := RingHom.Flat.of_bijective hb
  have e : (g.stalkMap x).hom =
      (inv (V.ι.stalkMap ⟨x, hx⟩)).hom.comp ((g.stalkMap (V.ι.base ⟨x, hx⟩) ≫ V.ι.stalkMap ⟨x, hx⟩).hom) := by
    rw [← CommRingCat.hom_comp, Category.assoc, IsIso.hom_inv_id, Category.comp_id]
    rfl
  rw [e]
  exact h.comp hi

theorem isIso_residueFieldMap_of_surjective {X Y : Scheme.{u}} (f : X ⟶ Y) (x : ↥X)
    (h : Function.Surjective (f.residueFieldMap x).hom) : IsIso (f.residueFieldMap x) :=
  (ConcreteCategory.isIso_iff_bijective _).mpr ⟨(f.residueFieldMap x).hom.injective, h⟩

theorem isIso_residueFieldMap_of_comp_eq {P Z T : Scheme.{u}} (s : P ⟶ T) (c : P ⟶ Z) (q : Z ⟶ T)
    (hc : c ≫ q = s) (t : ↥P) (hs : Function.Surjective (s.residueFieldMap t).hom) :
    IsIso (c.residueFieldMap t) := by
  subst hc
  rw [Scheme.residueFieldMap_comp] at hs
  refine isIso_residueFieldMap_of_surjective c t ?_
  change Function.Surjective (⇑(c.residueFieldMap t).hom ∘ ⇑(q.residueFieldMap (c.base t)).hom) at hs
  exact Function.Surjective.of_comp hs

theorem surjective_residueFieldMap_of_comp_eq {P Z T : Scheme.{u}} (s : P ⟶ T) (c : P ⟶ Z) (q : Z ⟶ T)
    (hc : c ≫ q = s) (t : ↥P) [IsIso (c.residueFieldMap t)]
    (hq : Function.Surjective (q.residueFieldMap (c.base t)).hom) :
    Function.Surjective (s.residueFieldMap t).hom := by
  subst hc
  rw [Scheme.residueFieldMap_comp]
  change Function.Surjective (⇑(c.residueFieldMap t).hom ∘ ⇑(q.residueFieldMap (c.base t)).hom)
  exact (ConcreteCategory.bijective_of_isIso (c.residueFieldMap t)).2.comp hq

theorem surjective_residueFieldMap_of_chart {X T Z : Scheme.{u}} (s : X ⟶ T) (U : X.Opens)
    (f : (↑U : Scheme.{u}) ⟶ Z) (q : Z ⟶ T) (hover : f ≫ q = U.ι ≫ s) (y : ↥(↑U : Scheme.{u}))
    [IsIso (f.residueFieldMap y)] (hq : Function.Surjective (q.residueFieldMap (f.base y)).hom) :
    Function.Surjective (s.residueFieldMap (U.ι.base y)).hom := by
  have h1 := surjective_residueFieldMap_of_comp_eq _ f q rfl y hq
  rw [hover, Scheme.residueFieldMap_comp] at h1
  change Function.Surjective (⇑(U.ι.residueFieldMap y).hom ∘ ⇑(s.residueFieldMap (U.ι.base y)).hom) at h1
  exact (Function.Surjective.of_comp_iff' (ConcreteCategory.bijective_of_isIso (U.ι.residueFieldMap y)) _).mp h1

theorem isIso_residueFieldMap_of_chart_over {Y X' T Z : Scheme.{u}} (ι : Y ⟶ X') [IsOpenImmersion ι] (s' : X' ⟶ T)
    (g : Y ⟶ Z) (q : Z ⟶ T) (hover : g ≫ q = ι ≫ s') (y : ↥Y)
    (hs : Function.Surjective (s'.residueFieldMap (ι.base y)).hom) : IsIso (g.residueFieldMap y) := by
  apply isIso_residueFieldMap_of_comp_eq _ g q hover y
  rw [Scheme.residueFieldMap_comp]
  change Function.Surjective (⇑(ι.residueFieldMap y).hom ∘ ⇑(s'.residueFieldMap (ι.base y)).hom)
  exact (ConcreteCategory.bijective_of_isIso (ι.residueFieldMap y)).2.comp hs

end N2aAsm

set_option maxHeartbeats 3200000 in
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
    (hor₄ : ∀ y : ↥(U : Scheme.{0}), U.ι.base y ∈ Set.range (𝔛.comp A hA ρ hρ 1 ≫ bcMap (ΓM M H) hj ρO toκ htoκ).base → CrossingQuotient.U (((p : ℕ) : O) ^ e) ∈ (f.base y).asIdeal)

    (O' : Type) [CommRing O'] [IsDomain O'] [IsDiscreteValuationRing O']
    (σ : O →+* O') (ιA' : O' →+* ↥A) (hσ : ιA'.comp σ = ιA) (hιA'inj : Function.Injective ιA') (hιA'loc : IsLocalHom ιA')
    (jO' : O' →+* AlgebraicClosure ℚ) (hjO' : jO'.comp (σ.comp ρO) = algebraMap (R p) (AlgebraicClosure ℚ)) (hιA'j : A.subtype.comp ιA' = jO')
    (htoκ' : ((IsLocalRing.residue ↥A).comp ιA').comp (σ.comp ρO) = (IsLocalRing.residue ↥A).comp ρ) :
    letI XQ : Scheme.{0} := pullback (toBase p (ΓM M H) hj) (Spec.map (CommRingCat.ofHom (algebraMap (R p) (AlgebraicClosure ℚ))))
    letI prJ : XQ ⟶ XO (ΓM M H) hj ρO :=
      pullback.map _ _ _ _ (𝟙 _) (Spec.map (CommRingCat.ofHom jO)) (𝟙 _)
        (by rw [Category.comp_id, Category.id_comp]) (by rw [Category.comp_id, ← Spec.map_comp, ← CommRingCat.ofHom_comp, hjO])
    letI VM : (𝔛.Meta).C.Opens := 𝔛.eeta ⁻¹ᵁ (prJ ⁻¹ᵁ U)
    letI Q := CrossingQuotient O (((p : ℕ) : O) ^ e)
    letI φ : Q →+* Γ(CrossingQuotient.crossingScheme (((p : ℕ) : O) ^ e), ⊤) := (Scheme.ΓSpecIso (CommRingCat.of Q)).inv.hom
    letI gv : Γ(XO (ΓM M H) hj ρO, U.ι ''ᵁ ⊤) := (U.ι.appIso ⊤).inv (f.appTop (φ (CrossingQuotient.V (((p : ℕ) : O) ^ e))))
    letI gu : Γ(XO (ΓM M H) hj ρO, U.ι ''ᵁ ⊤) := (U.ι.appIso ⊤).inv (f.appTop (φ (CrossingQuotient.U (((p : ℕ) : O) ^ e))))
    letI bc' := bcMap (ΓM M H) hj (σ.comp ρO) ((IsLocalRing.residue ↥A).comp ιA') htoκ'
    letI xn' : ↥(XO (ΓM M H) hj (σ.comp ρO)) := (pullback.fst (𝔛.comp A hA ρ hρ 0) (𝔛.comp A hA ρ hρ 1) ≫ 𝔛.comp A hA ρ hρ 0 ≫ bc').base n
    letI prJ' : XQ ⟶ XO (ΓM M H) hj (σ.comp ρO) :=
      pullback.map _ _ _ _ (𝟙 _) (Spec.map (CommRingCat.ofHom jO')) (𝟙 _)
        (by rw [Category.comp_id, Category.id_comp]) (by rw [Category.comp_id, ← Spec.map_comp, ← CommRingCat.ofHom_comp, hjO'])
    letI prσ : XO (ΓM M H) hj (σ.comp ρO) ⟶ XO (ΓM M H) hj ρO :=
      pullback.map _ _ _ _ (𝟙 _) (Spec.map (CommRingCat.ofHom σ)) (𝟙 _)
        (by rw [Category.comp_id, Category.id_comp]) (by rw [Category.comp_id, ← Spec.map_comp, ← CommRingCat.ofHom_comp])
    letI B := (XO (ΓM M H) hj (σ.comp ρO)).presheaf.stalk xn'
    letI σB : O' →+* ↥B := ((XO (ΓM M H) hj (σ.comp ρO)).presheaf.germ ⊤ xn' trivial).hom.comp
      (((XO.toBase (ΓM M H) hj (σ.comp ρO)).appTop).hom.comp (Scheme.ΓSpecIso (CommRingCat.of O')).inv.hom)
    letI W := U.ι ''ᵁ ⊤
    letI Y : Scheme.{0} := ↑(prσ ⁻¹ᵁ W)
    ∃ (hmem : xn' ∈ prσ ⁻¹ᵁ W)
      (g : Y ⟶ CrossingQuotient.crossingScheme (σ (((p : ℕ) : O) ^ e))),

      g ≫ Spec.map (CommRingCat.ofHom (algebraMap O' (CrossingQuotient O' (σ (((p : ℕ) : O) ^ e))))) =
        (prσ ⁻¹ᵁ W).ι ≫ pullback.snd _ _ ∧

      (CrossingQuotient.U (σ (((p : ℕ) : O) ^ e)) ∈ (g.base ⟨xn', hmem⟩).asIdeal ∧ CrossingQuotient.V (σ (((p : ℕ) : O) ^ e)) ∈ (g.base ⟨xn', hmem⟩).asIdeal) ∧

      ((g.stalkMap ⟨xn', hmem⟩).hom.Flat ∧
        Ideal.map (g.stalkMap ⟨xn', hmem⟩).hom (IsLocalRing.maximalIdeal _) = IsLocalRing.maximalIdeal _ ∧
        IsIso (g.residueFieldMap ⟨xn', hmem⟩)) ∧

      ((prσ ⁻¹ᵁ W).ι.stalkMap ⟨xn', hmem⟩).hom
          (((XO (ΓM M H) hj (σ.comp ρO)).presheaf.germ (prσ ⁻¹ᵁ W) xn' hmem).hom ((prσ.app W).hom gu)) =
        (Y.presheaf.germ ⊤ ⟨xn', hmem⟩ trivial).hom
          ((g.appTop).hom ((Scheme.ΓSpecIso (CommRingCat.of (CrossingQuotient O' (σ (((p : ℕ) : O) ^ e))))).inv.hom (CrossingQuotient.U (σ (((p : ℕ) : O) ^ e))))) ∧
      ((prσ ⁻¹ᵁ W).ι.stalkMap ⟨xn', hmem⟩).hom
          (((XO (ΓM M H) hj (σ.comp ρO)).presheaf.germ (prσ ⁻¹ᵁ W) xn' hmem).hom ((prσ.app W).hom gv)) =
        (Y.presheaf.germ ⊤ ⟨xn', hmem⟩ trivial).hom
          ((g.appTop).hom ((Scheme.ΓSpecIso (CommRingCat.of (CrossingQuotient O' (σ (((p : ℕ) : O) ^ e))))).inv.hom (CrossingQuotient.V (σ (((p : ℕ) : O) ^ e))))) := by
  classical

  set bc' := bcMap (ΓM M H) hj (σ.comp ρO) ((IsLocalRing.residue ↥A).comp ιA') htoκ' with hbc'def
  set xn' : ↥(XO (ΓM M H) hj (σ.comp ρO)) :=
    (pullback.fst (𝔛.comp A hA ρ hρ 0) (𝔛.comp A hA ρ hρ 1) ≫ 𝔛.comp A hA ρ hρ 0 ≫ bc').base n with hxn'def
  set prσ : XO (ΓM M H) hj (σ.comp ρO) ⟶ XO (ΓM M H) hj ρO :=
    pullback.map _ _ _ _ (𝟙 _) (Spec.map (CommRingCat.ofHom σ)) (𝟙 _)
      (by rw [Category.comp_id, Category.id_comp]) (by rw [Category.comp_id, ← Spec.map_comp, ← CommRingCat.ofHom_comp]) with hprσdef
  have hC := ModularCurve.XHDRModelAtP.exists_chart_baseChange_comp_spec_eq_morphismRestrict_comp_and_etale_of_chart
      p M H hpM hpM2 hHp hj 𝔛 A hA ρ hρ O ρO hϖ toκ htoκ jO hjO ιA hιA hιAκ n e he U hxU f hover hfib hpt het hor₁ hor₂ hor₃ hor₄ O' σ ιA' hσ hιA'inj hιA'loc jO' hjO' hιA'j htoκ'
  obtain ⟨hmem, hWU, ψ, g, hψσ, hψU, hψV, hover', hfac, hvert, V', hxV', hEt⟩ := hC
  haveI := hEt
  refine ⟨hmem, g, hover', hvert, ⟨?_, ?_, ?_⟩, ?_, ?_⟩
  ·
    exact N2aAsm.flat_stalkMap_of_etale_restrict g V' _ hxV'
  ·
    exact AlgebraicGeometry.Scheme.Hom.map_stalkMap_maximalIdeal_eq_of_etale_restrict g V' _ hxV'
  ·

    have hyn := hpt ⟨_, hxU⟩ rfl
    haveI := hyn.2.2
    have hvO := (hfib ⟨_, hxU⟩).mpr rfl
    have hsurjO := N2aAsm.surjective_residueFieldMap_of_chart _ U f _ hover ⟨_, hxU⟩
      (MvPolynomial.CrossingQuotient.surjective_residueFieldMap_specMap_algebraMap_of_U_mem_of_V_mem (((p : ℕ) : O) ^ e) _ hvO.1 hvO.2)
    haveI hisoO := N2aAsm.isIso_residueFieldMap_of_surjective _ _ hsurjO

    have htoκeq : ((IsLocalRing.residue ↥A).comp ιA').comp σ = toκ := by
      rw [RingHom.comp_assoc, hσ, hιAκ]
    have hbcprσ : bc' ≫ prσ = bcMap (ΓM M H) hj ρO toκ htoκ := by
      apply pullback.hom_ext
      · simp only [hprσdef, hbc'def, bcMap, pullback.map, Category.assoc, pullback.lift_fst, Category.comp_id]
      · simp only [hprσdef, hbc'def, bcMap, pullback.map, Category.assoc, pullback.lift_snd, pullback.lift_snd_assoc,
          Category.comp_id]
        rw [← Spec.map_comp, ← CommRingCat.ofHom_comp, htoκeq]
    have hprσ : prσ.base xn' = (pullback.fst (𝔛.comp A hA ρ hρ 0) (𝔛.comp A hA ρ hρ 1) ≫ 𝔛.comp A hA ρ hρ 0 ≫
        bcMap (ΓM M H) hj ρO toκ htoκ).base n := by
      rw [hxn'def]
      change ((pullback.fst (𝔛.comp A hA ρ hρ 0) (𝔛.comp A hA ρ hρ 1) ≫ 𝔛.comp A hA ρ hρ 0 ≫ bc') ≫ prσ).base n = _
      rw [Category.assoc, Category.assoc, hbcprσ]

    have hsq : IsPullback prσ (pullback.snd (toBase p (ΓM M H) hj) (Spec.map (CommRingCat.ofHom (σ.comp ρO))))
        (pullback.snd (toBase p (ΓM M H) hj) (Spec.map (CommRingCat.ofHom ρO))) (Spec.map (CommRingCat.ofHom σ)) := by
      have e1 : prσ ≫ pullback.fst _ _ = pullback.fst _ _ := by
        simp only [hprσdef, pullback.map, pullback.lift_fst, Category.comp_id]
      have e2 : prσ ≫ pullback.snd _ _ = pullback.snd _ _ ≫ Spec.map (CommRingCat.ofHom σ) := by
        simp only [hprσdef, pullback.map, pullback.lift_snd]
      have hbig : IsPullback (prσ ≫ pullback.fst (toBase p (ΓM M H) hj) (Spec.map (CommRingCat.ofHom ρO)))
          (pullback.snd (toBase p (ΓM M H) hj) (Spec.map (CommRingCat.ofHom (σ.comp ρO)))) (toBase p (ΓM M H) hj)
          (Spec.map (CommRingCat.ofHom σ) ≫ Spec.map (CommRingCat.ofHom ρO)) := by
        rw [e1, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
        exact IsPullback.of_hasPullback _ _
      exact IsPullback.of_right hbig e2 (IsPullback.of_hasPullback _ _)

    haveI : IsIso ((pullback.snd (toBase p (ΓM M H) hj) (Spec.map (CommRingCat.ofHom ρO))).residueFieldMap (prσ.base xn')) := by
      rw [hprσ]; exact hisoO
    exact N2aAsm.isIso_residueFieldMap_of_chart_over _ _ g _ hover' ⟨xn', hmem⟩
      (AlgebraicGeometry.IsPullback.surjective_residueFieldMap_of_isIso_residueFieldMap hsq xn')
  ·
    have h := AlgebraicGeometry.stalkMap_germ_app_appIso_inv_appTop_eq_germ_appTop_of_comp_spec_map_eq_isoOfEq_hom_comp_morphismRestrict_comp _ U f hWU g ψ hfac (CrossingQuotient.U (((p : ℕ) : O) ^ e)) _ hmem
    rw [hψU] at h
    exact h
  ·
    have h := AlgebraicGeometry.stalkMap_germ_app_appIso_inv_appTop_eq_germ_appTop_of_comp_spec_map_eq_isoOfEq_hom_comp_morphismRestrict_comp _ U f hWU g ψ hfac (CrossingQuotient.V (((p : ℕ) : O) ^ e)) _ hmem
    rw [hψV] at h
    exact h

end S_ModularCurve_XHDRModelAtP_exists_chart_baseChange_mem_and_flat_and_map_maximalIdeal_eq_and_isIso_residueFieldMap_and_germ_eq_of_chart
end P2MW
export P2MW.S_ModularCurve_XHDRModelAtP_exists_chart_baseChange_mem_and_flat_and_map_maximalIdeal_eq_and_isIso_residueFieldMap_and_germ_eq_of_chart (solution)
