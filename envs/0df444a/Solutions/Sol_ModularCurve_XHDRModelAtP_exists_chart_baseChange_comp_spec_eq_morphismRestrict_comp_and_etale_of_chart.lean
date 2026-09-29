-- Prove2me | solution 1 for ModularCurve.XHDRModelAtP.exists_chart_baseChange_comp_spec_eq_morphismRestrict_comp_and_etale_of_chart
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:11.002793+00:00
-- url     : https://prove2.me/submissions/dca74885-2798-5f05-999e-af40599ffd2f

import Mathlib
import Definitions.Def_ModularCurve_XHDRModelAtPCrossingFrame
import Definitions.Def_MvPolynomial_CrossingResolutionScheme
import Definitions.Def_AlgebraicCurve_PlaceEvaluation
import Definitions.Def_ModularCurve_ArithmeticGalois
import Definitions.Def_ModularCurve_JZeroNeronObjectAtP
import Definitions.Def_FLTPrelim_Ramification
import Definitions.Def_AlgebraicCurve_SemistableCharts
import Definitions.Def_ModularCurve_UVCrossingModel

import Theorems.Thm_AlgebraicGeometry_exists_baseChange_chart_isPullback_of_isPullback
import Theorems.Thm_MvPolynomial_CrossingQuotient_exists_algEquiv_tensorProduct_apply_U_and_apply_V
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_XHDRModelAtP_exists_chart_baseChange_comp_spec_eq_morphismRestrict_comp_and_etale_of_chart

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry IsLocalRing AlgebraicCurve ModularCurve ModularCurve.XHDRLevel ModularCurve.JZeroNeronObjectAtP MvPolynomial

open scoped MatrixGroups

namespace ChartBC

universe v u

theorem isPullback_of_comp_fst_eq_of_comp_snd_eq {C : Type u} [Category.{v} C]
    {X S T₁ T₂ : C} (f : X ⟶ S) (g₁ : T₁ ⟶ S) (g₂ : T₂ ⟶ T₁) (g : T₂ ⟶ S) (hg : g = g₂ ≫ g₁)
    [HasPullback f g] [HasPullback f g₁]
    (bc : pullback f g ⟶ pullback f g₁)
    (hbc₁ : bc ≫ pullback.fst f g₁ = pullback.fst f g)
    (hbc₂ : bc ≫ pullback.snd f g₁ = pullback.snd f g ≫ g₂) :
    IsPullback bc (pullback.snd f g) (pullback.snd f g₁) g₂ := by
  have big : IsPullback (bc ≫ pullback.fst f g₁) (pullback.snd f g) f (g₂ ≫ g₁) := by
    rw [hbc₁, ← hg]; exact IsPullback.of_hasPullback f g
  exact IsPullback.of_right big hbc₂ (IsPullback.of_hasPullback f g₁)

end ChartBC

open scoped TensorProduct in
open MvPolynomial in
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
    ∃ (hmem : xn' ∈ prσ ⁻¹ᵁ W) (hWU : prσ ⁻¹ᵁ W = prσ ⁻¹ᵁ U)
      (ψ : CrossingQuotient O (((p : ℕ) : O) ^ e) →+* CrossingQuotient O' (σ (((p : ℕ) : O) ^ e)))
      (g : Y ⟶ CrossingQuotient.crossingScheme (σ (((p : ℕ) : O) ^ e))),

      ψ.comp (algebraMap O (CrossingQuotient O (((p : ℕ) : O) ^ e))) = (algebraMap O' (CrossingQuotient O' (σ (((p : ℕ) : O) ^ e)))).comp σ ∧
      ψ (CrossingQuotient.U (((p : ℕ) : O) ^ e)) = CrossingQuotient.U (σ (((p : ℕ) : O) ^ e)) ∧ ψ (CrossingQuotient.V (((p : ℕ) : O) ^ e)) = CrossingQuotient.V (σ (((p : ℕ) : O) ^ e)) ∧

      g ≫ Spec.map (CommRingCat.ofHom (algebraMap O' (CrossingQuotient O' (σ (((p : ℕ) : O) ^ e))))) = (prσ ⁻¹ᵁ W).ι ≫ pullback.snd _ _ ∧

      g ≫ Spec.map (CommRingCat.ofHom ψ) = ((XO (ΓM M H) hj (σ.comp ρO)).isoOfEq hWU).hom ≫ (prσ ∣_ U) ≫ f ∧

      (CrossingQuotient.U (σ (((p : ℕ) : O) ^ e)) ∈ (g.base ⟨xn', hmem⟩).asIdeal ∧ CrossingQuotient.V (σ (((p : ℕ) : O) ^ e)) ∈ (g.base ⟨xn', hmem⟩).asIdeal) ∧

      ∃ V' : Y.Opens, (⟨xn', hmem⟩ : ↥Y) ∈ V' ∧ Etale (V'.ι ≫ g) := by
  classical

  have hκ : ((IsLocalRing.residue ↥A).comp ιA').comp σ = toκ := by
    rw [RingHom.comp_assoc, hσ, hιAκ]
  have hbc : bcMap (ΓM M H) hj (σ.comp ρO) ((IsLocalRing.residue ↥A).comp ιA') htoκ' ≫ (pullback.map _ _ _ _ (𝟙 _) (Spec.map (CommRingCat.ofHom σ)) (𝟙 _) (by rw [Category.comp_id, Category.id_comp]) (by rw [Category.comp_id, ← Spec.map_comp, ← CommRingCat.ofHom_comp]) : (XO (ΓM M H) hj (σ.comp ρO)) ⟶ (XO (ΓM M H) hj ρO)) =
      bcMap (ΓM M H) hj ρO toκ htoκ := by
    apply pullback.hom_ext
    · rw [Category.assoc, pullback.lift_fst, Category.comp_id, XHDRLevel.bcMap_fst, XHDRLevel.bcMap_fst]
    · rw [Category.assoc, pullback.lift_snd, XHDRLevel.bcMap_snd_assoc, XHDRLevel.bcMap_snd, ← Spec.map_comp, ← CommRingCat.ofHom_comp, hκ]

  let prσ : (XO (ΓM M H) hj (σ.comp ρO)) ⟶ (XO (ΓM M H) hj ρO) := (pullback.map _ _ _ _ (𝟙 _) (Spec.map (CommRingCat.ofHom σ)) (𝟙 _) (by rw [Category.comp_id, Category.id_comp]) (by rw [Category.comp_id, ← Spec.map_comp, ← CommRingCat.ofHom_comp]) : (XO (ΓM M H) hj (σ.comp ρO)) ⟶ (XO (ΓM M H) hj ρO))
  have hbc' : bcMap (ΓM M H) hj (σ.comp ρO) ((IsLocalRing.residue ↥A).comp ιA') htoκ' ≫ prσ = bcMap (ΓM M H) hj ρO toκ htoκ := hbc
  have hxn : prσ.base ((pullback.fst (𝔛.comp A hA ρ hρ 0) (𝔛.comp A hA ρ hρ 1) ≫ 𝔛.comp A hA ρ hρ 0 ≫ bcMap (ΓM M H) hj (σ.comp ρO) ((IsLocalRing.residue ↥A).comp ιA') htoκ').base n) = ((pullback.fst (𝔛.comp A hA ρ hρ 0) (𝔛.comp A hA ρ hρ 1) ≫ 𝔛.comp A hA ρ hρ 0 ≫ bcMap (ΓM M H) hj ρO toκ htoκ).base n) := by
    rw [← hbc']; rfl
  have hmem : ((pullback.fst (𝔛.comp A hA ρ hρ 0) (𝔛.comp A hA ρ hρ 1) ≫ 𝔛.comp A hA ρ hρ 0 ≫ bcMap (ΓM M H) hj (σ.comp ρO) ((IsLocalRing.residue ↥A).comp ιA') htoκ').base n) ∈ prσ ⁻¹ᵁ (U.ι ''ᵁ ⊤) := by
    show prσ.base _ ∈ U.ι ''ᵁ ⊤
    rw [hxn, Scheme.Opens.ι_image_top]; exact hxU
  have hWU : prσ ⁻¹ᵁ (U.ι ''ᵁ ⊤) = prσ ⁻¹ᵁ U := by rw [Scheme.Opens.ι_image_top]

  letI : Algebra O O' := σ.toAlgebra
  have hpr : IsPullback prσ (XO.toBase (ΓM M H) hj (σ.comp ρO)) (XO.toBase (ΓM M H) hj ρO) (Spec.map (CommRingCat.ofHom (algebraMap O O'))) := by
    refine ChartBC.isPullback_of_comp_fst_eq_of_comp_snd_eq (toBase p (ΓM M H) hj) (Spec.map (CommRingCat.ofHom ρO))
      (Spec.map (CommRingCat.ofHom σ)) (Spec.map (CommRingCat.ofHom (σ.comp ρO))) ?_ prσ ?_ ?_
    · rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
    · exact (pullback.lift_fst _ _ _).trans (Category.comp_id _)
    · exact pullback.lift_snd _ _ _
  obtain ⟨fK, hK1, hK2, hK3⟩ := AlgebraicGeometry.exists_baseChange_chart_isPullback_of_isPullback
    (XO.toBase (ΓM M H) hj ρO) (XO.toBase (ΓM M H) hj (σ.comp ρO)) prσ hpr U f hover
  obtain ⟨eQ, heU, heV⟩ := MvPolynomial.CrossingQuotient.exists_algEquiv_tensorProduct_apply_U_and_apply_V O (((p : ℕ) : O) ^ e) O' (σ (((p : ℕ) : O) ^ e)) rfl
  let ψ : (CrossingQuotient O (((p : ℕ) : O) ^ e)) →+* (CrossingQuotient O' (σ (((p : ℕ) : O) ^ e))) :=
    eQ.symm.toAlgHom.toRingHom.comp (Algebra.TensorProduct.includeRight (R := O) (A := O') (B := (CrossingQuotient O (((p : ℕ) : O) ^ e)))).toRingHom
  have hψapp : ∀ x, ψ x = eQ.symm (Algebra.TensorProduct.includeRight (R := O) (A := O') (B := (CrossingQuotient O (((p : ℕ) : O) ^ e))) x) := fun x => rfl
  have hψe : eQ.toAlgHom.toRingHom.comp ψ = (Algebra.TensorProduct.includeRight (R := O) (A := O') (B := (CrossingQuotient O (((p : ℕ) : O) ^ e)))).toRingHom :=
    RingHom.ext fun x => by
      show eQ (ψ x) = Algebra.TensorProduct.includeRight x
      rw [hψapp, AlgEquiv.apply_symm_apply]
  have hψU : ψ (CrossingQuotient.U (((p : ℕ) : O) ^ e)) = CrossingQuotient.U (σ (((p : ℕ) : O) ^ e)) := by
    rw [hψapp, Algebra.TensorProduct.includeRight_apply, ← heU, AlgEquiv.symm_apply_apply]
  have hψV : ψ (CrossingQuotient.V (((p : ℕ) : O) ^ e)) = CrossingQuotient.V (σ (((p : ℕ) : O) ^ e)) := by
    rw [hψapp, Algebra.TensorProduct.includeRight_apply, ← heV, AlgEquiv.symm_apply_apply]
  have hψO : ψ.comp (algebraMap O (CrossingQuotient O (((p : ℕ) : O) ^ e))) = (algebraMap O' (CrossingQuotient O' (σ (((p : ℕ) : O) ^ e)))).comp σ := by
    refine RingHom.ext fun o => ?_
    show ψ (algebraMap O (CrossingQuotient O (((p : ℕ) : O) ^ e)) o) = algebraMap O' (CrossingQuotient O' (σ (((p : ℕ) : O) ^ e))) (algebraMap O O' o)
    rw [hψapp, AlgHom.commutes, IsScalarTower.algebraMap_apply O O' (O' ⊗[O] (CrossingQuotient O (((p : ℕ) : O) ^ e))), AlgEquiv.commutes]

  let iW := ((XO (ΓM M H) hj (σ.comp ρO))).isoOfEq hWU
  let g : (↑(prσ ⁻¹ᵁ (U.ι ''ᵁ ⊤)) : Scheme.{0}) ⟶ CrossingQuotient.crossingScheme (σ (((p : ℕ) : O) ^ e)) :=
    iW.hom ≫ fK ≫ Spec.map (CommRingCat.ofHom eQ.toAlgHom.toRingHom)

  have hfac : g ≫ Spec.map (CommRingCat.ofHom ψ) = iW.hom ≫ (prσ ∣_ U) ≫ f := by
    show (iW.hom ≫ fK ≫ Spec.map _) ≫ _ = _
    simp only [Category.assoc]
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp, hψe, hK1]
  have hpt0 : (iW.hom ≫ (prσ ∣_ U)).base ⟨((pullback.fst (𝔛.comp A hA ρ hρ 0) (𝔛.comp A hA ρ hρ 1) ≫ 𝔛.comp A hA ρ hρ 0 ≫ bcMap (ΓM M H) hj (σ.comp ρO) ((IsLocalRing.residue ↥A).comp ιA') htoκ').base n), hmem⟩ = (⟨((pullback.fst (𝔛.comp A hA ρ hρ 0) (𝔛.comp A hA ρ hρ 1) ≫ 𝔛.comp A hA ρ hρ 0 ≫ bcMap (ΓM M H) hj ρO toκ htoκ).base n), hxU⟩ : ↥(U : Scheme.{0})) := by
    apply U.ι.isOpenEmbedding.injective
    show ((iW.hom ≫ (prσ ∣_ U)) ≫ U.ι).base _ = U.ι.base _
    rw [Category.assoc, morphismRestrict_ι, Scheme.isoOfEq_hom_ι_assoc]
    exact hxn
  obtain ⟨V, hyV, hVet⟩ := het ⟨((pullback.fst (𝔛.comp A hA ρ hρ 0) (𝔛.comp A hA ρ hρ 1) ≫ 𝔛.comp A hA ρ hρ 0 ≫ bcMap (ΓM M H) hj ρO toκ htoκ).base n), hxU⟩ rfl
  refine ⟨hmem, hWU, ψ, g, hψO, hψU, hψV, ?_, hfac, ?_, ?_⟩
  ·
    show (iW.hom ≫ fK ≫ Spec.map _) ≫ _ = _
    simp only [Category.assoc]
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp,
      show eQ.toAlgHom.toRingHom.comp (algebraMap O' (CrossingQuotient O' (σ (((p : ℕ) : O) ^ e)))) = algebraMap O' (O' ⊗[O] (CrossingQuotient O (((p : ℕ) : O) ^ e))) from eQ.toAlgHom.comp_algebraMap,
      hK2, Scheme.isoOfEq_hom_ι_assoc]
  ·
    have hq : ((Spec.map (CommRingCat.ofHom ψ)).base (g.base ⟨((pullback.fst (𝔛.comp A hA ρ hρ 0) (𝔛.comp A hA ρ hρ 1) ≫ 𝔛.comp A hA ρ hρ 0 ≫ bcMap (ΓM M H) hj (σ.comp ρO) ((IsLocalRing.residue ↥A).comp ιA') htoκ').base n), hmem⟩)).asIdeal =
        (f.base (⟨((pullback.fst (𝔛.comp A hA ρ hρ 0) (𝔛.comp A hA ρ hρ 1) ≫ 𝔛.comp A hA ρ hρ 0 ≫ bcMap (ΓM M H) hj ρO toκ htoκ).base n), hxU⟩ : ↥(U : Scheme.{0}))).asIdeal := by
      rw [← hpt0]
      show ((g ≫ Spec.map (CommRingCat.ofHom ψ)).base _).asIdeal = (((iW.hom ≫ (prσ ∣_ U)) ≫ f).base _).asIdeal
      rw [hfac, Category.assoc]
    have hUV := (hfib ⟨((pullback.fst (𝔛.comp A hA ρ hρ 0) (𝔛.comp A hA ρ hρ 1) ≫ 𝔛.comp A hA ρ hρ 0 ≫ bcMap (ΓM M H) hj ρO toκ htoκ).base n), hxU⟩).mpr rfl
    rw [← hq] at hUV
    exact ⟨hψU ▸ (Ideal.mem_comap.mp hUV.1), hψV ▸ (Ideal.mem_comap.mp hUV.2)⟩
  ·
    have hres := isPullback_morphismRestrict (prσ ∣_ U) V
    have hsq : IsPullback (((prσ ∣_ U) ⁻¹ᵁ V).ι ≫ fK) ((prσ ∣_ U) ∣_ V)
        (Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.includeRight (R := O) (A := O') (B := (CrossingQuotient O (((p : ℕ) : O) ^ e)))).toRingHom)) (V.ι ≫ f) :=
      hres.flip.paste_horiz hK3
    haveI : Etale (((prσ ∣_ U) ⁻¹ᵁ V).ι ≫ fK) := MorphismProperty.of_isPullback hsq.flip hVet
    refine ⟨iW.hom ⁻¹ᵁ ((prσ ∣_ U) ⁻¹ᵁ V), ?_, ?_⟩
    · show (iW.hom ≫ (prσ ∣_ U)).base _ ∈ V
      rw [hpt0]; exact hyV
    · have heq : (iW.hom ⁻¹ᵁ ((prσ ∣_ U) ⁻¹ᵁ V)).ι ≫ g =
          (iW.hom ∣_ ((prσ ∣_ U) ⁻¹ᵁ V)) ≫ ((((prσ ∣_ U) ⁻¹ᵁ V).ι ≫ fK) ≫ Spec.map (CommRingCat.ofHom eQ.toAlgHom.toRingHom)) := by
        show _ ≫ iW.hom ≫ fK ≫ _ = _
        rw [← morphismRestrict_ι_assoc, Category.assoc]
      rw [heq]
      haveI : IsIso (Spec.map (CommRingCat.ofHom eQ.toAlgHom.toRingHom) : Spec (CommRingCat.of (O' ⊗[O] (CrossingQuotient O (((p : ℕ) : O) ^ e)))) ⟶ Spec (CommRingCat.of (CrossingQuotient O' (σ (((p : ℕ) : O) ^ e))))) :=
        inferInstanceAs (IsIso (Spec.map (@RingEquiv.toCommRingCatIso (CrossingQuotient O' (σ (((p : ℕ) : O) ^ e))) (O' ⊗[O] (CrossingQuotient O (((p : ℕ) : O) ^ e))) _ _ eQ.toRingEquiv).hom))
      infer_instance

end S_ModularCurve_XHDRModelAtP_exists_chart_baseChange_comp_spec_eq_morphismRestrict_comp_and_etale_of_chart
end P2MW
export P2MW.S_ModularCurve_XHDRModelAtP_exists_chart_baseChange_comp_spec_eq_morphismRestrict_comp_and_etale_of_chart (solution)
