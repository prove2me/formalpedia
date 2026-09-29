-- Prove2me | solution 1 for ModularCurve.XHDRModelAtP.restrict_comp_one_chart_eq_qExpand_coeffMap_of_coeffMap_eq_coeffEmb
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:11.002793+00:00
-- url     : https://prove2.me/submissions/46aab7a3-5a0e-5906-810d-18859a73e910

import Mathlib
import Definitions.Def_ModularCurve_XHDRModelAtPCrossingFrame
import Definitions.Def_MvPolynomial_CrossingResolutionScheme
import Definitions.Def_AlgebraicCurve_PlaceEvaluation
import Definitions.Def_ModularCurve_ArithmeticGalois
import Definitions.Def_ModularCurve_JZeroNeronObjectAtP
import Definitions.Def_FLTPrelim_Ramification
import Definitions.Def_ModularCurve_JHPlaceSpecialization
import Theorems.Thm_ModularCurve_XHDRModelAtP_coe_ffEquiv_symm_germToFunctionField_app_comp_one_iotaFin_iota0_eq_qExpand_coeffMap_of_mfib
import Theorems.Thm_ModularCurve_exists_coeffMap_eq_coe_of_mem_chartAlg_twoChartIntegralModel_qExpFunctionFieldC
import Theorems.Thm_ModularCurve_coeffMap_injective
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_XHDRModelAtP_restrict_comp_one_chart_eq_qExpand_coeffMap_of_coeffMap_eq_coeffEmb

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry IsLocalRing AlgebraicCurve ModularCurve ModularCurve.XHDRLevel ModularCurve.JZeroNeronObjectAtP MvPolynomial

open scoped MatrixGroups

universe u

theorem auxP_comp_app_apply {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) (U : Z.Opens) (s : Γ(Z, U)) :
    ((f ≫ g).app U).hom s = (f.app (g ⁻¹ᵁ U)).hom ((g.app U).hom s) := by
  rw [Scheme.Hom.comp_app]; rfl

theorem auxP_germ_app_congr {X Z : Scheme.{u}} {h₁ h₂ : X ⟶ Z} (e : h₁ = h₂) (W : Z.Opens) (s : Γ(Z, W)) (x : X)
    (hx₁ : x ∈ h₁ ⁻¹ᵁ W) (hx₂ : x ∈ h₂ ⁻¹ᵁ W) :
    (X.presheaf.germ (h₁ ⁻¹ᵁ W) x hx₁).hom ((h₁.app W).hom s) = (X.presheaf.germ (h₂ ⁻¹ᵁ W) x hx₂).hom ((h₂.app W).hom s) := by
  subst e; rfl

theorem auxP_genericPoint_mem_of_nonempty {X : Scheme.{u}} [IsIntegral X] (U : X.Opens) [h : Nonempty (U : Scheme.{u})] :
    genericPoint X ∈ U := by
  obtain ⟨⟨x, hx⟩⟩ := h
  exact ((genericPoint_spec X).specializes (Set.mem_univ x)).mem_open U.2 hx

theorem auxP_germ_app_congr2 {X Z T : Scheme.{u}} (a : X ⟶ Z) (c : Z ⟶ T) {h : X ⟶ T} (e : a ≫ c = h)
    (W : T.Opens) (s : Γ(T, W)) (x : X) (hx₁ : x ∈ a ⁻¹ᵁ (c ⁻¹ᵁ W)) (hx₂ : x ∈ h ⁻¹ᵁ W) :
    (X.presheaf.germ (a ⁻¹ᵁ (c ⁻¹ᵁ W)) x hx₁).hom ((a.app (c ⁻¹ᵁ W)).hom ((c.app W).hom s)) =
      (X.presheaf.germ (h ⁻¹ᵁ W) x hx₂).hom ((h.app W).hom s) := by
  subst e
  rw [Scheme.Hom.comp_app]
  rfl

theorem auxP_germ_app_congr3 {X Y Z T : Scheme.{u}} (a : X ⟶ Y) (b : Y ⟶ Z) (c : Z ⟶ T) {h : X ⟶ T} (e : a ≫ b ≫ c = h)
    (W : T.Opens) (s : Γ(T, W)) (x : X) (hx₁ : x ∈ a ⁻¹ᵁ (b ⁻¹ᵁ (c ⁻¹ᵁ W))) (hx₂ : x ∈ h ⁻¹ᵁ W) :
    (X.presheaf.germ (a ⁻¹ᵁ (b ⁻¹ᵁ (c ⁻¹ᵁ W))) x hx₁).hom ((a.app (b ⁻¹ᵁ (c ⁻¹ᵁ W))).hom ((b.app (c ⁻¹ᵁ W)).hom ((c.app W).hom s))) =
      (X.presheaf.germ (h ⁻¹ᵁ W) x hx₂).hom ((h.app W).hom s) := by
  subst e
  rw [Scheme.Hom.comp_app, Scheme.Hom.comp_app]
  rfl

set_option maxHeartbeats 3200000 in

theorem solution
    (p M : ℕ) [Fact p.Prime] [NeZero M] (H : Subgroup (ZMod M)ˣ) (hpM : p ∣ M) (hpM2 : ¬ p ^ 2 ∣ M)
    (hHp : ∀ u : (ZMod M)ˣ, ZMod.unitsMap (Nat.div_dvd_of_dvd hpM) u = 1 → u ∈ H) [NeZero (M / p)]
    (hj : jqModC ℚ ∈ qExpFunctionFieldC ℚ (⊤ : Subgroup SL(2, ℤ)))
    (𝔛 : XHDRModelAtP p M H hpM hj)
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime p)
    [CharP (IsLocalRing.ResidueField ↥A) p] [IsAlgClosed (IsLocalRing.ResidueField ↥A)]
    (ρ : R p →+* ↥A) (hρ : A.subtype.comp ρ = algebraMap (R p) (AlgebraicClosure ℚ))

    (θ : ↥(xHFunctionFieldBar M H) ≃ₐ[AlgebraicClosure ℚ] ↥(xHFunctionFieldBar M H))
    (Psp : JHPlaceSpecialization p M H hpM A) (Rpd : JHPlaceSpecialization.ProlongationDatum Psp θ)

    (b : ↥(chartAlgFin p (ΓN p M H hpM) hj)) (y : LaurentSeries ↥A)
    (hy : coeffMap A.subtype y = coeffEmb (AlgebraicClosure ℚ) (((b : ↥(qExpFunctionFieldC ℚ (ΓN p M H hpM))) : LaurentSeries ℚ))) :
    letI XQ : Scheme.{0} := pullback (toBase p (ΓM M H) hj) (Spec.map (CommRingCat.ofHom (algebraMap (R p) (AlgebraicClosure ℚ))))
    letI prA : XQ ⟶ XO (ΓM M H) hj ρ :=
      pullback.map _ _ _ _ (𝟙 _) (Spec.map (CommRingCat.ofHom A.subtype)) (𝟙 _)
        (by rw [Category.comp_id, Category.id_comp]) (by rw [Category.comp_id, ← Spec.map_comp, ← CommRingCat.ofHom_comp, hρ])
    letI bcA := bcMap (ΓM M H) hj ρ (IsLocalRing.residue ↥A) rfl
    letI V : (XO (ΓM M H) hj ρ).Opens :=
      (pullback.fst (toBase p (ΓM M H) hj) (Spec.map (CommRingCat.ofHom ρ))) ⁻¹ᵁ ((ιFin p (ΓM M H) hj) ''ᵁ ⊤)
    letI gb : Γ(XO (ΓM M H) hj ρ, V) :=
      ((pullback.fst (toBase p (ΓM M H) hj) (Spec.map (CommRingCat.ofHom ρ))).app ((ιFin p (ΓM M H) hj) ''ᵁ ⊤)).hom
        (((ιFin p (ΓM M H) hj).appIso ⊤).inv ((Scheme.ΓSpecIso (CommRingCat.of ↥(chartAlgFin p (ΓM M H) hj))).inv (𝔛.iota0 b)))
    letI := (𝔛.Mfib A hA ρ hρ).isIntegral
    ∃ hg₁ : genericPoint (𝔛.Mfib A hA ρ hρ).C ∈ (𝔛.efib A hA ρ hρ ≫ 𝔛.comp A hA ρ hρ 1 ≫ bcA) ⁻¹ᵁ V,
      (((𝔛.Mfib A hA ρ hρ).ffEquiv.symm
          (((𝔛.Mfib A hA ρ hρ).C.presheaf.germ ((𝔛.efib A hA ρ hρ ≫ 𝔛.comp A hA ρ hρ 1 ≫ bcA) ⁻¹ᵁ V) (genericPoint (𝔛.Mfib A hA ρ hρ).C) hg₁)
            (((𝔛.efib A hA ρ hρ ≫ 𝔛.comp A hA ρ hρ 1 ≫ bcA).app V).hom gb)) : JHNeronObjectAtP.Fbar p M H hpM (IsLocalRing.ResidueField ↥A)) : LaurentSeries (IsLocalRing.ResidueField ↥A)) =
        qExpand (IsLocalRing.ResidueField ↥A) p (coeffMap (IsLocalRing.residue ↥A) y) := by
  letI := (𝔛.Mfib A hA ρ hρ).isIntegral

  have hC := ModularCurve.XHDRModelAtP.coe_ffEquiv_symm_germToFunctionField_app_comp_one_iotaFin_iota0_eq_qExpand_coeffMap_of_mfib
    p M H hpM hpM2 hHp hj 𝔛 A hA ρ hρ b
  obtain ⟨hne, hread⟩ := hC
  haveI := hne
  have hgen1 : genericPoint (𝔛.Mfib A hA ρ hρ).C ∈ (𝔛.efib A hA ρ hρ ≫ 𝔛.comp A hA ρ hρ 1 ≫ pullback.fst (toBase p (ΓM M H) hj) (Spec.map (CommRingCat.ofHom ((IsLocalRing.residue ↥A).comp ρ)))) ⁻¹ᵁ ((ιFin p (ΓM M H) hj) ''ᵁ ⊤) :=
    auxP_genericPoint_mem_of_nonempty _
  have hcomp1 : (𝔛.efib A hA ρ hρ ≫ 𝔛.comp A hA ρ hρ 1 ≫ bcMap (ΓM M H) hj ρ (IsLocalRing.residue ↥A) rfl) ≫ pullback.fst (toBase p (ΓM M H) hj) (Spec.map (CommRingCat.ofHom ρ)) =
      𝔛.efib A hA ρ hρ ≫ 𝔛.comp A hA ρ hρ 1 ≫ pullback.fst (toBase p (ΓM M H) hj) (Spec.map (CommRingCat.ofHom ((IsLocalRing.residue ↥A).comp ρ))) := by
    simp only [Category.assoc, bcMap_fst]
  have hg₁ : genericPoint (𝔛.Mfib A hA ρ hρ).C ∈ (𝔛.efib A hA ρ hρ ≫ 𝔛.comp A hA ρ hρ 1 ≫ bcMap (ΓM M H) hj ρ (IsLocalRing.residue ↥A) rfl) ⁻¹ᵁ ((pullback.fst (toBase p (ΓM M H) hj) (Spec.map (CommRingCat.ofHom ρ))) ⁻¹ᵁ ((ιFin p (ΓM M H) hj) ''ᵁ ⊤)) := by
    have h := hgen1
    rw [← hcomp1, Scheme.Hom.comp_preimage] at h
    exact h
  refine ⟨hg₁, ?_⟩

  obtain ⟨hfin, -⟩ := ModularCurve.exists_coeffMap_eq_coe_of_mem_chartAlg_twoChartIntegralModel_qExpFunctionFieldC (ΓN p M H hpM) p
    (jAt (ΓN p M H hpM) hj) (XHDRLevel.coe_jAt (ΓN p M H hpM) hj)
  obtain ⟨yR, hyR⟩ := hfin b
  have hyy : coeffMap ρ yR = y := by
    apply ModularCurve.coeffMap_injective (f := A.subtype) Subtype.val_injective
    rw [coeffMap_coeffMap, hρ, hy, ← hyR, coeffEmb, coeffMap_coeffMap]
    congr 1
  have hyy' : coeffMap (IsLocalRing.residue ↥A) y = coeffMap ((IsLocalRing.residue ↥A).comp ρ) yR := by
    rw [← hyy, coeffMap_coeffMap]
  rw [hyy', auxP_germ_app_congr2 (𝔛.efib A hA ρ hρ ≫ 𝔛.comp A hA ρ hρ 1 ≫ bcMap (ΓM M H) hj ρ (IsLocalRing.residue ↥A) rfl) (pullback.fst (toBase p (ΓM M H) hj) (Spec.map (CommRingCat.ofHom ρ))) hcomp1 ((ιFin p (ΓM M H) hj) ''ᵁ ⊤) (((ιFin p (ΓM M H) hj).appIso ⊤).inv ((Scheme.ΓSpecIso (CommRingCat.of ↥(chartAlgFin p (ΓM M H) hj))).inv (𝔛.iota0 b)))
    (genericPoint (𝔛.Mfib A hA ρ hρ).C) hg₁ hgen1]
  exact hread yR hyR

end S_ModularCurve_XHDRModelAtP_restrict_comp_one_chart_eq_qExpand_coeffMap_of_coeffMap_eq_coeffEmb
end P2MW
export P2MW.S_ModularCurve_XHDRModelAtP_restrict_comp_one_chart_eq_qExpand_coeffMap_of_coeffMap_eq_coeffEmb (solution)
