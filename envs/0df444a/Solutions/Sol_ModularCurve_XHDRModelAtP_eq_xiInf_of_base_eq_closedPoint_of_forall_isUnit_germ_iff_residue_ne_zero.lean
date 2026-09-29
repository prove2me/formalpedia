-- Prove2me | solution 1 for ModularCurve.XHDRModelAtP.eq_xiInf_of_base_eq_closedPoint_of_forall_isUnit_germ_iff_residue_ne_zero
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:11.002793+00:00
-- url     : https://prove2.me/submissions/3fd3510d-a5cf-597d-9779-46930a467a4a

import Mathlib
import Definitions.Def_ModularCurve_XHDRModelAtPCrossingFrame
import Definitions.Def_MvPolynomial_CrossingResolutionScheme
import Definitions.Def_AlgebraicCurve_PlaceEvaluation
import Definitions.Def_ModularCurve_ArithmeticGalois
import Definitions.Def_ModularCurve_JZeroNeronObjectAtP
import Definitions.Def_FLTPrelim_Ramification
import Definitions.Def_ModularCurve_JHPlaceSpecialization
import Theorems.Thm_AlgebraicCurve_isClosed_singleton_of_ne_genericPoint
import Theorems.Thm_ModularCurve_XHDRModelAtP_ne_comp_efib_of_mem_closedPoints_of_forall_isUnit_germ_iff_residue_ne_zero
import Theorems.Thm_ModularCurve_XHDRModelAtP_ne_xiZero_of_forall_isUnit_germ_iff_residue_ne_zero
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_XHDRModelAtP_eq_xiInf_of_base_eq_closedPoint_of_forall_isUnit_germ_iff_residue_ne_zero
p2m_attr_erase "simp" "ModularCurve.toRingAut_coeffSemilinearAut ModularCurve.baseAut_arithFrobC_apply ModularCurve.coe_coeffRingAut_apply ModularCurve.baseAut_coeffSemilinearAut ModularCurve.baseAut_x1ArithFrobC_apply ModularCurve.coe_qExpCoeffRingAut_apply ModularCurve.qExpCoeffSemilinearAutHom_apply ModularCurve.baseAut_x1x0ArithFrobC_apply ModularCurve.baseAut_qExpArithFrobC_apply ModularCurve.baseAut_qExpCoeffSemilinearAut ModularCurve.toRingAut_qExpCoeffSemilinearAut"

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry IsLocalRing AlgebraicCurve ModularCurve ModularCurve.XHDRLevel ModularCurve.JZeroNeronObjectAtP MvPolynomial

open scoped MatrixGroups

namespace CIS

theorem exists_bcMap_eq_of_base_eq_closedPoint
    (p M : ℕ) [Fact p.Prime] [NeZero M] (H : Subgroup (ZMod M)ˣ) (hpM : p ∣ M)
    (hj : jqModC ℚ ∈ qExpFunctionFieldC ℚ (⊤ : Subgroup SL(2, ℤ)))
    (A : ValuationSubring (AlgebraicClosure ℚ))
    (ρ : R p →+* ↥A)
    (c : ↥(XO (ΓM M H) hj ρ)) (hc : (XO.toBase (ΓM M H) hj ρ).base c = IsLocalRing.closedPoint ↥A) :
    ∃ y : ↥(fibre (Γ := ΓM M H) (hj := hj) ((IsLocalRing.residue ↥A).comp ρ)), (bcMap (ΓM M H) hj ρ (IsLocalRing.residue ↥A) rfl).base y = c := by
  have hmem : c ∈ Set.range (bcMap (ΓM M H) hj ρ (IsLocalRing.residue ↥A) rfl).base := by
    unfold XHDRLevel.bcMap
    erw [AlgebraicGeometry.Scheme.Pullback.range_map]
    refine ⟨⟨(pullback.fst (toBase p (ΓM M H) hj) (Spec.map (CommRingCat.ofHom ρ))).base c, ?_⟩,
      ⟨IsLocalRing.closedPoint (IsLocalRing.ResidueField ↥A), ?_⟩⟩
    · simp
    · show (Spec.map (CommRingCat.ofHom (IsLocalRing.residue ↥A))).base _ =
        (pullback.snd (toBase p (ΓM M H) hj) (Spec.map (CommRingCat.ofHom ρ))).base c
      exact (IsLocalRing.PrimeSpectrum.comap_residue (↥A) _).trans hc.symm
  obtain ⟨y, hy⟩ := hmem
  exact ⟨y, hy⟩

theorem eq_genericPoint_or_mem_closedPoints {K : Type} [Field K] {L : Type} [Field L] [Algebra K L]
    (Mdl : CurveModel K L) (w : ↥Mdl.C) :
    letI := Mdl.isIntegral
    w = genericPoint Mdl.C ∨ w ∈ closedPoints Mdl.C := by
  letI := Mdl.isIntegral
  by_cases hw : w = genericPoint Mdl.C
  · exact Or.inl hw
  · exact Or.inr ((mem_closedPoints_iff).mpr (AlgebraicCurve.isClosed_singleton_of_ne_genericPoint Mdl.toBase w hw))

end CIS

theorem solution
    (p M : ℕ) [Fact p.Prime] [NeZero M] (H : Subgroup (ZMod M)ˣ) (hpM : p ∣ M) (hpM2 : ¬ p ^ 2 ∣ M)
    (hHp : ∀ u : (ZMod M)ˣ, ZMod.unitsMap (Nat.div_dvd_of_dvd hpM) u = 1 → u ∈ H) [NeZero (M / p)]
    (hj : jqModC ℚ ∈ qExpFunctionFieldC ℚ (⊤ : Subgroup SL(2, ℤ)))
    (𝔛 : XHDRModelAtP p M H hpM hj)
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime p)
    [CharP (IsLocalRing.ResidueField ↥A) p] [IsAlgClosed (IsLocalRing.ResidueField ↥A)]
    (ρ : R p →+* ↥A) (hρ : A.subtype.comp ρ = algebraMap (R p) (AlgebraicClosure ℚ))

    (θ : ↥(xHFunctionFieldBar M H) ≃ₐ[AlgebraicClosure ℚ] ↥(xHFunctionFieldBar M H))
    (Psp : JHPlaceSpecialization p M H hpM A) (Rpd : JHPlaceSpecialization.ProlongationDatum Psp θ) :
    letI XQ : Scheme.{0} := pullback (toBase p (ΓM M H) hj) (Spec.map (CommRingCat.ofHom (algebraMap (R p) (AlgebraicClosure ℚ))))
    letI prA : XQ ⟶ XO (ΓM M H) hj ρ :=
      pullback.map _ _ _ _ (𝟙 _) (Spec.map (CommRingCat.ofHom A.subtype)) (𝟙 _)
        (by rw [Category.comp_id, Category.id_comp]) (by rw [Category.comp_id, ← Spec.map_comp, ← CommRingCat.ofHom_comp, hρ])
    ∀ c : ↥(XO (ΓM M H) hj ρ), (XO.toBase (ΓM M H) hj ρ).base c = IsLocalRing.closedPoint ↥A →
      (∀ (V : (XO (ΓM M H) hj ρ).Opens) (hgenV : genericPoint (𝔛.Meta).C ∈ 𝔛.eeta ⁻¹ᵁ (prA ⁻¹ᵁ V))
        (g : Γ(XO (ΓM M H) hj ρ, V)) (hc : c ∈ V),
        letI readA : Γ(XO (ΓM M H) hj ρ, V) →+* ↥(xHFunctionFieldBar M H) :=
          (𝔛.Meta).ffEquiv.symm.toRingHom.comp
            (((𝔛.Meta).C.presheaf.germ (𝔛.eeta ⁻¹ᵁ (prA ⁻¹ᵁ V)) (genericPoint (𝔛.Meta).C) hgenV).hom.comp
              ((𝔛.eeta.app (prA ⁻¹ᵁ V)).hom.comp (prA.app V).hom))
        ∃ h : readA g ∈ Rpd.R₁.integers,
          (IsUnit ((XO (ΓM M H) hj ρ).presheaf.germ V c hc g) ↔ Rpd.R₁.residue ⟨readA g, h⟩ ≠ 0)) →
      c = 𝔛.ξinf A hA ρ hρ ρ (IsLocalRing.residue ↥A) rfl := by
  intro c hc0 hD
  letI := (𝔛.Mfib A hA ρ hρ).isIntegral
  have hNC := ModularCurve.XHDRModelAtP.ne_comp_efib_of_mem_closedPoints_of_forall_isUnit_germ_iff_residue_ne_zero p M H hpM hpM2 hHp hj 𝔛 A hA ρ hρ θ Psp Rpd c hc0 hD
  have hNZ := ModularCurve.XHDRModelAtP.ne_xiZero_of_forall_isUnit_germ_iff_residue_ne_zero p M H hpM hpM2 hHp hj 𝔛 A hA ρ hρ θ Psp Rpd c hc0 hD
  clear hD
  obtain ⟨y, rfl⟩ := CIS.exists_bcMap_eq_of_base_eq_closedPoint p M H hpM hj A ρ c hc0

  have hz : ∀ z : ↥(fibre (Γ := ΓN p M H hpM) (hj := hj) ((IsLocalRing.residue ↥A).comp ρ)),
      ∃ w : ↥(𝔛.Mfib A hA ρ hρ).C, (𝔛.efib A hA ρ hρ).base w = z := fun z =>
    ⟨(inv (𝔛.efib A hA ρ hρ)).base z, by rw [← Scheme.Hom.comp_apply, IsIso.inv_hom_id]; rfl⟩
  rcases 𝔛.comp_jointly_surjective A hA ρ hρ y with ⟨z, rfl⟩ | ⟨z, rfl⟩
  · obtain ⟨w, rfl⟩ := hz z
    rcases CIS.eq_genericPoint_or_mem_closedPoints (𝔛.Mfib A hA ρ hρ) w with rfl | hw
    ·
      simp only [← Scheme.Hom.comp_apply, Category.assoc]
    · exact (hNC 0 w hw (by simp only [← Scheme.Hom.comp_apply, Category.assoc])).elim
  · obtain ⟨w, rfl⟩ := hz z
    rcases CIS.eq_genericPoint_or_mem_closedPoints (𝔛.Mfib A hA ρ hρ) w with rfl | hw
    · exact (hNZ (by simp only [← Scheme.Hom.comp_apply, Category.assoc])).elim
    · exact (hNC 1 w hw (by simp only [← Scheme.Hom.comp_apply, Category.assoc])).elim

end S_ModularCurve_XHDRModelAtP_eq_xiInf_of_base_eq_closedPoint_of_forall_isUnit_germ_iff_residue_ne_zero
end P2MW
export P2MW.S_ModularCurve_XHDRModelAtP_eq_xiInf_of_base_eq_closedPoint_of_forall_isUnit_germ_iff_residue_ne_zero (solution)
