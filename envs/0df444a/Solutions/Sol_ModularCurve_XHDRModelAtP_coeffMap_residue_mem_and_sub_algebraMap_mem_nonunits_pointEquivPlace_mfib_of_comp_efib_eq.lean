-- Prove2me | solution 1 for ModularCurve.XHDRModelAtP.coeffMap_residue_mem_and_sub_algebraMap_mem_nonunits_pointEquivPlace_mfib_of_comp_efib_eq
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:11.002793+00:00
-- url     : https://prove2.me/submissions/1617109d-31a6-56c1-83df-39f0fdae73ff

import Mathlib
import Definitions.Def_ModularCurve_JHPlaceSpecialization
import Definitions.Def_ModularCurve_XHDRModelAtP
import Definitions.Def_ModularCurve_JHNeronObjectAtP
import Theorems.Thm_AlgebraicCurve_CurveModel_ffEquiv_symm_germToFunctionField_sub_algebraMap_mem_nonunits_pointEquivPlace_of_comp_eq_specMap_comp
import Theorems.Thm_ModularCurve_XHDRModelAtP_coe_ffEquiv_symm_germToFunctionField_app_iotaInf_eq_coeffMap_of_mfib
import Theorems.Thm_ModularCurve_exists_coeffMap_eq_coe_of_mem_chartAlg_twoChartIntegralModel_qExpFunctionFieldC
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_XHDRModelAtP_coeffMap_residue_mem_and_sub_algebraMap_mem_nonunits_pointEquivPlace_mfib_of_comp_efib_eq

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian AlgebraicCurve IsLocalRing ModularCurve ModularCurve.XHDRLevel ModularCurve.JZeroNeronObjectAtP

open scoped MatrixGroups

namespace MfibCentre

theorem coeffMap_injective {R S : Type*} [CommRing R] [CommRing S] {f : R →+* S} (hf : Function.Injective f) :
    Function.Injective (coeffMap f) := by
  intro x y h
  ext k
  apply hf
  have := congrArg (fun z => HahnSeries.coeff z k) h
  simpa [coeffMap_coeff] using this

end MfibCentre

set_option maxHeartbeats 6400000 in
set_option synthInstance.maxHeartbeats 1600000 in
theorem solution
    (p M : ℕ) [Fact p.Prime] [NeZero M] (H : Subgroup (ZMod M)ˣ) (hpM : p ∣ M) [NeZero (M / p)]
    (hj : jqModC ℚ ∈ qExpFunctionFieldC ℚ (⊤ : Subgroup SL(2, ℤ)))
    (𝔛 : XHDRModelAtP p M H hpM hj)
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime p)
    [CharP (ResidueField ↥A) p] [IsAlgClosed (ResidueField ↥A)]
    (ρ : R p →+* ↥A) (hρ : A.subtype.comp ρ = algebraMap (R p) (AlgebraicClosure ℚ)) :
    (∀ (y : {q : Spec (CommRingCat.of (ResidueField ↥A)) ⟶ (𝔛.Mfib A hA ρ hρ).C // q ≫ (𝔛.Mfib A hA ρ hρ).toBase = 𝟙 _})
      (β : ↥(chartAlgFin p (ΓN p M H hpM) hj) →+* ResidueField ↥A),
      y.1 ≫ 𝔛.efib A hA ρ hρ ≫ pullback.fst (toBase p (ΓN p M H hpM) hj) _ =
        Spec.map (CommRingCat.ofHom β) ≫ ιFin p (ΓN p M H hpM) hj →
      ∀ (b : ↥(chartAlgFin p (ΓN p M H hpM) hj)) (yb : LaurentSeries ↥A),
        coeffMap A.subtype yb = coeffEmb (AlgebraicClosure ℚ) ((b : ↥(qExpFunctionFieldC ℚ (ΓN p M H hpM))) : LaurentSeries ℚ) →
        ∃ hmem : coeffMap (IsLocalRing.residue ↥A) yb ∈ qExpFunctionFieldC (ResidueField ↥A) (ΓN p M H hpM),
          (⟨coeffMap (IsLocalRing.residue ↥A) yb, hmem⟩ : ↥(qExpFunctionFieldC (ResidueField ↥A) (ΓN p M H hpM))) ∈ ((𝔛.Mfib A hA ρ hρ).pointEquivPlace y).toValuationSubring ∧
          (⟨coeffMap (IsLocalRing.residue ↥A) yb, hmem⟩ : ↥(qExpFunctionFieldC (ResidueField ↥A) (ΓN p M H hpM))) -
              algebraMap (ResidueField ↥A) ↥(qExpFunctionFieldC (ResidueField ↥A) (ΓN p M H hpM)) (β b) ∈
            ((𝔛.Mfib A hA ρ hρ).pointEquivPlace y).toValuationSubring.nonunits) ∧
    (∀ (y : {q : Spec (CommRingCat.of (ResidueField ↥A)) ⟶ (𝔛.Mfib A hA ρ hρ).C // q ≫ (𝔛.Mfib A hA ρ hρ).toBase = 𝟙 _})
      (β : ↥(chartAlgInf p (ΓN p M H hpM) hj) →+* ResidueField ↥A),
      y.1 ≫ 𝔛.efib A hA ρ hρ ≫ pullback.fst (toBase p (ΓN p M H hpM) hj) _ =
        Spec.map (CommRingCat.ofHom β) ≫ ιInf p (ΓN p M H hpM) hj →
      ∀ (b : ↥(chartAlgInf p (ΓN p M H hpM) hj)) (yb : LaurentSeries ↥A),
        coeffMap A.subtype yb = coeffEmb (AlgebraicClosure ℚ) ((b : ↥(qExpFunctionFieldC ℚ (ΓN p M H hpM))) : LaurentSeries ℚ) →
        ∃ hmem : coeffMap (IsLocalRing.residue ↥A) yb ∈ qExpFunctionFieldC (ResidueField ↥A) (ΓN p M H hpM),
          (⟨coeffMap (IsLocalRing.residue ↥A) yb, hmem⟩ : ↥(qExpFunctionFieldC (ResidueField ↥A) (ΓN p M H hpM))) ∈ ((𝔛.Mfib A hA ρ hρ).pointEquivPlace y).toValuationSubring ∧
          (⟨coeffMap (IsLocalRing.residue ↥A) yb, hmem⟩ : ↥(qExpFunctionFieldC (ResidueField ↥A) (ΓN p M H hpM))) -
              algebraMap (ResidueField ↥A) ↥(qExpFunctionFieldC (ResidueField ↥A) (ΓN p M H hpM)) (β b) ∈
            ((𝔛.Mfib A hA ρ hρ).pointEquivPlace y).toValuationSubring.nonunits) := by
  classical
  refine ⟨?_, ?_⟩
  · intro y β hy b yb hyb

    have hpin := 𝔛.Mfib_pin A hA ρ hρ b yb hyb
    have hmem : coeffMap (IsLocalRing.residue ↥A) yb ∈ qExpFunctionFieldC (ResidueField ↥A) (ΓN p M H hpM) := by
      rw [← hpin]; exact Subtype.property _
    refine ⟨hmem, ?_⟩
    have hRE : (⟨coeffMap (IsLocalRing.residue ↥A) yb, hmem⟩ : ↥(qExpFunctionFieldC (ResidueField ↥A) (ΓN p M H hpM))) =
        (𝔛.Mfib A hA ρ hρ).ffEquiv.symm
          ((𝔛.Mfib A hA ρ hρ).C.germToFunctionField
            ((𝔛.efib A hA ρ hρ ≫ pullback.fst (toBase p (ΓN p M H hpM) hj) (Spec.map (CommRingCat.ofHom ((IsLocalRing.residue ↥A).comp ρ)))) ⁻¹ᵁ
              ((ιFin p (ΓN p M H hpM) hj) ''ᵁ ⊤))
            (((𝔛.efib A hA ρ hρ ≫ pullback.fst (toBase p (ΓN p M H hpM) hj) (Spec.map (CommRingCat.ofHom ((IsLocalRing.residue ↥A).comp ρ)))).app
                ((ιFin p (ΓN p M H hpM) hj) ''ᵁ ⊤)).hom
              (((ιFin p (ΓN p M H hpM) hj).appIso ⊤).inv
                ((Scheme.ΓSpecIso (CommRingCat.of ↥(chartAlgFin p (ΓN p M H hpM) hj))).inv b)))) :=
      Subtype.ext hpin.symm

    haveI := 𝔛.Mfib_chart_nonempty A hA ρ hρ
    have hy' : y.1 ≫ (𝔛.efib A hA ρ hρ ≫ pullback.fst (toBase p (ΓN p M H hpM) hj) (Spec.map (CommRingCat.ofHom ((IsLocalRing.residue ↥A).comp ρ)))) =
        Spec.map (CommRingCat.ofHom β) ≫ ιFin p (ΓN p M H hpM) hj := by
      simpa only [Category.assoc] using hy
    have hval := AlgebraicCurve.CurveModel.ffEquiv_symm_germToFunctionField_sub_algebraMap_mem_nonunits_pointEquivPlace_of_comp_eq_specMap_comp
      (𝔛.Mfib A hA ρ hρ) (𝔛.efib A hA ρ hρ ≫ pullback.fst (toBase p (ΓN p M H hpM) hj) (Spec.map (CommRingCat.ofHom ((IsLocalRing.residue ↥A).comp ρ))))
      (ιFin p (ΓN p M H hpM) hj) y β hy' b
    rw [hRE]
    refine ⟨?_, hval⟩
    have := add_mem (ValuationSubring.nonunits_subset hval) (((𝔛.Mfib A hA ρ hρ).pointEquivPlace y).algebraMap_mem' (β b))
    rwa [sub_add_cancel] at this
  · intro y β hy b yb hyb

    obtain ⟨yR, hyR⟩ := (ModularCurve.exists_coeffMap_eq_coe_of_mem_chartAlg_twoChartIntegralModel_qExpFunctionFieldC
      (ΓN p M H hpM) p (jAt (ΓN p M H hpM) hj) (coe_jAt _ hj)).2 b
    obtain ⟨hne, hread⟩ := ModularCurve.XHDRModelAtP.coe_ffEquiv_symm_germToFunctionField_app_iotaInf_eq_coeffMap_of_mfib
      p M H hpM hj 𝔛 A hA ρ hρ b
    have hpinR := hread yR hyR

    have hybR : yb = coeffMap ρ yR := by
      apply MfibCentre.coeffMap_injective (f := A.subtype) Subtype.val_injective
      rw [hyb, coeffMap_coeffMap, hρ, ← hyR, coeffEmb, coeffMap_coeffMap]
      congr 1
    have hred : coeffMap (IsLocalRing.residue ↥A) yb = coeffMap ((IsLocalRing.residue ↥A).comp ρ) yR := by
      rw [hybR, coeffMap_coeffMap]
    have hmem : coeffMap (IsLocalRing.residue ↥A) yb ∈ qExpFunctionFieldC (ResidueField ↥A) (ΓN p M H hpM) := by
      rw [hred, ← hpinR]; exact Subtype.property _
    refine ⟨hmem, ?_⟩
    have hRE : (⟨coeffMap (IsLocalRing.residue ↥A) yb, hmem⟩ : ↥(qExpFunctionFieldC (ResidueField ↥A) (ΓN p M H hpM))) =
        (𝔛.Mfib A hA ρ hρ).ffEquiv.symm
          ((𝔛.Mfib A hA ρ hρ).C.germToFunctionField
            ((𝔛.efib A hA ρ hρ ≫ pullback.fst (toBase p (ΓN p M H hpM) hj) (Spec.map (CommRingCat.ofHom ((IsLocalRing.residue ↥A).comp ρ)))) ⁻¹ᵁ
              ((ιInf p (ΓN p M H hpM) hj) ''ᵁ ⊤))
            (((𝔛.efib A hA ρ hρ ≫ pullback.fst (toBase p (ΓN p M H hpM) hj) (Spec.map (CommRingCat.ofHom ((IsLocalRing.residue ↥A).comp ρ)))).app
                ((ιInf p (ΓN p M H hpM) hj) ''ᵁ ⊤)).hom
              (((ιInf p (ΓN p M H hpM) hj).appIso ⊤).inv
                ((Scheme.ΓSpecIso (CommRingCat.of ↥(chartAlgInf p (ΓN p M H hpM) hj))).inv b)))) :=
      by apply Subtype.ext; exact hred.trans hpinR.symm
    haveI := hne
    have hy' : y.1 ≫ (𝔛.efib A hA ρ hρ ≫ pullback.fst (toBase p (ΓN p M H hpM) hj) (Spec.map (CommRingCat.ofHom ((IsLocalRing.residue ↥A).comp ρ)))) =
        Spec.map (CommRingCat.ofHom β) ≫ ιInf p (ΓN p M H hpM) hj := by
      simpa only [Category.assoc] using hy
    have hval := AlgebraicCurve.CurveModel.ffEquiv_symm_germToFunctionField_sub_algebraMap_mem_nonunits_pointEquivPlace_of_comp_eq_specMap_comp
      (𝔛.Mfib A hA ρ hρ) (𝔛.efib A hA ρ hρ ≫ pullback.fst (toBase p (ΓN p M H hpM) hj) (Spec.map (CommRingCat.ofHom ((IsLocalRing.residue ↥A).comp ρ))))
      (ιInf p (ΓN p M H hpM) hj) y β hy' b
    rw [hRE]
    refine ⟨?_, hval⟩
    have := add_mem (ValuationSubring.nonunits_subset hval) (((𝔛.Mfib A hA ρ hρ).pointEquivPlace y).algebraMap_mem' (β b))
    rwa [sub_add_cancel] at this

end S_ModularCurve_XHDRModelAtP_coeffMap_residue_mem_and_sub_algebraMap_mem_nonunits_pointEquivPlace_mfib_of_comp_efib_eq
end P2MW
export P2MW.S_ModularCurve_XHDRModelAtP_coeffMap_residue_mem_and_sub_algebraMap_mem_nonunits_pointEquivPlace_mfib_of_comp_efib_eq (solution)
