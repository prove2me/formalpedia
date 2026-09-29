-- Prove2me | solution 1 for ModularCurve.JHNeronObjectAtP.levelData_ptsSp_frobeniusPushforward_eq_schemeHomOverComp_frobenius_ptsSp_of_hsp
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:09.976215+00:00
-- url     : https://prove2.me/submissions/babafa1b-86c8-5aaf-9cdd-89af48a097f8

import Mathlib
import Definitions.Def_ModularCurve_XHDRModelAtP
import Definitions.Def_ModularCurve_JHNeronObjectAtP
import Definitions.Def_AlgebraicCurve_GluedPic0Functoriality
import Definitions.Def_AlgebraicCurve_GluedPic0SliceOps
import Definitions.Def_AlgebraicGeometry_SchemeFrobenius
import Definitions.Def_ModularCurve_QExpCoeffSemilinearAut
import Definitions.Def_CuspForm_HeckeOperatorFormsGammaH
import Definitions.Def_ModularCurve_XH
import Theorems.Thm_ModularCurve_JHNeronObjectAtP_ptsSp_symm_frobeniusTwist_eq_glueMap_of_pointReduction
import Theorems.Thm_ModularCurve_qExpFrobeniusPlaceModL_eq_qExpArithFrobC_smul
import Theorems.Thm_AlgebraicCurve_GluedPic0_toPic0Pair_surjective
import Theorems.Thm_AlgebraicCurve_isCurveOver_of_isAlgClosed_of_transcendental
import Theorems.Thm_ModularCurve_exists_transcendental_finiteDimensional_qExpFunctionFieldC_of_isAlgClosed
import Theorems.Thm_ModularCurve_qExpFrobeniusPushforwardModL_mk_eq_mk_of_eq_mapDomain
import Theorems.Thm_ModularCurve_qExpFrobeniusPlaceModL_bijective
import Theorems.Thm_ModularCurve_image_qExpFrobeniusPlaceModL_ssPlacesQExp_eq
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_JHNeronObjectAtP_levelData_ptsSp_frobeniusPushforward_eq_schemeHomOverComp_frobenius_ptsSp_of_hsp
p2m_attr_erase "instance" "AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions GaloisRep.ratLocalizedAt.span_isPrime GaloisRep.instAlgebraRatLocalizedAtZMod"
p2m_attr_erase "simp" "AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal AlgebraicCurve.RationalFunctionField.placeInfty_toValuationSubring AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none ModularCurve.toRingAut_coeffSemilinearAut ModularCurve.baseAut_arithFrobC_apply ModularCurve.coe_coeffRingAut_apply ModularCurve.baseAut_coeffSemilinearAut WeierstrassCurve.reducePoint_zero WeierstrassCurve.Affine.Point.galoisRep_apply"

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian AlgebraicCurve IsLocalRing ModularCurve ModularCurve.JZeroNeronObjectAtP

p2m_open "ModularCurve.XHDRLevel~ΓN"
open scoped MatrixGroups

set_option synthInstance.maxHeartbeats 1600000 in
set_option maxHeartbeats 6400000 in
open ModularCurve ModularCurve.JHNeronObjectAtP in
theorem solution
    (p M : ℕ) [Fact p.Prime] [NeZero M] (H : Subgroup (ZMod M)ˣ) (hpM : p ∣ M) (hpM2 : ¬ p ^ 2 ∣ M)
    (hHp : ∀ u : (ZMod M)ˣ, ZMod.unitsMap (Nat.div_dvd_of_dvd hpM) u = 1 → u ∈ H) [NeZero (M / p)]
    (hj : jqModC ℚ ∈ qExpFunctionFieldC ℚ (⊤ : Subgroup SL(2, ℤ)))
    (𝔛 : XHDRModelAtP p M H hpM hj)
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime p)
    [CharP (ResidueField ↥A) p] [IsAlgClosed (ResidueField ↥A)]
    (Λ : JHNeronObjectAtP.LevelData p M H hpM A) (O : JHNeronObjectAtP p M H hpM A hA Λ)
    (ρ : R p →+* ↥A) (hρ : A.subtype.comp ρ = algebraMap (R p) (AlgebraicClosure ℚ))
    (hσA : Λ.σA = Spec.map (CommRingCat.ofHom ρ))

    (hsp : ∀ (i : Fin 2)
      (y₁ : {q : Spec (CommRingCat.of (AlgebraicClosure ℚ)) ⟶ 𝔛.Meta.C // q ≫ 𝔛.Meta.toBase = 𝟙 _})
      (u₁ : SchemeHomOver (Spec.map (CommRingCat.ofHom ρ)) (toBase p (ΓM M H) hj))
      (_ : barPt A ≫ u₁.1 = y₁.1 ≫ 𝔛.eeta ≫ pullback.fst _ _)
      (_ : Set.range u₁.1.base ⊆ (𝔛.smoothLocus : Set (X p (ΓM M H) hj)))
      (uκ₁ : Spec (CommRingCat.of (ResidueField ↥A)) ⟶ fibre (Γ := ΓM M H) (hj := hj) ((IsLocalRing.residue ↥A).comp ρ))
      (_ : uκ₁ ≫ pullback.fst _ _ = Spec.map (CommRingCat.ofHom (IsLocalRing.residue ↥A)) ≫ u₁.1)
      (_ : uκ₁ ≫ pullback.snd _ _ = 𝟙 _)
      (P₁ : closedPoints (𝔛.Mfib A hA ρ hρ).C)
      (_ : (𝔛.efib A hA ρ hρ ≫ 𝔛.comp A hA ρ hρ i).base P₁.1 = uκ₁.base (IsLocalRing.closedPoint (ResidueField ↥A)))
      (y₂ : {q : Spec (CommRingCat.of (AlgebraicClosure ℚ)) ⟶ 𝔛.Meta.C // q ≫ 𝔛.Meta.toBase = 𝟙 _})
      (u₂ : SchemeHomOver (Spec.map (CommRingCat.ofHom ρ)) (toBase p (ΓM M H) hj))
      (_ : barPt A ≫ u₂.1 = y₂.1 ≫ 𝔛.eeta ≫ pullback.fst _ _)
      (_ : Set.range u₂.1.base ⊆ (𝔛.smoothLocus : Set (X p (ΓM M H) hj)))
      (uκ₂ : Spec (CommRingCat.of (ResidueField ↥A)) ⟶ fibre (Γ := ΓM M H) (hj := hj) ((IsLocalRing.residue ↥A).comp ρ))
      (_ : uκ₂ ≫ pullback.fst _ _ = Spec.map (CommRingCat.ofHom (IsLocalRing.residue ↥A)) ≫ u₂.1)
      (_ : uκ₂ ≫ pullback.snd _ _ = 𝟙 _)
      (P₂ : closedPoints (𝔛.Mfib A hA ρ hρ).C)
      (_ : (𝔛.efib A hA ρ hρ ≫ 𝔛.comp A hA ρ hρ i).base P₂.1 = uκ₂.base (IsLocalRing.closedPoint (ResidueField ↥A)))
      (Dv : Divisor.degZero (K := AlgebraicClosure ℚ) (F := ↥(xHFunctionFieldBar M H)))
      (_ : (Dv : Divisor (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H)) =
        Finsupp.single (𝔛.Meta.pointEquivPlace y₁) 1 - Finsupp.single (𝔛.Meta.pointEquivPlace y₂) 1)
      (x : ↥(GluingData.admissible O.ssFinset))
      (_ : (x : GluingData (ResidueField ↥A) (Fbar p M H hpM (ResidueField ↥A)) O.ssFinset).1 =
        (if i = 0 then Finsupp.single ((𝔛.Mfib A hA ρ hρ).placeOfPoint P₁) 1 -
          Finsupp.single ((𝔛.Mfib A hA ρ hρ).placeOfPoint P₂) 1 else 0))
      (_ : (x : GluingData (ResidueField ↥A) (Fbar p M H hpM (ResidueField ↥A)) O.ssFinset).2.1 =
        (if i = 1 then Finsupp.single ((𝔛.Mfib A hA ρ hρ).placeOfPoint P₁) 1 -
          Finsupp.single ((𝔛.Mfib A hA ρ hρ).placeOfPoint P₂) 1 else 0))
      (_ : (x : GluingData (ResidueField ↥A) (Fbar p M H hpM (ResidueField ↥A)) O.ssFinset).2.2 = 0),
      ∃ s : SchemeHomOver Λ.σA O.g,
        (O.pts (Pic0.mk Dv)).1 = barPt A ≫ s.1 ∧
        O.ptsSp.symm (schemeHomOverComp ⟨resPt A, rfl⟩ s) = GluedPic0.mk O.ssFinset x)

    (F : Pic0 (ResidueField ↥A) (Fbar p M H hpM (ResidueField ↥A)) →+ Pic0 (ResidueField ↥A) (Fbar p M H hpM (ResidueField ↥A)))
    (hF : ∀ z, F z = qExpFrobeniusPushforwardModL (ResidueField ↥A) (ΓN p M H hpM) p z)

    (τF : SchemeHomOver (resPt A ≫ Λ.σA) (resPt A ≫ Λ.σA))
    (hτF : τF.1 = Spec.map (CommRingCat.ofHom (frobenius (ResidueField ↥A) p))) :
    ∀ z : Pic0 (ResidueField ↥A) (Fbar p M H hpM (ResidueField ↥A)),
      Λ.ptsSp (F z) = GoodReductionJacobian.schemeHomOverComp τF.1 τF.2 (Λ.ptsSp z) := by
  classical
  intro z

  obtain ⟨t, -, ht1, ht2⟩ := ModularCurve.exists_transcendental_finiteDimensional_qExpFunctionFieldC_of_isAlgClosed (ResidueField ↥A) (XHDRLevel.ΓN p M H hpM)
    (ModularCurve.translation_mem_GammaH (M / p) (infSubgroup p M H hpM))
  haveI := ht2
  haveI : IsCurveOver (ResidueField ↥A) (Fbar p M H hpM (ResidueField ↥A)) := AlgebraicCurve.isCurveOver_of_isAlgClosed_of_transcendental t ht1
  haveI : HasPrincipalDivisors (ResidueField ↥A) (Fbar p M H hpM (ResidueField ↥A)) := IsCurveOver.hasPrincipalDivisors

  let frob : ↥(SemilinearAut (ResidueField ↥A) (Fbar p M H hpM (ResidueField ↥A))) := qExpArithFrobC p (ResidueField ↥A) (XHDRLevel.ΓN p M H hpM)
  have hfrob : ∀ (x : Fbar p M H hpM (ResidueField ↥A)) (n : ℤ),
      ((frob • x : Fbar p M H hpM (ResidueField ↥A)) : LaurentSeries (ResidueField ↥A)).coeff n = ((x : LaurentSeries (ResidueField ↥A)).coeff n) ^ p :=
    coeff_qExpArithFrobC_smul p (ResidueField ↥A) (XHDRLevel.ΓN p M H hpM)
  have hΦ' : ∀ w, qExpFrobeniusPlaceModL (ResidueField ↥A) (XHDRLevel.ΓN p M H hpM) p w = frob • w :=
    ModularCurve.qExpFrobeniusPlaceModL_eq_qExpArithFrobC_smul p (ResidueField ↥A) (XHDRLevel.ΓN p M H hpM)
  have himg := ModularCurve.image_qExpFrobeniusPlaceModL_ssPlacesQExp_eq (ResidueField ↥A) p (XHDRLevel.ΓN p M H hpM)
  have hstab : SemilinearAut.IsNodeStable O.ssFinset frob := by
    intro s hs
    rw [O.mem_ssFinset_iff, ModularCurve.mem_ssNodePairsQExp_iff] at hs ⊢
    obtain ⟨h2, h1⟩ := hs
    refine ⟨?_, ?_⟩
    · show frob • s.2 ∈ _
      rw [← hΦ', ← himg]
      exact ⟨s.2, h2, rfl⟩
    · show frob • s.1 = qExpFrobeniusPlaceModL (ResidueField ↥A) (XHDRLevel.ΓN p M H hpM) p (frob • s.2)
      rw [h1, hΦ', hΦ']

  obtain ⟨ξ, hξ⟩ := AlgebraicCurve.GluedPic0.toPic0Pair_surjective O.ssFinset ((0 : Pic0 (ResidueField ↥A) (Fbar p M H hpM (ResidueField ↥A))), z)
  have hT2 := ModularCurve.JHNeronObjectAtP.ptsSp_symm_frobeniusTwist_eq_glueMap_of_pointReduction p M H hpM hpM2 hHp hj 𝔛 A hA ρ hρ Λ O hσA hsp
    frob hfrob hstab (frobenius (ResidueField ↥A) p) (fun a => frobenius_def p a) τF hτF (O.ptsSp ξ)
  rw [Equiv.symm_apply_apply] at hT2
  have htw : GoodReductionJacobian.schemeHomOverComp τF.1 τF.2 (O.ptsSp ξ) = O.ptsSp (GluedPic0.glueMap O.ssFinset frob hstab ξ) := by
    rw [← hT2, Equiv.apply_symm_apply]

  have h1 : fibreMap (O.abqFibre 1) (O.ptsSp ξ) = Λ.ptsSp z := by
    have h := O.abqFibre_ptsSp ξ 1
    simp only [Fin.isValue, one_ne_zero, ↓reduceIte, hξ] at h
    rw [← h, Equiv.apply_symm_apply]
  have h2 : fibreMap (O.abqFibre 1) (O.ptsSp (GluedPic0.glueMap O.ssFinset frob hstab ξ)) = Λ.ptsSp (frob • z) := by
    have h := O.abqFibre_ptsSp (GluedPic0.glueMap O.ssFinset frob hstab ξ) 1
    simp only [Fin.isValue, one_ne_zero, ↓reduceIte, GluedPic0.toPic0Pair_glueMap, hξ] at h
    rw [← h, Equiv.apply_symm_apply]

  have h3 : frob • z = F z := by
    obtain ⟨D, rfl⟩ := Pic0.mk_surjective z
    have hxT : ∃ x : qExpFunctionFieldC (ResidueField ↥A) (XHDRLevel.ΓN p M H hpM), Transcendental (ResidueField ↥A) x ∧
        FiniteDimensional (IntermediateField.adjoin (ResidueField ↥A) ({x} : Set (qExpFunctionFieldC (ResidueField ↥A) (XHDRLevel.ΓN p M H hpM)))) (qExpFunctionFieldC (ResidueField ↥A) (XHDRLevel.ΓN p M H hpM)) :=
      ⟨t, ht1, ht2⟩
    let Φ : Place (ResidueField ↥A) (Fbar p M H hpM (ResidueField ↥A)) ≃ Place (ResidueField ↥A) (Fbar p M H hpM (ResidueField ↥A)) :=
      Equiv.ofBijective _ (ModularCurve.qExpFrobeniusPlaceModL_bijective (ResidueField ↥A) p (XHDRLevel.ΓN p M H hpM))
    have h7 := ModularCurve.qExpFrobeniusPushforwardModL_mk_eq_mk_of_eq_mapDomain (ResidueField ↥A) p (XHDRLevel.ΓN p M H hpM) hxT F hF Φ (fun v => rfl)
      D (SemilinearAut.degZeroSMulHom frob D) (by
        rw [SemilinearAut.coe_degZeroSMulHom, SemilinearAut.divisor_smul_def]
        congr 1
        funext w
        exact (hΦ' w).symm)
    rw [SemilinearAut.pic0_smul_mk, h7]

  rw [← h3, ← h2, ← htw, O.abqFibre_twist τF 1 (O.ptsSp ξ), h1]

end S_ModularCurve_JHNeronObjectAtP_levelData_ptsSp_frobeniusPushforward_eq_schemeHomOverComp_frobenius_ptsSp_of_hsp
end P2MW
export P2MW.S_ModularCurve_JHNeronObjectAtP_levelData_ptsSp_frobeniusPushforward_eq_schemeHomOverComp_frobenius_ptsSp_of_hsp (solution)
