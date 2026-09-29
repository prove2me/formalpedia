-- Prove2me | solution 1 for ModularCurve.JHNeronObjectAtP.ptsSp_symm_schemeHomOverComp_hecke_dia_eq_glueMap
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:09.976215+00:00
-- url     : https://prove2.me/submissions/b62d5e94-22a5-5f0b-b792-ebf485cffe3f

import Mathlib
import Definitions.Def_ModularCurve_XHDRModelAtP
import Definitions.Def_ModularCurve_JHNeronObjectAtP
import Definitions.Def_AlgebraicCurve_GluedPic0Functoriality
import Theorems.Thm_AlgebraicGeometry_SchemeHomOver_eq_of_isSeparated_of_valuationRing_of_fst_eq
import Theorems.Thm_AlgebraicCurve_isCurveOver_of_ringEquiv_functionField_of_isIntegral_of_smoothOfRelativeDimension_one
import Theorems.Thm_AlgebraicCurve_Place_deg_eq_one_iff_surjective_algebraMap_residueField
import Theorems.Thm_AlgebraicCurve_GluedPic0_closure_setOf_mk_single_sub_single_eq_top
import Theorems.Thm_AlgebraicCurve_finite_compl_of_isOpen
import Theorems.Thm_AlgebraicCurve_Place_exists_forall_mem_hasValue
import Theorems.Thm_ModularCurve_XHDRModelAtP_exists_schemeHomOver_range_subset_smoothLocus_of_mem_smoothLocus
import Theorems.Thm_ModularCurve_XHDRModelAtP_exists_schemeHomOver_comp_dia_pointEquivPlace_eq_smul_placeOfPoint_eq_smul
import Theorems.Thm_ModularCurve_JHNeronObjectAtP_exists_addMonoidHom_apply_eq_ptsSp_symm_schemeHomOverComp_hecke
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_JHNeronObjectAtP_ptsSp_symm_schemeHomOverComp_hecke_dia_eq_glueMap
p2m_attr_erase "instance" "AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions"
p2m_attr_erase "simp" "AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal AlgebraicCurve.RationalFunctionField.placeInfty_toValuationSubring AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none"

set_option autoImplicit false

universe u v

p2m_open "CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian AlgebraicCurve P2MW.S_ModularCurve_JHNeronObjectAtP_ptsSp_symm_schemeHomOverComp_hecke_dia_eq_glueMap.AlgebraicCurve IsLocalRing ModularCurve ModularCurve.XHDRLevel ModularCurve.JZeroNeronObjectAtP"

open scoped MatrixGroups

namespace AlgebraicCurve p2m_export "AlgebraicCurve" "SemilinearAut SemilinearAut.ofAlgAut SemilinearAut.smul_single SemilinearAut.degZeroSMulHom SemilinearAut.coe_degZeroSMulHom SemilinearAut.pic0_smul_mk Place Divisor Divisor.degree_single Divisor.degZero Divisor.mem_degZero Pic0 Pic0.mk GluingData GluingData.admissible GluedPic0 GluedPic0.mk SemilinearAut.IsNodeStable SemilinearAut.gluingMap_apply SemilinearAut.admissibleMap SemilinearAut.coe_admissibleMap GluedPic0.glueMap GluedPic0.glueMap_mk IsCurveOver IsCurveOver.finiteResidue isCurveOver_of_ringEquiv_functionField_of_isIntegral_of_smoothOfRelativeDimension_one Place.deg_eq_one_iff_surjective_algebraMap_residueField GluedPic0.closure_setOf_mk_single_sub_single_eq_top finite_compl_of_isOpen Place.exists_forall_mem_hasValue" namespace GluedPic0 p2m_export "AlgebraicCurve.GluedPic0" "mk glueMap glueMap_mk closure_setOf_mk_single_sub_single_eq_top" end AlgebraicCurve.GluedPic0
p2m_open_scoped "AlgebraicCurve AlgebraicCurve.GluedPic0" in

theorem AlgebraicCurve.GluedPic0.hsdia_coe_admissibleMap_of_single_sub_single
    {K F : Type*} [Field K] [Field F] [Algebra K F]
    (S : Finset (Place K F × Place K F)) (g : SemilinearAut K F) (hstab : SemilinearAut.IsNodeStable S g)
    (i : Fin 2) (P Q P' Q' : Place K F) (hP : P' = g • P) (hQ : Q' = g • Q)
    (x : ↥(GluingData.admissible S))
    (hx₁ : (x : GluingData K F S).1 = (if i = 0 then Finsupp.single P 1 - Finsupp.single Q 1 else 0))
    (hx₂ : (x : GluingData K F S).2.1 = (if i = 1 then Finsupp.single P 1 - Finsupp.single Q 1 else 0))
    (hx₃ : (x : GluingData K F S).2.2 = 0) :
    ((SemilinearAut.admissibleMap S g hstab x : ↥(GluingData.admissible S)) : GluingData K F S).1 =
        (if i = 0 then Finsupp.single P' 1 - Finsupp.single Q' 1 else 0) ∧
      ((SemilinearAut.admissibleMap S g hstab x : ↥(GluingData.admissible S)) : GluingData K F S).2.1 =
        (if i = 1 then Finsupp.single P' 1 - Finsupp.single Q' 1 else 0) ∧
      ((SemilinearAut.admissibleMap S g hstab x : ↥(GluingData.admissible S)) : GluingData K F S).2.2 = 0 := by
  subst hP hQ
  refine ⟨?_, ?_, ?_⟩
  · rw [SemilinearAut.coe_admissibleMap, SemilinearAut.gluingMap_apply, hx₁]
    split_ifs
    · rw [smul_sub, SemilinearAut.smul_single, SemilinearAut.smul_single]
    · rw [smul_zero]
  · rw [SemilinearAut.coe_admissibleMap, SemilinearAut.gluingMap_apply]
    dsimp only
    rw [hx₂]
    split_ifs
    · rw [smul_sub, SemilinearAut.smul_single, SemilinearAut.smul_single]
    · rw [smul_zero]
  · rw [SemilinearAut.coe_admissibleMap, SemilinearAut.gluingMap_apply]
    dsimp only
    funext t
    simp [hx₃]

namespace AlgebraicCurve p2m_export "AlgebraicCurve" "SemilinearAut SemilinearAut.ofAlgAut SemilinearAut.smul_single SemilinearAut.degZeroSMulHom SemilinearAut.coe_degZeroSMulHom SemilinearAut.pic0_smul_mk Place Divisor Divisor.degree_single Divisor.degZero Divisor.mem_degZero Pic0 Pic0.mk GluingData GluingData.admissible GluedPic0 GluedPic0.mk SemilinearAut.IsNodeStable SemilinearAut.gluingMap_apply SemilinearAut.admissibleMap SemilinearAut.coe_admissibleMap GluedPic0.glueMap GluedPic0.glueMap_mk IsCurveOver IsCurveOver.finiteResidue isCurveOver_of_ringEquiv_functionField_of_isIntegral_of_smoothOfRelativeDimension_one Place.deg_eq_one_iff_surjective_algebraMap_residueField GluedPic0.closure_setOf_mk_single_sub_single_eq_top finite_compl_of_isOpen Place.exists_forall_mem_hasValue" namespace SemilinearAut p2m_export "AlgebraicCurve.SemilinearAut" "baseAut commutes ofAlgAut smul_single degZeroSMulHom coe_degZeroSMulHom pic0_smul_mk IsNodeStable gluingMap_apply admissibleMap coe_admissibleMap" end AlgebraicCurve.SemilinearAut
p2m_open_scoped "AlgebraicCurve AlgebraicCurve.SemilinearAut" in

theorem AlgebraicCurve.SemilinearAut.hsdia_coe_degZeroSMulHom_single_sub_single
    {K F : Type*} [Field K] [Field F] [Algebra K F] (g : SemilinearAut K F)
    (D : Divisor.degZero (K := K) (F := F)) (P Q P' Q' : Place K F) (hP : P' = g • P) (hQ : Q' = g • Q)
    (hD : (D : Divisor K F) = Finsupp.single P 1 - Finsupp.single Q 1) :
    ((SemilinearAut.degZeroSMulHom g D : Divisor.degZero (K := K) (F := F)) : Divisor K F) =
      Finsupp.single P' 1 - Finsupp.single Q' 1 := by
  subst hP hQ
  rw [SemilinearAut.coe_degZeroSMulHom, hD, smul_sub, SemilinearAut.smul_single, SemilinearAut.smul_single]

open ModularCurve.JHNeronObjectAtP

set_option maxHeartbeats 6400000
set_option synthInstance.maxHeartbeats 1600000

theorem solution
    (p M : ℕ) [Fact p.Prime] [NeZero M] (H : Subgroup (ZMod M)ˣ) (hpM : p ∣ M) [NeZero (M / p)]
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

    (hdia0 : ∀ (e : (ZMod (M / p))ˣ) (P : closedPoints (𝔛.Mfib A hA ρ hρ).C),
      ∃ h : (inv (𝔛.efib A hA ρ hρ)).base
          ((fibreMap (overOfIso (𝔛.dia0 e) (𝔛.dia0_over e)) ((IsLocalRing.residue ↥A).comp ρ)).base
            ((𝔛.efib A hA ρ hρ).base P.1)) ∈ closedPoints (𝔛.Mfib A hA ρ hρ).C,
        (𝔛.Mfib A hA ρ hρ).placeOfPoint ⟨_, h⟩ =
          SemilinearAut.ofAlgAut (diamondActionModL (ResidueField ↥A) (M / p) (infSubgroup p M H hpM)
            (CuspForm.gammaLift (M / p) e)) • (𝔛.Mfib A hA ρ hρ).placeOfPoint P)
    (S : Set ℕ) (d : (ZMod M)ˣ)
    (hstab : SemilinearAut.IsNodeStable O.ssFinset
      (SemilinearAut.ofAlgAut (diamondActionModL (ResidueField ↥A) (M / p) (infSubgroup p M H hpM)
        (CuspForm.gammaLift (M / p) (ZMod.unitsMap (Nat.div_dvd_of_dvd hpM) d))))) :
    ∀ ξ : GluedPic0 (ResidueField ↥A) (Fbar p M H hpM (ResidueField ↥A)) O.ssFinset,
      O.ptsSp.symm (schemeHomOverComp (O.ptsSp ξ) (O.hecke S (CohCarrier.Gen.dia d))) =
        GluedPic0.glueMap O.ssFinset
          (SemilinearAut.ofAlgAut (diamondActionModL (ResidueField ↥A) (M / p) (infSubgroup p M H hpM)
            (CuspForm.gammaLift (M / p) (ZMod.unitsMap (Nat.div_dvd_of_dvd hpM) d)))) hstab ξ := by

  have hA0 := ModularCurve.JHNeronObjectAtP.exists_addMonoidHom_apply_eq_ptsSp_symm_schemeHomOverComp_hecke
    p M H hpM A hA Λ O S (CohCarrier.Gen.dia d)
  obtain ⟨Φ, hΦ⟩ := hA0

  haveI hCO : IsCurveOver (ResidueField ↥A) (Fbar p M H hpM (ResidueField ↥A)) :=
    AlgebraicCurve.isCurveOver_of_ringEquiv_functionField_of_isIntegral_of_smoothOfRelativeDimension_one
      (𝔛.Mfib A hA ρ hρ).toBase (𝔛.Mfib A hA ρ hρ).ffEquiv (𝔛.Mfib A hA ρ hρ).ffEquiv_algebraMap
  haveI hCOgen : IsCurveOver (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H) :=
    AlgebraicCurve.isCurveOver_of_ringEquiv_functionField_of_isIntegral_of_smoothOfRelativeDimension_one
      𝔛.Meta.toBase 𝔛.Meta.ffEquiv 𝔛.Meta.ffEquiv_algebraMap
  have hrat : ∀ v : Place (ResidueField ↥A) (Fbar p M H hpM (ResidueField ↥A)), Function.Surjective (algebraMap (ResidueField ↥A) v.ResidueField) := by
    intro v
    haveI := IsCurveOver.finiteResidue (K := (ResidueField ↥A)) (F := (Fbar p M H hpM (ResidueField ↥A))) v
    exact IsAlgClosed.algebraMap_bijective_of_isIntegral.2
  have hdeg1 : ∀ v : Place (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H), v.deg = 1 := by
    intro v
    haveI := IsCurveOver.finiteResidue (K := AlgebraicClosure ℚ) (F := ↥(xHFunctionFieldBar M H)) v
    exact (AlgebraicCurve.Place.deg_eq_one_iff_surjective_algebraMap_residueField v).mpr
      IsAlgClosed.algebraMap_bijective_of_isIntegral.2

  have hS : Set.InjOn Prod.snd (O.ssFinset : Set (Place (ResidueField ↥A) (Fbar p M H hpM (ResidueField ↥A)) × Place (ResidueField ↥A) (Fbar p M H hpM (ResidueField ↥A)))) := by
    intro a ha b hb hab
    have ha' := ((O.mem_ssFinset_iff a).mp ha)
    have hb' := ((O.mem_ssFinset_iff b).mp hb)
    rw [mem_ssNodePairsQExp_iff] at ha' hb'
    refine Prod.ext ?_ hab
    rw [ha'.2, hb'.2]
    exact congrArg _ hab

  have hne : ∀ i : Fin 2,
      (((((𝔛.efib A hA ρ hρ) ≫ 𝔛.comp A hA ρ hρ i ≫ pullback.fst (toBase p (ΓM M H) hj) (Spec.map (CommRingCat.ofHom ((IsLocalRing.residue ↥A).comp ρ)))) ⁻¹ᵁ
        𝔛.smoothLocus : (𝔛.Mfib A hA ρ hρ).C.Opens) : Set (𝔛.Mfib A hA ρ hρ).C)).Nonempty := by

    have key : ∀ (i : Fin 2) (ε : SchemeHomOver (𝟙 (Spec (CommRingCat.of (R p)))) (toBase p (ΓM M H) hj)),
        Set.range ε.1.base ⊆ (𝔛.smoothLocus : Set (X p (ΓM M H) hj)) →
        Set.range (sectionFibre ε ((IsLocalRing.residue ↥A).comp ρ)).base ⊆ Set.range (𝔛.comp A hA ρ hρ i).base →
        (((((𝔛.efib A hA ρ hρ) ≫ 𝔛.comp A hA ρ hρ i ≫ pullback.fst (toBase p (ΓM M H) hj) (Spec.map (CommRingCat.ofHom ((IsLocalRing.residue ↥A).comp ρ)))) ⁻¹ᵁ
          𝔛.smoothLocus : (𝔛.Mfib A hA ρ hρ).C.Opens) : Set (𝔛.Mfib A hA ρ hρ).C)).Nonempty := by
      intro i ε hsm hcomp
      obtain ⟨w, hw⟩ := hcomp ⟨IsLocalRing.closedPoint (ResidueField ↥A), rfl⟩
      refine ⟨(inv (𝔛.efib A hA ρ hρ)).base w, ?_⟩
      show ((𝔛.efib A hA ρ hρ) ≫ 𝔛.comp A hA ρ hρ i ≫ pullback.fst (toBase p (ΓM M H) hj) (Spec.map (CommRingCat.ofHom ((IsLocalRing.residue ↥A).comp ρ)))).base
        ((inv (𝔛.efib A hA ρ hρ)).base w) ∈ (𝔛.smoothLocus : Set (X p (ΓM M H) hj))
      have h1 : (𝔛.efib A hA ρ hρ).base ((inv (𝔛.efib A hA ρ hρ)).base w) = w := by
        rw [← Scheme.Hom.comp_apply, IsIso.inv_hom_id]
        rfl
      rw [Scheme.Hom.comp_apply, Scheme.Hom.comp_apply, h1, hw, ← Scheme.Hom.comp_apply, sectionFibre, pullback.lift_fst,
        Scheme.Hom.comp_apply]
      exact hsm ⟨_, rfl⟩
    intro i
    fin_cases i
    · exact key 0 𝔛.εinf (𝔛.εinf_mem_smoothLocus) (𝔛.εinf_mem_comp0 A hA ρ hρ)
    · exact key 1 𝔛.εzero (𝔛.εzero_mem_smoothLocus) (𝔛.εzero_mem_comp1 A hA ρ hρ)
  have hfin : ∀ i : Fin 2, {x : closedPoints (𝔛.Mfib A hA ρ hρ).C |
      x.1 ∉ (((𝔛.efib A hA ρ hρ) ≫ 𝔛.comp A hA ρ hρ i ≫ pullback.fst (toBase p (ΓM M H) hj) (Spec.map (CommRingCat.ofHom ((IsLocalRing.residue ↥A).comp ρ)))) ⁻¹ᵁ
        𝔛.smoothLocus : (𝔛.Mfib A hA ρ hρ).C.Opens)}.Finite := fun i =>
    (AlgebraicCurve.finite_compl_of_isOpen (𝔛.Mfib A hA ρ hρ).toBase _ (hne i)).preimage Subtype.val_injective.injOn

  have hA67 : AddSubgroup.closure {ξ | ∃ (i : Fin 2)
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
        ξ = GluedPic0.mk O.ssFinset x} = ⊤ := by
    classical
    have hgen := AlgebraicCurve.GluedPic0.closure_setOf_mk_single_sub_single_eq_top O.ssFinset hS hrat
      (AlgebraicCurve.Place.exists_forall_mem_hasValue)
      ((hfin 0).toFinset.image (fun x => (𝔛.Mfib A hA ρ hρ).placeOfPoint x))
      ((hfin 1).toFinset.image (fun x => (𝔛.Mfib A hA ρ hρ).placeOfPoint x))
    rw [eq_top_iff, ← hgen]
    refine AddSubgroup.closure_mono ?_
    rintro ξ ⟨i, Ppl, Qpl, x, hPT, hQT, hx₁, hx₂, hx₃, rfl⟩

    obtain ⟨P₁, rfl⟩ := (𝔛.Mfib A hA ρ hρ).placeOfPoint_bijective.2 Ppl
    obtain ⟨P₂, rfl⟩ := (𝔛.Mfib A hA ρ hρ).placeOfPoint_bijective.2 Qpl

    have hmemU : ∀ (P : closedPoints (𝔛.Mfib A hA ρ hρ).C),
        (𝔛.Mfib A hA ρ hρ).placeOfPoint P ∉ (if i = 0 then (hfin 0).toFinset.image (fun x => (𝔛.Mfib A hA ρ hρ).placeOfPoint x)
          else (hfin 1).toFinset.image (fun x => (𝔛.Mfib A hA ρ hρ).placeOfPoint x)) →
        (pullback.fst (toBase p (ΓM M H) hj) (Spec.map (CommRingCat.ofHom ((IsLocalRing.residue ↥A).comp ρ)))).base
          (((𝔛.efib A hA ρ hρ) ≫ 𝔛.comp A hA ρ hρ i).base P.1) ∈ (𝔛.smoothLocus : Set (X p (ΓM M H) hj)) := by
      intro P hP
      have hP' : (𝔛.Mfib A hA ρ hρ).placeOfPoint P ∉ (hfin i).toFinset.image (fun x => (𝔛.Mfib A hA ρ hρ).placeOfPoint x) := by
        fin_cases i <;> simpa using hP
      by_contra hcon
      apply hP'
      refine Finset.mem_image.mpr ⟨P, ?_, rfl⟩
      rw [Set.Finite.mem_toFinset]
      show P.1 ∉ _
      intro hin
      apply hcon
      rw [← Scheme.Hom.comp_apply, Category.assoc]
      exact hin
    have hL₁ := ModularCurve.XHDRModelAtP.exists_schemeHomOver_range_subset_smoothLocus_of_mem_smoothLocus
      p M H hpM hj 𝔛 A hA ρ hρ i P₁ (hmemU P₁ hPT)
    have hL₂ := ModularCurve.XHDRModelAtP.exists_schemeHomOver_range_subset_smoothLocus_of_mem_smoothLocus
      p M H hpM hj 𝔛 A hA ρ hρ i P₂ (hmemU P₂ hQT)
    obtain ⟨y₁, u₁, hu₁, hu₁sm, uκ₁, huκ₁₁, huκ₁₂, hP₁⟩ := hL₁
    obtain ⟨y₂, u₂, hu₂, hu₂sm, uκ₂, huκ₂₁, huκ₂₂, hP₂⟩ := hL₂

    have hDvmem : (Finsupp.single (𝔛.Meta.pointEquivPlace y₁) 1 - Finsupp.single (𝔛.Meta.pointEquivPlace y₂) 1 :
        Divisor (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H)) ∈ Divisor.degZero (K := AlgebraicClosure ℚ) (F := ↥(xHFunctionFieldBar M H)) := by
      rw [Divisor.mem_degZero, map_sub, Divisor.degree_single, Divisor.degree_single, hdeg1, hdeg1, sub_self]
    refine ⟨i, y₁, u₁, hu₁, hu₁sm, uκ₁, huκ₁₁, huκ₁₂, P₁, hP₁, y₂, u₂, hu₂, hu₂sm, uκ₂, huκ₂₁, huκ₂₂, P₂, hP₂,
      ⟨_, hDvmem⟩, rfl, x, ?_, ?_, hx₃, rfl⟩
    · rw [hx₁]
    · rw [hx₂]

  have hagree : Set.EqOn Φ (GluedPic0.glueMap O.ssFinset (SemilinearAut.ofAlgAut (diamondActionModL (ResidueField ↥A) (M / p) (infSubgroup p M H hpM)
            (CuspForm.gammaLift (M / p) (ZMod.unitsMap (Nat.div_dvd_of_dvd hpM) d)))) hstab)
      {ξ | ∃ (i : Fin 2)
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
        ξ = GluedPic0.mk O.ssFinset x} := by
    rintro ξ ⟨i, y₁, u₁, hu₁, hu₁sm, uκ₁, huκ₁₁, huκ₁₂, P₁, hP₁, y₂, u₂, hu₂, hu₂sm, uκ₂, huκ₂₁, huκ₂₂, P₂, hP₂, Dv, hDv,
      x, hx₁, hx₂, hx₃, rfl⟩
    have hS0 := hsp i y₁ u₁ hu₁ hu₁sm uκ₁ huκ₁₁ huκ₁₂ P₁ hP₁ y₂ u₂ hu₂ hu₂sm uκ₂ huκ₂₁ huκ₂₂ P₂ hP₂ Dv hDv x hx₁ hx₂ hx₃
    obtain ⟨s, hs, hsx⟩ := hS0

    have hA2 : (O.pts ((SemilinearAut.ofAlgAut (diamondAutHBar M H d)) • Pic0.mk Dv)).1 =
        (O.pts (Pic0.mk Dv)).1 ≫ (O.hecke S (CohCarrier.Gen.dia d)).1 :=
      O.hecke_pts S (CohCarrier.Gen.dia d) (Pic0.mk Dv)

    have hA1 : NeronModelInfra.schemeHomOverComp (O.ptsSp (GluedPic0.mk O.ssFinset x)) (O.hecke S (CohCarrier.Gen.dia d)) =
        NeronModelInfra.schemeHomOverComp ⟨resPt A, rfl⟩
          (NeronModelInfra.schemeHomOverComp s (O.hecke S (CohCarrier.Gen.dia d))) := by
      rw [Equiv.symm_apply_eq] at hsx
      rw [← hsx]
      exact (NeronModelInfra.schemeHomOverComp_assoc _ _ _).symm

    have h₁ := ModularCurve.XHDRModelAtP.exists_schemeHomOver_comp_dia_pointEquivPlace_eq_smul_placeOfPoint_eq_smul
      p M H hpM hj 𝔛 A hA ρ hρ hdia0 d i y₁ u₁ hu₁ hu₁sm uκ₁ huκ₁₁ huκ₁₂ P₁ hP₁
    have h₂ := ModularCurve.XHDRModelAtP.exists_schemeHomOver_comp_dia_pointEquivPlace_eq_smul_placeOfPoint_eq_smul
      p M H hpM hj 𝔛 A hA ρ hρ hdia0 d i y₂ u₂ hu₂ hu₂sm uκ₂ huκ₂₁ huκ₂₂ P₂ hP₂
    obtain ⟨y₁', u₁', hu₁', hu₁'val, hu₁'sm, hy₁'pl, uκ₁', huκ₁'₁, huκ₁'₂, huκ₁'val, P₁', hP₁', hP₁'pl⟩ := h₁
    obtain ⟨y₂', u₂', hu₂', hu₂'val, hu₂'sm, hy₂'pl, uκ₂', huκ₂'₁, huκ₂'₂, huκ₂'val, P₂', hP₂', hP₂'pl⟩ := h₂

    have hDv' : ((SemilinearAut.degZeroSMulHom (SemilinearAut.ofAlgAut (diamondAutHBar M H d)) Dv :
          Divisor.degZero (K := AlgebraicClosure ℚ) (F := ↥(xHFunctionFieldBar M H))) :
          Divisor (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H)) =
        Finsupp.single (𝔛.Meta.pointEquivPlace y₁') 1 - Finsupp.single (𝔛.Meta.pointEquivPlace y₂') 1 := by
      exact AlgebraicCurve.SemilinearAut.hsdia_coe_degZeroSMulHom_single_sub_single _ Dv _ _ _ _ hy₁'pl hy₂'pl hDv

    have hx' := AlgebraicCurve.GluedPic0.hsdia_coe_admissibleMap_of_single_sub_single O.ssFinset (SemilinearAut.ofAlgAut (diamondActionModL (ResidueField ↥A) (M / p) (infSubgroup p M H hpM)
            (CuspForm.gammaLift (M / p) (ZMod.unitsMap (Nat.div_dvd_of_dvd hpM) d)))) hstab i
      ((𝔛.Mfib A hA ρ hρ).placeOfPoint P₁) ((𝔛.Mfib A hA ρ hρ).placeOfPoint P₂) ((𝔛.Mfib A hA ρ hρ).placeOfPoint P₁') ((𝔛.Mfib A hA ρ hρ).placeOfPoint P₂')
      hP₁'pl hP₂'pl x hx₁ hx₂ hx₃
    obtain ⟨hx'₁, hx'₂, hx'₃⟩ := hx'

    have hS1 := hsp i y₁' u₁' hu₁' hu₁'sm uκ₁' huκ₁'₁ huκ₁'₂ P₁' hP₁' y₂' u₂' hu₂' hu₂'sm uκ₂' huκ₂'₁ huκ₂'₂ P₂' hP₂'
      (SemilinearAut.degZeroSMulHom (SemilinearAut.ofAlgAut (diamondAutHBar M H d)) Dv) hDv' _ hx'₁ hx'₂ hx'₃
    obtain ⟨s', hs', hs'x⟩ := hS1

    haveI : IsSeparated O.g := O.separated
    letI : Algebra (R p) ↥A := ρ.toAlgebra
    have hgen_eq : Spec.map (CommRingCat.ofHom (algebraMap ↥A (AlgebraicClosure ℚ))) ≫ s'.1 =
        Spec.map (CommRingCat.ofHom (algebraMap ↥A (AlgebraicClosure ℚ))) ≫
          (NeronModelInfra.schemeHomOverComp s (O.hecke S (CohCarrier.Gen.dia d))).1 := by
      show barPt A ≫ s'.1 = barPt A ≫ s.1 ≫ (O.hecke S (CohCarrier.Gen.dia d)).1
      rw [← hs', ← Category.assoc, ← hs, ← hA2, SemilinearAut.pic0_smul_mk]
    have hA8 := @AlgebraicGeometry.SchemeHomOver.eq_of_isSeparated_of_valuationRing_of_fst_eq (R p) _ O.G O.g _ ↥A _ _ _ _
      (AlgebraicClosure ℚ) _ _ _ _ (IsScalarTower.of_algebraMap_eq' hρ.symm)
      ⟨s'.1, s'.2.trans hσA⟩ ⟨(NeronModelInfra.schemeHomOverComp s (O.hecke S (CohCarrier.Gen.dia d))).1,
        (NeronModelInfra.schemeHomOverComp s (O.hecke S (CohCarrier.Gen.dia d))).2.trans hσA⟩ hgen_eq
    have hA8' : NeronModelInfra.schemeHomOverComp ⟨resPt A, rfl⟩ s' =
        NeronModelInfra.schemeHomOverComp ⟨resPt A, rfl⟩
          (NeronModelInfra.schemeHomOverComp s (O.hecke S (CohCarrier.Gen.dia d))) :=
      Subtype.ext (congrArg (fun t : SchemeHomOver (Spec.map (CommRingCat.ofHom (algebraMap (R p) ↥A))) O.g => resPt A ≫ t.1) hA8)

    have hA4 : Φ (GluedPic0.mk O.ssFinset x) = GluedPic0.mk O.ssFinset (SemilinearAut.admissibleMap O.ssFinset (SemilinearAut.ofAlgAut (diamondActionModL (ResidueField ↥A) (M / p) (infSubgroup p M H hpM)
            (CuspForm.gammaLift (M / p) (ZMod.unitsMap (Nat.div_dvd_of_dvd hpM) d)))) hstab x) :=
      (hΦ _).trans <| (congrArg O.ptsSp.symm hA1).trans <| (congrArg O.ptsSp.symm hA8').symm.trans hs'x
    exact hA4.trans (GluedPic0.glueMap_mk O.ssFinset _ hstab x).symm

  intro ξ
  rw [← hΦ ξ]
  exact DFunLike.congr_fun (AddMonoidHom.eq_of_eqOn_dense hA67 hagree) ξ

#print axioms solution

end S_ModularCurve_JHNeronObjectAtP_ptsSp_symm_schemeHomOverComp_hecke_dia_eq_glueMap
end P2MW
export P2MW.S_ModularCurve_JHNeronObjectAtP_ptsSp_symm_schemeHomOverComp_hecke_dia_eq_glueMap (solution)
