-- Prove2me | solution 1 for ModularCurve.JHNeronObjectAtP.ptsSp_symm_hecke_U_add_crossMap_eq_ptsSp_symm_degeneracyHom_degPull
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:09.976215+00:00
-- url     : https://prove2.me/submissions/523ae733-1dfd-5903-8f6e-f88d6bd413b9

import Mathlib
import Definitions.Def_ModularCurve_XHDRModelAtP
import Definitions.Def_ModularCurve_JHNeronObjectAtP
import Definitions.Def_AlgebraicCurve_GluedPic0Functoriality
import Definitions.Def_AlgebraicCurve_GluedPic0SliceOps
import Definitions.Def_AlgebraicCurve_GluedPic0CrossFunctionality
import Theorems.Thm_ModularCurve_JHNeronObjectAtP_exists_addMonoidHom_apply_eq_ptsSp_symm_schemeHomOverComp_hecke
import Theorems.Thm_AlgebraicCurve_isCurveOver_of_ringEquiv_functionField_of_isIntegral_of_smoothOfRelativeDimension_one
import Theorems.Thm_AlgebraicCurve_Place_deg_eq_one_iff_surjective_algebraMap_residueField
import Theorems.Thm_AlgebraicCurve_GluedPic0_closure_setOf_mk_single_sub_single_eq_top
import Theorems.Thm_AlgebraicCurve_finite_compl_of_isOpen
import Theorems.Thm_AlgebraicCurve_Place_exists_forall_mem_hasValue
import Theorems.Thm_ModularCurve_XHDRModelAtP_exists_schemeHomOver_range_subset_smoothLocus_of_mem_smoothLocus
import Theorems.Thm_AlgebraicGeometry_SchemeHomOver_eq_of_isSeparated_of_valuationRing_of_fst_eq
import Theorems.Thm_ModularCurve_XHDRModelAtP_exists_schemeHomOver_comp_w_inv_pointEquivPlace_eq_smul_placeOfPoint_eq
import Theorems.Thm_ModularCurve_XHDRModelAtP_smul_frob_mem_ssPlacesQExp_and_frob_smul_frob_eq_of_mem_ssPlacesQExp
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_JHNeronObjectAtP_ptsSp_symm_hecke_U_add_crossMap_eq_ptsSp_symm_degeneracyHom_degPull
p2m_attr_erase "instance" "AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions"
p2m_attr_erase "simp" "AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal AlgebraicCurve.RationalFunctionField.placeInfty_toValuationSubring AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none"

set_option autoImplicit false

p2m_open "CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian AlgebraicCurve P2MW.S_ModularCurve_JHNeronObjectAtP_ptsSp_symm_hecke_U_add_crossMap_eq_ptsSp_symm_degeneracyHom_degPull.AlgebraicCurve IsLocalRing ModularCurve P2MW.S_ModularCurve_JHNeronObjectAtP_ptsSp_symm_hecke_U_add_crossMap_eq_ptsSp_symm_degeneracyHom_degPull.ModularCurve ModularCurve.XHDRLevel ModularCurve.JZeroNeronObjectAtP"

open scoped MatrixGroups

open _root_.ModularCurve.JHNeronObjectAtP (Fbar)

universe u v

namespace ModularCurve p2m_export "ModularCurve" "XHDRLevel.ΓN XHDRModelAtP diamondActionModL infSubgroup mem_ssNodePairsQExp_iff xHFunctionFieldBar JH qExpFunctionFieldC qExpFrobeniusPushforwardModL jqModC genOpH JHNeronObjectAtP.LevelData JHNeronObjectAtP JZeroNeronObjectAtP JHNeronObjectAtP.exists_addMonoidHom_apply_eq_ptsSp_symm_schemeHomOverComp_hecke XHDRModelAtP.exists_schemeHomOver_range_subset_smoothLocus_of_mem_smoothLocus XHDRModelAtP.exists_schemeHomOver_comp_w_inv_pointEquivPlace_eq_smul_placeOfPoint_eq XHDRModelAtP.smul_frob_mem_ssPlacesQExp_and_frob_smul_frob_eq_of_mem_ssPlacesQExp" namespace JHNeronObjectAtP p2m_export "ModularCurve.JHNeronObjectAtP" "ΓN Fbar LevelData ptsSp abqFibre_ptsSp ssFinset degeneracyHom_mul mk pts hecke g hecke_pts pts_add degeneracyHom_pts separated degeneracyHom_special degPts degeneracyHom G smooth ptsSp_add mem_ssFinset_iff L exists_addMonoidHom_apply_eq_ptsSp_symm_schemeHomOverComp_hecke" end ModularCurve.JHNeronObjectAtP
p2m_open_scoped "ModularCurve ModularCurve.JHNeronObjectAtP" in

theorem ModularCurve.JHNeronObjectAtP.ptsSp_symm_eq_add_of_pts_add
    (p M : ℕ) [Fact p.Prime] [NeZero M] (H : Subgroup (ZMod M)ˣ) (hpM : p ∣ M)
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime p)
    [CharP (ResidueField ↥A) p] [IsAlgClosed (ResidueField ↥A)]
    (Λ : JHNeronObjectAtP.LevelData p M H hpM A) (O : JHNeronObjectAtP p M H hpM A hA Λ)
    (ρ : baseRing p →+* ↥A) (hρ : A.subtype.comp ρ = algebraMap (baseRing p) (AlgebraicClosure ℚ))
    (hσA : Λ.σA = Spec.map (CommRingCat.ofHom ρ))
    (X Y Z : SchemeHomOver Λ.σA O.g) (zX zY : JH M H)
    (hX : (O.pts zX).1 = barPt A ≫ X.1) (hY : (O.pts zY).1 = barPt A ≫ Y.1)
    (hZ : (O.pts (zX + zY)).1 = barPt A ≫ Z.1) :
    O.ptsSp.symm (NeronModelInfra.schemeHomOverComp ⟨resPt A, rfl⟩ Z) =
      O.ptsSp.symm (NeronModelInfra.schemeHomOverComp ⟨resPt A, rfl⟩ X) +
        O.ptsSp.symm (NeronModelInfra.schemeHomOverComp ⟨resPt A, rfl⟩ Y) := by

  have R1 : ∀ U V : SchemeHomOver (resPt A ≫ Λ.σA) O.g,
      O.ptsSp.symm (O.L.mul _ U V) = O.ptsSp.symm U + O.ptsSp.symm V := by
    intro U V
    apply O.ptsSp.injective
    rw [Equiv.apply_symm_apply, O.ptsSp_add, Equiv.apply_symm_apply, Equiv.apply_symm_apply]

    apply Subtype.ext
    simp only [toFibrePt, ofFibrePt, RelativeGroupLaw.baseChange_mul, RelativeGroupLaw.baseChangePointToBase_ofBase]
    have hn := congrArg Subtype.val (O.L.mul_natural (resPt A ≫ Λ.σA) (𝟙 _ ≫ resPt A ≫ Λ.σA) (𝟙 _) rfl U V)
    rw [GoodReductionJacobian.schemeHomOverComp_coe, Category.id_comp] at hn
    rw [hn]
    have hU : GoodReductionJacobian.schemeHomOverComp (𝟙 _) rfl U = overId U := Subtype.ext (Category.id_comp _)
    have hV : GoodReductionJacobian.schemeHomOverComp (𝟙 _) rfl V = overId V := Subtype.ext (Category.id_comp _)
    rw [hU, hV]

  haveI : IsSeparated O.g := O.separated
  letI : Algebra (baseRing p) ↥A := ρ.toAlgebra
  have hgen : Spec.map (CommRingCat.ofHom (algebraMap ↥A (AlgebraicClosure ℚ))) ≫ Z.1 =
      Spec.map (CommRingCat.ofHom (algebraMap ↥A (AlgebraicClosure ℚ))) ≫ (O.L.mul Λ.σA X Y).1 := by
    show barPt A ≫ Z.1 = barPt A ≫ (O.L.mul Λ.σA X Y).1
    have hn := congrArg Subtype.val (O.L.mul_natural Λ.σA (genPt p) (barPt A) Λ.hσA X Y)
    rw [GoodReductionJacobian.schemeHomOverComp_coe] at hn
    have hX' : O.pts zX = GoodReductionJacobian.schemeHomOverComp (barPt A) Λ.hσA X := Subtype.ext hX
    have hY' : O.pts zY = GoodReductionJacobian.schemeHomOverComp (barPt A) Λ.hσA Y := Subtype.ext hY
    rw [← hZ, O.pts_add, hX', hY']
    exact hn.symm
  have hZeq := @AlgebraicGeometry.SchemeHomOver.eq_of_isSeparated_of_valuationRing_of_fst_eq (baseRing p) _ O.G O.g _ ↥A _ _ _ _
    (AlgebraicClosure ℚ) _ _ _ _ (IsScalarTower.of_algebraMap_eq' hρ.symm)
    ⟨Z.1, Z.2.trans hσA⟩ ⟨(O.L.mul Λ.σA X Y).1, (O.L.mul Λ.σA X Y).2.trans hσA⟩ hgen
  have hZ1 : Z.1 = (O.L.mul Λ.σA X Y).1 := by
    have h := congrArg Subtype.val hZeq
    exact h

  have hsp : NeronModelInfra.schemeHomOverComp ⟨resPt A, rfl⟩ Z =
      O.L.mul _ (NeronModelInfra.schemeHomOverComp ⟨resPt A, rfl⟩ X) (NeronModelInfra.schemeHomOverComp ⟨resPt A, rfl⟩ Y) := by
    have hn := O.L.mul_natural Λ.σA (resPt A ≫ Λ.σA) (resPt A) rfl X Y
    have e1 : GoodReductionJacobian.schemeHomOverComp (resPt A) rfl X = NeronModelInfra.schemeHomOverComp ⟨resPt A, rfl⟩ X :=
      Subtype.ext rfl
    have e2 : GoodReductionJacobian.schemeHomOverComp (resPt A) rfl Y = NeronModelInfra.schemeHomOverComp ⟨resPt A, rfl⟩ Y :=
      Subtype.ext rfl
    rw [e1, e2] at hn
    rw [← hn]
    apply Subtype.ext
    show resPt A ≫ Z.1 = resPt A ≫ (O.L.mul Λ.σA X Y).1
    rw [hZ1]
  rw [hsp, R1]

namespace AlgebraicCurve p2m_export "AlgebraicCurve" "SemilinearAut SemilinearAut.baseAut SemilinearAut.ofAlgAut SemilinearAut.smul_single SemilinearAut.degZeroSMulHom SemilinearAut.coe_degZeroSMulHom SemilinearAut.pic0_smul_mk Place Divisor Divisor.degree_single Divisor.degZero Divisor.mem_degZero Pic Pic0 Pic0.mk GluingData GluingData.admissible GluingData.mem_admissible GluedPic0 GluedPic0.mk GluedPic0.toPic0Pair GluedPic0.toPic0Pair_mk SemilinearAut.baseAutUnitsHom IsCurveOver IsCurveOver.finiteResidue SemilinearAut.IsCrossStable SemilinearAut.crossGluingMap_apply SemilinearAut.coe_crossAdmissibleMap GluedPic0.crossMap GluedPic0.crossMap_mk isCurveOver_of_ringEquiv_functionField_of_isIntegral_of_smoothOfRelativeDimension_one Place.deg_eq_one_iff_surjective_algebraMap_residueField GluedPic0.closure_setOf_mk_single_sub_single_eq_top finite_compl_of_isOpen Place.exists_forall_mem_hasValue" namespace SemilinearAut p2m_export "AlgebraicCurve.SemilinearAut" "baseAut ofAlgAut smul_single degZeroSMulHom coe_degZeroSMulHom pic0_smul_mk baseAutUnitsHom IsCrossStable crossGluingMap_apply coe_crossAdmissibleMap" end AlgebraicCurve.SemilinearAut
p2m_open_scoped "AlgebraicCurve AlgebraicCurve.SemilinearAut" in

theorem AlgebraicCurve.SemilinearAut.hsup_coe_degZeroSMulHom_single_sub_single
    {K F : Type*} [Field K] [Field F] [Algebra K F] (g : SemilinearAut K F)
    (D : Divisor.degZero (K := K) (F := F)) (P Q P' Q' : Place K F) (hP : P' = g • P) (hQ : Q' = g • Q)
    (hD : (D : Divisor K F) = Finsupp.single P 1 - Finsupp.single Q 1) :
    ((SemilinearAut.degZeroSMulHom g D : Divisor.degZero (K := K) (F := F)) : Divisor K F) =
      Finsupp.single P' 1 - Finsupp.single Q' 1 := by
  subst hP hQ
  rw [SemilinearAut.coe_degZeroSMulHom, hD, smul_sub, SemilinearAut.smul_single, SemilinearAut.smul_single]

namespace AlgebraicCurve p2m_export "AlgebraicCurve" "SemilinearAut SemilinearAut.baseAut SemilinearAut.ofAlgAut SemilinearAut.smul_single SemilinearAut.degZeroSMulHom SemilinearAut.coe_degZeroSMulHom SemilinearAut.pic0_smul_mk Place Divisor Divisor.degree_single Divisor.degZero Divisor.mem_degZero Pic Pic0 Pic0.mk GluingData GluingData.admissible GluingData.mem_admissible GluedPic0 GluedPic0.mk GluedPic0.toPic0Pair GluedPic0.toPic0Pair_mk SemilinearAut.baseAutUnitsHom IsCurveOver IsCurveOver.finiteResidue SemilinearAut.IsCrossStable SemilinearAut.crossGluingMap_apply SemilinearAut.coe_crossAdmissibleMap GluedPic0.crossMap GluedPic0.crossMap_mk isCurveOver_of_ringEquiv_functionField_of_isIntegral_of_smoothOfRelativeDimension_one Place.deg_eq_one_iff_surjective_algebraMap_residueField GluedPic0.closure_setOf_mk_single_sub_single_eq_top finite_compl_of_isOpen Place.exists_forall_mem_hasValue" namespace Divisor p2m_export "AlgebraicCurve.Divisor" "degree degree_single degZero mem_degZero smul_single pullback" end AlgebraicCurve.Divisor
p2m_open_scoped "AlgebraicCurve AlgebraicCurve.Divisor" in

theorem AlgebraicCurve.Divisor.hsup_single_sub_single_mem_degZero_and_apply
    {K F : Type*} [Field K] [Field F] [Algebra K F] (hdeg : ∀ v : Place K F, v.deg = 1) (P Q : Place K F) :
    (Finsupp.single P 1 - Finsupp.single Q 1 : Divisor K F) ∈ Divisor.degZero (K := K) (F := F) ∧
      ∀ w : Place K F, P ≠ w → Q ≠ w → (Finsupp.single P 1 - Finsupp.single Q 1 : Divisor K F) w = 0 := by
  refine ⟨?_, fun w hP hQ => ?_⟩
  · rw [Divisor.mem_degZero, map_sub, Divisor.degree_single, Divisor.degree_single, hdeg, hdeg, sub_self]
  · classical
    rw [Finsupp.sub_apply, Finsupp.single_apply, Finsupp.single_apply, if_neg hP, if_neg hQ, sub_zero]

p2m_open_scoped "ModularCurve ModularCurve.JHNeronObjectAtP" in
set_option synthInstance.maxHeartbeats 1600000 in
set_option maxHeartbeats 12800000 in

theorem ModularCurve.JHNeronObjectAtP.hsup_S46
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

    (hspΛ : ∀ (i : Fin 2)
      (y₁ : {q : Spec (CommRingCat.of (AlgebraicClosure ℚ)) ⟶ 𝔛.Meta.C // q ≫ 𝔛.Meta.toBase = 𝟙 _})
      (u₁ : SchemeHomOver (Spec.map (CommRingCat.ofHom ρ)) (toBase p (ΓM M H) hj))
      (_ : barPt A ≫ u₁.1 = y₁.1 ≫ 𝔛.eeta ≫ pullback.fst _ _)
      (uκ₁ : Spec (CommRingCat.of (ResidueField ↥A)) ⟶ fibre (Γ := ΓM M H) (hj := hj) ((IsLocalRing.residue ↥A).comp ρ))
      (_ : uκ₁ ≫ pullback.fst _ _ = Spec.map (CommRingCat.ofHom (IsLocalRing.residue ↥A)) ≫ u₁.1)
      (_ : uκ₁ ≫ pullback.snd _ _ = 𝟙 _)
      (Q₁ : closedPoints (𝔛.Mfib A hA ρ hρ).C)
      (_ : (𝔛.efib A hA ρ hρ).base Q₁.1 =
        (uκ₁ ≫ fibreMap (if i = 0 then 𝔛.π else 𝔛.πw) ((IsLocalRing.residue ↥A).comp ρ)).base
          (IsLocalRing.closedPoint (ResidueField ↥A)))
      (y₂ : {q : Spec (CommRingCat.of (AlgebraicClosure ℚ)) ⟶ 𝔛.Meta.C // q ≫ 𝔛.Meta.toBase = 𝟙 _})
      (u₂ : SchemeHomOver (Spec.map (CommRingCat.ofHom ρ)) (toBase p (ΓM M H) hj))
      (_ : barPt A ≫ u₂.1 = y₂.1 ≫ 𝔛.eeta ≫ pullback.fst _ _)
      (uκ₂ : Spec (CommRingCat.of (ResidueField ↥A)) ⟶ fibre (Γ := ΓM M H) (hj := hj) ((IsLocalRing.residue ↥A).comp ρ))
      (_ : uκ₂ ≫ pullback.fst _ _ = Spec.map (CommRingCat.ofHom (IsLocalRing.residue ↥A)) ≫ u₂.1)
      (_ : uκ₂ ≫ pullback.snd _ _ = 𝟙 _)
      (Q₂ : closedPoints (𝔛.Mfib A hA ρ hρ).C)
      (_ : (𝔛.efib A hA ρ hρ).base Q₂.1 =
        (uκ₂ ≫ fibreMap (if i = 0 then 𝔛.π else 𝔛.πw) ((IsLocalRing.residue ↥A).comp ρ)).base
          (IsLocalRing.closedPoint (ResidueField ↥A)))
      (Dv : Divisor.degZero (K := AlgebraicClosure ℚ) (F := ↥(xHFunctionFieldBar M H)))
      (_ : (Dv : Divisor (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H)) =
        Finsupp.single (𝔛.Meta.pointEquivPlace y₁) 1 - Finsupp.single (𝔛.Meta.pointEquivPlace y₂) 1)
      (Dw : Divisor.degZero (K := ResidueField ↥A) (F := Fbar p M H hpM (ResidueField ↥A)))
      (_ : (Dw : Divisor (ResidueField ↥A) (Fbar p M H hpM (ResidueField ↥A))) =
        Finsupp.single ((𝔛.Mfib A hA ρ hρ).placeOfPoint Q₁) 1 -
          Finsupp.single ((𝔛.Mfib A hA ρ hρ).placeOfPoint Q₂) 1),
      ∃ s₀ : SchemeHomOver Λ.σA Λ.f,
        (Λ.pts (O.degPts i (Pic0.mk Dv))).1 = barPt A ≫ s₀.1 ∧
        Λ.ptsSp.symm (schemeHomOverComp ⟨resPt A, rfl⟩ s₀) = Pic0.mk Dw)

    (hdia0 : ∀ (e : (ZMod (M / p))ˣ) (P : closedPoints (𝔛.Mfib A hA ρ hρ).C),
      ∃ h : (inv (𝔛.efib A hA ρ hρ)).base
          ((fibreMap (overOfIso (𝔛.dia0 e) (𝔛.dia0_over e)) ((IsLocalRing.residue ↥A).comp ρ)).base
            ((𝔛.efib A hA ρ hρ).base P.1)) ∈ closedPoints (𝔛.Mfib A hA ρ hρ).C,
        (𝔛.Mfib A hA ρ hρ).placeOfPoint ⟨_, h⟩ =
          SemilinearAut.ofAlgAut (diamondActionModL (ResidueField ↥A) (M / p) (infSubgroup p M H hpM)
            (CuspForm.gammaLift (M / p) e)) • (𝔛.Mfib A hA ρ hρ).placeOfPoint P)

    (F Finv Fstar : Pic0 (ResidueField ↥A) (Fbar p M H hpM (ResidueField ↥A)) →+
      Pic0 (ResidueField ↥A) (Fbar p M H hpM (ResidueField ↥A)))
    (hF : ∀ z, F z = qExpFrobeniusPushforwardModL (ResidueField ↥A) (ΓN p M H hpM) p z)
    (hFinv : F.comp Finv = AddMonoidHom.id _ ∧ Finv.comp F = AddMonoidHom.id _)
    (hFstar : ∀ z, Fstar z = (p : ℤ) • Finv z)

    (pb : (ZMod (M / p))ˣ) (hpb : ((pb : (ZMod (M / p))ˣ) : ZMod (M / p)) = (p : ZMod (M / p)))
    (δ : Pic0 (ResidueField ↥A) (Fbar p M H hpM (ResidueField ↥A)) →+
      Pic0 (ResidueField ↥A) (Fbar p M H hpM (ResidueField ↥A)))
    (hδ : ∀ z, δ z = SemilinearAut.ofAlgAut (diamondActionModL (ResidueField ↥A) (M / p) (infSubgroup p M H hpM)
      (CuspForm.gammaLift (M / p) pb)) • z)

    (αpull : Fin 2 → (JH (M / p) (infSubgroup p M H hpM) →+ JH M H))
    (degPull : Fin 2 → SchemeHomOver Λ.f O.g)
    (hpull : ∀ (i : Fin 2) (x : JH (M / p) (infSubgroup p M H hpM)),
      (O.pts (αpull i x)).1 = (Λ.pts x).1 ≫ (degPull i).1)

    (hpullsp : ∀ (i : Fin 2) (x : SchemeHomOver (resPt A ≫ Λ.σA) Λ.f),
      GluedPic0.toPic0Pair O.ssFinset (O.ptsSp.symm (schemeHomOverComp x (degPull i))) =
        if i = 0 then (Λ.ptsSp.symm x, Fstar (Λ.ptsSp.symm x))
        else (Fstar (Λ.ptsSp.symm x), δ (Λ.ptsSp.symm x)))

    (Wbar : JH M H →+ JH M H)
    (wgen : SemilinearAut (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H))
    (hWbar : ∀ x : JH M H, Wbar x = wgen • x)
    (hwgen : ∀ (y y' : {q : Spec (CommRingCat.of (AlgebraicClosure ℚ)) ⟶ 𝔛.Meta.C // q ≫ 𝔛.Meta.toBase = 𝟙 _}),
y'.1 ≫ 𝔛.eeta ≫ pullback.fst _ _ ≫ 𝔛.w.hom = y.1 ≫ 𝔛.eeta ≫ pullback.fst _ _ →
      𝔛.Meta.pointEquivPlace y' = wgen • 𝔛.Meta.pointEquivPlace y)

    (S : Set ℕ)
    (hUPgen : ∀ x : JH M H,
      genOpH M H S (CohCarrier.Gen.U p (Fact.out) hpM) x + Wbar x = αpull 1 (O.degPts 0 x))
    (Φ : GluedPic0 (ResidueField ↥A) (Fbar p M H hpM (ResidueField ↥A)) O.ssFinset →+ GluedPic0 (ResidueField ↥A) (Fbar p M H hpM (ResidueField ↥A)) O.ssFinset)
    (hΦ : ∀ ξ, Φ ξ = O.ptsSp.symm (NeronModelInfra.schemeHomOverComp (O.ptsSp ξ) (O.hecke S (CohCarrier.Gen.U p (Fact.out) hpM))))
    (hdegF : ∀ v : Place (ResidueField ↥A) (Fbar p M H hpM (ResidueField ↥A)), v.deg = 1)
    (i : Fin 2)
    (y₁ : {q : Spec (CommRingCat.of (AlgebraicClosure ℚ)) ⟶ 𝔛.Meta.C // q ≫ 𝔛.Meta.toBase = 𝟙 _}) (u₁ : SchemeHomOver (Spec.map (CommRingCat.ofHom ρ)) (toBase p (ΓM M H) hj))
    (hu₁ : barPt A ≫ u₁.1 = y₁.1 ≫ 𝔛.eeta ≫ pullback.fst _ _)
    (hu₁sm : Set.range u₁.1.base ⊆ (𝔛.smoothLocus : Set (X p (ΓM M H) hj)))
    (uκ₁ : (Spec (CommRingCat.of (ResidueField ↥A)) ⟶ fibre (Γ := ΓM M H) (hj := hj) ((IsLocalRing.residue ↥A).comp ρ)))
    (huκ₁₁ : uκ₁ ≫ pullback.fst _ _ = Spec.map (CommRingCat.ofHom (IsLocalRing.residue ↥A)) ≫ u₁.1)
    (huκ₁₂ : uκ₁ ≫ pullback.snd _ _ = 𝟙 _)
    (P₁ : closedPoints (𝔛.Mfib A hA ρ hρ).C)
    (hP₁ : (𝔛.efib A hA ρ hρ ≫ 𝔛.comp A hA ρ hρ i).base P₁.1 = uκ₁.base (IsLocalRing.closedPoint (ResidueField ↥A)))
    (y₂ : {q : Spec (CommRingCat.of (AlgebraicClosure ℚ)) ⟶ 𝔛.Meta.C // q ≫ 𝔛.Meta.toBase = 𝟙 _}) (u₂ : SchemeHomOver (Spec.map (CommRingCat.ofHom ρ)) (toBase p (ΓM M H) hj))
    (hu₂ : barPt A ≫ u₂.1 = y₂.1 ≫ 𝔛.eeta ≫ pullback.fst _ _)
    (hu₂sm : Set.range u₂.1.base ⊆ (𝔛.smoothLocus : Set (X p (ΓM M H) hj)))
    (uκ₂ : (Spec (CommRingCat.of (ResidueField ↥A)) ⟶ fibre (Γ := ΓM M H) (hj := hj) ((IsLocalRing.residue ↥A).comp ρ)))
    (huκ₂₁ : uκ₂ ≫ pullback.fst _ _ = Spec.map (CommRingCat.ofHom (IsLocalRing.residue ↥A)) ≫ u₂.1)
    (huκ₂₂ : uκ₂ ≫ pullback.snd _ _ = 𝟙 _)
    (P₂ : closedPoints (𝔛.Mfib A hA ρ hρ).C)
    (hP₂ : (𝔛.efib A hA ρ hρ ≫ 𝔛.comp A hA ρ hρ i).base P₂.1 = uκ₂.base (IsLocalRing.closedPoint (ResidueField ↥A)))
    (Dv : Divisor.degZero (K := AlgebraicClosure ℚ) (F := ↥(xHFunctionFieldBar M H)))
    (hDv : (Dv : Divisor (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H)) =
      Finsupp.single (𝔛.Meta.pointEquivPlace y₁) 1 - Finsupp.single (𝔛.Meta.pointEquivPlace y₂) 1)
    (x : ↥(GluingData.admissible O.ssFinset))
    (hx₁ : (x : GluingData (ResidueField ↥A) (Fbar p M H hpM (ResidueField ↥A)) O.ssFinset).1 =
      (if i = 0 then Finsupp.single ((𝔛.Mfib A hA ρ hρ).placeOfPoint P₁) 1 - Finsupp.single ((𝔛.Mfib A hA ρ hρ).placeOfPoint P₂) 1 else 0))
    (hx₂ : (x : GluingData (ResidueField ↥A) (Fbar p M H hpM (ResidueField ↥A)) O.ssFinset).2.1 =
      (if i = 1 then Finsupp.single ((𝔛.Mfib A hA ρ hρ).placeOfPoint P₁) 1 - Finsupp.single ((𝔛.Mfib A hA ρ hρ).placeOfPoint P₂) 1 else 0))
    (hx₃ : (x : GluingData (ResidueField ↥A) (Fbar p M H hpM (ResidueField ↥A)) O.ssFinset).2.2 = 0)
    (havoid : (∀ s ∈ O.ssFinset, (if i = 0 then ((SemilinearAut.ofAlgAut (diamondActionModL (ResidueField ↥A) (M / p) (infSubgroup p M H hpM)
        (CuspForm.gammaLift (M / p) pb))) • ((𝔛.Mfib A hA ρ hρ).placeOfPoint P₁) ≠ s.2 ∧ (SemilinearAut.ofAlgAut (diamondActionModL (ResidueField ↥A) (M / p) (infSubgroup p M H hpM)
        (CuspForm.gammaLift (M / p) pb))) • ((𝔛.Mfib A hA ρ hρ).placeOfPoint P₂) ≠ s.2)
        else (((𝔛.Mfib A hA ρ hρ).placeOfPoint P₁) ≠ s.1 ∧ ((𝔛.Mfib A hA ρ hρ).placeOfPoint P₂) ≠ s.1)))) :
    ∃ η : GluedPic0 (ResidueField ↥A) (Fbar p M H hpM (ResidueField ↥A)) O.ssFinset,
      GluedPic0.toPic0Pair O.ssFinset η =
        ((GluedPic0.toPic0Pair O.ssFinset (GluedPic0.mk O.ssFinset x)).2,
         δ (GluedPic0.toPic0Pair O.ssFinset (GluedPic0.mk O.ssFinset x)).1) ∧
      Φ (GluedPic0.mk O.ssFinset x) = O.ptsSp.symm (NeronModelInfra.schemeHomOverComp
          (NeronModelInfra.schemeHomOverComp (O.ptsSp (GluedPic0.mk O.ssFinset x)) (O.degeneracyHom 0)) (degPull 1)) - η:= by

  have hS0 := hsp i y₁ u₁ hu₁ hu₁sm uκ₁ huκ₁₁ huκ₁₂ P₁ hP₁ y₂ u₂ hu₂ hu₂sm uκ₂ huκ₂₁ huκ₂₂ P₂ hP₂ Dv hDv x hx₁ hx₂ hx₃
  obtain ⟨s, hs, hsx⟩ := hS0
  have hsx' : O.ptsSp (GluedPic0.mk O.ssFinset x) = NeronModelInfra.schemeHomOverComp ⟨resPt A, rfl⟩ s :=
    ((Equiv.symm_apply_eq _).mp hsx).symm

  have hPhi : Φ (GluedPic0.mk O.ssFinset x) = O.ptsSp.symm (NeronModelInfra.schemeHomOverComp ⟨resPt A, rfl⟩
      (NeronModelInfra.schemeHomOverComp s (O.hecke S (CohCarrier.Gen.U p (Fact.out) hpM)))) := by
    rw [hΦ, hsx']
    exact congrArg O.ptsSp.symm (NeronModelInfra.schemeHomOverComp_assoc _ _ _)
  have hT1 : O.ptsSp.symm (NeronModelInfra.schemeHomOverComp
          (NeronModelInfra.schemeHomOverComp (O.ptsSp (GluedPic0.mk O.ssFinset x)) (O.degeneracyHom 0)) (degPull 1)) =
      O.ptsSp.symm (NeronModelInfra.schemeHomOverComp ⟨resPt A, rfl⟩
        (NeronModelInfra.schemeHomOverComp (NeronModelInfra.schemeHomOverComp s (O.degeneracyHom 0)) (degPull 1))) := by
    rw [hsx']
    exact congrArg O.ptsSp.symm ((congrArg (fun t => NeronModelInfra.schemeHomOverComp t (degPull 1))
      (NeronModelInfra.schemeHomOverComp_assoc _ _ _)).trans (NeronModelInfra.schemeHomOverComp_assoc _ _ _))

  have hX : (O.pts (genOpH M H S (CohCarrier.Gen.U p (Fact.out) hpM) (Pic0.mk Dv))).1 =
      barPt A ≫ (NeronModelInfra.schemeHomOverComp s (O.hecke S (CohCarrier.Gen.U p (Fact.out) hpM))).1 := by
    rw [NeronModelInfra.schemeHomOverComp_coe, ← Category.assoc, ← hs]
    exact O.hecke_pts S _ (Pic0.mk Dv)
  have hZ : (O.pts (genOpH M H S (CohCarrier.Gen.U p (Fact.out) hpM) (Pic0.mk Dv) + Wbar (Pic0.mk Dv))).1 =
      barPt A ≫ (NeronModelInfra.schemeHomOverComp (NeronModelInfra.schemeHomOverComp s (O.degeneracyHom 0)) (degPull 1)).1 := by
    rw [hUPgen, hpull 1, O.degeneracyHom_pts 0, hs]
    simp only [NeronModelInfra.schemeHomOverComp_coe, Category.assoc]

  have hW₁ := ModularCurve.XHDRModelAtP.exists_schemeHomOver_comp_w_inv_pointEquivPlace_eq_smul_placeOfPoint_eq
    p M H hpM hj 𝔛 A hA ρ hρ hdia0 pb hpb wgen hwgen i y₁ u₁ hu₁ hu₁sm uκ₁ huκ₁₁ huκ₁₂ P₁ hP₁
  have hW₂ := ModularCurve.XHDRModelAtP.exists_schemeHomOver_comp_w_inv_pointEquivPlace_eq_smul_placeOfPoint_eq
    p M H hpM hj 𝔛 A hA ρ hρ hdia0 pb hpb wgen hwgen i y₂ u₂ hu₂ hu₂sm uκ₂ huκ₂₁ huκ₂₂ P₂ hP₂
  obtain ⟨y₁', u₁', hu₁', -, hu₁'sm, hy₁'pl, uκ₁', huκ₁'₁, huκ₁'₂, -, P₁', hP₁', hP₁'pl⟩ := hW₁
  obtain ⟨y₂', u₂', hu₂', -, hu₂'sm, hy₂'pl, uκ₂', huκ₂'₁, huκ₂'₂, -, P₂', hP₂', hP₂'pl⟩ := hW₂
  have hDvw := AlgebraicCurve.SemilinearAut.hsup_coe_degZeroSMulHom_single_sub_single wgen Dv _ _ _ _ hy₁'pl hy₂'pl hDv

  obtain hi | hi : i = 0 ∨ i = 1 := by
    fin_cases i
    · exact Or.inl rfl
    · exact Or.inr rfl
  · subst hi

    have ej : (if (0 : Fin 2) = 0 then (1 : Fin 2) else 0) = 1 := by decide
    rw [ej] at hP₁' hP₂'
    have hpl₁ : ((𝔛.Mfib A hA ρ hρ).placeOfPoint P₁') = (SemilinearAut.ofAlgAut (diamondActionModL (ResidueField ↥A) (M / p) (infSubgroup p M H hpM)
        (CuspForm.gammaLift (M / p) pb))) • ((𝔛.Mfib A hA ρ hρ).placeOfPoint P₁) := by simpa using hP₁'pl
    have hpl₂ : ((𝔛.Mfib A hA ρ hρ).placeOfPoint P₂') = (SemilinearAut.ofAlgAut (diamondActionModL (ResidueField ↥A) (M / p) (infSubgroup p M H hpM)
        (CuspForm.gammaLift (M / p) pb))) • ((𝔛.Mfib A hA ρ hρ).placeOfPoint P₂) := by simpa using hP₂'pl
    have hav : ∀ s ∈ O.ssFinset, ((𝔛.Mfib A hA ρ hρ).placeOfPoint P₁') ≠ s.2 ∧ ((𝔛.Mfib A hA ρ hρ).placeOfPoint P₂') ≠ s.2 := by
      intro s hs
      have h := havoid s hs
      rw [hpl₁, hpl₂]
      simpa using h
    have hdiff := AlgebraicCurve.Divisor.hsup_single_sub_single_mem_degZero_and_apply hdegF ((𝔛.Mfib A hA ρ hρ).placeOfPoint P₁') ((𝔛.Mfib A hA ρ hρ).placeOfPoint P₂')

    have hadm : ((0 : Divisor (ResidueField ↥A) (Fbar p M H hpM (ResidueField ↥A))), (Finsupp.single ((𝔛.Mfib A hA ρ hρ).placeOfPoint P₁') 1 - Finsupp.single ((𝔛.Mfib A hA ρ hρ).placeOfPoint P₂') 1 :
        Divisor (ResidueField ↥A) (Fbar p M H hpM (ResidueField ↥A))), (0 : ↥O.ssFinset → Additive (ResidueField ↥A)ˣ)) ∈ GluingData.admissible O.ssFinset := by
      rw [GluingData.mem_admissible]
      refine ⟨zero_mem _, hdiff.1, fun s hs => ⟨?_, ?_⟩⟩
      · rfl
      · exact hdiff.2 s.2 (hav s hs).1 (hav s hs).2

    have hS' := hsp 1 y₁' u₁' hu₁' hu₁'sm uκ₁' huκ₁'₁ huκ₁'₂ P₁' hP₁' y₂' u₂' hu₂' hu₂'sm uκ₂' huκ₂'₁ huκ₂'₂ P₂' hP₂'
      (SemilinearAut.degZeroSMulHom wgen Dv) hDvw ⟨_, hadm⟩ (by simp) (by simp) rfl
    obtain ⟨sw, hsw, hswx⟩ := hS'

    have hY : (O.pts (Wbar (Pic0.mk Dv))).1 = barPt A ≫ sw.1 := by
      rw [hWbar, SemilinearAut.pic0_smul_mk]
      exact hsw
    have hadd := ModularCurve.JHNeronObjectAtP.ptsSp_symm_eq_add_of_pts_add p M H hpM A hA Λ O ρ hρ hσA
      (NeronModelInfra.schemeHomOverComp s (O.hecke S (CohCarrier.Gen.U p (Fact.out) hpM))) sw
      (NeronModelInfra.schemeHomOverComp (NeronModelInfra.schemeHomOverComp s (O.degeneracyHom 0)) (degPull 1))
      _ _ hX hY hZ
    refine ⟨GluedPic0.mk O.ssFinset ⟨_, hadm⟩, ?_, ?_⟩
    ·
      rw [GluedPic0.toPic0Pair_mk, GluedPic0.toPic0Pair_mk, hδ, SemilinearAut.pic0_smul_mk]
      refine Prod.ext (congrArg Pic0.mk (Subtype.ext ?_)) (congrArg Pic0.mk (Subtype.ext ?_))
      · show (0 : Divisor (ResidueField ↥A) (Fbar p M H hpM (ResidueField ↥A))) = (x : GluingData (ResidueField ↥A) (Fbar p M H hpM (ResidueField ↥A)) O.ssFinset).2.1
        rw [hx₂]
        simp
      · show (Finsupp.single ((𝔛.Mfib A hA ρ hρ).placeOfPoint P₁') 1 - Finsupp.single ((𝔛.Mfib A hA ρ hρ).placeOfPoint P₂') 1 :
        Divisor (ResidueField ↥A) (Fbar p M H hpM (ResidueField ↥A))) = _
        rw [AlgebraicCurve.SemilinearAut.hsup_coe_degZeroSMulHom_single_sub_single _ _ ((𝔛.Mfib A hA ρ hρ).placeOfPoint P₁) ((𝔛.Mfib A hA ρ hρ).placeOfPoint P₂) _ _ hpl₁ hpl₂ (by simpa using hx₁)]
    ·
      rw [hPhi, hT1, ← hswx]
      exact eq_sub_of_add_eq hadd.symm
  · subst hi

    have ej : (if (1 : Fin 2) = 0 then (1 : Fin 2) else 0) = 0 := by decide
    rw [ej] at hP₁' hP₂'
    have hpl₁ : ((𝔛.Mfib A hA ρ hρ).placeOfPoint P₁') = ((𝔛.Mfib A hA ρ hρ).placeOfPoint P₁) := by simpa using hP₁'pl
    have hpl₂ : ((𝔛.Mfib A hA ρ hρ).placeOfPoint P₂') = ((𝔛.Mfib A hA ρ hρ).placeOfPoint P₂) := by simpa using hP₂'pl
    have hav : ∀ s ∈ O.ssFinset, ((𝔛.Mfib A hA ρ hρ).placeOfPoint P₁') ≠ s.1 ∧ ((𝔛.Mfib A hA ρ hρ).placeOfPoint P₂') ≠ s.1 := by
      intro s hs
      have h := havoid s hs
      rw [hpl₁, hpl₂]
      simpa using h
    have hdiff := AlgebraicCurve.Divisor.hsup_single_sub_single_mem_degZero_and_apply hdegF ((𝔛.Mfib A hA ρ hρ).placeOfPoint P₁') ((𝔛.Mfib A hA ρ hρ).placeOfPoint P₂')

    have hadm : ((Finsupp.single ((𝔛.Mfib A hA ρ hρ).placeOfPoint P₁') 1 - Finsupp.single ((𝔛.Mfib A hA ρ hρ).placeOfPoint P₂') 1 :
        Divisor (ResidueField ↥A) (Fbar p M H hpM (ResidueField ↥A))), (0 : Divisor (ResidueField ↥A) (Fbar p M H hpM (ResidueField ↥A))), (0 : ↥O.ssFinset → Additive (ResidueField ↥A)ˣ)) ∈ GluingData.admissible O.ssFinset := by
      rw [GluingData.mem_admissible]
      refine ⟨hdiff.1, zero_mem _, fun s hs => ⟨?_, ?_⟩⟩
      · exact hdiff.2 s.1 (hav s hs).1 (hav s hs).2
      · rfl

    have hS' := hsp 0 y₁' u₁' hu₁' hu₁'sm uκ₁' huκ₁'₁ huκ₁'₂ P₁' hP₁' y₂' u₂' hu₂' hu₂'sm uκ₂' huκ₂'₁ huκ₂'₂ P₂' hP₂'
      (SemilinearAut.degZeroSMulHom wgen Dv) hDvw ⟨_, hadm⟩ (by simp) (by simp) rfl
    obtain ⟨sw, hsw, hswx⟩ := hS'

    have hY : (O.pts (Wbar (Pic0.mk Dv))).1 = barPt A ≫ sw.1 := by
      rw [hWbar, SemilinearAut.pic0_smul_mk]
      exact hsw
    have hadd := ModularCurve.JHNeronObjectAtP.ptsSp_symm_eq_add_of_pts_add p M H hpM A hA Λ O ρ hρ hσA
      (NeronModelInfra.schemeHomOverComp s (O.hecke S (CohCarrier.Gen.U p (Fact.out) hpM))) sw
      (NeronModelInfra.schemeHomOverComp (NeronModelInfra.schemeHomOverComp s (O.degeneracyHom 0)) (degPull 1))
      _ _ hX hY hZ
    refine ⟨GluedPic0.mk O.ssFinset ⟨_, hadm⟩, ?_, ?_⟩
    ·
      rw [GluedPic0.toPic0Pair_mk, GluedPic0.toPic0Pair_mk, hδ, SemilinearAut.pic0_smul_mk]
      refine Prod.ext (congrArg Pic0.mk (Subtype.ext ?_)) (congrArg Pic0.mk (Subtype.ext ?_))
      · show (Finsupp.single ((𝔛.Mfib A hA ρ hρ).placeOfPoint P₁') 1 - Finsupp.single ((𝔛.Mfib A hA ρ hρ).placeOfPoint P₂') 1 :
        Divisor (ResidueField ↥A) (Fbar p M H hpM (ResidueField ↥A))) = (x : GluingData (ResidueField ↥A) (Fbar p M H hpM (ResidueField ↥A)) O.ssFinset).2.1
        rw [hx₂]
        rw [if_pos rfl, hpl₁, hpl₂]
      · show (0 : Divisor (ResidueField ↥A) (Fbar p M H hpM (ResidueField ↥A))) = _
        rw [SemilinearAut.coe_degZeroSMulHom]
        show (0 : Divisor _ _) = _ • (x : GluingData (ResidueField ↥A) (Fbar p M H hpM (ResidueField ↥A)) O.ssFinset).1
        rw [hx₁, if_neg (by decide), smul_zero]
    ·
      rw [hPhi, hT1, ← hswx]
      exact eq_sub_of_add_eq hadd.symm

p2m_open_scoped "ModularCurve ModularCurve.JHNeronObjectAtP" in
set_option synthInstance.maxHeartbeats 1600000 in
set_option maxHeartbeats 32000000 in

theorem ModularCurve.JHNeronObjectAtP.hsup_S46_tor
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

    (hspΛ : ∀ (i : Fin 2)
      (y₁ : {q : Spec (CommRingCat.of (AlgebraicClosure ℚ)) ⟶ 𝔛.Meta.C // q ≫ 𝔛.Meta.toBase = 𝟙 _})
      (u₁ : SchemeHomOver (Spec.map (CommRingCat.ofHom ρ)) (toBase p (ΓM M H) hj))
      (_ : barPt A ≫ u₁.1 = y₁.1 ≫ 𝔛.eeta ≫ pullback.fst _ _)
      (uκ₁ : Spec (CommRingCat.of (ResidueField ↥A)) ⟶ fibre (Γ := ΓM M H) (hj := hj) ((IsLocalRing.residue ↥A).comp ρ))
      (_ : uκ₁ ≫ pullback.fst _ _ = Spec.map (CommRingCat.ofHom (IsLocalRing.residue ↥A)) ≫ u₁.1)
      (_ : uκ₁ ≫ pullback.snd _ _ = 𝟙 _)
      (Q₁ : closedPoints (𝔛.Mfib A hA ρ hρ).C)
      (_ : (𝔛.efib A hA ρ hρ).base Q₁.1 =
        (uκ₁ ≫ fibreMap (if i = 0 then 𝔛.π else 𝔛.πw) ((IsLocalRing.residue ↥A).comp ρ)).base
          (IsLocalRing.closedPoint (ResidueField ↥A)))
      (y₂ : {q : Spec (CommRingCat.of (AlgebraicClosure ℚ)) ⟶ 𝔛.Meta.C // q ≫ 𝔛.Meta.toBase = 𝟙 _})
      (u₂ : SchemeHomOver (Spec.map (CommRingCat.ofHom ρ)) (toBase p (ΓM M H) hj))
      (_ : barPt A ≫ u₂.1 = y₂.1 ≫ 𝔛.eeta ≫ pullback.fst _ _)
      (uκ₂ : Spec (CommRingCat.of (ResidueField ↥A)) ⟶ fibre (Γ := ΓM M H) (hj := hj) ((IsLocalRing.residue ↥A).comp ρ))
      (_ : uκ₂ ≫ pullback.fst _ _ = Spec.map (CommRingCat.ofHom (IsLocalRing.residue ↥A)) ≫ u₂.1)
      (_ : uκ₂ ≫ pullback.snd _ _ = 𝟙 _)
      (Q₂ : closedPoints (𝔛.Mfib A hA ρ hρ).C)
      (_ : (𝔛.efib A hA ρ hρ).base Q₂.1 =
        (uκ₂ ≫ fibreMap (if i = 0 then 𝔛.π else 𝔛.πw) ((IsLocalRing.residue ↥A).comp ρ)).base
          (IsLocalRing.closedPoint (ResidueField ↥A)))
      (Dv : Divisor.degZero (K := AlgebraicClosure ℚ) (F := ↥(xHFunctionFieldBar M H)))
      (_ : (Dv : Divisor (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H)) =
        Finsupp.single (𝔛.Meta.pointEquivPlace y₁) 1 - Finsupp.single (𝔛.Meta.pointEquivPlace y₂) 1)
      (Dw : Divisor.degZero (K := ResidueField ↥A) (F := Fbar p M H hpM (ResidueField ↥A)))
      (_ : (Dw : Divisor (ResidueField ↥A) (Fbar p M H hpM (ResidueField ↥A))) =
        Finsupp.single ((𝔛.Mfib A hA ρ hρ).placeOfPoint Q₁) 1 -
          Finsupp.single ((𝔛.Mfib A hA ρ hρ).placeOfPoint Q₂) 1),
      ∃ s₀ : SchemeHomOver Λ.σA Λ.f,
        (Λ.pts (O.degPts i (Pic0.mk Dv))).1 = barPt A ≫ s₀.1 ∧
        Λ.ptsSp.symm (schemeHomOverComp ⟨resPt A, rfl⟩ s₀) = Pic0.mk Dw)

    (hdia0 : ∀ (e : (ZMod (M / p))ˣ) (P : closedPoints (𝔛.Mfib A hA ρ hρ).C),
      ∃ h : (inv (𝔛.efib A hA ρ hρ)).base
          ((fibreMap (overOfIso (𝔛.dia0 e) (𝔛.dia0_over e)) ((IsLocalRing.residue ↥A).comp ρ)).base
            ((𝔛.efib A hA ρ hρ).base P.1)) ∈ closedPoints (𝔛.Mfib A hA ρ hρ).C,
        (𝔛.Mfib A hA ρ hρ).placeOfPoint ⟨_, h⟩ =
          SemilinearAut.ofAlgAut (diamondActionModL (ResidueField ↥A) (M / p) (infSubgroup p M H hpM)
            (CuspForm.gammaLift (M / p) e)) • (𝔛.Mfib A hA ρ hρ).placeOfPoint P)

    (F Finv Fstar : Pic0 (ResidueField ↥A) (Fbar p M H hpM (ResidueField ↥A)) →+
      Pic0 (ResidueField ↥A) (Fbar p M H hpM (ResidueField ↥A)))
    (hF : ∀ z, F z = qExpFrobeniusPushforwardModL (ResidueField ↥A) (ΓN p M H hpM) p z)
    (hFinv : F.comp Finv = AddMonoidHom.id _ ∧ Finv.comp F = AddMonoidHom.id _)
    (hFstar : ∀ z, Fstar z = (p : ℤ) • Finv z)

    (pb : (ZMod (M / p))ˣ) (hpb : ((pb : (ZMod (M / p))ˣ) : ZMod (M / p)) = (p : ZMod (M / p)))
    (δ : Pic0 (ResidueField ↥A) (Fbar p M H hpM (ResidueField ↥A)) →+
      Pic0 (ResidueField ↥A) (Fbar p M H hpM (ResidueField ↥A)))
    (hδ : ∀ z, δ z = SemilinearAut.ofAlgAut (diamondActionModL (ResidueField ↥A) (M / p) (infSubgroup p M H hpM)
      (CuspForm.gammaLift (M / p) pb)) • z)

    (αpull : Fin 2 → (JH (M / p) (infSubgroup p M H hpM) →+ JH M H))
    (degPull : Fin 2 → SchemeHomOver Λ.f O.g)
    (hpull : ∀ (i : Fin 2) (x : JH (M / p) (infSubgroup p M H hpM)),
      (O.pts (αpull i x)).1 = (Λ.pts x).1 ≫ (degPull i).1)

    (hpullsp : ∀ (i : Fin 2) (x : SchemeHomOver (resPt A ≫ Λ.σA) Λ.f),
      GluedPic0.toPic0Pair O.ssFinset (O.ptsSp.symm (schemeHomOverComp x (degPull i))) =
        if i = 0 then (Λ.ptsSp.symm x, Fstar (Λ.ptsSp.symm x))
        else (Fstar (Λ.ptsSp.symm x), δ (Λ.ptsSp.symm x)))

    (Wbar : JH M H →+ JH M H)
    (wgen : SemilinearAut (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H))
    (hWbar : ∀ x : JH M H, Wbar x = wgen • x)
    (hwgen : ∀ (y y' : {q : Spec (CommRingCat.of (AlgebraicClosure ℚ)) ⟶ 𝔛.Meta.C // q ≫ 𝔛.Meta.toBase = 𝟙 _}),
y'.1 ≫ 𝔛.eeta ≫ pullback.fst _ _ ≫ 𝔛.w.hom = y.1 ≫ 𝔛.eeta ≫ pullback.fst _ _ →
      𝔛.Meta.pointEquivPlace y' = wgen • 𝔛.Meta.pointEquivPlace y)

    (S : Set ℕ)
    (hUPgen : ∀ x : JH M H,
      genOpH M H S (CohCarrier.Gen.U p (Fact.out) hpM) x + Wbar x = αpull 1 (O.degPts 0 x))
    (Φ : GluedPic0 (ResidueField ↥A) (Fbar p M H hpM (ResidueField ↥A)) O.ssFinset →+ GluedPic0 (ResidueField ↥A) (Fbar p M H hpM (ResidueField ↥A)) O.ssFinset)
    (hΦ : ∀ ξ, Φ ξ = O.ptsSp.symm (NeronModelInfra.schemeHomOverComp (O.ptsSp ξ) (O.hecke S (CohCarrier.Gen.U p (Fact.out) hpM))))
    (hdegF : ∀ v : Place (ResidueField ↥A) (Fbar p M H hpM (ResidueField ↥A)), v.deg = 1)
    (i : Fin 2)
    (y₁ : {q : Spec (CommRingCat.of (AlgebraicClosure ℚ)) ⟶ 𝔛.Meta.C // q ≫ 𝔛.Meta.toBase = 𝟙 _}) (u₁ : SchemeHomOver (Spec.map (CommRingCat.ofHom ρ)) (toBase p (ΓM M H) hj))
    (hu₁ : barPt A ≫ u₁.1 = y₁.1 ≫ 𝔛.eeta ≫ pullback.fst _ _)
    (hu₁sm : Set.range u₁.1.base ⊆ (𝔛.smoothLocus : Set (X p (ΓM M H) hj)))
    (uκ₁ : (Spec (CommRingCat.of (ResidueField ↥A)) ⟶ fibre (Γ := ΓM M H) (hj := hj) ((IsLocalRing.residue ↥A).comp ρ)))
    (huκ₁₁ : uκ₁ ≫ pullback.fst _ _ = Spec.map (CommRingCat.ofHom (IsLocalRing.residue ↥A)) ≫ u₁.1)
    (huκ₁₂ : uκ₁ ≫ pullback.snd _ _ = 𝟙 _)
    (P₁ : closedPoints (𝔛.Mfib A hA ρ hρ).C)
    (hP₁ : (𝔛.efib A hA ρ hρ ≫ 𝔛.comp A hA ρ hρ i).base P₁.1 = uκ₁.base (IsLocalRing.closedPoint (ResidueField ↥A)))
    (y₂ : {q : Spec (CommRingCat.of (AlgebraicClosure ℚ)) ⟶ 𝔛.Meta.C // q ≫ 𝔛.Meta.toBase = 𝟙 _}) (u₂ : SchemeHomOver (Spec.map (CommRingCat.ofHom ρ)) (toBase p (ΓM M H) hj))
    (hu₂ : barPt A ≫ u₂.1 = y₂.1 ≫ 𝔛.eeta ≫ pullback.fst _ _)
    (hu₂sm : Set.range u₂.1.base ⊆ (𝔛.smoothLocus : Set (X p (ΓM M H) hj)))
    (uκ₂ : (Spec (CommRingCat.of (ResidueField ↥A)) ⟶ fibre (Γ := ΓM M H) (hj := hj) ((IsLocalRing.residue ↥A).comp ρ)))
    (huκ₂₁ : uκ₂ ≫ pullback.fst _ _ = Spec.map (CommRingCat.ofHom (IsLocalRing.residue ↥A)) ≫ u₂.1)
    (huκ₂₂ : uκ₂ ≫ pullback.snd _ _ = 𝟙 _)
    (P₂ : closedPoints (𝔛.Mfib A hA ρ hρ).C)
    (hP₂ : (𝔛.efib A hA ρ hρ ≫ 𝔛.comp A hA ρ hρ i).base P₂.1 = uκ₂.base (IsLocalRing.closedPoint (ResidueField ↥A)))
    (Dv : Divisor.degZero (K := AlgebraicClosure ℚ) (F := ↥(xHFunctionFieldBar M H)))
    (hDv : (Dv : Divisor (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H)) =
      Finsupp.single (𝔛.Meta.pointEquivPlace y₁) 1 - Finsupp.single (𝔛.Meta.pointEquivPlace y₂) 1)
    (x : ↥(GluingData.admissible O.ssFinset))
    (hx₁ : (x : GluingData (ResidueField ↥A) (Fbar p M H hpM (ResidueField ↥A)) O.ssFinset).1 =
      (if i = 0 then Finsupp.single ((𝔛.Mfib A hA ρ hρ).placeOfPoint P₁) 1 - Finsupp.single ((𝔛.Mfib A hA ρ hρ).placeOfPoint P₂) 1 else 0))
    (hx₂ : (x : GluingData (ResidueField ↥A) (Fbar p M H hpM (ResidueField ↥A)) O.ssFinset).2.1 =
      (if i = 1 then Finsupp.single ((𝔛.Mfib A hA ρ hρ).placeOfPoint P₁) 1 - Finsupp.single ((𝔛.Mfib A hA ρ hρ).placeOfPoint P₂) 1 else 0))
    (hx₃ : (x : GluingData (ResidueField ↥A) (Fbar p M H hpM (ResidueField ↥A)) O.ssFinset).2.2 = 0)
    (havoid : (∀ s ∈ O.ssFinset, (if i = 0 then ((SemilinearAut.ofAlgAut (diamondActionModL (ResidueField ↥A) (M / p) (infSubgroup p M H hpM)
        (CuspForm.gammaLift (M / p) pb))) • ((𝔛.Mfib A hA ρ hρ).placeOfPoint P₁) ≠ s.2 ∧ (SemilinearAut.ofAlgAut (diamondActionModL (ResidueField ↥A) (M / p) (infSubgroup p M H hpM)
        (CuspForm.gammaLift (M / p) pb))) • ((𝔛.Mfib A hA ρ hρ).placeOfPoint P₂) ≠ s.2)
        else (((𝔛.Mfib A hA ρ hρ).placeOfPoint P₁) ≠ s.1 ∧ ((𝔛.Mfib A hA ρ hρ).placeOfPoint P₂) ≠ s.1))))
    (C : GluedPic0 (ResidueField ↥A) (Fbar p M H hpM (ResidueField ↥A)) O.ssFinset →+ GluedPic0 (ResidueField ↥A) (Fbar p M H hpM (ResidueField ↥A)) O.ssFinset)
    (hC : ∀ (z z' : ↥(GluingData.admissible O.ssFinset)),
      (z : GluingData (ResidueField ↥A) (Fbar p M H hpM (ResidueField ↥A)) O.ssFinset).2.2 = 0 → (z' : GluingData (ResidueField ↥A) (Fbar p M H hpM (ResidueField ↥A)) O.ssFinset).1 = (z : GluingData (ResidueField ↥A) (Fbar p M H hpM (ResidueField ↥A)) O.ssFinset).2.1 →
      (z' : GluingData (ResidueField ↥A) (Fbar p M H hpM (ResidueField ↥A)) O.ssFinset).2.1 = (SemilinearAut.ofAlgAut (diamondActionModL (ResidueField ↥A) (M / p) (infSubgroup p M H hpM)
        (CuspForm.gammaLift (M / p) pb))) • (z : GluingData (ResidueField ↥A) (Fbar p M H hpM (ResidueField ↥A)) O.ssFinset).1 →
      (z' : GluingData (ResidueField ↥A) (Fbar p M H hpM (ResidueField ↥A)) O.ssFinset).2.2 = 0 → C (GluedPic0.mk O.ssFinset z) = GluedPic0.mk O.ssFinset z') :
    Φ (GluedPic0.mk O.ssFinset x) = O.ptsSp.symm (NeronModelInfra.schemeHomOverComp
          (NeronModelInfra.schemeHomOverComp (O.ptsSp (GluedPic0.mk O.ssFinset x)) (O.degeneracyHom 0)) (degPull 1)) -
      C (GluedPic0.mk O.ssFinset x) := by

  have hS0 := hsp i y₁ u₁ hu₁ hu₁sm uκ₁ huκ₁₁ huκ₁₂ P₁ hP₁ y₂ u₂ hu₂ hu₂sm uκ₂ huκ₂₁ huκ₂₂ P₂ hP₂ Dv hDv x hx₁ hx₂ hx₃
  obtain ⟨s, hs, hsx⟩ := hS0
  have hsx' : O.ptsSp (GluedPic0.mk O.ssFinset x) = NeronModelInfra.schemeHomOverComp ⟨resPt A, rfl⟩ s :=
    ((Equiv.symm_apply_eq _).mp hsx).symm

  have hPhi : Φ (GluedPic0.mk O.ssFinset x) = O.ptsSp.symm (NeronModelInfra.schemeHomOverComp ⟨resPt A, rfl⟩
      (NeronModelInfra.schemeHomOverComp s (O.hecke S (CohCarrier.Gen.U p (Fact.out) hpM)))) := by
    rw [hΦ, hsx']
    exact congrArg O.ptsSp.symm (NeronModelInfra.schemeHomOverComp_assoc _ _ _)
  have hT1 : O.ptsSp.symm (NeronModelInfra.schemeHomOverComp
          (NeronModelInfra.schemeHomOverComp (O.ptsSp (GluedPic0.mk O.ssFinset x)) (O.degeneracyHom 0)) (degPull 1)) =
      O.ptsSp.symm (NeronModelInfra.schemeHomOverComp ⟨resPt A, rfl⟩
        (NeronModelInfra.schemeHomOverComp (NeronModelInfra.schemeHomOverComp s (O.degeneracyHom 0)) (degPull 1))) := by
    rw [hsx']
    exact congrArg O.ptsSp.symm ((congrArg (fun t => NeronModelInfra.schemeHomOverComp t (degPull 1))
      (NeronModelInfra.schemeHomOverComp_assoc _ _ _)).trans (NeronModelInfra.schemeHomOverComp_assoc _ _ _))

  have hX : (O.pts (genOpH M H S (CohCarrier.Gen.U p (Fact.out) hpM) (Pic0.mk Dv))).1 =
      barPt A ≫ (NeronModelInfra.schemeHomOverComp s (O.hecke S (CohCarrier.Gen.U p (Fact.out) hpM))).1 := by
    rw [NeronModelInfra.schemeHomOverComp_coe, ← Category.assoc, ← hs]
    exact O.hecke_pts S _ (Pic0.mk Dv)
  have hZ : (O.pts (genOpH M H S (CohCarrier.Gen.U p (Fact.out) hpM) (Pic0.mk Dv) + Wbar (Pic0.mk Dv))).1 =
      barPt A ≫ (NeronModelInfra.schemeHomOverComp (NeronModelInfra.schemeHomOverComp s (O.degeneracyHom 0)) (degPull 1)).1 := by
    rw [hUPgen, hpull 1, O.degeneracyHom_pts 0, hs]
    simp only [NeronModelInfra.schemeHomOverComp_coe, Category.assoc]

  have hW₁ := ModularCurve.XHDRModelAtP.exists_schemeHomOver_comp_w_inv_pointEquivPlace_eq_smul_placeOfPoint_eq
    p M H hpM hj 𝔛 A hA ρ hρ hdia0 pb hpb wgen hwgen i y₁ u₁ hu₁ hu₁sm uκ₁ huκ₁₁ huκ₁₂ P₁ hP₁
  have hW₂ := ModularCurve.XHDRModelAtP.exists_schemeHomOver_comp_w_inv_pointEquivPlace_eq_smul_placeOfPoint_eq
    p M H hpM hj 𝔛 A hA ρ hρ hdia0 pb hpb wgen hwgen i y₂ u₂ hu₂ hu₂sm uκ₂ huκ₂₁ huκ₂₂ P₂ hP₂
  obtain ⟨y₁', u₁', hu₁', -, hu₁'sm, hy₁'pl, uκ₁', huκ₁'₁, huκ₁'₂, -, P₁', hP₁', hP₁'pl⟩ := hW₁
  obtain ⟨y₂', u₂', hu₂', -, hu₂'sm, hy₂'pl, uκ₂', huκ₂'₁, huκ₂'₂, -, P₂', hP₂', hP₂'pl⟩ := hW₂
  have hDvw := AlgebraicCurve.SemilinearAut.hsup_coe_degZeroSMulHom_single_sub_single wgen Dv _ _ _ _ hy₁'pl hy₂'pl hDv

  obtain hi | hi : i = 0 ∨ i = 1 := by
    fin_cases i
    · exact Or.inl rfl
    · exact Or.inr rfl
  · subst hi

    have ej : (if (0 : Fin 2) = 0 then (1 : Fin 2) else 0) = 1 := by decide
    rw [ej] at hP₁' hP₂'
    have hpl₁ : ((𝔛.Mfib A hA ρ hρ).placeOfPoint P₁') = (SemilinearAut.ofAlgAut (diamondActionModL (ResidueField ↥A) (M / p) (infSubgroup p M H hpM)
        (CuspForm.gammaLift (M / p) pb))) • ((𝔛.Mfib A hA ρ hρ).placeOfPoint P₁) := by simpa using hP₁'pl
    have hpl₂ : ((𝔛.Mfib A hA ρ hρ).placeOfPoint P₂') = (SemilinearAut.ofAlgAut (diamondActionModL (ResidueField ↥A) (M / p) (infSubgroup p M H hpM)
        (CuspForm.gammaLift (M / p) pb))) • ((𝔛.Mfib A hA ρ hρ).placeOfPoint P₂) := by simpa using hP₂'pl
    have hav : ∀ s ∈ O.ssFinset, ((𝔛.Mfib A hA ρ hρ).placeOfPoint P₁') ≠ s.2 ∧ ((𝔛.Mfib A hA ρ hρ).placeOfPoint P₂') ≠ s.2 := by
      intro s hs
      have h := havoid s hs
      rw [hpl₁, hpl₂]
      simpa using h
    have hdiff := AlgebraicCurve.Divisor.hsup_single_sub_single_mem_degZero_and_apply hdegF ((𝔛.Mfib A hA ρ hρ).placeOfPoint P₁') ((𝔛.Mfib A hA ρ hρ).placeOfPoint P₂')

    have hadm : ((0 : Divisor (ResidueField ↥A) (Fbar p M H hpM (ResidueField ↥A))), (Finsupp.single ((𝔛.Mfib A hA ρ hρ).placeOfPoint P₁') 1 - Finsupp.single ((𝔛.Mfib A hA ρ hρ).placeOfPoint P₂') 1 :
        Divisor (ResidueField ↥A) (Fbar p M H hpM (ResidueField ↥A))), (0 : ↥O.ssFinset → Additive (ResidueField ↥A)ˣ)) ∈ GluingData.admissible O.ssFinset := by
      rw [GluingData.mem_admissible]
      refine ⟨zero_mem _, hdiff.1, fun s hs => ⟨?_, ?_⟩⟩
      · rfl
      · exact hdiff.2 s.2 (hav s hs).1 (hav s hs).2

    have hS' := hsp 1 y₁' u₁' hu₁' hu₁'sm uκ₁' huκ₁'₁ huκ₁'₂ P₁' hP₁' y₂' u₂' hu₂' hu₂'sm uκ₂' huκ₂'₁ huκ₂'₂ P₂' hP₂'
      (SemilinearAut.degZeroSMulHom wgen Dv) hDvw ⟨_, hadm⟩ (by simp) (by simp) rfl
    obtain ⟨sw, hsw, hswx⟩ := hS'

    have hY : (O.pts (Wbar (Pic0.mk Dv))).1 = barPt A ≫ sw.1 := by
      rw [hWbar, SemilinearAut.pic0_smul_mk]
      exact hsw
    have hadd := ModularCurve.JHNeronObjectAtP.ptsSp_symm_eq_add_of_pts_add p M H hpM A hA Λ O ρ hρ hσA
      (NeronModelInfra.schemeHomOverComp s (O.hecke S (CohCarrier.Gen.U p (Fact.out) hpM))) sw
      (NeronModelInfra.schemeHomOverComp (NeronModelInfra.schemeHomOverComp s (O.degeneracyHom 0)) (degPull 1))
      _ _ hX hY hZ
    have hCx : C (GluedPic0.mk O.ssFinset x) = GluedPic0.mk O.ssFinset ⟨_, hadm⟩ := by
      refine hC x ⟨_, hadm⟩ hx₃ ?_ ?_ rfl
      · show (0 : Divisor (ResidueField ↥A) (Fbar p M H hpM (ResidueField ↥A))) =
          (x : GluingData (ResidueField ↥A) (Fbar p M H hpM (ResidueField ↥A)) O.ssFinset).2.1
        rw [hx₂, if_neg (by decide)]
      · show (Finsupp.single ((𝔛.Mfib A hA ρ hρ).placeOfPoint P₁') 1 - Finsupp.single ((𝔛.Mfib A hA ρ hρ).placeOfPoint P₂') 1 :
          Divisor (ResidueField ↥A) (Fbar p M H hpM (ResidueField ↥A))) = _ • (x : GluingData (ResidueField ↥A) (Fbar p M H hpM (ResidueField ↥A)) O.ssFinset).1
        rw [hpl₁, hpl₂, hx₁, if_pos rfl, smul_sub, SemilinearAut.smul_single, SemilinearAut.smul_single]
    rw [hPhi, hT1, hCx, ← hswx]
    exact eq_sub_of_add_eq hadd.symm
  · subst hi

    have ej : (if (1 : Fin 2) = 0 then (1 : Fin 2) else 0) = 0 := by decide
    rw [ej] at hP₁' hP₂'
    have hpl₁ : ((𝔛.Mfib A hA ρ hρ).placeOfPoint P₁') = ((𝔛.Mfib A hA ρ hρ).placeOfPoint P₁) := by simpa using hP₁'pl
    have hpl₂ : ((𝔛.Mfib A hA ρ hρ).placeOfPoint P₂') = ((𝔛.Mfib A hA ρ hρ).placeOfPoint P₂) := by simpa using hP₂'pl
    have hav : ∀ s ∈ O.ssFinset, ((𝔛.Mfib A hA ρ hρ).placeOfPoint P₁') ≠ s.1 ∧ ((𝔛.Mfib A hA ρ hρ).placeOfPoint P₂') ≠ s.1 := by
      intro s hs
      have h := havoid s hs
      rw [hpl₁, hpl₂]
      simpa using h
    have hdiff := AlgebraicCurve.Divisor.hsup_single_sub_single_mem_degZero_and_apply hdegF ((𝔛.Mfib A hA ρ hρ).placeOfPoint P₁') ((𝔛.Mfib A hA ρ hρ).placeOfPoint P₂')

    have hadm : ((Finsupp.single ((𝔛.Mfib A hA ρ hρ).placeOfPoint P₁') 1 - Finsupp.single ((𝔛.Mfib A hA ρ hρ).placeOfPoint P₂') 1 :
        Divisor (ResidueField ↥A) (Fbar p M H hpM (ResidueField ↥A))), (0 : Divisor (ResidueField ↥A) (Fbar p M H hpM (ResidueField ↥A))), (0 : ↥O.ssFinset → Additive (ResidueField ↥A)ˣ)) ∈ GluingData.admissible O.ssFinset := by
      rw [GluingData.mem_admissible]
      refine ⟨hdiff.1, zero_mem _, fun s hs => ⟨?_, ?_⟩⟩
      · exact hdiff.2 s.1 (hav s hs).1 (hav s hs).2
      · rfl

    have hS' := hsp 0 y₁' u₁' hu₁' hu₁'sm uκ₁' huκ₁'₁ huκ₁'₂ P₁' hP₁' y₂' u₂' hu₂' hu₂'sm uκ₂' huκ₂'₁ huκ₂'₂ P₂' hP₂'
      (SemilinearAut.degZeroSMulHom wgen Dv) hDvw ⟨_, hadm⟩ (by simp) (by simp) rfl
    obtain ⟨sw, hsw, hswx⟩ := hS'

    have hY : (O.pts (Wbar (Pic0.mk Dv))).1 = barPt A ≫ sw.1 := by
      rw [hWbar, SemilinearAut.pic0_smul_mk]
      exact hsw
    have hadd := ModularCurve.JHNeronObjectAtP.ptsSp_symm_eq_add_of_pts_add p M H hpM A hA Λ O ρ hρ hσA
      (NeronModelInfra.schemeHomOverComp s (O.hecke S (CohCarrier.Gen.U p (Fact.out) hpM))) sw
      (NeronModelInfra.schemeHomOverComp (NeronModelInfra.schemeHomOverComp s (O.degeneracyHom 0)) (degPull 1))
      _ _ hX hY hZ
    have hCx : C (GluedPic0.mk O.ssFinset x) = GluedPic0.mk O.ssFinset ⟨_, hadm⟩ := by
      refine hC x ⟨_, hadm⟩ hx₃ ?_ ?_ rfl
      · show (Finsupp.single ((𝔛.Mfib A hA ρ hρ).placeOfPoint P₁') 1 - Finsupp.single ((𝔛.Mfib A hA ρ hρ).placeOfPoint P₂') 1 :
          Divisor (ResidueField ↥A) (Fbar p M H hpM (ResidueField ↥A))) = (x : GluingData (ResidueField ↥A) (Fbar p M H hpM (ResidueField ↥A)) O.ssFinset).2.1
        rw [hx₂, if_pos rfl, hpl₁, hpl₂]
      · show (0 : Divisor (ResidueField ↥A) (Fbar p M H hpM (ResidueField ↥A))) =
          (SemilinearAut.ofAlgAut (diamondActionModL (ResidueField ↥A) (M / p) (infSubgroup p M H hpM)
        (CuspForm.gammaLift (M / p) pb))) • (x : GluingData (ResidueField ↥A) (Fbar p M H hpM (ResidueField ↥A)) O.ssFinset).1
        rw [hx₁, if_neg (by decide), smul_zero]
    rw [hPhi, hT1, hCx, ← hswx]
    exact eq_sub_of_add_eq hadd.symm

set_option synthInstance.maxHeartbeats 6400000 in
set_option maxHeartbeats 64000000 in

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

    (hspΛ : ∀ (i : Fin 2)
      (y₁ : {q : Spec (CommRingCat.of (AlgebraicClosure ℚ)) ⟶ 𝔛.Meta.C // q ≫ 𝔛.Meta.toBase = 𝟙 _})
      (u₁ : SchemeHomOver (Spec.map (CommRingCat.ofHom ρ)) (toBase p (ΓM M H) hj))
      (_ : barPt A ≫ u₁.1 = y₁.1 ≫ 𝔛.eeta ≫ pullback.fst _ _)
      (uκ₁ : Spec (CommRingCat.of (ResidueField ↥A)) ⟶ fibre (Γ := ΓM M H) (hj := hj) ((IsLocalRing.residue ↥A).comp ρ))
      (_ : uκ₁ ≫ pullback.fst _ _ = Spec.map (CommRingCat.ofHom (IsLocalRing.residue ↥A)) ≫ u₁.1)
      (_ : uκ₁ ≫ pullback.snd _ _ = 𝟙 _)
      (Q₁ : closedPoints (𝔛.Mfib A hA ρ hρ).C)
      (_ : (𝔛.efib A hA ρ hρ).base Q₁.1 =
        (uκ₁ ≫ fibreMap (if i = 0 then 𝔛.π else 𝔛.πw) ((IsLocalRing.residue ↥A).comp ρ)).base
          (IsLocalRing.closedPoint (ResidueField ↥A)))
      (y₂ : {q : Spec (CommRingCat.of (AlgebraicClosure ℚ)) ⟶ 𝔛.Meta.C // q ≫ 𝔛.Meta.toBase = 𝟙 _})
      (u₂ : SchemeHomOver (Spec.map (CommRingCat.ofHom ρ)) (toBase p (ΓM M H) hj))
      (_ : barPt A ≫ u₂.1 = y₂.1 ≫ 𝔛.eeta ≫ pullback.fst _ _)
      (uκ₂ : Spec (CommRingCat.of (ResidueField ↥A)) ⟶ fibre (Γ := ΓM M H) (hj := hj) ((IsLocalRing.residue ↥A).comp ρ))
      (_ : uκ₂ ≫ pullback.fst _ _ = Spec.map (CommRingCat.ofHom (IsLocalRing.residue ↥A)) ≫ u₂.1)
      (_ : uκ₂ ≫ pullback.snd _ _ = 𝟙 _)
      (Q₂ : closedPoints (𝔛.Mfib A hA ρ hρ).C)
      (_ : (𝔛.efib A hA ρ hρ).base Q₂.1 =
        (uκ₂ ≫ fibreMap (if i = 0 then 𝔛.π else 𝔛.πw) ((IsLocalRing.residue ↥A).comp ρ)).base
          (IsLocalRing.closedPoint (ResidueField ↥A)))
      (Dv : Divisor.degZero (K := AlgebraicClosure ℚ) (F := ↥(xHFunctionFieldBar M H)))
      (_ : (Dv : Divisor (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H)) =
        Finsupp.single (𝔛.Meta.pointEquivPlace y₁) 1 - Finsupp.single (𝔛.Meta.pointEquivPlace y₂) 1)
      (Dw : Divisor.degZero (K := ResidueField ↥A) (F := Fbar p M H hpM (ResidueField ↥A)))
      (_ : (Dw : Divisor (ResidueField ↥A) (Fbar p M H hpM (ResidueField ↥A))) =
        Finsupp.single ((𝔛.Mfib A hA ρ hρ).placeOfPoint Q₁) 1 -
          Finsupp.single ((𝔛.Mfib A hA ρ hρ).placeOfPoint Q₂) 1),
      ∃ s₀ : SchemeHomOver Λ.σA Λ.f,
        (Λ.pts (O.degPts i (Pic0.mk Dv))).1 = barPt A ≫ s₀.1 ∧
        Λ.ptsSp.symm (schemeHomOverComp ⟨resPt A, rfl⟩ s₀) = Pic0.mk Dw)

    (hdia0 : ∀ (e : (ZMod (M / p))ˣ) (P : closedPoints (𝔛.Mfib A hA ρ hρ).C),
      ∃ h : (inv (𝔛.efib A hA ρ hρ)).base
          ((fibreMap (overOfIso (𝔛.dia0 e) (𝔛.dia0_over e)) ((IsLocalRing.residue ↥A).comp ρ)).base
            ((𝔛.efib A hA ρ hρ).base P.1)) ∈ closedPoints (𝔛.Mfib A hA ρ hρ).C,
        (𝔛.Mfib A hA ρ hρ).placeOfPoint ⟨_, h⟩ =
          SemilinearAut.ofAlgAut (diamondActionModL (ResidueField ↥A) (M / p) (infSubgroup p M H hpM)
            (CuspForm.gammaLift (M / p) e)) • (𝔛.Mfib A hA ρ hρ).placeOfPoint P)

    (F Finv Fstar : Pic0 (ResidueField ↥A) (Fbar p M H hpM (ResidueField ↥A)) →+
      Pic0 (ResidueField ↥A) (Fbar p M H hpM (ResidueField ↥A)))
    (hF : ∀ z, F z = qExpFrobeniusPushforwardModL (ResidueField ↥A) (ΓN p M H hpM) p z)
    (hFinv : F.comp Finv = AddMonoidHom.id _ ∧ Finv.comp F = AddMonoidHom.id _)
    (hFstar : ∀ z, Fstar z = (p : ℤ) • Finv z)

    (pb : (ZMod (M / p))ˣ) (hpb : ((pb : (ZMod (M / p))ˣ) : ZMod (M / p)) = (p : ZMod (M / p)))
    (δ : Pic0 (ResidueField ↥A) (Fbar p M H hpM (ResidueField ↥A)) →+
      Pic0 (ResidueField ↥A) (Fbar p M H hpM (ResidueField ↥A)))
    (hδ : ∀ z, δ z = SemilinearAut.ofAlgAut (diamondActionModL (ResidueField ↥A) (M / p) (infSubgroup p M H hpM)
      (CuspForm.gammaLift (M / p) pb)) • z)

    (αpull : Fin 2 → (JH (M / p) (infSubgroup p M H hpM) →+ JH M H))
    (degPull : Fin 2 → SchemeHomOver Λ.f O.g)
    (hpull : ∀ (i : Fin 2) (x : JH (M / p) (infSubgroup p M H hpM)),
      (O.pts (αpull i x)).1 = (Λ.pts x).1 ≫ (degPull i).1)

    (hpull_mul : ∀ (i : Fin 2) {T : Scheme.{0}} (s : T ⟶ base p) (x y : SchemeHomOver s Λ.f),
      schemeHomOverComp (Λ.L.mul s x y) (degPull i) =
        O.L.mul s (schemeHomOverComp x (degPull i)) (schemeHomOverComp y (degPull i)))

    (hpullsp : ∀ (i : Fin 2) (x : SchemeHomOver (resPt A ≫ Λ.σA) Λ.f),
      GluedPic0.toPic0Pair O.ssFinset (O.ptsSp.symm (schemeHomOverComp x (degPull i))) =
        if i = 0 then (Λ.ptsSp.symm x, Fstar (Λ.ptsSp.symm x))
        else (Fstar (Λ.ptsSp.symm x), δ (Λ.ptsSp.symm x)))

    (Wbar : JH M H →+ JH M H)
    (wgen : SemilinearAut (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H))
    (hWbar : ∀ x : JH M H, Wbar x = wgen • x)
    (hwgen : ∀ (y y' : {q : Spec (CommRingCat.of (AlgebraicClosure ℚ)) ⟶ 𝔛.Meta.C // q ≫ 𝔛.Meta.toBase = 𝟙 _}),
y'.1 ≫ 𝔛.eeta ≫ pullback.fst _ _ ≫ 𝔛.w.hom = y.1 ≫ 𝔛.eeta ≫ pullback.fst _ _ →
      𝔛.Meta.pointEquivPlace y' = wgen • 𝔛.Meta.pointEquivPlace y)

    (S : Set ℕ)
    (hUPgen : ∀ x : JH M H,
      genOpH M H S (CohCarrier.Gen.U p (Fact.out) hpM) x + Wbar x = αpull 1 (O.degPts 0 x))

    (hss : SemilinearAut.IsCrossStable O.ssFinset
      (SemilinearAut.ofAlgAut (diamondActionModL (ResidueField ↥A) (M / p) (infSubgroup p M H hpM)
          (CuspForm.gammaLift (M / p) pb))) 1)
    (hβ : SemilinearAut.baseAut
        (SemilinearAut.ofAlgAut (diamondActionModL (ResidueField ↥A) (M / p) (infSubgroup p M H hpM)
          (CuspForm.gammaLift (M / p) pb))) =
      SemilinearAut.baseAut (1 : SemilinearAut (ResidueField ↥A) (Fbar p M H hpM (ResidueField ↥A)))) :
    ∀ ξ : GluedPic0 (ResidueField ↥A) (Fbar p M H hpM (ResidueField ↥A)) O.ssFinset,
      O.ptsSp.symm (schemeHomOverComp (O.ptsSp ξ) (O.hecke S (CohCarrier.Gen.U p (Fact.out) hpM))) +
        GluedPic0.crossMap O.ssFinset
          (SemilinearAut.ofAlgAut (diamondActionModL (ResidueField ↥A) (M / p) (infSubgroup p M H hpM)
          (CuspForm.gammaLift (M / p) pb))) 1 hss hβ ξ =
      O.ptsSp.symm (schemeHomOverComp (schemeHomOverComp (O.ptsSp ξ) (O.degeneracyHom 0)) (degPull 1)) := by

  have hS1 := ModularCurve.JHNeronObjectAtP.exists_addMonoidHom_apply_eq_ptsSp_symm_schemeHomOverComp_hecke
    p M H hpM A hA Λ O S (CohCarrier.Gen.U p (Fact.out) hpM)
  obtain ⟨Φ, hΦ⟩ := hS1

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
  have hS2 : AddSubgroup.closure {ξ | ∃ (i : Fin 2)
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
        (∀ s ∈ O.ssFinset, (if i = 0 then ((SemilinearAut.ofAlgAut (diamondActionModL (ResidueField ↥A) (M / p) (infSubgroup p M H hpM)
        (CuspForm.gammaLift (M / p) pb))) • ((𝔛.Mfib A hA ρ hρ).placeOfPoint P₁) ≠ s.2 ∧ (SemilinearAut.ofAlgAut (diamondActionModL (ResidueField ↥A) (M / p) (infSubgroup p M H hpM)
        (CuspForm.gammaLift (M / p) pb))) • ((𝔛.Mfib A hA ρ hρ).placeOfPoint P₂) ≠ s.2)
        else (((𝔛.Mfib A hA ρ hρ).placeOfPoint P₁) ≠ s.1 ∧ ((𝔛.Mfib A hA ρ hρ).placeOfPoint P₂) ≠ s.1))) ∧
        ξ = GluedPic0.mk O.ssFinset x} = ⊤ := by
    classical
    have hgen := AlgebraicCurve.GluedPic0.closure_setOf_mk_single_sub_single_eq_top O.ssFinset hS hrat
      (AlgebraicCurve.Place.exists_forall_mem_hasValue)
      (((hfin 0).toFinset.image (fun x => (𝔛.Mfib A hA ρ hρ).placeOfPoint x)) ∪ (O.ssFinset.image (fun s => (SemilinearAut.ofAlgAut (diamondActionModL (ResidueField ↥A) (M / p) (infSubgroup p M H hpM)
        (CuspForm.gammaLift (M / p) pb)))⁻¹ • s.2)))
      (((hfin 1).toFinset.image (fun x => (𝔛.Mfib A hA ρ hρ).placeOfPoint x)) ∪ (O.ssFinset.image Prod.fst))
    rw [eq_top_iff, ← hgen]
    refine AddSubgroup.closure_mono ?_
    rintro ξ ⟨i, Ppl, Qpl, x, hPT, hQT, hx₁, hx₂, hx₃, rfl⟩

    obtain ⟨P₁, rfl⟩ := (𝔛.Mfib A hA ρ hρ).placeOfPoint_bijective.2 Ppl
    obtain ⟨P₂, rfl⟩ := (𝔛.Mfib A hA ρ hρ).placeOfPoint_bijective.2 Qpl
    obtain hi | hi : i = 0 ∨ i = 1 := by
      fin_cases i
      · exact Or.inl rfl
      · exact Or.inr rfl
    · subst hi
      rw [if_pos rfl] at hPT hQT
      rw [Finset.mem_union, not_or] at hPT hQT

      have hmemU : ∀ (P : closedPoints (𝔛.Mfib A hA ρ hρ).C), (𝔛.Mfib A hA ρ hρ).placeOfPoint P ∉ ((hfin 0).toFinset.image (fun x => (𝔛.Mfib A hA ρ hρ).placeOfPoint x)) →
          (pullback.fst (toBase p (ΓM M H) hj) (Spec.map (CommRingCat.ofHom ((IsLocalRing.residue ↥A).comp ρ)))).base
            (((𝔛.efib A hA ρ hρ) ≫ 𝔛.comp A hA ρ hρ 0).base P.1) ∈ (𝔛.smoothLocus : Set (X p (ΓM M H) hj)) := by
        intro P hP'
        by_contra hcon
        apply hP'
        refine Finset.mem_image.mpr ⟨P, ?_, rfl⟩
        rw [Set.Finite.mem_toFinset]
        show P.1 ∉ _
        intro hin
        apply hcon
        rw [← Scheme.Hom.comp_apply, Category.assoc]
        exact hin

      have hav : ∀ (P : closedPoints (𝔛.Mfib A hA ρ hρ).C), (𝔛.Mfib A hA ρ hρ).placeOfPoint P ∉ (O.ssFinset.image (fun s => (SemilinearAut.ofAlgAut (diamondActionModL (ResidueField ↥A) (M / p) (infSubgroup p M H hpM)
        (CuspForm.gammaLift (M / p) pb)))⁻¹ • s.2)) →
          ∀ s ∈ O.ssFinset, (SemilinearAut.ofAlgAut (diamondActionModL (ResidueField ↥A) (M / p) (infSubgroup p M H hpM)
        (CuspForm.gammaLift (M / p) pb))) • (𝔛.Mfib A hA ρ hρ).placeOfPoint P ≠ s.2 := by
        intro P hP' s hs heq
        apply hP'
        refine Finset.mem_image.mpr ⟨s, hs, ?_⟩
        rw [← heq, inv_smul_smul]
      have hL₁ := ModularCurve.XHDRModelAtP.exists_schemeHomOver_range_subset_smoothLocus_of_mem_smoothLocus
        p M H hpM hj 𝔛 A hA ρ hρ 0 P₁ (hmemU P₁ hPT.1)
      have hL₂ := ModularCurve.XHDRModelAtP.exists_schemeHomOver_range_subset_smoothLocus_of_mem_smoothLocus
        p M H hpM hj 𝔛 A hA ρ hρ 0 P₂ (hmemU P₂ hQT.1)
      obtain ⟨y₁, u₁, hu₁, hu₁sm, uκ₁, huκ₁₁, huκ₁₂, hP₁⟩ := hL₁
      obtain ⟨y₂, u₂, hu₂, hu₂sm, uκ₂, huκ₂₁, huκ₂₂, hP₂⟩ := hL₂
      have hDvmem : (Finsupp.single (𝔛.Meta.pointEquivPlace y₁) 1 - Finsupp.single (𝔛.Meta.pointEquivPlace y₂) 1 :
          Divisor (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H)) ∈ Divisor.degZero (K := AlgebraicClosure ℚ) (F := ↥(xHFunctionFieldBar M H)) := by
        rw [Divisor.mem_degZero, map_sub, Divisor.degree_single, Divisor.degree_single, hdeg1, hdeg1, sub_self]
      refine ⟨0, y₁, u₁, hu₁, hu₁sm, uκ₁, huκ₁₁, huκ₁₂, P₁, hP₁, y₂, u₂, hu₂, hu₂sm, uκ₂, huκ₂₁, huκ₂₂, P₂, hP₂,
        ⟨_, hDvmem⟩, rfl, x, ?_, ?_, hx₃, fun s hs => ?_, rfl⟩
      · rw [hx₁]
      · rw [hx₂]
      · rw [if_pos rfl]
        exact ⟨hav P₁ hPT.2 s hs, hav P₂ hQT.2 s hs⟩
    · subst hi
      rw [if_neg (by decide)] at hPT hQT
      rw [Finset.mem_union, not_or] at hPT hQT

      have hmemU : ∀ (P : closedPoints (𝔛.Mfib A hA ρ hρ).C), (𝔛.Mfib A hA ρ hρ).placeOfPoint P ∉ ((hfin 1).toFinset.image (fun x => (𝔛.Mfib A hA ρ hρ).placeOfPoint x)) →
          (pullback.fst (toBase p (ΓM M H) hj) (Spec.map (CommRingCat.ofHom ((IsLocalRing.residue ↥A).comp ρ)))).base
            (((𝔛.efib A hA ρ hρ) ≫ 𝔛.comp A hA ρ hρ 1).base P.1) ∈ (𝔛.smoothLocus : Set (X p (ΓM M H) hj)) := by
        intro P hP'
        by_contra hcon
        apply hP'
        refine Finset.mem_image.mpr ⟨P, ?_, rfl⟩
        rw [Set.Finite.mem_toFinset]
        show P.1 ∉ _
        intro hin
        apply hcon
        rw [← Scheme.Hom.comp_apply, Category.assoc]
        exact hin

      have hav : ∀ (P : closedPoints (𝔛.Mfib A hA ρ hρ).C), (𝔛.Mfib A hA ρ hρ).placeOfPoint P ∉ (O.ssFinset.image Prod.fst) →
          ∀ s ∈ O.ssFinset, (𝔛.Mfib A hA ρ hρ).placeOfPoint P ≠ s.1 := by
        intro P hP' s hs heq
        apply hP'
        refine Finset.mem_image.mpr ⟨s, hs, ?_⟩
        exact heq.symm
      have hL₁ := ModularCurve.XHDRModelAtP.exists_schemeHomOver_range_subset_smoothLocus_of_mem_smoothLocus
        p M H hpM hj 𝔛 A hA ρ hρ 1 P₁ (hmemU P₁ hPT.1)
      have hL₂ := ModularCurve.XHDRModelAtP.exists_schemeHomOver_range_subset_smoothLocus_of_mem_smoothLocus
        p M H hpM hj 𝔛 A hA ρ hρ 1 P₂ (hmemU P₂ hQT.1)
      obtain ⟨y₁, u₁, hu₁, hu₁sm, uκ₁, huκ₁₁, huκ₁₂, hP₁⟩ := hL₁
      obtain ⟨y₂, u₂, hu₂, hu₂sm, uκ₂, huκ₂₁, huκ₂₂, hP₂⟩ := hL₂
      have hDvmem : (Finsupp.single (𝔛.Meta.pointEquivPlace y₁) 1 - Finsupp.single (𝔛.Meta.pointEquivPlace y₂) 1 :
          Divisor (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H)) ∈ Divisor.degZero (K := AlgebraicClosure ℚ) (F := ↥(xHFunctionFieldBar M H)) := by
        rw [Divisor.mem_degZero, map_sub, Divisor.degree_single, Divisor.degree_single, hdeg1, hdeg1, sub_self]
      refine ⟨1, y₁, u₁, hu₁, hu₁sm, uκ₁, huκ₁₁, huκ₁₂, P₁, hP₁, y₂, u₂, hu₂, hu₂sm, uκ₂, huκ₂₁, huκ₂₂, P₂, hP₂,
        ⟨_, hDvmem⟩, rfl, x, ?_, ?_, hx₃, fun s hs => ?_, rfl⟩
      · rw [hx₁]
      · rw [hx₂]
      · rw [if_neg (by decide)]
        exact ⟨hav P₁ hPT.2 s hs, hav P₂ hQT.2 s hs⟩

  have hS3a : ∀ ξ : GluedPic0 (ResidueField ↥A) (Fbar p M H hpM (ResidueField ↥A)) O.ssFinset,
      Λ.ptsSp.symm (NeronModelInfra.schemeHomOverComp (O.ptsSp ξ) (O.degeneracyHom 0)) =
        (GluedPic0.toPic0Pair O.ssFinset ξ).1 + F (GluedPic0.toPic0Pair O.ssFinset ξ).2 := by

    intro ξ
    have hē : (((pb⁻¹ : (ZMod (M / p))ˣ) : (ZMod (M / p))ˣ) : ZMod (M / p)) * (p : ZMod (M / p)) = 1 := by
      rw [← hpb, Units.inv_mul]
    have h := (O.degeneracyHom_special pb⁻¹ hē (O.ptsSp ξ)).1
    rw [O.abqFibre_ptsSp ξ 0, O.abqFibre_ptsSp ξ 1, if_pos rfl, if_neg (by decide), ← hF] at h
    exact h
  have hdegF : ∀ v : Place (ResidueField ↥A) (Fbar p M H hpM (ResidueField ↥A)), v.deg = 1 := by
    intro v
    haveI := IsCurveOver.finiteResidue (K := (ResidueField ↥A)) (F := (Fbar p M H hpM (ResidueField ↥A))) v
    exact (AlgebraicCurve.Place.deg_eq_one_iff_surjective_algebraMap_residueField v).mpr
      IsAlgClosed.algebraMap_bijective_of_isIntegral.2

  obtain ⟨C, hCdef⟩ : ∃ C : GluedPic0 (ResidueField ↥A) (Fbar p M H hpM (ResidueField ↥A)) O.ssFinset →+ GluedPic0 (ResidueField ↥A) (Fbar p M H hpM (ResidueField ↥A)) O.ssFinset, C = GluedPic0.crossMap O.ssFinset (SemilinearAut.ofAlgAut (diamondActionModL (ResidueField ↥A) (M / p) (infSubgroup p M H hpM)
        (CuspForm.gammaLift (M / p) pb))) 1 hss hβ := ⟨_, rfl⟩
  have hC : ∀ (z z' : ↥(GluingData.admissible O.ssFinset)),
      (z : GluingData (ResidueField ↥A) (Fbar p M H hpM (ResidueField ↥A)) O.ssFinset).2.2 = 0 → (z' : GluingData (ResidueField ↥A) (Fbar p M H hpM (ResidueField ↥A)) O.ssFinset).1 = (z : GluingData (ResidueField ↥A) (Fbar p M H hpM (ResidueField ↥A)) O.ssFinset).2.1 →
      (z' : GluingData (ResidueField ↥A) (Fbar p M H hpM (ResidueField ↥A)) O.ssFinset).2.1 = (SemilinearAut.ofAlgAut (diamondActionModL (ResidueField ↥A) (M / p) (infSubgroup p M H hpM)
        (CuspForm.gammaLift (M / p) pb))) • (z : GluingData (ResidueField ↥A) (Fbar p M H hpM (ResidueField ↥A)) O.ssFinset).1 →
      (z' : GluingData (ResidueField ↥A) (Fbar p M H hpM (ResidueField ↥A)) O.ssFinset).2.2 = 0 → C (GluedPic0.mk O.ssFinset z) = GluedPic0.mk O.ssFinset z' := by
    intro z z' hz3 h1 h2 h3
    rw [hCdef, GluedPic0.crossMap_mk]
    refine congrArg (GluedPic0.mk O.ssFinset) (Subtype.ext ?_)
    rw [SemilinearAut.coe_crossAdmissibleMap, SemilinearAut.crossGluingMap_apply]
    refine Prod.ext ?_ (Prod.ext ?_ ?_)
    · show (1 : SemilinearAut (ResidueField ↥A) (Fbar p M H hpM (ResidueField ↥A))) • (z : GluingData (ResidueField ↥A) (Fbar p M H hpM (ResidueField ↥A)) O.ssFinset).2.1 = (z' : GluingData (ResidueField ↥A) (Fbar p M H hpM (ResidueField ↥A)) O.ssFinset).1
      rw [one_smul, h1]
    · exact h2.symm
    · funext t
      show -SemilinearAut.baseAutUnitsHom _ ((z : GluingData (ResidueField ↥A) (Fbar p M H hpM (ResidueField ↥A)) O.ssFinset).2.2 _) = (z' : GluingData (ResidueField ↥A) (Fbar p M H hpM (ResidueField ↥A)) O.ssFinset).2.2 t
      rw [hz3, h3]
      show -SemilinearAut.baseAutUnitsHom _ (0 : Additive (ResidueField ↥A)ˣ) = 0
      rw [map_zero, neg_zero]

  have hS6 : ∀ ξ ∈ {ξ | ∃ (i : Fin 2)
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
        (∀ s ∈ O.ssFinset, (if i = 0 then ((SemilinearAut.ofAlgAut (diamondActionModL (ResidueField ↥A) (M / p) (infSubgroup p M H hpM)
        (CuspForm.gammaLift (M / p) pb))) • ((𝔛.Mfib A hA ρ hρ).placeOfPoint P₁) ≠ s.2 ∧ (SemilinearAut.ofAlgAut (diamondActionModL (ResidueField ↥A) (M / p) (infSubgroup p M H hpM)
        (CuspForm.gammaLift (M / p) pb))) • ((𝔛.Mfib A hA ρ hρ).placeOfPoint P₂) ≠ s.2)
        else (((𝔛.Mfib A hA ρ hρ).placeOfPoint P₁) ≠ s.1 ∧ ((𝔛.Mfib A hA ρ hρ).placeOfPoint P₂) ≠ s.1))) ∧
        ξ = GluedPic0.mk O.ssFinset x},
      Φ ξ = O.ptsSp.symm (NeronModelInfra.schemeHomOverComp
          (NeronModelInfra.schemeHomOverComp (O.ptsSp ξ) (O.degeneracyHom 0)) (degPull 1)) - C ξ := by
    rintro ξ ⟨i, y₁, u₁, hu₁, hu₁sm, uκ₁, huκ₁₁, huκ₁₂, P₁, hP₁, y₂, u₂, hu₂, hu₂sm, uκ₂, huκ₂₁, huκ₂₂, P₂, hP₂, Dv, hDv,
      x, hx₁, hx₂, hx₃, havoid, rfl⟩
    exact ModularCurve.JHNeronObjectAtP.hsup_S46_tor p M H hpM hj 𝔛 A hA Λ O ρ hρ hσA hsp hspΛ hdia0 F Finv Fstar hF hFinv hFstar
      pb hpb δ hδ αpull degPull hpull hpullsp Wbar wgen hWbar hwgen S hUPgen Φ hΦ hdegF i y₁ u₁ hu₁ hu₁sm uκ₁ huκ₁₁ huκ₁₂ P₁ hP₁
      y₂ u₂ hu₂ hu₂sm uκ₂ huκ₂₁ huκ₂₂ P₂ hP₂ Dv hDv x hx₁ hx₂ hx₃ havoid C hC

  let e : SchemeHomOver O.g O.g := NeronModelInfra.schemeHomOverComp (O.degeneracyHom 0) (degPull 1)
  have he_mul : ∀ {T : Scheme.{0}} (s : T ⟶ base p) (x y : SchemeHomOver s O.g),
      NeronModelInfra.schemeHomOverComp (O.L.mul s x y) e =
        O.L.mul s (NeronModelInfra.schemeHomOverComp x e) (NeronModelInfra.schemeHomOverComp y e) := by
    intro T s x y
    show NeronModelInfra.schemeHomOverComp (O.L.mul s x y)
        (NeronModelInfra.schemeHomOverComp (O.degeneracyHom 0) (degPull 1)) = _
    rw [← NeronModelInfra.schemeHomOverComp_assoc, O.degeneracyHom_mul, hpull_mul,
      NeronModelInfra.schemeHomOverComp_assoc, NeronModelInfra.schemeHomOverComp_assoc]
  have key : ∀ X Y : SchemeHomOver (resPt A ≫ Λ.σA) O.g,
      NeronModelInfra.schemeHomOverComp
          (ofFibrePt ((O.L.baseChange (resPt A ≫ Λ.σA)).mul _ (toFibrePt X) (toFibrePt Y))) e =
        ofFibrePt ((O.L.baseChange (resPt A ≫ Λ.σA)).mul _
          (toFibrePt (NeronModelInfra.schemeHomOverComp X e))
          (toFibrePt (NeronModelInfra.schemeHomOverComp Y e))) := by
    intro X Y
    apply Subtype.ext
    simp only [NeronModelInfra.schemeHomOverComp_coe, toFibrePt, ofFibrePt, RelativeGroupLaw.baseChange_mul,
      RelativeGroupLaw.baseChangePointToBase_ofBase]
    have h := congrArg Subtype.val (he_mul (𝟙 _ ≫ resPt A ≫ Λ.σA) (overId X) (overId Y))
    rw [NeronModelInfra.schemeHomOverComp_coe] at h
    rw [h]
    rfl
  let T₁ : GluedPic0 (ResidueField ↥A) (Fbar p M H hpM (ResidueField ↥A)) O.ssFinset →+
      GluedPic0 (ResidueField ↥A) (Fbar p M H hpM (ResidueField ↥A)) O.ssFinset :=
    AddMonoidHom.mk' (fun ξ => O.ptsSp.symm (NeronModelInfra.schemeHomOverComp (O.ptsSp ξ) e)) (by
      intro ξ η
      apply O.ptsSp.injective
      rw [Equiv.apply_symm_apply, O.ptsSp_add, O.ptsSp_add, Equiv.apply_symm_apply, Equiv.apply_symm_apply, key])
  have hT₁ : ∀ ξ, T₁ ξ = O.ptsSp.symm (NeronModelInfra.schemeHomOverComp
      (NeronModelInfra.schemeHomOverComp (O.ptsSp ξ) (O.degeneracyHom 0)) (degPull 1)) := fun ξ => by
    show O.ptsSp.symm (NeronModelInfra.schemeHomOverComp (O.ptsSp ξ)
      (NeronModelInfra.schemeHomOverComp (O.degeneracyHom 0) (degPull 1))) = _
    rw [NeronModelInfra.schemeHomOverComp_assoc]

  let ΦC : GluedPic0 (ResidueField ↥A) (Fbar p M H hpM (ResidueField ↥A)) O.ssFinset →+
      GluedPic0 (ResidueField ↥A) (Fbar p M H hpM (ResidueField ↥A)) O.ssFinset :=
    AddMonoidHom.mk' (fun ξ => Φ ξ + C ξ) (fun a b => by
      show Φ (a + b) + C (a + b) = (Φ a + C a) + (Φ b + C b)
      rw [Φ.map_add, C.map_add, add_add_add_comm])
  have hΦC : ΦC = T₁ :=
    AddMonoidHom.eq_of_eqOn_dense hS2 fun ξ hξ => by
      show Φ ξ + C ξ = T₁ ξ
      rw [hS6 ξ hξ, hT₁, sub_add_cancel]

  intro ξ
  have h : Φ ξ + C ξ = T₁ ξ := DFunLike.congr_fun hΦC ξ
  rw [hΦ, hT₁, hCdef] at h
  exact h

end S_ModularCurve_JHNeronObjectAtP_ptsSp_symm_hecke_U_add_crossMap_eq_ptsSp_symm_degeneracyHom_degPull
end P2MW
export P2MW.S_ModularCurve_JHNeronObjectAtP_ptsSp_symm_hecke_U_add_crossMap_eq_ptsSp_symm_degeneracyHom_degPull (solution)
