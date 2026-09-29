-- Prove2me | solution 1 for ModularCurve.JHNeronObjectAtP.ptsSp_symm_frobeniusTwist_eq_glueMap_of_pointReduction
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:09.976215+00:00
-- url     : https://prove2.me/submissions/0bba21b2-baf6-507e-bf38-76c88fface16

import Mathlib
import Definitions.Def_ModularCurve_XHDRModelAtP
import Definitions.Def_ModularCurve_JHNeronObjectAtP
import Definitions.Def_AlgebraicCurve_GluedPic0Functoriality
import Definitions.Def_AlgebraicGeometry_SchemeFrobenius
import Theorems.Thm_AlgebraicGeometry_SchemeHomOver_ext_of_forall_algebraicClosure_point_of_isReduced_of_flat
import Theorems.Thm_AlgebraicCurve_isCurveOver_of_ringEquiv_functionField_of_isIntegral_of_smoothOfRelativeDimension_one
import Theorems.Thm_AlgebraicCurve_Place_deg_eq_one_iff_surjective_algebraMap_residueField
import Theorems.Thm_AlgebraicCurve_GluedPic0_closure_setOf_mk_single_sub_single_eq_top
import Theorems.Thm_AlgebraicCurve_finite_compl_of_isOpen
import Theorems.Thm_AlgebraicCurve_Place_exists_forall_mem_hasValue
import Theorems.Thm_ModularCurve_XHDRModelAtP_exists_schemeHomOver_range_subset_smoothLocus_of_mem_smoothLocus
import Theorems.Thm_ValuationSubring_exists_isFrobeniusAt_of_liesOverPrime_algebraicClosure_rat
import Theorems.Thm_ModularCurve_XHDRModelAtP_comp_base_baseTwist_eq_baseTwist_comp_base_of_mem_range_iotaInf
import Theorems.Thm_ModularCurve_XHDRModelAtP_exists_placeOfPoint_frobeniusTwist_eq_smul
import Theorems.Thm_ModularCurve_XHDRModelAtP_exists_schemeHomOver_specMap_decomposition_comp_pointEquivPlace_eq_smul_placeOfPoint_eq_smul
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_JHNeronObjectAtP_ptsSp_symm_frobeniusTwist_eq_glueMap_of_pointReduction
p2m_attr_erase "instance" "AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions GaloisRep.ratLocalizedAt.span_isPrime GaloisRep.instAlgebraRatLocalizedAtZMod"
p2m_attr_erase "simp" "AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal AlgebraicCurve.RationalFunctionField.placeInfty_toValuationSubring AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none ModularCurve.baseAut_x1ArithFrobC_apply ModularCurve.coe_qExpCoeffRingAut_apply ModularCurve.qExpCoeffSemilinearAutHom_apply ModularCurve.baseAut_x1x0ArithFrobC_apply ModularCurve.baseAut_qExpArithFrobC_apply ModularCurve.baseAut_qExpCoeffSemilinearAut ModularCurve.toRingAut_qExpCoeffSemilinearAut ModularCurve.toRingAut_coeffSemilinearAut ModularCurve.baseAut_arithFrobC_apply ModularCurve.coe_coeffRingAut_apply ModularCurve.baseAut_coeffSemilinearAut"

set_option autoImplicit false

p2m_open "CategoryTheory CategoryTheory.Limits AlgebraicGeometry P2MW.S_ModularCurve_JHNeronObjectAtP_ptsSp_symm_frobeniusTwist_eq_glueMap_of_pointReduction.AlgebraicGeometry NeronModelInfra AlgebraicCurve P2MW.S_ModularCurve_JHNeronObjectAtP_ptsSp_symm_frobeniusTwist_eq_glueMap_of_pointReduction.AlgebraicCurve IsLocalRing ModularCurve P2MW.S_ModularCurve_JHNeronObjectAtP_ptsSp_symm_frobeniusTwist_eq_glueMap_of_pointReduction.ModularCurve ModularCurve.XHDRLevel P2MW.S_ModularCurve_JHNeronObjectAtP_ptsSp_symm_frobeniusTwist_eq_glueMap_of_pointReduction.ModularCurve.XHDRLevel"

open scoped MatrixGroups

open GoodReductionJacobian ModularCurve.JZeroNeronObjectAtP

namespace AlgebraicCurve p2m_export "AlgebraicCurve" "SemilinearAut SemilinearAut.smul_single SemilinearAut.degZeroSMulHom SemilinearAut.coe_degZeroSMulHom SemilinearAut.pic0_smul_mk Place Divisor Divisor.degree_single Divisor.degZero Divisor.mem_degZero Pic0 Pic0.mk GluingData GluingData.admissible GluedPic0 GluedPic0.mk SemilinearAut.IsNodeStable SemilinearAut.gluingMap_apply SemilinearAut.admissibleMap SemilinearAut.coe_admissibleMap GluedPic0.glueMap GluedPic0.glueMap_mk IsCurveOver IsCurveOver.finiteResidue isCurveOver_of_ringEquiv_functionField_of_isIntegral_of_smoothOfRelativeDimension_one Place.deg_eq_one_iff_surjective_algebraMap_residueField GluedPic0.closure_setOf_mk_single_sub_single_eq_top finite_compl_of_isOpen Place.exists_forall_mem_hasValue" namespace GluedPic0 p2m_export "AlgebraicCurve.GluedPic0" "mk glueMap glueMap_mk closure_setOf_mk_single_sub_single_eq_top" end AlgebraicCurve.GluedPic0
p2m_open_scoped "AlgebraicCurve AlgebraicCurve.GluedPic0" in

theorem AlgebraicCurve.GluedPic0.t2_coe_admissibleMap_of_single_sub_single
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

namespace AlgebraicCurve p2m_export "AlgebraicCurve" "SemilinearAut SemilinearAut.smul_single SemilinearAut.degZeroSMulHom SemilinearAut.coe_degZeroSMulHom SemilinearAut.pic0_smul_mk Place Divisor Divisor.degree_single Divisor.degZero Divisor.mem_degZero Pic0 Pic0.mk GluingData GluingData.admissible GluedPic0 GluedPic0.mk SemilinearAut.IsNodeStable SemilinearAut.gluingMap_apply SemilinearAut.admissibleMap SemilinearAut.coe_admissibleMap GluedPic0.glueMap GluedPic0.glueMap_mk IsCurveOver IsCurveOver.finiteResidue isCurveOver_of_ringEquiv_functionField_of_isIntegral_of_smoothOfRelativeDimension_one Place.deg_eq_one_iff_surjective_algebraMap_residueField GluedPic0.closure_setOf_mk_single_sub_single_eq_top finite_compl_of_isOpen Place.exists_forall_mem_hasValue" namespace SemilinearAut p2m_export "AlgebraicCurve.SemilinearAut" "commutes smul_single degZeroSMulHom coe_degZeroSMulHom pic0_smul_mk IsNodeStable gluingMap_apply admissibleMap coe_admissibleMap" end AlgebraicCurve.SemilinearAut
p2m_open_scoped "AlgebraicCurve AlgebraicCurve.SemilinearAut" in

theorem AlgebraicCurve.SemilinearAut.t2_coe_degZeroSMulHom_single_sub_single
    {K F : Type*} [Field K] [Field F] [Algebra K F] (g : SemilinearAut K F)
    (D : Divisor.degZero (K := K) (F := F)) (P Q P' Q' : Place K F) (hP : P' = g • P) (hQ : Q' = g • Q)
    (hD : (D : Divisor K F) = Finsupp.single P 1 - Finsupp.single Q 1) :
    ((SemilinearAut.degZeroSMulHom g D : Divisor.degZero (K := K) (F := F)) : Divisor K F) =
      Finsupp.single P' 1 - Finsupp.single Q' 1 := by
  subst hP hQ
  rw [SemilinearAut.coe_degZeroSMulHom, hD, smul_sub, SemilinearAut.smul_single, SemilinearAut.smul_single]

namespace AlgebraicGeometry p2m_export "AlgebraicGeometry" "Spec.map_comp Spec.map_preimage Surjective Scheme.Hom Scheme.Hom.image_top_eq_opensRange Spec Spec.map Scheme Spec.map_injective IsSeparated Spec.preimage Spec.map_id Scheme.Hom.comp_apply Scheme.ΓSpecIso powCharRingHom_apply Scheme.frobenius_comp Scheme.frobenius_Spec SchemeHomOver.ext_of_forall_algebraicClosure_point_of_isReduced_of_flat" end AlgebraicGeometry
p2m_open_scoped "AlgebraicGeometry" in

theorem AlgebraicGeometry.t2_natCast_eq_zero_of_hom_Spec {κ : Type} [CommRing κ] (p : ℕ) [CharP κ p]
    {Y : Scheme.{0}} (f : Y ⟶ Spec (CommRingCat.of κ)) : (p : Γ(Y, ⊤)) = 0 := by
  have h : f.appTop.hom ((Scheme.ΓSpecIso (CommRingCat.of κ)).inv.hom (p : κ)) = (p : Γ(Y, ⊤)) := by
    rw [map_natCast, map_natCast]
  rw [← h, CharP.cast_eq_zero, map_zero, map_zero]

namespace ModularCurve p2m_export "ModularCurve" "XHDRLevel.ΓN XHDRModelAtP mem_ssNodePairsQExp_iff xHFunctionField xHFunctionFieldBar JH qExpFunctionFieldC arithmeticGalois galois_smul_pic0_def jqModC JHNeronObjectAtP.LevelData JHNeronObjectAtP JZeroNeronObjectAtP XHDRModelAtP.exists_schemeHomOver_range_subset_smoothLocus_of_mem_smoothLocus XHDRModelAtP.comp_base_baseTwist_eq_baseTwist_comp_base_of_mem_range_iotaInf XHDRModelAtP.exists_placeOfPoint_frobeniusTwist_eq_smul XHDRModelAtP.exists_schemeHomOver_specMap_decomposition_comp_pointEquivPlace_eq_smul_placeOfPoint_eq_smul" namespace XHDRLevel p2m_export "ModularCurve.XHDRLevel" "R X toBase ιInf fibre sectionFibre ΓN ΓM" end ModularCurve.XHDRLevel
p2m_open_scoped "ModularCurve ModularCurve.XHDRLevel" in

theorem ModularCurve.XHDRLevel.t2_frobenius_fst_toBase {p : ℕ} [Fact p.Prime] {Γ : Subgroup SL(2, ℤ)}
    {hj : jqModC ℚ ∈ qExpFunctionFieldC ℚ (⊤ : Subgroup SL(2, ℤ))}
    {κ : Type} [CommRing κ] (toκ : R p →+* κ) (φ : κ →+* κ)
    (hφ : Spec.map (CommRingCat.ofHom φ) ≫ Spec.map (CommRingCat.ofHom toκ) = Spec.map (CommRingCat.ofHom toκ))
    (hY : (p : Γ(fibre (Γ := Γ) (hj := hj) toκ, ⊤)) = 0) (hκ : (p : Γ(Spec (CommRingCat.of κ), ⊤)) = 0)
    (hφ' : (Spec (CommRingCat.of κ)).frobenius p 1 Fact.out hκ = Spec.map (CommRingCat.ofHom φ)) :
    ((fibre (Γ := Γ) (hj := hj) toκ).frobenius p 1 Fact.out hY ≫ pullback.fst _ _) ≫ toBase p Γ hj =
      pullback.snd _ _ ≫ Spec.map (CommRingCat.ofHom toκ) := by
  rw [Category.assoc, pullback.condition, ← Category.assoc,
    Scheme.frobenius_comp (pullback.snd _ _) p 1 Fact.out hY hκ, Category.assoc, hφ', hφ]

p2m_open_scoped "ModularCurve ModularCurve.XHDRLevel" in

theorem ModularCurve.XHDRLevel.t2_fst_toBase_twist {p : ℕ} {Γ : Subgroup SL(2, ℤ)}
    {hj : jqModC ℚ ∈ qExpFunctionFieldC ℚ (⊤ : Subgroup SL(2, ℤ))}
    {κ : Type} [CommRing κ] (toκ : R p →+* κ) (ψ : κ →+* κ)
    (hψ : Spec.map (CommRingCat.ofHom ψ) ≫ Spec.map (CommRingCat.ofHom toκ) = Spec.map (CommRingCat.ofHom toκ)) :
    pullback.fst (toBase p Γ hj) (Spec.map (CommRingCat.ofHom toκ)) ≫ toBase p Γ hj =
      (pullback.snd _ _ ≫ Spec.map (CommRingCat.ofHom ψ)) ≫ Spec.map (CommRingCat.ofHom toκ) := by
  rw [pullback.condition, Category.assoc, hψ]

noncomputable section

namespace T2Frob

open ModularCurve.JHNeronObjectAtP

variable {p M : ℕ} [Fact p.Prime] [NeZero M] {H : Subgroup (ZMod M)ˣ} {hpM : p ∣ M}
  {A : ValuationSubring (AlgebraicClosure ℚ)} {hA : A.LiesOverPrime p}
  [CharP (ResidueField ↥A) p] [IsAlgClosed (ResidueField ↥A)]
  {Λ : JHNeronObjectAtP.LevelData p M H hpM A}

omit [Fact p.Prime] [CharP (ResidueField ↥A) p] [IsAlgClosed (ResidueField ↥A)] in
theorem ext_unique_aux {X : Scheme.{0}} {f : X ⟶ base p} [IsSeparated f]
    (P Q : SchemeHomOver Λ.σA f) (h : barPt A ≫ P.1 = barPt A ≫ Q.1) : P = Q := by
  haveI : IsSeparated (RelativeGroupLaw.baseChangeStr Λ.σA f) := by
    show IsSeparated (pullback.snd f Λ.σA); infer_instance
  have key : toFibrePt P = toFibrePt Q := by
    refine AlgebraicGeometry.SchemeHomOver.ext_of_forall_algebraicClosure_point_of_isReduced_of_flat
      (R := ↥A) (AlgebraicClosure ℚ) (AlgebraicClosure ℚ) (gY := 𝟙 (Spec (CommRingCat.of ↥A)))
      (gX := RelativeGroupLaw.baseChangeStr Λ.σA f) (toFibrePt P) (toFibrePt Q) ?_
    intro z
    have hz : z.1 = barPt A := by have h__af := z.2; simp at h__af; exact h__af
    rw [hz]
    show barPt A ≫ pullback.lift P.1 (𝟙 _) _ = barPt A ≫ pullback.lift Q.1 (𝟙 _) _
    apply pullback.hom_ext
    · simpa only [Category.assoc, pullback.lift_fst] using h
    · simp only [Category.assoc, pullback.lift_snd]
  apply Subtype.ext
  have h1 : P.1 = (toFibrePt P).1 ≫ pullback.fst f Λ.σA := by
    show P.1 = pullback.lift P.1 (𝟙 _) _ ≫ pullback.fst f Λ.σA
    rw [pullback.lift_fst]
  have h2 : Q.1 = (toFibrePt Q).1 ≫ pullback.fst f Λ.σA := by
    show Q.1 = pullback.lift Q.1 (𝟙 _) _ ≫ pullback.fst f Λ.σA
    rw [pullback.lift_fst]
  rw [h1, h2, key]

theorem ext_unique (O : JHNeronObjectAtP p M H hpM A hA Λ)
    (P Q : SchemeHomOver Λ.σA O.g) (h : barPt A ≫ P.1 = barPt A ≫ Q.1) : P = Q := by
  haveI : IsSeparated O.g := O.separated
  exact ext_unique_aux P Q h

def decAut (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) (hσ : σ ∈ A.decompositionSubgroup ℚ) : ↥A →+* ↥A :=
  MulSemiringAction.toRingHom (A.decompositionSubgroup ℚ) ↥A ⟨σ, hσ⟩

omit [Fact p.Prime] [CharP (ResidueField ↥A) p] [IsAlgClosed (ResidueField ↥A)] in
theorem subtype_comp_decAut (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) (hσ : σ ∈ A.decompositionSubgroup ℚ) :
    A.subtype.comp (decAut σ hσ) = (σ : AlgebraicClosure ℚ →+* AlgebraicClosure ℚ).comp A.subtype :=
  RingHom.ext fun _ => rfl

omit [Fact p.Prime] [CharP (ResidueField ↥A) p] [IsAlgClosed (ResidueField ↥A)] in
theorem specMap_comp_barPt (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) (hσ : σ ∈ A.decompositionSubgroup ℚ) :
    Spec.map (CommRingCat.ofHom (σ : AlgebraicClosure ℚ →+* AlgebraicClosure ℚ)) ≫ barPt A =
      barPt A ≫ Spec.map (CommRingCat.ofHom (decAut σ hσ)) := by
  rw [barPt, ← Spec.map_comp, ← Spec.map_comp, ← CommRingCat.ofHom_comp, ← CommRingCat.ofHom_comp, subtype_comp_decAut]

omit [Fact p.Prime] [CharP (ResidueField ↥A) p] [IsAlgClosed (ResidueField ↥A)] in
theorem specMap_comp_genPt (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) :
    Spec.map (CommRingCat.ofHom (σ : AlgebraicClosure ℚ →+* AlgebraicClosure ℚ)) ≫ genPt p = genPt p := by
  rw [genPt, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
  congr 2
  ext s
  show σ (algebraMap (baseRing p) (AlgebraicClosure ℚ) s) = algebraMap (baseRing p) (AlgebraicClosure ℚ) s
  rw [IsScalarTower.algebraMap_apply (baseRing p) ℚ (AlgebraicClosure ℚ), AlgEquiv.commutes]

omit [CharP (ResidueField ↥A) p] [IsAlgClosed (ResidueField ↥A)] in
theorem specMap_decAut_comp_σA (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) (hσ : σ ∈ A.decompositionSubgroup ℚ) :
    Spec.map (CommRingCat.ofHom (decAut σ hσ)) ≫ Λ.σA = Λ.σA := by
  have h : barPt A ≫ (Spec.map (CommRingCat.ofHom (decAut σ hσ)) ≫ Λ.σA) = barPt A ≫ Λ.σA := by
    rw [← Category.assoc, ← specMap_comp_barPt, Category.assoc, Λ.hσA, specMap_comp_genPt]
  set a := Spec.preimage (Spec.map (CommRingCat.ofHom (decAut σ hσ)) ≫ Λ.σA) with ha
  set b := Spec.preimage Λ.σA with hb
  have ha' : Spec.map a = Spec.map (CommRingCat.ofHom (decAut σ hσ)) ≫ Λ.σA := Spec.map_preimage _
  have hb' : Spec.map b = Λ.σA := Spec.map_preimage _
  rw [← ha', ← hb'] at h ⊢
  rw [barPt, ← Spec.map_comp, ← Spec.map_comp] at h
  have h2 := Spec.map_injective h
  haveI : Mono (CommRingCat.ofHom A.subtype) := ConcreteCategory.mono_of_injective _ Subtype.val_injective
  rw [cancel_mono] at h2
  rw [h2]

omit [IsAlgClosed (ResidueField ↥A)] in

theorem resPt_comp_specMap_decAut {σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ} (hσ : σ ∈ A.decompositionSubgroup ℚ)
    (φκ : ResidueField ↥A →+* ResidueField ↥A)
    (hσφ : ∀ a : ↥A, IsLocalRing.residue ↥A ((⟨σ, hσ⟩ : ↥(A.decompositionSubgroup ℚ)) • a) = φκ (IsLocalRing.residue ↥A a)) :
    resPt A ≫ Spec.map (CommRingCat.ofHom (decAut σ hσ)) =
      Spec.map (CommRingCat.ofHom φκ) ≫ resPt A := by
  have hring : (IsLocalRing.residue ↥A).comp (decAut σ hσ) = φκ.comp (IsLocalRing.residue ↥A) :=
    RingHom.ext fun a => hσφ a
  rw [resPt, ← Spec.map_comp, ← Spec.map_comp, ← CommRingCat.ofHom_comp, ← CommRingCat.ofHom_comp, hring]

def smulPt (O : JHNeronObjectAtP p M H hpM A hA Λ) {σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ}
    (hσ : σ ∈ A.decompositionSubgroup ℚ) (s : SchemeHomOver Λ.σA O.g) : SchemeHomOver Λ.σA O.g :=
  ⟨Spec.map (CommRingCat.ofHom (decAut σ hσ)) ≫ s.1, by rw [Category.assoc, s.2, specMap_decAut_comp_σA]⟩

theorem pts_smul_eq (O : JHNeronObjectAtP p M H hpM A hA Λ) {σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ}
    (hσ : σ ∈ A.decompositionSubgroup ℚ) {x : JH M H} {s : SchemeHomOver Λ.σA O.g} (hs : (O.pts x).1 = barPt A ≫ s.1) :
    (O.pts (σ • x)).1 = barPt A ≫ (smulPt O hσ s).1 := by
  show _ = barPt A ≫ Spec.map (CommRingCat.ofHom (decAut σ hσ)) ≫ s.1
  rw [O.pts_galois, hs, ← Category.assoc, specMap_comp_barPt, Category.assoc]

theorem eq_smulPt (O : JHNeronObjectAtP p M H hpM A hA Λ) {σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ}
    (hσ : σ ∈ A.decompositionSubgroup ℚ) {x : JH M H} {s s' : SchemeHomOver Λ.σA O.g}
    (hs : (O.pts x).1 = barPt A ≫ s.1) (hs' : (O.pts (σ • x)).1 = barPt A ≫ s'.1) : s' = smulPt O hσ s :=
  ext_unique O _ _ (hs'.symm.trans (pts_smul_eq O hσ hs))

theorem red_smulPt (O : JHNeronObjectAtP p M H hpM A hA Λ) {σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ}
    (hσ : σ ∈ A.decompositionSubgroup ℚ) (φκ : ResidueField ↥A →+* ResidueField ↥A)
    (hσφ : ∀ a : ↥A, IsLocalRing.residue ↥A ((⟨σ, hσ⟩ : ↥(A.decompositionSubgroup ℚ)) • a) = φκ (IsLocalRing.residue ↥A a))
    (τ : SchemeHomOver (resPt A ≫ Λ.σA) (resPt A ≫ Λ.σA)) (hτ : τ.1 = Spec.map (CommRingCat.ofHom φκ))
    (s : SchemeHomOver Λ.σA O.g) :
    NeronModelInfra.schemeHomOverComp ⟨resPt A, rfl⟩ (smulPt O hσ s) =
      GoodReductionJacobian.schemeHomOverComp τ.1 τ.2 (NeronModelInfra.schemeHomOverComp ⟨resPt A, rfl⟩ s) := by
  apply Subtype.ext
  show resPt A ≫ Spec.map (CommRingCat.ofHom (decAut σ hσ)) ≫ s.1 = τ.1 ≫ resPt A ≫ s.1
  rw [← Category.assoc, resPt_comp_specMap_decAut hσ φκ hσφ, Category.assoc, hτ]

theorem ptsSp_symm_mul (O : JHNeronObjectAtP p M H hpM A hA Λ) (U V : SchemeHomOver (resPt A ≫ Λ.σA) O.g) :
    O.ptsSp.symm (O.L.mul _ U V) = O.ptsSp.symm U + O.ptsSp.symm V := by
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

theorem exists_addMonoidHom_twist (O : JHNeronObjectAtP p M H hpM A hA Λ)
    (τ : SchemeHomOver (resPt A ≫ Λ.σA) (resPt A ≫ Λ.σA)) :
    ∃ Ψ : GluedPic0 (ResidueField ↥A) (Fbar p M H hpM (ResidueField ↥A)) O.ssFinset →+
        GluedPic0 (ResidueField ↥A) (Fbar p M H hpM (ResidueField ↥A)) O.ssFinset,
      ∀ ξ, Ψ ξ = O.ptsSp.symm (GoodReductionJacobian.schemeHomOverComp τ.1 τ.2 (O.ptsSp ξ)) := by
  have R0 : ∀ ξ η, O.ptsSp (ξ + η) = O.L.mul _ (O.ptsSp ξ) (O.ptsSp η) := by
    intro ξ η
    apply O.ptsSp.symm.injective
    rw [Equiv.symm_apply_apply, ptsSp_symm_mul, Equiv.symm_apply_apply, Equiv.symm_apply_apply]
  refine ⟨AddMonoidHom.mk' (fun ξ => O.ptsSp.symm (GoodReductionJacobian.schemeHomOverComp τ.1 τ.2 (O.ptsSp ξ))) ?_,
    fun ξ => rfl⟩
  intro ξ η
  show O.ptsSp.symm (GoodReductionJacobian.schemeHomOverComp τ.1 τ.2 (O.ptsSp (ξ + η))) =
    O.ptsSp.symm (GoodReductionJacobian.schemeHomOverComp τ.1 τ.2 (O.ptsSp ξ)) +
      O.ptsSp.symm (GoodReductionJacobian.schemeHomOverComp τ.1 τ.2 (O.ptsSp η))
  rw [R0]
  exact (congrArg O.ptsSp.symm (O.L.mul_natural _ _ τ.1 τ.2 _ _)).trans (ptsSp_symm_mul O _ _)

end T2Frob

end

open ModularCurve.JHNeronObjectAtP
open T2Frob

set_option maxHeartbeats 6400000
set_option synthInstance.maxHeartbeats 1600000

theorem solution
    (p M : ℕ) [Fact p.Prime] [NeZero M] (H : Subgroup (ZMod M)ˣ) (hpM : p ∣ M) (hpM2 : ¬ p ^ 2 ∣ M)
    (hHp : ∀ u : (ZMod M)ˣ, ZMod.unitsMap (Nat.div_dvd_of_dvd hpM) u = 1 → u ∈ H) [NeZero (M / p)]
    (hj : jqModC ℚ ∈ qExpFunctionFieldC ℚ (⊤ : Subgroup SL(2, ℤ)))
    (𝔛 : XHDRModelAtP p M H hpM hj)
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime p)
    [CharP (ResidueField ↥A) p] [IsAlgClosed (ResidueField ↥A)]
    (ρ : R p →+* ↥A) (hρ : A.subtype.comp ρ = algebraMap (R p) (AlgebraicClosure ℚ))
    (Λ : JHNeronObjectAtP.LevelData p M H hpM A) (O : JHNeronObjectAtP p M H hpM A hA Λ)
    (hσA : Λ.σA = Spec.map (CommRingCat.ofHom ρ))
    (hsp : (∀ (i : Fin 2)
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
        O.ptsSp.symm (schemeHomOverComp ⟨resPt A, rfl⟩ s) = GluedPic0.mk O.ssFinset x))
    (frob : SemilinearAut (ResidueField ↥A) ↥(qExpFunctionFieldC (ResidueField ↥A) (XHDRLevel.ΓN p M H hpM)))
    (hfrob : ∀ (x : ↥(qExpFunctionFieldC (ResidueField ↥A) (XHDRLevel.ΓN p M H hpM))) (n : ℤ),
      ((frob • x : ↥(qExpFunctionFieldC (ResidueField ↥A) (XHDRLevel.ΓN p M H hpM))) :
          LaurentSeries (ResidueField ↥A)).coeff n =
        ((x : LaurentSeries (ResidueField ↥A)).coeff n) ^ p)
    (hstab : SemilinearAut.IsNodeStable O.ssFinset frob)
    (φκ : ResidueField ↥A →+* ResidueField ↥A) (hφκ : ∀ a : ResidueField ↥A, φκ a = a ^ p)
    (τ : SchemeHomOver (resPt A ≫ Λ.σA) (resPt A ≫ Λ.σA))
    (hτ : τ.1 = Spec.map (CommRingCat.ofHom φκ))
    (y : SchemeHomOver (resPt A ≫ Λ.σA) O.g) :
    O.ptsSp.symm (GoodReductionJacobian.schemeHomOverComp τ.1 τ.2 y) =
      GluedPic0.glueMap O.ssFinset frob hstab (O.ptsSp.symm y) := by
  classical

  have hFrE := ValuationSubring.exists_isFrobeniusAt_of_liesOverPrime_algebraicClosure_rat (Fact.out : p.Prime) hA
  obtain ⟨Fr, hFrob⟩ := hFrE
  have hFr : Fr ∈ A.decompositionSubgroup ℚ := hFrob.mem_decompositionSubgroup
  have hFrφ : ∀ a : ↥A, IsLocalRing.residue ↥A ((⟨Fr, hFr⟩ : ↥(A.decompositionSubgroup ℚ)) • a) = φκ (IsLocalRing.residue ↥A a) := by
    intro a
    rw [IsLocalRing.ResidueField.residue_smul, hφκ]
    exact hFrob.smul_residue_eq _

  have hΨE := exists_addMonoidHom_twist O τ
  obtain ⟨Ψ, hΨ⟩ := hΨE

  have hφκ' : φκ = frobenius (ResidueField ↥A) p := RingHom.ext fun a => (hφκ a).trans (frobenius_def p a).symm
  have hbase : Spec.map (CommRingCat.ofHom φκ) ≫ Spec.map (CommRingCat.ofHom ((IsLocalRing.residue ↥A).comp ρ)) =
      Spec.map (CommRingCat.ofHom ((IsLocalRing.residue ↥A).comp ρ)) := by
    have h := τ.2
    rw [hτ, hσA] at h
    rw [CommRingCat.ofHom_comp, Spec.map_comp]
    exact h

  have hκ0 : (p : Γ(Spec (CommRingCat.of (ResidueField ↥A)), ⊤)) = 0 :=
    AlgebraicGeometry.t2_natCast_eq_zero_of_hom_Spec p (𝟙 _)
  have hN : (p : Γ((fibre (Γ := XHDRLevel.ΓN p M H hpM) (hj := hj) ((IsLocalRing.residue ↥A).comp ρ)), ⊤)) = 0 :=
    AlgebraicGeometry.t2_natCast_eq_zero_of_hom_Spec p (pullback.snd _ _)
  have hM : (p : Γ((fibre (Γ := ΓM M H) (hj := hj) ((IsLocalRing.residue ↥A).comp ρ)), ⊤)) = 0 :=
    AlgebraicGeometry.t2_natCast_eq_zero_of_hom_Spec p (pullback.snd _ _)
  have hFrobSpec : (Spec (CommRingCat.of (ResidueField ↥A))).frobenius p 1 Fact.out hκ0 = Spec.map (CommRingCat.ofHom φκ) := by
    refine (Scheme.frobenius_Spec p 1 Fact.out (CharP.cast_eq_zero (ResidueField ↥A) p)).trans ?_
    congr 2
    exact RingHom.ext fun a => by rw [AlgebraicGeometry.powCharRingHom_apply, pow_one, hφκ]
  have hθNE : ∃ θN : (fibre (Γ := XHDRLevel.ΓN p M H hpM) (hj := hj) ((IsLocalRing.residue ↥A).comp ρ)) ⟶
      (fibre (Γ := XHDRLevel.ΓN p M H hpM) (hj := hj) ((IsLocalRing.residue ↥A).comp ρ)),
      θN ≫ pullback.fst _ _ = (fibre (Γ := XHDRLevel.ΓN p M H hpM) (hj := hj) ((IsLocalRing.residue ↥A).comp ρ)).frobenius p 1 Fact.out hN ≫ pullback.fst _ _ ∧
      θN ≫ pullback.snd _ _ = pullback.snd _ _ :=
    ⟨pullback.lift _ _ (ModularCurve.XHDRLevel.t2_frobenius_fst_toBase _ φκ hbase hN hκ0 hFrobSpec),
      pullback.lift_fst _ _ _, pullback.lift_snd _ _ _⟩
  obtain ⟨θN, hθN₁, hθN₂⟩ := hθNE
  have hθME : ∃ θM : (fibre (Γ := ΓM M H) (hj := hj) ((IsLocalRing.residue ↥A).comp ρ)) ⟶
      (fibre (Γ := ΓM M H) (hj := hj) ((IsLocalRing.residue ↥A).comp ρ)),
      θM ≫ pullback.fst _ _ = (fibre (Γ := ΓM M H) (hj := hj) ((IsLocalRing.residue ↥A).comp ρ)).frobenius p 1 Fact.out hM ≫ pullback.fst _ _ ∧
      θM ≫ pullback.snd _ _ = pullback.snd _ _ :=
    ⟨pullback.lift _ _ (ModularCurve.XHDRLevel.t2_frobenius_fst_toBase _ φκ hbase hM hκ0 hFrobSpec),
      pullback.lift_fst _ _ _, pullback.lift_snd _ _ _⟩
  obtain ⟨θM, hθM₁, hθM₂⟩ := hθME

  haveI : PerfectField (ResidueField ↥A) := IsAlgClosed.perfectField (ResidueField ↥A)
  have hψE : ∃ ψ : ResidueField ↥A ≃+* ResidueField ↥A,
      ψ.toRingHom.comp φκ = RingHom.id _ ∧ φκ.comp ψ.toRingHom = RingHom.id _ := by
    refine ⟨(frobeniusEquiv (ResidueField ↥A) p).symm, ?_, ?_⟩
    · exact RingHom.ext fun a => by
        show (frobeniusEquiv (ResidueField ↥A) p).symm (φκ a) = a
        rw [hφκ', frobeniusEquiv_symm_apply_frobenius]
    · exact RingHom.ext fun a => by
        show φκ ((frobeniusEquiv (ResidueField ↥A) p).symm a) = a
        rw [hφκ', frobenius_apply_frobeniusEquiv_symm]
  obtain ⟨ψ, hψ₁, hψ₂⟩ := hψE
  have hψbase : Spec.map (CommRingCat.ofHom ψ.toRingHom) ≫ Spec.map (CommRingCat.ofHom ((IsLocalRing.residue ↥A).comp ρ)) =
      Spec.map (CommRingCat.ofHom ((IsLocalRing.residue ↥A).comp ρ)) := by
    rw [← hbase, ← Category.assoc, ← Spec.map_comp, ← CommRingCat.ofHom_comp, hψ₁, CommRingCat.ofHom_id]
    erw [Spec.map_id]
    rw [Category.id_comp, hbase]
  have hψ : ψ.toRingHom.comp ((IsLocalRing.residue ↥A).comp ρ) = (IsLocalRing.residue ↥A).comp ρ := by
    have h : Spec.map (CommRingCat.ofHom (ψ.toRingHom.comp ((IsLocalRing.residue ↥A).comp ρ))) =
        Spec.map (CommRingCat.ofHom ((IsLocalRing.residue ↥A).comp ρ)) := by
      rw [CommRingCat.ofHom_comp, Spec.map_comp]; exact hψbase
    have h3 := congrArg CommRingCat.Hom.hom (Spec.map_injective h)
    simpa only [CommRingCat.hom_ofHom] using h3
  have hΞNE : ∃ ΞN : (fibre (Γ := XHDRLevel.ΓN p M H hpM) (hj := hj) ((IsLocalRing.residue ↥A).comp ρ)) ⟶
      (fibre (Γ := XHDRLevel.ΓN p M H hpM) (hj := hj) ((IsLocalRing.residue ↥A).comp ρ)),
      ΞN ≫ pullback.fst _ _ = pullback.fst _ _ ∧
      ΞN ≫ pullback.snd _ _ = pullback.snd _ _ ≫ Spec.map (CommRingCat.ofHom ψ.toRingHom) :=
    ⟨pullback.lift _ _ (ModularCurve.XHDRLevel.t2_fst_toBase_twist _ ψ.toRingHom hψbase),
      pullback.lift_fst _ _ _, pullback.lift_snd _ _ _⟩
  obtain ⟨ΞN, hΞN₁, hΞN₂⟩ := hΞNE
  have hΞME : ∃ ΞM : (fibre (Γ := ΓM M H) (hj := hj) ((IsLocalRing.residue ↥A).comp ρ)) ⟶
      (fibre (Γ := ΓM M H) (hj := hj) ((IsLocalRing.residue ↥A).comp ρ)),
      ΞM ≫ pullback.fst _ _ = pullback.fst _ _ ∧
      ΞM ≫ pullback.snd _ _ = pullback.snd _ _ ≫ Spec.map (CommRingCat.ofHom ψ.toRingHom) :=
    ⟨pullback.lift _ _ (ModularCurve.XHDRLevel.t2_fst_toBase_twist _ ψ.toRingHom hψbase),
      pullback.lift_fst _ _ _, pullback.lift_snd _ _ _⟩
  obtain ⟨ΞM, hΞM₁, hΞM₂⟩ := hΞME
  have hSpecφψ : Spec.map (CommRingCat.ofHom φκ) ≫ Spec.map (CommRingCat.ofHom ψ.toRingHom) = 𝟙 _ := by
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp, hψ₂, CommRingCat.ofHom_id]
    exact Spec.map_id _
  have hθΞN : θN = (fibre (Γ := XHDRLevel.ΓN p M H hpM) (hj := hj) ((IsLocalRing.residue ↥A).comp ρ)).frobenius p 1 Fact.out hN ≫ ΞN := by
    apply pullback.hom_ext
    · rw [hθN₁, Category.assoc, hΞN₁]
    · rw [hθN₂, Category.assoc, hΞN₂, ← Category.assoc, Scheme.frobenius_comp (pullback.snd _ _) p 1 Fact.out hN hκ0,
        Category.assoc, hFrobSpec, hSpecφψ, Category.comp_id]
  have hθΞM : θM = (fibre (Γ := ΓM M H) (hj := hj) ((IsLocalRing.residue ↥A).comp ρ)).frobenius p 1 Fact.out hM ≫ ΞM := by
    apply pullback.hom_ext
    · rw [hθM₁, Category.assoc, hΞM₁]
    · rw [hθM₂, Category.assoc, hΞM₂, ← Category.assoc, Scheme.frobenius_comp (pullback.snd _ _) p 1 Fact.out hM hκ0,
        Category.assoc, hFrobSpec, hSpecφψ, Category.comp_id]
  have hθΞNpt : ∀ z, θN.base z = ΞN.base z := by intro z; rw [hθΞN]; rfl
  have hθΞMpt : ∀ z, θM.base z = ΞM.base z := by intro z; rw [hθΞM]; rfl

  have hcompθ : ∀ (i : Fin 2) (P : closedPoints (𝔛.Mfib A hA ρ hρ).C),
      (pullback.fst (toBase p (ΓM M H) hj) (Spec.map (CommRingCat.ofHom ((IsLocalRing.residue ↥A).comp ρ)))).base
        ((𝔛.comp A hA ρ hρ 0).base ((𝔛.efib A hA ρ hρ).base P.1)) ∈ Set.range (ιInf p (ΓM M H) hj).base →
      (𝔛.comp A hA ρ hρ i).base (θN.base ((𝔛.efib A hA ρ hρ).base P.1)) =
        θM.base ((𝔛.efib A hA ρ hρ ≫ 𝔛.comp A hA ρ hρ i).base P.1) := by
    intro i P hz
    rw [hθΞNpt, Scheme.Hom.comp_apply, hθΞMpt]
    exact ModularCurve.XHDRModelAtP.comp_base_baseTwist_eq_baseTwist_comp_base_of_mem_range_iotaInf p M H hpM hj 𝔛 A hA ρ hρ
      ψ hψ ΞN hΞN₁ hΞN₂ ΞM hΞM₁ hΞM₂ _ hz i

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

  have hneV : (((((𝔛.efib A hA ρ hρ) ≫ 𝔛.comp A hA ρ hρ 0 ≫ pullback.fst (toBase p (ΓM M H) hj) (Spec.map (CommRingCat.ofHom ((IsLocalRing.residue ↥A).comp ρ)))) ⁻¹ᵁ
        ((ιInf p (ΓM M H) hj) ''ᵁ ⊤) : (𝔛.Mfib A hA ρ hρ).C.Opens) : Set (𝔛.Mfib A hA ρ hρ).C)).Nonempty := by
    obtain ⟨w, hw⟩ := 𝔛.εinf_mem_comp0 A hA ρ hρ ⟨IsLocalRing.closedPoint (ResidueField ↥A), rfl⟩
    refine ⟨(inv (𝔛.efib A hA ρ hρ)).base w, ?_⟩
    show ((𝔛.efib A hA ρ hρ) ≫ 𝔛.comp A hA ρ hρ 0 ≫ pullback.fst (toBase p (ΓM M H) hj) (Spec.map (CommRingCat.ofHom ((IsLocalRing.residue ↥A).comp ρ)))).base
      ((inv (𝔛.efib A hA ρ hρ)).base w) ∈ ((ιInf p (ΓM M H) hj) ''ᵁ ⊤ : (X p (ΓM M H) hj).Opens)
    have h1 : (𝔛.efib A hA ρ hρ).base ((inv (𝔛.efib A hA ρ hρ)).base w) = w := by
      rw [← Scheme.Hom.comp_apply, IsIso.inv_hom_id]
      rfl
    rw [Scheme.Hom.comp_apply, Scheme.Hom.comp_apply, h1, hw, ← Scheme.Hom.comp_apply, sectionFibre, pullback.lift_fst,
      Scheme.Hom.comp_apply, 𝔛.εinf_chart, Scheme.Hom.comp_apply, Scheme.Hom.image_top_eq_opensRange]
    exact ⟨_, rfl⟩
  have hfinV : {x : closedPoints (𝔛.Mfib A hA ρ hρ).C |
      x.1 ∉ (((𝔛.efib A hA ρ hρ) ≫ 𝔛.comp A hA ρ hρ 0 ≫ pullback.fst (toBase p (ΓM M H) hj) (Spec.map (CommRingCat.ofHom ((IsLocalRing.residue ↥A).comp ρ)))) ⁻¹ᵁ
        ((ιInf p (ΓM M H) hj) ''ᵁ ⊤) : (𝔛.Mfib A hA ρ hρ).C.Opens)}.Finite :=
    (AlgebraicCurve.finite_compl_of_isOpen (𝔛.Mfib A hA ρ hρ).toBase _ hneV).preimage Subtype.val_injective.injOn
  have hmemV : ∀ (P : closedPoints (𝔛.Mfib A hA ρ hρ).C),
      (𝔛.Mfib A hA ρ hρ).placeOfPoint P ∉ hfinV.toFinset.image (fun x => (𝔛.Mfib A hA ρ hρ).placeOfPoint x) →
      (pullback.fst (toBase p (ΓM M H) hj) (Spec.map (CommRingCat.ofHom ((IsLocalRing.residue ↥A).comp ρ)))).base
        ((𝔛.comp A hA ρ hρ 0).base ((𝔛.efib A hA ρ hρ).base P.1)) ∈ Set.range (ιInf p (ΓM M H) hj).base := by
    intro P hP
    by_contra hcon
    apply hP
    refine Finset.mem_image.mpr ⟨P, ?_, rfl⟩
    rw [Set.Finite.mem_toFinset]
    show P.1 ∉ _
    intro hin
    apply hcon
    have hin' : ((𝔛.efib A hA ρ hρ) ≫ 𝔛.comp A hA ρ hρ 0 ≫ pullback.fst (toBase p (ΓM M H) hj) (Spec.map (CommRingCat.ofHom ((IsLocalRing.residue ↥A).comp ρ)))).base P.1 ∈
        ((ιInf p (ΓM M H) hj) ''ᵁ ⊤ : (X p (ΓM M H) hj).Opens) := hin
    rw [Scheme.Hom.image_top_eq_opensRange] at hin'
    simp only [Scheme.Hom.comp_apply] at hin'
    exact hin'

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
      (_ : (pullback.fst (toBase p (ΓM M H) hj) (Spec.map (CommRingCat.ofHom ((IsLocalRing.residue ↥A).comp ρ)))).base
        ((𝔛.comp A hA ρ hρ 0).base ((𝔛.efib A hA ρ hρ).base P₁.1)) ∈ Set.range (ιInf p (ΓM M H) hj).base)
      (y₂ : {q : Spec (CommRingCat.of (AlgebraicClosure ℚ)) ⟶ 𝔛.Meta.C // q ≫ 𝔛.Meta.toBase = 𝟙 _})
      (u₂ : SchemeHomOver (Spec.map (CommRingCat.ofHom ρ)) (toBase p (ΓM M H) hj))
      (_ : barPt A ≫ u₂.1 = y₂.1 ≫ 𝔛.eeta ≫ pullback.fst _ _)
      (_ : Set.range u₂.1.base ⊆ (𝔛.smoothLocus : Set (X p (ΓM M H) hj)))
      (uκ₂ : Spec (CommRingCat.of (ResidueField ↥A)) ⟶ fibre (Γ := ΓM M H) (hj := hj) ((IsLocalRing.residue ↥A).comp ρ))
      (_ : uκ₂ ≫ pullback.fst _ _ = Spec.map (CommRingCat.ofHom (IsLocalRing.residue ↥A)) ≫ u₂.1)
      (_ : uκ₂ ≫ pullback.snd _ _ = 𝟙 _)
      (P₂ : closedPoints (𝔛.Mfib A hA ρ hρ).C)
      (_ : (𝔛.efib A hA ρ hρ ≫ 𝔛.comp A hA ρ hρ i).base P₂.1 = uκ₂.base (IsLocalRing.closedPoint (ResidueField ↥A)))
      (_ : (pullback.fst (toBase p (ΓM M H) hj) (Spec.map (CommRingCat.ofHom ((IsLocalRing.residue ↥A).comp ρ)))).base
        ((𝔛.comp A hA ρ hρ 0).base ((𝔛.efib A hA ρ hρ).base P₂.1)) ∈ Set.range (ιInf p (ΓM M H) hj).base)
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
    have hgen := AlgebraicCurve.GluedPic0.closure_setOf_mk_single_sub_single_eq_top O.ssFinset hS hrat
      (AlgebraicCurve.Place.exists_forall_mem_hasValue)
      ((hfin 0).toFinset.image (fun x => (𝔛.Mfib A hA ρ hρ).placeOfPoint x) ∪ hfinV.toFinset.image (fun x => (𝔛.Mfib A hA ρ hρ).placeOfPoint x))
      ((hfin 1).toFinset.image (fun x => (𝔛.Mfib A hA ρ hρ).placeOfPoint x) ∪ hfinV.toFinset.image (fun x => (𝔛.Mfib A hA ρ hρ).placeOfPoint x))
    rw [eq_top_iff, ← hgen]
    refine AddSubgroup.closure_mono ?_
    rintro ξ ⟨i, Ppl, Qpl, x, hPT, hQT, hx₁, hx₂, hx₃, rfl⟩

    obtain ⟨P₁, rfl⟩ := (𝔛.Mfib A hA ρ hρ).placeOfPoint_bijective.2 Ppl
    obtain ⟨P₂, rfl⟩ := (𝔛.Mfib A hA ρ hρ).placeOfPoint_bijective.2 Qpl
    have hTi : (if i = 0 then (hfin 0).toFinset.image (fun x => (𝔛.Mfib A hA ρ hρ).placeOfPoint x) ∪ hfinV.toFinset.image (fun x => (𝔛.Mfib A hA ρ hρ).placeOfPoint x)
        else (hfin 1).toFinset.image (fun x => (𝔛.Mfib A hA ρ hρ).placeOfPoint x) ∪ hfinV.toFinset.image (fun x => (𝔛.Mfib A hA ρ hρ).placeOfPoint x)) =
        (hfin i).toFinset.image (fun x => (𝔛.Mfib A hA ρ hρ).placeOfPoint x) ∪ hfinV.toFinset.image (fun x => (𝔛.Mfib A hA ρ hρ).placeOfPoint x) := by
      obtain (hi | hi) : i = 0 ∨ i = 1 := by fin_cases i <;> simp
      · subst hi; rw [if_pos rfl]
      · subst hi; rw [if_neg (show (1 : Fin 2) ≠ 0 by decide)]
    rw [hTi] at hPT hQT
    simp only [Finset.mem_union, not_or] at hPT hQT

    have hmemU : ∀ (P : closedPoints (𝔛.Mfib A hA ρ hρ).C),
        (𝔛.Mfib A hA ρ hρ).placeOfPoint P ∉ (hfin i).toFinset.image (fun x => (𝔛.Mfib A hA ρ hρ).placeOfPoint x) →
        (pullback.fst (toBase p (ΓM M H) hj) (Spec.map (CommRingCat.ofHom ((IsLocalRing.residue ↥A).comp ρ)))).base
          (((𝔛.efib A hA ρ hρ) ≫ 𝔛.comp A hA ρ hρ i).base P.1) ∈ (𝔛.smoothLocus : Set (X p (ΓM M H) hj)) := by
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
    have hL₁ := ModularCurve.XHDRModelAtP.exists_schemeHomOver_range_subset_smoothLocus_of_mem_smoothLocus
      p M H hpM hj 𝔛 A hA ρ hρ i P₁ (hmemU P₁ hPT.1)
    have hL₂ := ModularCurve.XHDRModelAtP.exists_schemeHomOver_range_subset_smoothLocus_of_mem_smoothLocus
      p M H hpM hj 𝔛 A hA ρ hρ i P₂ (hmemU P₂ hQT.1)
    obtain ⟨y₁, u₁, hu₁, hu₁sm, uκ₁, huκ₁₁, huκ₁₂, hP₁⟩ := hL₁
    obtain ⟨y₂, u₂, hu₂, hu₂sm, uκ₂, huκ₂₁, huκ₂₂, hP₂⟩ := hL₂

    have hDvmem : (Finsupp.single (𝔛.Meta.pointEquivPlace y₁) 1 - Finsupp.single (𝔛.Meta.pointEquivPlace y₂) 1 :
        Divisor (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H)) ∈ Divisor.degZero (K := AlgebraicClosure ℚ) (F := ↥(xHFunctionFieldBar M H)) := by
      rw [Divisor.mem_degZero, map_sub, Divisor.degree_single, Divisor.degree_single, hdeg1, hdeg1, sub_self]
    refine ⟨i, y₁, u₁, hu₁, hu₁sm, uκ₁, huκ₁₁, huκ₁₂, P₁, hP₁, hmemV P₁ hPT.2, y₂, u₂, hu₂, hu₂sm, uκ₂, huκ₂₁, huκ₂₂, P₂, hP₂, hmemV P₂ hQT.2,
      ⟨_, hDvmem⟩, rfl, x, ?_, ?_, hx₃, rfl⟩
    · rw [hx₁]
    · rw [hx₂]

  have hagree : Set.EqOn Ψ (GluedPic0.glueMap O.ssFinset frob hstab) {ξ | ∃ (i : Fin 2)
      (y₁ : {q : Spec (CommRingCat.of (AlgebraicClosure ℚ)) ⟶ 𝔛.Meta.C // q ≫ 𝔛.Meta.toBase = 𝟙 _})
      (u₁ : SchemeHomOver (Spec.map (CommRingCat.ofHom ρ)) (toBase p (ΓM M H) hj))
      (_ : barPt A ≫ u₁.1 = y₁.1 ≫ 𝔛.eeta ≫ pullback.fst _ _)
      (_ : Set.range u₁.1.base ⊆ (𝔛.smoothLocus : Set (X p (ΓM M H) hj)))
      (uκ₁ : Spec (CommRingCat.of (ResidueField ↥A)) ⟶ fibre (Γ := ΓM M H) (hj := hj) ((IsLocalRing.residue ↥A).comp ρ))
      (_ : uκ₁ ≫ pullback.fst _ _ = Spec.map (CommRingCat.ofHom (IsLocalRing.residue ↥A)) ≫ u₁.1)
      (_ : uκ₁ ≫ pullback.snd _ _ = 𝟙 _)
      (P₁ : closedPoints (𝔛.Mfib A hA ρ hρ).C)
      (_ : (𝔛.efib A hA ρ hρ ≫ 𝔛.comp A hA ρ hρ i).base P₁.1 = uκ₁.base (IsLocalRing.closedPoint (ResidueField ↥A)))
      (_ : (pullback.fst (toBase p (ΓM M H) hj) (Spec.map (CommRingCat.ofHom ((IsLocalRing.residue ↥A).comp ρ)))).base
        ((𝔛.comp A hA ρ hρ 0).base ((𝔛.efib A hA ρ hρ).base P₁.1)) ∈ Set.range (ιInf p (ΓM M H) hj).base)
      (y₂ : {q : Spec (CommRingCat.of (AlgebraicClosure ℚ)) ⟶ 𝔛.Meta.C // q ≫ 𝔛.Meta.toBase = 𝟙 _})
      (u₂ : SchemeHomOver (Spec.map (CommRingCat.ofHom ρ)) (toBase p (ΓM M H) hj))
      (_ : barPt A ≫ u₂.1 = y₂.1 ≫ 𝔛.eeta ≫ pullback.fst _ _)
      (_ : Set.range u₂.1.base ⊆ (𝔛.smoothLocus : Set (X p (ΓM M H) hj)))
      (uκ₂ : Spec (CommRingCat.of (ResidueField ↥A)) ⟶ fibre (Γ := ΓM M H) (hj := hj) ((IsLocalRing.residue ↥A).comp ρ))
      (_ : uκ₂ ≫ pullback.fst _ _ = Spec.map (CommRingCat.ofHom (IsLocalRing.residue ↥A)) ≫ u₂.1)
      (_ : uκ₂ ≫ pullback.snd _ _ = 𝟙 _)
      (P₂ : closedPoints (𝔛.Mfib A hA ρ hρ).C)
      (_ : (𝔛.efib A hA ρ hρ ≫ 𝔛.comp A hA ρ hρ i).base P₂.1 = uκ₂.base (IsLocalRing.closedPoint (ResidueField ↥A)))
      (_ : (pullback.fst (toBase p (ΓM M H) hj) (Spec.map (CommRingCat.ofHom ((IsLocalRing.residue ↥A).comp ρ)))).base
        ((𝔛.comp A hA ρ hρ 0).base ((𝔛.efib A hA ρ hρ).base P₂.1)) ∈ Set.range (ιInf p (ΓM M H) hj).base)
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
    rintro ξ ⟨i, y₁, u₁, hu₁, hu₁sm, uκ₁, huκ₁₁, huκ₁₂, P₁, hP₁, hz₁, y₂, u₂, hu₂, hu₂sm, uκ₂, huκ₂₁, huκ₂₂, P₂, hP₂, hz₂, Dv, hDv,
      x, hx₁, hx₂, hx₃, rfl⟩
    have hS0 := hsp i y₁ u₁ hu₁ hu₁sm uκ₁ huκ₁₁ huκ₁₂ P₁ hP₁ y₂ u₂ hu₂ hu₂sm uκ₂ huκ₂₁ huκ₂₂ P₂ hP₂ Dv hDv x hx₁ hx₂ hx₃
    obtain ⟨s, hs, hsx⟩ := hS0

    have h₁ := ModularCurve.XHDRModelAtP.exists_schemeHomOver_specMap_decomposition_comp_pointEquivPlace_eq_smul_placeOfPoint_eq_smul
      p M H hpM hj 𝔛 A hA ρ hρ frob hfrob hN θN hθN₁ hθN₂ hM θM hθM₁ hθM₂
      (fun P => ModularCurve.XHDRModelAtP.exists_placeOfPoint_frobeniusTwist_eq_smul p M H hpM hj 𝔛 A hA ρ hρ frob hfrob hN θN hθN₁ hθN₂ P)
      Fr hFr φκ hφκ hFrφ i y₁ u₁ hu₁ hu₁sm uκ₁ huκ₁₁ huκ₁₂ P₁ hP₁ (hcompθ i P₁ hz₁)
    have h₂ := ModularCurve.XHDRModelAtP.exists_schemeHomOver_specMap_decomposition_comp_pointEquivPlace_eq_smul_placeOfPoint_eq_smul
      p M H hpM hj 𝔛 A hA ρ hρ frob hfrob hN θN hθN₁ hθN₂ hM θM hθM₁ hθM₂
      (fun P => ModularCurve.XHDRModelAtP.exists_placeOfPoint_frobeniusTwist_eq_smul p M H hpM hj 𝔛 A hA ρ hρ frob hfrob hN θN hθN₁ hθN₂ P)
      Fr hFr φκ hφκ hFrφ i y₂ u₂ hu₂ hu₂sm uκ₂ huκ₂₁ huκ₂₂ P₂ hP₂ (hcompθ i P₂ hz₂)
    obtain ⟨y₁', u₁', hu₁', hu₁'val, hu₁'sm, hy₁'pl, uκ₁', huκ₁'₁, huκ₁'₂, huκ₁'val, P₁', hP₁', hP₁'pl⟩ := h₁
    obtain ⟨y₂', u₂', hu₂', hu₂'val, hu₂'sm, hy₂'pl, uκ₂', huκ₂'₁, huκ₂'₂, huκ₂'val, P₂', hP₂', hP₂'pl⟩ := h₂

    have hDv' : ((SemilinearAut.degZeroSMulHom (arithmeticGalois (L := AlgebraicClosure ℚ) (xHFunctionField M H) Fr) Dv :
          Divisor.degZero (K := AlgebraicClosure ℚ) (F := ↥(xHFunctionFieldBar M H))) :
          Divisor (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H)) =
        Finsupp.single (𝔛.Meta.pointEquivPlace y₁') 1 - Finsupp.single (𝔛.Meta.pointEquivPlace y₂') 1 :=
      AlgebraicCurve.SemilinearAut.t2_coe_degZeroSMulHom_single_sub_single _ Dv _ _ _ _ hy₁'pl hy₂'pl hDv

    have hx' := AlgebraicCurve.GluedPic0.t2_coe_admissibleMap_of_single_sub_single O.ssFinset frob hstab i
      ((𝔛.Mfib A hA ρ hρ).placeOfPoint P₁) ((𝔛.Mfib A hA ρ hρ).placeOfPoint P₂) ((𝔛.Mfib A hA ρ hρ).placeOfPoint P₁') ((𝔛.Mfib A hA ρ hρ).placeOfPoint P₂')
      hP₁'pl hP₂'pl x hx₁ hx₂ hx₃
    obtain ⟨hx'₁, hx'₂, hx'₃⟩ := hx'

    have hS1 := hsp i y₁' u₁' hu₁' hu₁'sm uκ₁' huκ₁'₁ huκ₁'₂ P₁' hP₁' y₂' u₂' hu₂' hu₂'sm uκ₂' huκ₂'₁ huκ₂'₂ P₂' hP₂'
      (SemilinearAut.degZeroSMulHom (arithmeticGalois (L := AlgebraicClosure ℚ) (xHFunctionField M H) Fr) Dv) hDv' _ hx'₁ hx'₂ hx'₃
    obtain ⟨s', hs', hs'x⟩ := hS1

    have hmk : Pic0.mk (SemilinearAut.degZeroSMulHom (arithmeticGalois (L := AlgebraicClosure ℚ) (xHFunctionField M H) Fr) Dv) =
        Fr • Pic0.mk Dv := by
      rw [galois_smul_pic0_def, SemilinearAut.pic0_smul_mk]
    rw [hmk] at hs'
    have hseq : s' = smulPt O hFr s := eq_smulPt O hFr hs hs'

    have hred := red_smulPt O hFr φκ hFrφ τ hτ s
    have hsx' : NeronModelInfra.schemeHomOverComp ⟨resPt A, rfl⟩ s = O.ptsSp (GluedPic0.mk O.ssFinset x) := by
      rw [← hsx, Equiv.apply_symm_apply]
    have hA4 : Ψ (GluedPic0.mk O.ssFinset x) = GluedPic0.mk O.ssFinset (SemilinearAut.admissibleMap O.ssFinset frob hstab x) :=
      (hΨ _).trans <| (congrArg (fun t => O.ptsSp.symm (GoodReductionJacobian.schemeHomOverComp τ.1 τ.2 t)) hsx'.symm).trans <|
        (congrArg O.ptsSp.symm hred).symm.trans <|
          (congrArg (fun t => O.ptsSp.symm (NeronModelInfra.schemeHomOverComp ⟨resPt A, rfl⟩ t)) hseq).symm.trans hs'x
    exact hA4.trans (GluedPic0.glueMap_mk O.ssFinset _ hstab x).symm

  have key := DFunLike.congr_fun (AddMonoidHom.eq_of_eqOn_dense hA67 hagree) (O.ptsSp.symm y)
  exact ((congrArg (fun t => O.ptsSp.symm (GoodReductionJacobian.schemeHomOverComp τ.1 τ.2 t)) (O.ptsSp.apply_symm_apply y)).symm.trans
    ((hΨ _).symm.trans key))

#print axioms solution

end S_ModularCurve_JHNeronObjectAtP_ptsSp_symm_frobeniusTwist_eq_glueMap_of_pointReduction
end P2MW
export P2MW.S_ModularCurve_JHNeronObjectAtP_ptsSp_symm_frobeniusTwist_eq_glueMap_of_pointReduction (solution)
