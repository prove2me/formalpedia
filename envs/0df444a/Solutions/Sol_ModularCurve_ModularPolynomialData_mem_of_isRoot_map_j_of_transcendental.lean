-- Prove2me | solution 1 for ModularCurve.ModularPolynomialData.mem_of_isRoot_map_j_of_transcendental
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:10.583295+00:00
-- url     : https://prove2.me/submissions/763104d4-878a-531a-90b7-72887afb5599

import Mathlib
import Definitions.Def_ModularCurve_X0
import Definitions.Def_HahnSeries_RamificationBound
import Definitions.Def_WeierstrassCurve_Velu
import Definitions.Def_WeierstrassCurve_OddOrderSummingSet
import Definitions.Def_WeierstrassCurve_VeluOrderTwo
import Definitions.Def_WeierstrassCurve_VeluPointMap2
import Definitions.Def_Isogeny_ConditionalCurrency
import Definitions.Def_WeierstrassCurve_GenusOnePlaceGateCentred
import Definitions.Def_ModularCurve_FibrePoly
import Theorems.Thm_ModularCurve_ModularPolynomialData_mem_of_isRoot_map_j_of_transcendental_of_odd
import Theorems.Thm_WeierstrassCurve_Affine_eval_modularPolynomial_map_j_eq_zero_of_isAddCyclic_ker_pointMapOfPushforward
import Theorems.Thm_WeierstrassCurve_exists_velu2FunctionFieldHom_restrictAlong_placeOfPoint_veluPointMap2
import Theorems.Thm_WeierstrassCurve_Affine_ker_pointMapOfPushforward_eq_of_j_eq_of_forall_pointEnd_eq_zsmul
import Theorems.Thm_WeierstrassCurve_Affine_IsogenyEndDatum_exists_forall_pointEnd_eq_zsmul_of_transcendental_j
import Theorems.Thm_WeierstrassCurve_exists_veluFunctionFieldHom_pointMapOfPushforward_ker_eq_zmultiples
import Theorems.Thm_WeierstrassCurve_veluQuotient_oddOrderSummingSet_discriminant_ne_zero
import Theorems.Thm_WeierstrassCurve_veluQuotient_j_mem_of_mem
import Theorems.Thm_WeierstrassCurve_veluQuotient2_Delta_ne_zero
import Theorems.Thm_WeierstrassCurve_isElliptic_veluQuotient2_of_isElliptic
import Theorems.Thm_WeierstrassCurve_natCard_addSubgroup_isAddCyclic_card_eq_dedekindPsi_of_isAlgClosed
import Theorems.Thm_ModularCurve_card_roots_fibrePoly_of_monic
import Theorems.Thm_HahnSeries_isAlgClosed_rat
import Theorems.Thm_WeierstrassCurve_Affine_exists_genusOnePlaceGate_isCentred_and_abelTheorem
import Theorems.Thm_WeierstrassCurve_Affine_CoordinateRing_isDedekindDomain
import Theorems.Thm_WeierstrassCurve_Affine_hasPrincipalDivisors_functionField
import Theorems.Thm_AlgebraicCurve_normFormulaAlong
import Theorems.Thm_AlgebraicCurve_Divisor_pushforwardAlong_pushforwardAlong
import Theorems.Thm_AlgebraicCurve_finiteAlong_comp
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_ModularPolynomialData_mem_of_isRoot_map_j_of_transcendental
p2m_attr_erase "instance" "WeierstrassCurve.Affine.instIsScalarTowerPolynomialRatFuncFunctionField_definitions WeierstrassCurve.Affine.instAlgebraRatFuncFunctionField_definitions WeierstrassCurve.Affine.instIsScalarTowerRatFuncFunctionField_definitions AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation WeierstrassCurve.Affine.CoordinateRing.moduleFinite WeierstrassCurve.Affine.instDecidableEqFunctionField WeierstrassCurve.Affine.CoordinateRing.isIntegral AlgebraicCurve.IsCurveOver.instNontrivialKaehler AlgebraicCurve.IsCurveOver.instFreeKaehler AlgebraicCurve.IsCurveOver.toHasPrincipalDivisors AlgebraicCurve.IsCurveOver.instFiniteResidue instDecEqAlgebraicClosureRat WeierstrassCurve.Affine.Point.instDistribMulActionAlgEquiv WeierstrassCurve.Affine.Point.instModuleZModTorsionBy WeierstrassCurve.Affine.Point.instSMulTorsionBy WeierstrassCurve.Affine.Point.instDistribMulActionTorsionBy WeierstrassCurve.Affine.Point.instSMulAlgEquiv WeierstrassCurve.Affine.Point.instSMulCommClassAlgEquivZModTorsionBy WeierstrassCurve.instIsEllipticBaseChange WeierstrassCurve.Univ.Affine.instAddGroupPointFieldBaseChangeMvPolynomialCoeffIntCurve WeierstrassCurve.Univ.instIsEllipticFieldPointedCurve WeierstrassCurve.Univ.instCommRingPoly ModularCurve.PhiGen.instNeZeroPhiGenCosetA ModularCurve.instFiniteProjectiveLine ModularCurve.unimodularRowSetoid"
p2m_attr_erase "simp" "PeriodPair.weierstrassCurve_a₆ PeriodPair.weierstrassCurve_a₃ PeriodPair.weierstrassCurve_a₁ PeriodPair.ofTau_ω₂ PeriodPair.scale_ω₂ PeriodPair.ofTau_ω₁ PeriodPair.toPoint_zero PeriodPair.toPoint_of_mem PeriodPair.weierstrassCurve_a₂ PeriodPair.ofTau_lattice PeriodPair.scale_ω₁ PeriodPair.weierstrassCurve_a₄ WeierstrassCurve.Affine.ratFuncToFunctionField_algebraMap WeierstrassCurve.Affine.vcY_vcYInv WeierstrassCurve.Affine.vcXInv_vcX WeierstrassCurve.Affine.Point.vcFun_zero WeierstrassCurve.Affine.vcX_vcXInv WeierstrassCurve.Affine.vcYInv_vcY WeierstrassCurve.Affine.Point.vcInvFun_zero AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal AlgebraicCurve.Divisor.evalFun_zero AlgebraicCurve.Place.evalAt_one AlgebraicCurve.Place.congrEquiv_symm_apply AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply AlgebraicCurve.RationalFunctionField.deg_placeOfPoint WeierstrassCurve.Affine.pointHom_mk_C_C WeierstrassCurve.Affine.Point.yc_some WeierstrassCurve.Affine.Point.xc_some WeierstrassCurve.Affine.pointPull_algebraMap WeierstrassCurve.Affine.pointHom_mk_C_X WeierstrassCurve.Affine.pointHom_mk_Y WeierstrassCurve.Affine.placeOf_asIdeal AlgebraicCurve.IsFrobeniusEndo.frobNormRingHom_apply"
p2m_attr_erase "simp" "ModularCurve.frobeniusPushforwardGeomLevelPic0_mk ModularCurve.coe_frobeniusGeomLevelEquiv_apply ModularCurve.coe_frobeniusPushforwardGeomLevelDegZero ModularCurve.heckeFibreGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusGeomLevel_apply_coe ModularCurve.frobeniusPullbackGeomLevelPic0OfIsCurveOver_mk ModularCurve.coe_heckeFibreGeomLevelDegZero ModularCurve.coe_frobeniusPullbackGeomLevelDegZero ModularCurve.frobeniusPullbackGeomLevelPic0_mk ModularCurve.frobeniusPullbackGeomLevel_single ModularCurve.heckeFibreGeomLevelPic0_mk ModularCurve.frobeniusPushforwardGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusPushforwardGeomLevel_single ModularCurve.qExpandAlgC_apply AlgebraicCurve.coe_frobeniusPushforwardDegZero AlgebraicCurve.IsFrobeniusEndo.coe_frobeniusPullbackDegZero ModularCurve.jqNModC_one ModularCurve.aeval_heckeGen ModularCurve.coe_mTorsionGaloisRep_apply ModularCurve.eisensteinSystem_of_dvd ModularCurve.eisensteinSystem_of_not_dvd FreyPackage.mk.sizeOf_spec FreyPackage.mk.injEq WeierstrassCurve.Affine.Point.galoisRepModuleEnd_apply compl₂EDSAux_neg_two compl₂EDSAux_zero WeierstrassCurve.ωe_zero WeierstrassCurve.Univ.pointedCurve_a₁ WeierstrassCurve.Univ.polyToField_polynomial WeierstrassCurve.Coeff.A₁.sizeOf_spec compl₂EDS_zero compl₂EDS_one WeierstrassCurve.Univ.Affine.smulY_zero Param.C.sizeOf_spec EllSequence.redInvarDenom_zero compl₂EDSAux_two compl₂EDSAux_neg_one compl₂EDSAux_one WeierstrassCurve.Coeff.A₆.sizeOf_spec WeierstrassCurve.ψc_neg"
p2m_attr_erase "simp" "WeierstrassCurve.Univ.Affine.smulY_one WeierstrassCurve.Univ.Affine.smulX_one WeierstrassCurve.Coeff.A₂.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₄ compl₂EDS_neg WeierstrassCurve.Univ.pointedCurve_a₃ EllSequence.redInvarDenom_two WeierstrassCurve.Univ.pointedCurve_a₆ Param.D.sizeOf_spec WeierstrassCurve.ωe_one WeierstrassCurve.Univ.Affine.smulX_zero WeierstrassCurve.Coeff.A₃.sizeOf_spec EllSequence.redInvarDenom_one WeierstrassCurve.Coeff.A₄.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₂ Param.B.sizeOf_spec compl₂EDS_two ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ ModularCurve.coeffEmb_coeff ModularCurve.coeffMap_coeff ModularCurve.coeffMap_id ModularCurve.coeffMap_single ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero"
p2m_attr_erase "simp" "ModularForm.val_upperTriangularGL WeierstrassCurve.veluY_empty WeierstrassCurve.veluX_empty AddMonoid.End.DualEndData.symm_trace AddMonoid.End.dualEndData_intCast_norm AddMonoid.End.DualEndData.ofCharPoly_norm AddMonoid.End.DualEndData.mk.sizeOf_spec AddMonoid.End.DualEndData.mk.injEq AddMonoid.End.DualEndData.ofCharPoly_dual AddMonoid.End.dualEndData_intCast_dual AddMonoid.End.DualEndData.intLinComb_norm AddMonoid.End.DualEndData.ofCharPoly_trace AddMonoid.End.DualEndData.intLinComb_dual AddMonoid.End.DualEndData.symm_dual AddMonoid.End.DualEndData.intLinComb_trace AddMonoid.End.dualEndData_intCast_trace AddMonoid.End.DualEndData.symm_norm ModularCurve.ProjectiveLine.map_mk"

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 6400000
set_option synthInstance.maxHeartbeats 1600000

noncomputable section

open AlgebraicCurve

namespace WeierstrassCurve
p2m_export "WeierstrassCurve" "Affine isUnit_Δ a₃ a₁ map b₂ a₄ a₂ a₆ Affine.Point.some Affine.Point.zero_def IsIntegral toAffine Affine.Point Δ Affine.Y_eq_of_X_eq Affine.Point.neg_some j veluGx veluGy veluGy_eq_zero_of_negY_eq veluQuotient oddOrderSummingSet mem_oddOrderSummingSet veluQuotient2 veluQuotient2_a₁ veluQuotient2_a₂ veluQuotient2_a₃ veluQuotient2_a₄ veluQuotient2_a₆ velu2X velu2Y veluPointMap2 veluPointMap2_zero veluPointMap2_some_of_eq veluPointMap2_some_of_ne Affine.eval_modularPolynomial_map_j_eq_zero_of_isAddCyclic_ker_pointMapOfPushforward exists_velu2FunctionFieldHom_restrictAlong_placeOfPoint_veluPointMap2 Affine.ker_pointMapOfPushforward_eq_of_j_eq_of_forall_pointEnd_eq_zsmul exists_veluFunctionFieldHom_pointMapOfPushforward_ker_eq_zmultiples veluQuotient_oddOrderSummingSet_discriminant_ne_zero veluQuotient_j_mem_of_mem veluQuotient2_Delta_ne_zero isElliptic_veluQuotient2_of_isElliptic natCard_addSubgroup_isAddCyclic_card_eq_dedekindPsi_of_isAlgClosed"
namespace Affine
p2m_export "WeierstrassCurve.Affine" "Equation negY CoordinateRing map Point.some Nonsingular Point.zero_def FunctionField Point Y_eq_of_X_eq Point.neg_some pointMapOfPushforward pointMapOfPushforward_apply pointMapOfPushforward_eq_of_seam IsogenyEndDatum GenusOnePlaceGate pointClass AbelTheorem genusOnePic0Equiv genusOnePic0Equiv_symm_apply GenusOnePlaceGate.IsCentred eval_modularPolynomial_map_j_eq_zero_of_isAddCyclic_ker_pointMapOfPushforward ker_pointMapOfPushforward_eq_of_j_eq_of_forall_pointEnd_eq_zsmul IsogenyEndDatum.exists_forall_pointEnd_eq_zsmul_of_transcendental_j exists_genusOnePlaceGate_isCentred_and_abelTheorem CoordinateRing.isDedekindDomain hasPrincipalDivisors_functionField"
p2m_open "WeierstrassCurve.Affine WeierstrassCurve"

scoped instance instHasPrincipalDivisorsFunctionField_a68p {F : Type*} [Field F] [CharZero F]
    {W : Affine F} : HasPrincipalDivisors F W.FunctionField :=
  hasPrincipalDivisors_functionField W

section AutoNorm

variable {F : Type*} [Field F] [DecidableEq F] [IsAlgClosed F] [CharZero F]
variable {V W : Affine F} [V.IsElliptic] [W.IsElliptic]

theorem normFormulaAlong_of_elliptic (ι : V.FunctionField →ₐ[F] W.FunctionField)
    (hfin : FiniteAlong F ι) : NormFormulaAlong F ι hfin := by
  haveI : CharZero V.FunctionField :=
    charZero_of_injective_algebraMap (algebraMap F V.FunctionField).injective
  have hsep : SeparableAlong F ι := by
    letI := algebraAlong ι
    haveI := isScalarTower_along ι
    haveI : Module.Finite V.FunctionField W.FunctionField := hfin
    show Algebra.IsSeparable V.FunctionField W.FunctionField
    infer_instance
  exact AlgebraicCurve.normFormulaAlong ι hfin hsep

end AutoNorm

section Functoriality

universe u

variable {F : Type u} [Field F] [DecidableEq F] [IsAlgClosed F] [CharZero F]
variable {A B C : Affine F}
  [A.IsElliptic] [GenusOnePlaceGate A] [AbelTheorem A]
  [B.IsElliptic] [GenusOnePlaceGate B] [AbelTheorem B]
  [C.IsElliptic] [GenusOnePlaceGate C] [AbelTheorem C]

theorem Pic0_pushforwardAlongHom_comp
    (f : B.FunctionField →ₐ[F] A.FunctionField) (hf : f.toRingHom.IsIntegral)
    (hfinf : FiniteAlong F f) (hNf : NormFormulaAlong F f hfinf)
    (g : C.FunctionField →ₐ[F] B.FunctionField) (hg : g.toRingHom.IsIntegral)
    (hfing : FiniteAlong F g) (hNg : NormFormulaAlong F g hfing)
    (hfg : (f.comp g).toRingHom.IsIntegral) (hfinfg : FiniteAlong F (f.comp g))
    (hNfg : NormFormulaAlong F (f.comp g) hfinfg)
    (x : Pic0 F A.FunctionField) :
    Pic0.pushforwardAlongHom g hg hfing hNg (Pic0.pushforwardAlongHom f hf hfinf hNf x)
      = Pic0.pushforwardAlongHom (f.comp g) hfg hfinfg hNfg x := by
  obtain ⟨D, rfl⟩ := Pic0.mk_surjective x
  rw [Pic0.pushforwardAlongHom_mk, Pic0.pushforwardAlongHom_mk, Pic0.pushforwardAlongHom_mk]
  refine congrArg _ ?_
  refine Subtype.ext ?_
  rw [Pic0.coe_pushforwardAlongDegZero, Pic0.coe_pushforwardAlongDegZero,
    Pic0.coe_pushforwardAlongDegZero]
  exact Divisor.pushforwardAlong_pushforwardAlong g f hg hf hfg (D : Divisor F A.FunctionField)

theorem pointMapOfPushforward_comp
    (f : B.FunctionField →ₐ[F] A.FunctionField) (hf : f.toRingHom.IsIntegral)
    (hfinf : FiniteAlong F f) (hNf : NormFormulaAlong F f hfinf)
    (g : C.FunctionField →ₐ[F] B.FunctionField) (hg : g.toRingHom.IsIntegral)
    (hfing : FiniteAlong F g) (hNg : NormFormulaAlong F g hfing)
    (hfg : (f.comp g).toRingHom.IsIntegral) (hfinfg : FiniteAlong F (f.comp g))
    (hNfg : NormFormulaAlong F (f.comp g) hfinfg) (P : A.Point) :
    pointMapOfPushforward (f.comp g) hfg hfinfg hNfg P
      = pointMapOfPushforward g hg hfing hNg (pointMapOfPushforward f hf hfinf hNf P) := by
  have key : ∀ x : Pic0 F B.FunctionField, pointClass (genusOnePic0Equiv B x) = x := fun x => by
    rw [← genusOnePic0Equiv_symm_apply, AddEquiv.symm_apply_apply]
  rw [pointMapOfPushforward_apply, pointMapOfPushforward_apply, pointMapOfPushforward_apply, key,
    Pic0_pushforwardAlongHom_comp f hf hfinf hNf g hg hfing hNg hfg hfinfg hNfg]

end Functoriality

end WeierstrassCurve.Affine
p2m_reactivate "P2MW.S_ModularCurve_ModularPolynomialData_mem_of_isRoot_map_j_of_transcendental.WeierstrassCurve P2MW.S_ModularCurve_ModularPolynomialData_mem_of_isRoot_map_j_of_transcendental.WeierstrassCurve.Affine"
p2m_reactivate "P2MW.S_ModularCurve_ModularPolynomialData_mem_of_isRoot_map_j_of_transcendental.WeierstrassCurve"

namespace A68

p2m_open "WeierstrassCurve P2MW.S_ModularCurve_ModularPolynomialData_mem_of_isRoot_map_j_of_transcendental.WeierstrassCurve WeierstrassCurve.Affine P2MW.S_ModularCurve_ModularPolynomialData_mem_of_isRoot_map_j_of_transcendental.WeierstrassCurve.Affine AlgebraicCurve Polynomial"

attribute [local instance] Classical.propDecidable

section Generic

variable {F : Type} [Field F] [DecidableEq F] [IsAlgClosed F] [CharZero F]

theorem oddOrderSummingSet_coords_mem (W : WeierstrassCurve F) (L : Subfield F) {n : ℕ}
    {Q : W.toAffine.Point} (hord : addOrderOf Q = 2 * n + 1)
    (hcoord : ∀ (k : ℕ) (x y : F) (h : W.toAffine.Nonsingular x y),
      k • Q = Point.some x y h → x ∈ L ∧ y ∈ L) :
    ∀ P ∈ W.oddOrderSummingSet Q n, P.1 ∈ L ∧ P.2 ∈ L := by
  intro P hP
  obtain ⟨k, hk1, hkn, hkP⟩ := W.mem_oddOrderSummingSet.mp hP
  have hkQne : k • Q ≠ 0 := by
    intro h
    rw [← addOrderOf_dvd_iff_nsmul_eq_zero, hord] at h
    exact absurd (Nat.le_of_dvd hk1 h) (by omega)
  rcases hkQ : (k • Q) with _ | ⟨x, y, hns⟩
  · exact absurd hkQ hkQne
  rw [← hkP, hkQ]
  exact hcoord k x y hns hkQ

theorem exists_generator_of_isAddCyclic {G : Type*} [AddCommGroup G] (H : AddSubgroup G)
    (hc : IsAddCyclic H) {m : ℕ} (hm : Nat.card H = m) :
    ∃ g : G, AddSubgroup.zmultiples g = H ∧ addOrderOf g = m := by
  obtain ⟨⟨g, hgH⟩, hg⟩ := hc.exists_generator
  have hzm : AddSubgroup.zmultiples g = H := by
    apply le_antisymm (AddSubgroup.zmultiples_le.mpr hgH)
    intro x hx
    obtain ⟨k, hk⟩ := AddSubgroup.mem_zmultiples_iff.mp (hg ⟨x, hx⟩)
    exact AddSubgroup.mem_zmultiples_iff.mpr ⟨k, by simpa using congrArg Subtype.val hk⟩
  refine ⟨g, hzm, ?_⟩
  rw [← Nat.card_zmultiples g, hzm, hm]

set_option genInjectivity false in
structure IsoTarget (W : WeierstrassCurve F) [W.IsElliptic] [GenusOnePlaceGate W.toAffine]
    [AbelTheorem W.toAffine] (g : W.toAffine.Point) (L : Subfield F) where
  V : WeierstrassCurve F
  [ell : V.IsElliptic]
  [gate : GenusOnePlaceGate V.toAffine]
  [centred : GenusOnePlaceGate.IsCentred V.toAffine]
  [abel : AbelTheorem V.toAffine]
  ι : V.toAffine.FunctionField →ₐ[F] W.toAffine.FunctionField
  hι : ι.toRingHom.IsIntegral
  hfin : FiniteAlong F ι
  j_mem : V.j ∈ L
  ker_eq : ∀ hN : NormFormulaAlong F ι hfin,
    (pointMapOfPushforward ι hι hfin hN).ker = AddSubgroup.zmultiples g

theorem isoTarget_odd (n : ℕ) (W : WeierstrassCurve F) [W.IsElliptic]
    [GenusOnePlaceGate W.toAffine] [GenusOnePlaceGate.IsCentred W.toAffine]
    [AbelTheorem W.toAffine] (L : Subfield F)
    (h₁ : W.a₁ ∈ L) (h₂ : W.a₂ ∈ L) (h₃ : W.a₃ ∈ L) (h₄ : W.a₄ ∈ L) (h₆ : W.a₆ ∈ L)
    (g : W.toAffine.Point) (hg : addOrderOf g = 2 * n + 1)
    (hcoord : ∀ (k : ℕ) (x y : F) (h : W.toAffine.Nonsingular x y),
      k • g = Point.some x y h → x ∈ L ∧ y ∈ L) :
    Nonempty (IsoTarget W g L) := by
  have hΔ' : (W.veluQuotient (W.oddOrderSummingSet g n)).Δ ≠ 0 :=
    WeierstrassCurve.veluQuotient_oddOrderSummingSet_discriminant_ne_zero two_ne_zero W n g hg
  haveI hell : (W.veluQuotient (W.oddOrderSummingSet g n)).IsElliptic :=
    ⟨isUnit_iff_ne_zero.mpr hΔ'⟩
  haveI : IsDedekindDomain (W.veluQuotient (W.oddOrderSummingSet g n)).toAffine.CoordinateRing :=
    CoordinateRing.isDedekindDomain (W.veluQuotient (W.oddOrderSummingSet g n))
  obtain ⟨gV, hcV, haV⟩ := exists_genusOnePlaceGate_isCentred_and_abelTheorem
    (W := (W.veluQuotient (W.oddOrderSummingSet g n)).toAffine)
  letI := gV
  haveI := hcV
  haveI := haV
  obtain ⟨ι, hι, hfin, -, hker⟩ :=
    WeierstrassCurve.exists_veluFunctionFieldHom_pointMapOfPushforward_ker_eq_zmultiples hg hΔ'
  have hj : (W.veluQuotient (W.oddOrderSummingSet g n)).j ∈ L :=
    WeierstrassCurve.veluQuotient_j_mem_of_mem W L _ h₁ h₂ h₃ h₄ h₆
      (oddOrderSummingSet_coords_mem W L hg hcoord) hΔ'
  exact ⟨{ V := W.veluQuotient (W.oddOrderSummingSet g n), ι := ι, hι := hι, hfin := hfin,
           j_mem := hj, ker_eq := hker }⟩

theorem veluGx_mem (W : WeierstrassCurve F) (L : Subfield F)
    (h₁ : W.a₁ ∈ L) (h₂ : W.a₂ ∈ L) (h₄ : W.a₄ ∈ L) {x₀ y₀ : F} (hx : x₀ ∈ L) (hy : y₀ ∈ L) :
    W.veluGx x₀ y₀ ∈ L := by
  unfold WeierstrassCurve.veluGx
  have h3 : (3 : F) ∈ L := by simpa using natCast_mem L 3
  have h2' : (2 : F) ∈ L := by simpa using natCast_mem L 2
  exact sub_mem (add_mem (add_mem (mul_mem h3 (pow_mem hx 2)) (mul_mem (mul_mem h2' h₂) hx)) h₄)
    (mul_mem h₁ hy)

theorem isoTarget_even_step (M : ℕ) (hM : 0 < M)
    (ih : ∀ (W' : WeierstrassCurve F) [W'.IsElliptic] [GenusOnePlaceGate W'.toAffine]
      [GenusOnePlaceGate.IsCentred W'.toAffine] [AbelTheorem W'.toAffine] (L : Subfield F),
      W'.a₁ ∈ L → W'.a₂ ∈ L → W'.a₃ ∈ L → W'.a₄ ∈ L → W'.a₆ ∈ L →
      ∀ g' : W'.toAffine.Point, addOrderOf g' = M →
      (∀ (k : ℕ) (x y : F) (h : W'.toAffine.Nonsingular x y),
        k • g' = Point.some x y h → x ∈ L ∧ y ∈ L) → Nonempty (IsoTarget W' g' L))
    (W : WeierstrassCurve F) [W.IsElliptic]
    [GenusOnePlaceGate W.toAffine] [GenusOnePlaceGate.IsCentred W.toAffine]
    [AbelTheorem W.toAffine] (L : Subfield F)
    (h₁ : W.a₁ ∈ L) (h₂ : W.a₂ ∈ L) (h₃ : W.a₃ ∈ L) (h₄ : W.a₄ ∈ L) (h₆ : W.a₆ ∈ L)
    (g : W.toAffine.Point) (hg : addOrderOf g = 2 * M)
    (hcoord : ∀ (k : ℕ) (x y : F) (h : W.toAffine.Nonsingular x y),
      k • g = Point.some x y h → x ∈ L ∧ y ∈ L) :
    Nonempty (IsoTarget W g L) := by

  have hQne : M • g ≠ 0 := by
    intro h
    have hdvd := addOrderOf_dvd_of_nsmul_eq_zero h
    rw [hg] at hdvd
    exact absurd (Nat.le_of_dvd hM hdvd) (by omega)
  have hQQ : M • g + M • g = 0 := by
    rw [← add_nsmul, ← two_mul, ← hg]; exact addOrderOf_nsmul_eq_zero g
  rcases hQ : (M • g) with _ | ⟨x₀, y₀, hns⟩
  · exact absurd hQ hQne
  rw [hQ] at hQQ
  have hneg : -(Point.some x₀ y₀ hns : W.toAffine.Point) = Point.some x₀ y₀ hns :=
    neg_eq_iff_add_eq_zero.mpr hQQ
  rw [Affine.Point.neg_some] at hneg
  have hy : W.toAffine.negY x₀ y₀ = y₀ := by injection hneg
  have hgy : W.veluGy x₀ y₀ = 0 := WeierstrassCurve.veluGy_eq_zero_of_negY_eq (W := W) hy
  have hQeq : W.toAffine.Equation x₀ y₀ := hns.1
  obtain ⟨hx₀L, hy₀L⟩ := hcoord M x₀ y₀ hns hQ

  have hΔW : W.Δ ≠ 0 := W.isUnit_Δ.ne_zero
  have hΔ₁ : (W.veluQuotient2 x₀ y₀).Δ ≠ 0 := WeierstrassCurve.veluQuotient2_Delta_ne_zero hΔW hQeq hgy
  haveI : (W.veluQuotient2 x₀ y₀).IsElliptic :=
    WeierstrassCurve.isElliptic_veluQuotient2_of_isElliptic hQeq hgy
  haveI : IsDedekindDomain (W.veluQuotient2 x₀ y₀).toAffine.CoordinateRing :=
    CoordinateRing.isDedekindDomain (W.veluQuotient2 x₀ y₀)
  obtain ⟨gV, hcV, haV⟩ := exists_genusOnePlaceGate_isCentred_and_abelTheorem
    (W := (W.veluQuotient2 x₀ y₀).toAffine)
  letI := gV
  haveI := hcV
  haveI := haV

  obtain ⟨ι₁, hι₁, hfin₁, hseam⟩ :=
    WeierstrassCurve.exists_velu2FunctionFieldHom_restrictAlong_placeOfPoint_veluPointMap2 hQeq hgy hΔ₁
  have hN₁ : NormFormulaAlong F ι₁ hfin₁ := normFormulaAlong_of_elliptic ι₁ hfin₁
  set p₁ := pointMapOfPushforward ι₁ hι₁ hfin₁ hN₁ with hp₁_def
  have hp₁ : ∀ P, p₁ P = WeierstrassCurve.veluPointMap2 two_ne_zero hQeq hgy hΔ₁ P :=
    pointMapOfPushforward_eq_of_seam ι₁ hι₁ hfin₁ hN₁ _
      (by rw [Affine.Point.zero_def]; exact WeierstrassCurve.veluPointMap2_zero _ _ _ _) hseam

  have hp₁Q : p₁ (Point.some x₀ y₀ hns) = 0 := by
    rw [hp₁, WeierstrassCurve.veluPointMap2_some_of_eq two_ne_zero hQeq hgy hΔ₁ hns rfl,
      Affine.Point.zero_def]
  have hker₁ : ∀ P : W.toAffine.Point, p₁ P = 0 → P = 0 ∨ P = Point.some x₀ y₀ hns := by
    intro P hP
    rcases P with _ | ⟨x, y, h⟩
    · exact Or.inl Affine.Point.zero_def.symm
    · right
      by_cases hx : x = x₀
      · rcases Affine.Y_eq_of_X_eq h.1 hns.1 hx with hyy | hyy
        · subst hx; subst hyy; rfl
        · subst hx; rw [hy] at hyy; subst hyy; rfl
      · rw [hp₁, WeierstrassCurve.veluPointMap2_some_of_ne two_ne_zero hQeq hgy hΔ₁ h hx,
          Affine.Point.zero_def] at hP
        cases hP

  have hg₁ord : addOrderOf (p₁ g) = M := by
    refine (addOrderOf_eq_iff hM).mpr ⟨?_, ?_⟩
    · rw [← map_nsmul, hQ, hp₁Q]
    · intro k hkM hk0 hk
      rw [← map_nsmul] at hk
      rcases hker₁ _ hk with hk' | hk'
      · have hdvd := addOrderOf_dvd_of_nsmul_eq_zero hk'
        rw [hg] at hdvd
        exact absurd (Nat.le_of_dvd hk0 hdvd) (by omega)
      · have hsub : (M - k) • g = 0 := by
          have : (M - k) • g + k • g = M • g := by
            rw [← add_nsmul, Nat.sub_add_cancel hkM.le]
          rw [hk', ← hQ] at this
          exact add_eq_right.mp this
        have hdvd := addOrderOf_dvd_of_nsmul_eq_zero hsub
        rw [hg] at hdvd
        exact absurd (Nat.le_of_dvd (by omega) hdvd) (by omega)

  have hgx : W.veluGx x₀ y₀ ∈ L := veluGx_mem W L h₁ h₂ h₄ hx₀L hy₀L
  have hcoord₁ : ∀ (k : ℕ) (x y : F) (h : (W.veluQuotient2 x₀ y₀).toAffine.Nonsingular x y),
      k • p₁ g = Point.some x y h → x ∈ L ∧ y ∈ L := by
    intro k x y h hk
    rw [← map_nsmul, hp₁] at hk
    rcases hkg : (k • g) with _ | ⟨x', y', h'⟩
    · rw [hkg, WeierstrassCurve.veluPointMap2_zero] at hk; cases hk
    · rw [hkg] at hk
      by_cases hx' : x' = x₀
      · rw [WeierstrassCurve.veluPointMap2_some_of_eq two_ne_zero hQeq hgy hΔ₁ h' hx'] at hk
        cases hk
      · rw [WeierstrassCurve.veluPointMap2_some_of_ne two_ne_zero hQeq hgy hΔ₁ h' hx'] at hk
        obtain ⟨hxL, hyL⟩ := hcoord k x' y' h' hkg
        have hxx : W.velu2X x₀ y₀ x' = x ∧ W.velu2Y x₀ y₀ x' y' = y := by
          injection hk with hxe hye; exact ⟨hxe, hye⟩
        obtain ⟨hxe, hye⟩ := hxx
        refine ⟨?_, ?_⟩
        · rw [← hxe]; unfold WeierstrassCurve.velu2X
          exact add_mem hxL (div_mem hgx (sub_mem hxL hx₀L))
        · rw [← hye]; unfold WeierstrassCurve.velu2Y
          exact sub_mem hyL (div_mem (mul_mem hgx (sub_mem (add_mem (mul_mem h₁ (sub_mem hxL hx₀L))
            hyL) hy₀L)) (pow_mem (sub_mem hxL hx₀L) 2))

  have hb₂ : W.b₂ ∈ L := by
    unfold WeierstrassCurve.b₂
    have h4 : (4 : F) ∈ L := by simpa using natCast_mem L 4
    exact add_mem (pow_mem h₁ 2) (mul_mem h4 h₂)
  have h₄' : (W.veluQuotient2 x₀ y₀).a₄ ∈ L := by
    rw [WeierstrassCurve.veluQuotient2_a₄]
    have h5 : (5 : F) ∈ L := by simpa using natCast_mem L 5
    exact sub_mem h₄ (mul_mem h5 hgx)
  have h₆' : (W.veluQuotient2 x₀ y₀).a₆ ∈ L := by
    rw [WeierstrassCurve.veluQuotient2_a₆]
    have h7 : (7 : F) ∈ L := by simpa using natCast_mem L 7
    exact sub_mem (sub_mem h₆ (mul_mem hb₂ hgx)) (mul_mem h7 (mul_mem hx₀L hgx))

  obtain ⟨T₂⟩ := ih (W.veluQuotient2 x₀ y₀) L
    (by rw [WeierstrassCurve.veluQuotient2_a₁]; exact h₁)
    (by rw [WeierstrassCurve.veluQuotient2_a₂]; exact h₂)
    (by rw [WeierstrassCurve.veluQuotient2_a₃]; exact h₃) h₄' h₆' (p₁ g) hg₁ord hcoord₁
  letI := T₂.gate
  haveI := T₂.ell
  haveI := T₂.centred
  haveI := T₂.abel
  have hN₂ : NormFormulaAlong F T₂.ι T₂.hfin := normFormulaAlong_of_elliptic T₂.ι T₂.hfin
  set p₂ := pointMapOfPushforward T₂.ι T₂.hι T₂.hfin hN₂ with hp₂_def
  have hker₂ : p₂.ker = AddSubgroup.zmultiples (p₁ g) := T₂.ker_eq hN₂

  have hι : (ι₁.comp T₂.ι).toRingHom.IsIntegral := RingHom.IsIntegral.trans _ _ T₂.hι hι₁
  have hfin : FiniteAlong F (ι₁.comp T₂.ι) := finiteAlong_comp T₂.ι ι₁ T₂.hfin hfin₁
  have hker : ∀ hN : NormFormulaAlong F (ι₁.comp T₂.ι) hfin,
      (pointMapOfPushforward (ι₁.comp T₂.ι) hι hfin hN).ker = AddSubgroup.zmultiples g := by
    intro hN
    have hcomp : ∀ P, pointMapOfPushforward (ι₁.comp T₂.ι) hι hfin hN P = p₂ (p₁ P) := fun P =>
      pointMapOfPushforward_comp ι₁ hι₁ hfin₁ hN₁ T₂.ι T₂.hι T₂.hfin hN₂ hι hfin hN P
    refine AddSubgroup.ext fun P => ?_
    rw [AddMonoidHom.mem_ker, hcomp]
    constructor
    · intro hP
      have hP' : p₁ P ∈ p₂.ker := AddMonoidHom.mem_ker.mpr hP
      rw [hker₂, AddSubgroup.mem_zmultiples_iff] at hP'
      obtain ⟨k, hk⟩ := hP'
      have hdiff : p₁ (P - k • g) = 0 := by rw [map_sub, map_zsmul, hk, sub_self]
      rcases hker₁ _ hdiff with h0 | h0
      · rw [sub_eq_zero] at h0
        rw [h0]; exact AddSubgroup.zsmul_mem _ (AddSubgroup.mem_zmultiples g) k
      · rw [sub_eq_iff_eq_add] at h0
        rw [h0, ← hQ]
        exact AddSubgroup.add_mem _ (AddSubgroup.nsmul_mem _ (AddSubgroup.mem_zmultiples g) M)
          (AddSubgroup.zsmul_mem _ (AddSubgroup.mem_zmultiples g) k)
    · intro hP
      obtain ⟨k, rfl⟩ := AddSubgroup.mem_zmultiples_iff.mp hP
      have : p₂ (p₁ g) = 0 := by
        have hmem : p₁ g ∈ p₂.ker := by rw [hker₂]; exact AddSubgroup.mem_zmultiples _
        exact AddMonoidHom.mem_ker.mp hmem
      rw [map_zsmul, map_zsmul, this, zsmul_zero]
  exact ⟨{ V := T₂.V, ι := ι₁.comp T₂.ι, hι := hι, hfin := hfin, j_mem := T₂.j_mem,
           ker_eq := hker }⟩

theorem exists_isoTarget (N : ℕ) :
    ∀ (W : WeierstrassCurve F) [W.IsElliptic] [GenusOnePlaceGate W.toAffine]
      [GenusOnePlaceGate.IsCentred W.toAffine] [AbelTheorem W.toAffine] (L : Subfield F),
      W.a₁ ∈ L → W.a₂ ∈ L → W.a₃ ∈ L → W.a₄ ∈ L → W.a₆ ∈ L →
      ∀ g : W.toAffine.Point, 0 < N → addOrderOf g = N →
      (∀ (k : ℕ) (x y : F) (h : W.toAffine.Nonsingular x y),
        k • g = Point.some x y h → x ∈ L ∧ y ∈ L) → Nonempty (IsoTarget W g L) := by
  induction N using Nat.strong_induction_on with
  | _ N ih =>
    intro W _ _ _ _ L h₁ h₂ h₃ h₄ h₆ g hN hg hcoord
    rcases Nat.even_or_odd N with ⟨M, rfl⟩ | ⟨n, rfl⟩
    · have hM : 0 < M := by omega
      exact isoTarget_even_step M hM
        (fun W' _ _ _ _ L' h₁' h₂' h₃' h₄' h₆' g' hg' hcoord' =>
          ih M (by omega) W' L' h₁' h₂' h₃' h₄' h₆' g' hM hg' hcoord')
        W L h₁ h₂ h₃ h₄ h₆ g (by rw [hg]; ring) hcoord
    · exact isoTarget_odd n W L h₁ h₂ h₃ h₄ h₆ g hg hcoord

theorem main {N : ℕ} [NeZero N] (data : ModularCurve.ModularPolynomialData N)
    (W : WeierstrassCurve F) [W.IsElliptic] (ht : Transcendental ℚ W.j) (L : Subfield F)
    (h₁ : W.a₁ ∈ L) (h₂ : W.a₂ ∈ L) (h₃ : W.a₃ ∈ L) (h₄ : W.a₄ ∈ L) (h₆ : W.a₆ ∈ L)
    (htors : ∀ (x y : F) (h : W.toAffine.Nonsingular x y),
      N • (Point.some x y h : W.toAffine.Point) = 0 → x ∈ L ∧ y ∈ L)
    (r : F) (hr : (data.Φ.map (Polynomial.eval₂RingHom (Int.castRingHom F) W.j)).IsRoot r) :
    r ∈ L := by
  classical

  haveI : IsDedekindDomain W.toAffine.CoordinateRing := CoordinateRing.isDedekindDomain W
  obtain ⟨gW, hcW, haW⟩ := exists_genusOnePlaceGate_isCentred_and_abelTheorem (W := W.toAffine)
  letI := gW
  haveI := hcW
  haveI := haW
  have hNs : ∀ D : IsogenyEndDatum W.toAffine, NormFormulaAlong F D.ι D.hfin := fun D =>
    normFormulaAlong_of_elliptic D.ι D.hfin
  have hEnd : ∀ D : IsogenyEndDatum W.toAffine, ∃ m : ℤ, ∀ P : W.toAffine.Point,
      D.pointEnd (hNs D) P = m • P := fun D =>
    IsogenyEndDatum.exists_forall_pointEnd_eq_zsmul_of_transcendental_j W hNs ht D
  have hN0 : 0 < N := Nat.pos_of_ne_zero (NeZero.ne N)
  have hNK : ((N : ℕ) : F) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne N)
  set Φj := data.Φ.map (Polynomial.eval₂RingHom (Int.castRingHom F) W.j) with hΦj
  have hΦjm : Φj.Monic := data.monic.map _

  let B := {H : AddSubgroup W.toAffine.Point // IsAddCyclic H ∧ Nat.card H = N}
  have hBcard : Nat.card B = ModularCurve.dedekindPsi N :=
    WeierstrassCurve.natCard_addSubgroup_isAddCyclic_card_eq_dedekindPsi_of_isAlgClosed
      (F := F) (K := F) W hNK
  have hψpos : 0 < ModularCurve.dedekindPsi N := by
    unfold ModularCurve.dedekindPsi
    refine Finset.sum_pos' (fun _ _ => Nat.zero_le _) ⟨1, ?_, ?_⟩
    · simp [Nat.mem_divisors, NeZero.ne N]
    · simp [hN0]
  haveI : Finite B := Nat.finite_of_card_ne_zero (hBcard ▸ hψpos.ne')
  haveI : Fintype B := Fintype.ofFinite _

  have hgen : ∀ H : B, ∃ g : W.toAffine.Point, AddSubgroup.zmultiples g = H.1 ∧ addOrderOf g = N :=
    fun H => exists_generator_of_isAddCyclic H.1 H.2.1 H.2.2
  choose gen hgenH hgenord using hgen
  have hcoord : ∀ (H : B) (k : ℕ) (x y : F) (h : W.toAffine.Nonsingular x y),
      k • gen H = Point.some x y h → x ∈ L ∧ y ∈ L := by
    intro H k x y h hk
    apply htors
    rw [← hk, smul_comm, (hgenord H ▸ addOrderOf_nsmul_eq_zero (gen H) : N • gen H = 0), smul_zero]

  let T : ∀ H : B, IsoTarget W (gen H) L := fun H =>
    Classical.choice (exists_isoTarget N W L h₁ h₂ h₃ h₄ h₆ (gen H) hN0 (hgenord H) (hcoord H))
  let jH : B → F := fun H =>
    haveI := (T H).ell
    (T H).V.j

  have hjHmem : ∀ H : B, jH H ∈ L := fun H => (T H).j_mem

  have hjHroot : ∀ H : B, Φj.IsRoot (jH H) := by
    intro H
    letI := (T H).gate
    haveI := (T H).ell
    haveI := (T H).centred
    haveI := (T H).abel
    have hN' : NormFormulaAlong F (T H).ι (T H).hfin := normFormulaAlong_of_elliptic _ _
    have hker := (T H).ker_eq hN'
    have hcyc : IsAddCyclic (pointMapOfPushforward (T H).ι (T H).hι (T H).hfin hN').ker := by
      rw [hker]; infer_instance
    have hcard : Nat.card (pointMapOfPushforward (T H).ι (T H).hι (T H).hfin hN').ker = N := by
      rw [hker, Nat.card_zmultiples, hgenord]
    exact WeierstrassCurve.Affine.eval_modularPolynomial_map_j_eq_zero_of_isAddCyclic_ker_pointMapOfPushforward
      F W.toAffine (T H).V.toAffine (T H).ι (T H).hι (T H).hfin hN' N hcyc hcard data

  have hjHinj : Function.Injective jH := by
    intro H H' hjeq
    letI := (T H).gate
    haveI := (T H).ell
    haveI := (T H).centred
    haveI := (T H).abel
    letI := (T H').gate
    haveI := (T H').ell
    haveI := (T H').centred
    haveI := (T H').abel
    have hN₁ : NormFormulaAlong F (T H).ι (T H).hfin := normFormulaAlong_of_elliptic _ _
    have hN₂ : NormFormulaAlong F (T H').ι (T H').hfin := normFormulaAlong_of_elliptic _ _
    have hker := (T H).ker_eq hN₁
    have hker' := (T H').ker_eq hN₂
    have hcard : Nat.card (pointMapOfPushforward (T H).ι (T H).hι (T H).hfin hN₁).ker
        = Nat.card (pointMapOfPushforward (T H').ι (T H').hι (T H').hfin hN₂).ker := by
      rw [hker, hker', Nat.card_zmultiples, Nat.card_zmultiples, hgenord, hgenord]
    have heq := WeierstrassCurve.Affine.ker_pointMapOfPushforward_eq_of_j_eq_of_forall_pointEnd_eq_zsmul
      W hNs hEnd (T H).V (T H').V (T H).ι (T H).hι (T H).hfin hN₁ (T H').ι (T H').hι (T H').hfin
      hN₂ hcard hjeq
    rw [hker, hker'] at heq
    exact Subtype.ext ((hgenH H).symm.trans (heq.trans (hgenH H')))

  have hJcard : (Finset.univ.image jH).card = ModularCurve.dedekindPsi N := by
    rw [Finset.card_image_of_injective _ hjHinj, Finset.card_univ, ← Nat.card_eq_fintype_card,
      hBcard]
  have hJsub : Finset.univ.image jH ⊆ Φj.roots.toFinset := by
    intro x hx
    obtain ⟨H, -, rfl⟩ := Finset.mem_image.mp hx
    rw [Multiset.mem_toFinset, Polynomial.mem_roots hΦjm.ne_zero]
    exact hjHroot H
  have hroots : Φj.roots.toFinset = Finset.univ.image jH := by
    refine (Finset.eq_of_subset_of_card_le hJsub ?_).symm
    calc Φj.roots.toFinset.card ≤ Multiset.card Φj.roots := Multiset.toFinset_card_le _
      _ = ModularCurve.dedekindPsi N := by
          rw [hΦj, ← data.natDegree_eq]
          exact ModularCurve.card_roots_fibrePoly_of_monic (K := F) data.monic W.j
      _ = (Finset.univ.image jH).card := hJcard.symm

  have hrmem : r ∈ Φj.roots.toFinset := by
    rw [Multiset.mem_toFinset, Polynomial.mem_roots hΦjm.ne_zero]; exact hr
  rw [hroots] at hrmem
  obtain ⟨H, -, rfl⟩ := Finset.mem_image.mp hrmem
  exact hjHmem H

end Generic
p2m_reactivate "P2MW.S_ModularCurve_ModularPolynomialData_mem_of_isRoot_map_j_of_transcendental.WeierstrassCurve P2MW.S_ModularCurve_ModularPolynomialData_mem_of_isRoot_map_j_of_transcendental.WeierstrassCurve.Affine"

end A68
p2m_reactivate "P2MW.S_ModularCurve_ModularPolynomialData_mem_of_isRoot_map_j_of_transcendental.WeierstrassCurve P2MW.S_ModularCurve_ModularPolynomialData_mem_of_isRoot_map_j_of_transcendental.WeierstrassCurve.Affine"

end
p2m_reactivate "P2MW.S_ModularCurve_ModularPolynomialData_mem_of_isRoot_map_j_of_transcendental.WeierstrassCurve P2MW.S_ModularCurve_ModularPolynomialData_mem_of_isRoot_map_j_of_transcendental.WeierstrassCurve.Affine"

theorem solution
    {N : ℕ} [NeZero N] (data : ModularCurve.ModularPolynomialData N)
    [DecidableEq (HahnSeries ℚ (AlgebraicClosure ℚ))]
    (W : WeierstrassCurve (HahnSeries ℚ (AlgebraicClosure ℚ))) [W.IsElliptic] (ht : Transcendental ℚ W.j)
    (L : Subfield (HahnSeries ℚ (AlgebraicClosure ℚ)))
    (h₁ : W.a₁ ∈ L) (h₂ : W.a₂ ∈ L) (h₃ : W.a₃ ∈ L) (h₄ : W.a₄ ∈ L) (h₆ : W.a₆ ∈ L)
    (htors : ∀ (x y : HahnSeries ℚ (AlgebraicClosure ℚ)) (h : W.toAffine.Nonsingular x y),
      N • (WeierstrassCurve.Affine.Point.some x y h : W.toAffine.Point) = 0 → x ∈ L ∧ y ∈ L)
    (r : HahnSeries ℚ (AlgebraicClosure ℚ))
    (hr : (data.Φ.map (Polynomial.eval₂RingHom (Int.castRingHom (HahnSeries ℚ (AlgebraicClosure ℚ))) W.j)).IsRoot r) :
    r ∈ L := by
  by_cases hodd : Odd N
  ·
    exact ModularCurve.ModularPolynomialData.mem_of_isRoot_map_j_of_transcendental_of_odd hodd data W
      ht L h₁ h₂ h₃ h₄ h₆ htors r hr
  · haveI : IsAlgClosed (HahnSeries ℚ (AlgebraicClosure ℚ)) := HahnSeries.isAlgClosed_rat
    haveI : CharZero (HahnSeries ℚ (AlgebraicClosure ℚ)) :=
      (RingHom.charZero_iff (HahnSeries.C (R := AlgebraicClosure ℚ) (Γ := ℚ)).injective).mp
        inferInstance

    have ht' : @Transcendental ℚ (HahnSeries ℚ (AlgebraicClosure ℚ)) _ _
        DivisionRing.toRatAlgebra W.j := by
      convert ht; exact Subsingleton.elim _ _
    exact A68.main data W ht' L h₁ h₂ h₃ h₄ h₆ htors r hr

end S_ModularCurve_ModularPolynomialData_mem_of_isRoot_map_j_of_transcendental
end P2MW
export P2MW.S_ModularCurve_ModularPolynomialData_mem_of_isRoot_map_j_of_transcendental (solution)
