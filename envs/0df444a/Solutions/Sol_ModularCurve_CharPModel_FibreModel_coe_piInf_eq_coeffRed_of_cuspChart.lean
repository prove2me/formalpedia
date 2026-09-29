-- Prove2me | solution 1 for ModularCurve.CharPModel.FibreModel.coe_piInf_eq_coeffRed_of_cuspChart
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:09.007888+00:00
-- url     : https://prove2.me/submissions/331320f7-6ebd-527a-ac80-b5115a5c67d2

import Mathlib
import Definitions.Def_ModularCurve_FibreModelCuspChart
import Definitions.Def_ModularCurve_CharPReduction
import Theorems.Thm_ModularCurve_coeffMap_qExpand
import Theorems.Thm_ModularCurve_transcendental_jqModC
import Theorems.Thm_ModularCurve_functionFieldGeneration
import Theorems.Thm_ModularCurve_isRoot_map_Phi_apply_jBar
import Theorems.Thm_ModularCurve_laurentBaseChange_le_of_divisor_generators_mem
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_CharPModel_FibreModel_coe_piInf_eq_coeffRed_of_cuspChart
p2m_attr_erase "instance" "AlgebraicCurve.instFundamentalIdentityOfSumRamificationInertia AlgebraicCurve.Place.instIsScalarTowerResidueFieldRestrictPushforward AlgebraicCurve.Place.instAlgebraResidueFieldRestrictPushforward AlgebraicCurve.Place.instIsLocalHomRestrictInclusion AlgebraicCurve.SemilinearAut.instDistribMulActionSubtypeProdRingAutMemSubgroupPic0 AlgebraicCurve.SemilinearAut.instDistribMulActionSubtypeProdRingAutMemSubgroupDivisor AlgebraicCurve.Pic0.instModuleZModTorsion AlgebraicCurve.SemilinearAut.instSMulSubtypeProdRingAutMemSubgroupPlace AlgebraicCurve.SemilinearAut.instDistribMulActionTorsion AlgebraicCurve.SemilinearAut.instSMulSubtypeProdRingAutMemSubgroupPic0 AlgebraicCurve.SemilinearAut.instSMulTorsion AlgebraicCurve.SemilinearAut.instMulActionSubtypeProdRingAutMemSubgroupPlace AlgebraicCurve.SemilinearAut.instSMulCommClassZModTorsion AlgebraicCurve.SemilinearAut.instMulSemiringActionSubtypeProdRingAutMemSubgroup AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.IsCurveOver.instNontrivialKaehler AlgebraicCurve.IsCurveOver.instFreeKaehler AlgebraicCurve.IsCurveOver.toHasPrincipalDivisors AlgebraicCurve.IsCurveOver.instFiniteResidue instDecEqAlgebraicClosureRat WeierstrassCurve.Affine.Point.instDistribMulActionAlgEquiv WeierstrassCurve.Affine.Point.instModuleZModTorsionBy WeierstrassCurve.Affine.Point.instSMulTorsionBy WeierstrassCurve.Affine.Point.instDistribMulActionTorsionBy WeierstrassCurve.Affine.Point.instSMulAlgEquiv WeierstrassCurve.Affine.Point.instSMulCommClassAlgEquivZModTorsionBy AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions"
p2m_attr_erase "simp" "ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL HahnSeries.ramScale_apply AlgebraicCurve.Divisor.mapRestrict_single AlgebraicCurve.Divisor.pushforward_single AlgebraicCurve.Place.coe_restrictInclusion AlgebraicCurve.Place.mem_fiber AlgebraicCurve.Place.restrict_toValuationSubring AlgebraicCurve.Divisor.degree_pushforward AlgebraicCurve.Place.restrictResidueMap_residue AlgebraicCurve.Pic0.coe_pushforwardDegZeroHom AlgebraicCurve.Pic0.coe_pullbackDegZeroHom AlgebraicCurve.SemilinearAut.toRingAut_inv AlgebraicCurve.SemilinearAut.smul_def AlgebraicCurve.SemilinearAut.smul_single AlgebraicCurve.SemilinearAut.smul_toValuationSubring AlgebraicCurve.SemilinearAut.baseAut_inv AlgebraicCurve.SemilinearAut.baseAut_ofAlgAut AlgebraicCurve.SemilinearAut.toRingAut_ofAlgAut AlgebraicCurve.SemilinearAut.torsionRep_apply AlgebraicCurve.SemilinearAut.toRingAut_one AlgebraicCurve.SemilinearAut.deg_smul AlgebraicCurve.SemilinearAut.degree_smul AlgebraicCurve.SemilinearAut.coe_degZeroSMulHom AlgebraicCurve.SemilinearAut.baseAut_mul AlgebraicCurve.SemilinearAut.coe_smulValuationSubringEquiv_apply AlgebraicCurve.SemilinearAut.baseAut_one AlgebraicCurve.SemilinearAut.ofAlgAut_smul AlgebraicCurve.SemilinearAut.coe_torsion_smul AlgebraicCurve.SemilinearAut.toRingAut_mul AlgebraicCurve.Place.congrEquiv_symm_apply AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal AlgebraicCurve.Place.congrRingEquiv_toValuationSubring"
p2m_attr_erase "simp" "AlgebraicCurve.Place.congrEquiv_apply AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply AlgebraicCurve.RationalFunctionField.deg_placeOfPoint AlgebraicCurve.RationalFunctionField.placeInfty_toValuationSubring AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal AlgebraicCurve.IsFrobeniusEndo.frobNormRingHom_apply ModularCurve.frobeniusPushforwardGeomLevelPic0_mk ModularCurve.coe_frobeniusGeomLevelEquiv_apply ModularCurve.coe_frobeniusPushforwardGeomLevelDegZero ModularCurve.heckeFibreGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusGeomLevel_apply_coe ModularCurve.frobeniusPullbackGeomLevelPic0OfIsCurveOver_mk ModularCurve.coe_heckeFibreGeomLevelDegZero ModularCurve.coe_frobeniusPullbackGeomLevelDegZero ModularCurve.frobeniusPullbackGeomLevelPic0_mk ModularCurve.frobeniusPullbackGeomLevel_single ModularCurve.heckeFibreGeomLevelPic0_mk ModularCurve.frobeniusPushforwardGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusPushforwardGeomLevel_single ModularCurve.qExpandAlgC_apply AlgebraicCurve.Divisor.degree_pushforwardAlong AlgebraicCurve.Pic0.coe_degZeroCorrespondence AlgebraicCurve.Place.mem_fiberAlong AlgebraicCurve.coe_frobeniusPushforwardDegZero AlgebraicCurve.IsFrobeniusEndo.coe_frobeniusPullbackDegZero ModularCurve.reduceModBivar_C_X ModularCurve.laurentMap_coeff ModularCurve.reduceModBivar_X ModularCurve.laurentMap_single ModularCurve.evalAtJInt_X ModularCurve.evalAtJMod_X ModularCurve.jqNMod_one ModularCurve.aeval_heckeGen ModularCurve.coe_mTorsionGaloisRep_apply ModularCurve.eisensteinSystem_of_dvd ModularCurve.eisensteinSystem_of_not_dvd"
p2m_attr_erase "simp" "FreyPackage.mk.sizeOf_spec FreyPackage.mk.injEq WeierstrassCurve.Affine.Point.galoisRepModuleEnd_apply AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none AlgebraicCurve.Divisor.evalFun_zero AlgebraicCurve.Place.evalAt_one"

set_option autoImplicit false

open Polynomial
open scoped IntermediateField

namespace PiInfQExpansion
namespace Gauss

variable {Kc E : Type*} [Field Kc] [Field E] [Algebra Kc E] (A : ValuationSubring Kc) (J : E)

noncomputable def evJ : Polynomial A →+* E := eval₂RingHom ((algebraMap Kc E).comp A.subtype) J

theorem evJ_eq_aeval (P : Polynomial A) : evJ A J P = aeval J (P.map A.subtype) := by
  rw [evJ, coe_eval₂RingHom, aeval_def, eval₂_map]

def IsGaussInt (x : E) : Prop :=
  ∃ P Q : Polynomial A, Q.map (IsLocalRing.residue A) ≠ 0 ∧ x * evJ A J Q = evJ A J P

variable {A J}

theorem ne_zero_of_map_residue_ne_zero {Q : Polynomial A}
    (hQ : Q.map (IsLocalRing.residue A) ≠ 0) : Q ≠ 0 := by
  rintro rfl; exact hQ (Polynomial.map_zero _)

theorem evJ_injective (hJ : Transcendental Kc J) : Function.Injective (evJ A J) := by
  rw [injective_iff_map_eq_zero]
  intro P hP
  rw [evJ_eq_aeval] at hP
  have := (transcendental_iff.mp hJ) _ hP
  exact (Polynomial.map_injective A.subtype Subtype.coe_injective) (by rwa [Polynomial.map_zero])

theorem evJ_ne_zero (hJ : Transcendental Kc J) {Q : Polynomial A}
    (hQ : Q.map (IsLocalRing.residue A) ≠ 0) : evJ A J Q ≠ 0 := fun h =>
  ne_zero_of_map_residue_ne_zero hQ (evJ_injective hJ (by rw [h, map_zero]))

theorem map_residue_mul_ne_zero {Q Q' : Polynomial A}
    (hQ : Q.map (IsLocalRing.residue A) ≠ 0) (hQ' : Q'.map (IsLocalRing.residue A) ≠ 0) :
    (Q * Q').map (IsLocalRing.residue A) ≠ 0 := by
  rw [Polynomial.map_mul]; exact mul_ne_zero hQ hQ'

namespace IsGaussInt

theorem zero : IsGaussInt A J 0 := ⟨0, 1, by simp, by simp⟩

theorem one : IsGaussInt A J 1 := ⟨1, 1, by simp, by simp⟩

theorem const (a : A) : IsGaussInt A J (algebraMap Kc E a) :=
  ⟨C a, 1, by simp, by simp [evJ]⟩

theorem self : IsGaussInt A J J := ⟨X, 1, by simp, by simp [evJ]⟩

theorem inv_self : IsGaussInt A J J⁻¹ := by
  by_cases hJ : J = 0
  · rw [hJ, inv_zero]; exact zero
  · exact ⟨1, X, by simp, by simp [evJ, hJ]⟩

theorem add {x y : E} (hx : IsGaussInt A J x) (hy : IsGaussInt A J y) :
    IsGaussInt A J (x + y) := by
  obtain ⟨P, Q, hQ, h⟩ := hx
  obtain ⟨P', Q', hQ', h'⟩ := hy
  refine ⟨P * Q' + P' * Q, Q * Q', map_residue_mul_ne_zero hQ hQ', ?_⟩
  simp only [map_mul, map_add]
  rw [← h, ← h']; ring

theorem neg {x : E} (hx : IsGaussInt A J x) : IsGaussInt A J (-x) := by
  obtain ⟨P, Q, hQ, h⟩ := hx
  exact ⟨-P, Q, hQ, by rw [map_neg, ← h, neg_mul]⟩

theorem mul {x y : E} (hx : IsGaussInt A J x) (hy : IsGaussInt A J y) :
    IsGaussInt A J (x * y) := by
  obtain ⟨P, Q, hQ, h⟩ := hx
  obtain ⟨P', Q', hQ', h'⟩ := hy
  refine ⟨P * P', Q * Q', map_residue_mul_ne_zero hQ hQ', ?_⟩
  simp only [map_mul]
  rw [← h, ← h']; ring

theorem inv_evJ {Q : Polynomial A} (hQ : Q.map (IsLocalRing.residue A) ≠ 0)
    (hJ : Transcendental Kc J) : IsGaussInt A J (evJ A J Q)⁻¹ :=
  ⟨1, Q, hQ, by rw [inv_mul_cancel₀ (evJ_ne_zero hJ hQ), map_one]⟩

end IsGaussInt

theorem exists_normalize (p : Kc[X]) (hp : p ≠ 0) :
    ∃ (c : Kc) (P : Polynomial A), c ≠ 0 ∧ P.map A.subtype = C c * p ∧
      P.map (IsLocalRing.residue A) ≠ 0 := by
  classical
  have hne : p.support.Nonempty := by
    rw [Finset.nonempty_iff_ne_empty, Ne, Polynomial.support_eq_empty]; exact hp
  obtain ⟨i₀, hi₀, hmax⟩ := Finset.exists_max_image p.support (fun i => A.valuation (p.coeff i)) hne
  have hc₀ : p.coeff i₀ ≠ 0 := mem_support_iff.mp hi₀
  set c := (p.coeff i₀)⁻¹ with hc
  have hcne : c ≠ 0 := inv_ne_zero hc₀
  have hlifts : C c * p ∈ Polynomial.lifts A.subtype := by
    rw [lifts_iff_coeff_lifts]
    intro n
    rw [coeff_C_mul]
    by_cases hn : n ∈ p.support
    · have hmem : c * p.coeff n ∈ A := by
        rw [← A.valuation_le_one_iff, map_mul, hc, map_inv₀, mul_comm, ← div_eq_mul_inv]
        exact div_le_one_of_le₀ (hmax n hn) zero_le'
      exact ⟨⟨_, hmem⟩, rfl⟩
    · rw [notMem_support_iff.mp hn, mul_zero]; exact ⟨0, map_zero _⟩
  obtain ⟨P, hP⟩ := (mem_lifts _).mp hlifts
  refine ⟨c, P, hcne, hP, fun h => ?_⟩
  have h1 : (P.coeff i₀ : Kc) = 1 := by
    have := congrArg (fun q => q.coeff i₀) hP
    simp only [coeff_map, coeff_C_mul] at this
    rw [show A.subtype (P.coeff i₀) = (P.coeff i₀ : Kc) from rfl] at this
    rw [this, hc, inv_mul_cancel₀ hc₀]
  have h2 : P.coeff i₀ = 1 := Subtype.ext h1
  have := congrArg (fun q => q.coeff i₀) h
  simp only [coeff_map, h2, map_one, coeff_zero] at this
  exact one_ne_zero this

theorem isGaussInt_or_inv (hJ : Transcendental Kc J) (x : E) (hx : x ∈ Kc⟮J⟯) :
    IsGaussInt A J x ∨ IsGaussInt A J x⁻¹ := by
  rw [IntermediateField.mem_adjoin_simple_iff] at hx
  obtain ⟨r, s, hx⟩ := hx
  by_cases hr : r = 0
  · left; rw [hx, hr, map_zero, zero_div]; exact IsGaussInt.zero
  by_cases hs : s = 0
  · left; rw [hx, hs, map_zero, div_zero]; exact IsGaussInt.zero
  obtain ⟨cr, Pr, hcr, hPr, hPr'⟩ := exists_normalize (A := A) r hr
  obtain ⟨cs, Ps, hcs, hPs, hPs'⟩ := exists_normalize (A := A) s hs
  have her : evJ A J Pr = algebraMap Kc E cr * aeval J r := by
    rw [evJ_eq_aeval, hPr, map_mul, aeval_C]
  have hes : evJ A J Ps = algebraMap Kc E cs * aeval J s := by
    rw [evJ_eq_aeval, hPs, map_mul, aeval_C]
  have hs0 : aeval J s ≠ 0 := fun h => hs ((transcendental_iff.mp hJ) _ h)
  have hr0 : aeval J r ≠ 0 := fun h => hr ((transcendental_iff.mp hJ) _ h)
  have hcrE : algebraMap Kc E cr ≠ 0 := (_root_.map_ne_zero _).mpr hcr
  have hcsE : algebraMap Kc E cs ≠ 0 := (_root_.map_ne_zero _).mpr hcs
  by_cases ha : cs / cr ∈ A
  · left
    refine ⟨C ⟨cs / cr, ha⟩ * Pr, Ps, hPs', ?_⟩
    rw [map_mul, her, hes, hx]
    have : evJ A J (C ⟨cs / cr, ha⟩) = algebraMap Kc E (cs / cr) := by simp [evJ]
    rw [this, map_div₀]
    field_simp
  · right
    have ha' : (cs / cr)⁻¹ ∈ A := (A.mem_or_inv_mem _).resolve_left ha
    refine ⟨C ⟨(cs / cr)⁻¹, ha'⟩ * Ps, Pr, hPr', ?_⟩
    rw [map_mul, her, hes, hx]
    have : evJ A J (C ⟨(cs / cr)⁻¹, ha'⟩) = algebraMap Kc E (cs / cr)⁻¹ := by simp [evJ]
    rw [this, map_inv₀, map_div₀]
    field_simp

noncomputable def gaussVal (hJ : Transcendental Kc J) : ValuationSubring Kc⟮J⟯ where
  carrier := {x | IsGaussInt A J (x : E)}
  mul_mem' hx hy := by simpa using IsGaussInt.mul hx hy
  one_mem' := by simpa using (IsGaussInt.one : IsGaussInt A J 1)
  add_mem' hx hy := by simpa using IsGaussInt.add hx hy
  zero_mem' := by simpa using (IsGaussInt.zero : IsGaussInt A J 0)
  neg_mem' hx := by simpa using IsGaussInt.neg hx
  mem_or_inv_mem' x := by
    simpa using isGaussInt_or_inv (A := A) hJ (x : E) x.2

variable (hJ : Transcendental Kc J)

theorem mem_gaussVal_iff (x : Kc⟮J⟯) : x ∈ gaussVal (A := A) hJ ↔ IsGaussInt A J (x : E) :=
  Iff.rfl

noncomputable def gJ : gaussVal (A := A) hJ :=
  ⟨IntermediateField.AdjoinSimple.gen Kc J, by
    rw [mem_gaussVal_iff, IntermediateField.AdjoinSimple.coe_gen]; exact IsGaussInt.self⟩

@[scoped simp] theorem coe_coe_gJ : ((gJ (A := A) hJ : Kc⟮J⟯) : E) = J := rfl

noncomputable def gJinv : gaussVal (A := A) hJ :=
  ⟨(IntermediateField.AdjoinSimple.gen Kc J)⁻¹, by
    rw [mem_gaussVal_iff, IntermediateField.coe_inv, IntermediateField.AdjoinSimple.coe_gen]
    exact IsGaussInt.inv_self⟩

@[scoped simp] theorem coe_coe_gJinv : ((gJinv (A := A) hJ : Kc⟮J⟯) : E) = J⁻¹ := by
  simp [gJinv]

noncomputable def gConst : A →+* gaussVal (A := A) hJ :=
  ((algebraMap Kc Kc⟮J⟯).comp A.subtype).codRestrict _ fun a => by
    rw [mem_gaussVal_iff]
    show IsGaussInt A J ((algebraMap Kc Kc⟮J⟯ (a : Kc) : Kc⟮J⟯) : E)
    rw [IntermediateField.coe_algebraMap_apply]
    exact IsGaussInt.const a

@[scoped simp] theorem coe_coe_gConst (a : A) :
    ((gConst (A := A) hJ a : Kc⟮J⟯) : E) = algebraMap Kc E a := by
  show ((algebraMap Kc Kc⟮J⟯ (a : Kc) : Kc⟮J⟯) : E) = _
  rw [IntermediateField.coe_algebraMap_apply]

noncomputable def gEv : Polynomial A →+* gaussVal (A := A) hJ :=
  eval₂RingHom (gConst hJ) (gJ hJ)

theorem coe_coe_gEv (P : Polynomial A) :
    ((gEv (A := A) hJ P : Kc⟮J⟯) : E) = evJ A J P := by
  have : ((algebraMap Kc⟮J⟯ E).comp (gaussVal (A := A) hJ).subtype).comp (gEv hJ) = evJ A J := by
    refine Polynomial.ringHom_ext (fun a => ?_) ?_
    · simp only [RingHom.comp_apply, gEv, coe_eval₂RingHom, eval₂_C, evJ]
      exact coe_coe_gConst hJ a
    · simp only [RingHom.comp_apply, gEv, coe_eval₂RingHom, eval₂_X, evJ]
      rfl
  exact (RingHom.congr_fun this P)

theorem isUnit_gEv {Q : Polynomial A} (hQ : Q.map (IsLocalRing.residue A) ≠ 0) :
    IsUnit (gEv (A := A) hJ Q) := by
  have hne : ((gEv (A := A) hJ Q : Kc⟮J⟯) : E) ≠ 0 := by
    rw [coe_coe_gEv]; exact evJ_ne_zero hJ hQ
  have hne' : (gEv (A := A) hJ Q : Kc⟮J⟯) ≠ 0 := fun h => hne (by rw [h]; rfl)
  have hmem : (gEv (A := A) hJ Q : Kc⟮J⟯)⁻¹ ∈ gaussVal (A := A) hJ := by
    rw [mem_gaussVal_iff, IntermediateField.coe_inv, coe_coe_gEv]
    exact IsGaussInt.inv_evJ hQ hJ
  refine IsUnit.of_mul_eq_one ⟨_, hmem⟩ ?_
  apply Subtype.ext
  show (gEv (A := A) hJ Q : Kc⟮J⟯) * (gEv (A := A) hJ Q : Kc⟮J⟯)⁻¹ = 1
  exact mul_inv_cancel₀ hne'

theorem gEv_mem_maximalIdeal {P : Polynomial A} (hP : P.map (IsLocalRing.residue A) = 0) :
    gEv (A := A) hJ P ∈ IsLocalRing.maximalIdeal _ := by
  rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
  rintro ⟨w, hw⟩
  obtain ⟨P', Q', hQ', h⟩ := (mem_gaussVal_iff hJ _).mp (w⁻¹ : (gaussVal (A := A) hJ)ˣ).1.2

  have h1 : ((((w⁻¹ : (gaussVal (A := A) hJ)ˣ) : gaussVal (A := A) hJ) : Kc⟮J⟯) : E) *
      evJ A J P = 1 := by
    rw [← coe_coe_gEv hJ, ← hw]
    rw [← IntermediateField.coe_mul, ← MulMemClass.coe_mul, Units.inv_mul]
    rfl
  have h2 : evJ A J (P' * P) = evJ A J Q' := by
    rw [map_mul, ← h, mul_assoc, mul_comm (evJ A J Q'), ← mul_assoc, h1, one_mul]
  have h3 : P' * P = Q' := evJ_injective hJ h2
  apply hQ'
  rw [← h3, Polynomial.map_mul, hP, mul_zero]

theorem gConst_mem_maximalIdeal {a : A} (ha : a ∈ IsLocalRing.maximalIdeal A) :
    gConst (A := A) hJ a ∈ IsLocalRing.maximalIdeal _ := by
  have : gEv (A := A) hJ (C a) = gConst hJ a := by simp [gEv]
  rw [← this]
  apply gEv_mem_maximalIdeal
  rw [map_C, (IsLocalRing.residue_eq_zero_iff _).mpr ha, C_0]

end PiInfQExpansion.Gauss
p2m_reactivate "P2MW.S_ModularCurve_CharPModel_FibreModel_coe_piInf_eq_coeffRed_of_cuspChart.PiInfQExpansion P2MW.S_ModularCurve_CharPModel_FibreModel_coe_piInf_eq_coeffRed_of_cuspChart.PiInfQExpansion.Gauss"
p2m_reactivate "P2MW.S_ModularCurve_CharPModel_FibreModel_coe_piInf_eq_coeffRed_of_cuspChart.PiInfQExpansion"

open Polynomial
open scoped IntermediateField

namespace PiInfQExpansion
namespace Dedekind

variable {K L : Type*} [Field K] [Field L] [Algebra K L]

theorem map_residue_scaleRoots (V : ValuationSubring K) (q : Polynomial V) (hq : q.Monic)
    (π : V) (hπ : π ∈ IsLocalRing.maximalIdeal V) :
    (q.scaleRoots π).map (IsLocalRing.residue V) = X ^ q.natDegree := by
  ext i
  rw [coeff_map, coeff_scaleRoots, coeff_X_pow]
  by_cases hi : i = q.natDegree
  · subst hi
    rw [if_pos rfl, hq.coeff_natDegree, one_mul, Nat.sub_self, pow_zero, map_one]
  · rw [if_neg hi]
    rcases lt_or_gt_of_ne hi with h | h
    · have hmem : π ^ (q.natDegree - i) ∈ IsLocalRing.maximalIdeal V :=
        Ideal.pow_mem_of_mem _ hπ _ (Nat.sub_pos_of_lt h)
      rw [map_mul, (IsLocalRing.residue_eq_zero_iff _).mpr hmem, mul_zero]
    · rw [coeff_eq_zero_of_natDegree_lt h, zero_mul, map_zero]

theorem exists_eq_sum_of_isIntegral (V : ValuationSubring K) (y : L) (f : Polynomial V)
    (hf : f.Monic) (hfy : aeval y (f.map (algebraMap V K)) = 0)
    (hsq : Squarefree (f.map (IsLocalRing.residue V)))
    (x : L) (hx : x ∈ K⟮y⟯) (q : Polynomial V) (hq : q.Monic)
    (hqx : aeval x (q.map (algebraMap V K)) = 0) :
    ∃ (n : ℕ) (c : Fin n → V), x = ∑ i, algebraMap K L (c i : K) * y ^ (i : ℕ) := by
  classical
  have hfy' : aeval y f = 0 := by rwa [aeval_map_algebraMap] at hfy
  have hqx' : aeval x q = 0 := by rwa [aeval_map_algebraMap] at hqx
  have hyV : IsIntegral V y := ⟨f, hf, by rwa [← aeval_def]⟩
  have hyK : IsIntegral K y := hyV.tower_top
  let pb := IntermediateField.adjoin.powerBasis hyK
  let d := pb.dim
  let c : Fin d → K := fun i => pb.basis.repr ⟨x, hx⟩ i
  have hxsum : x = ∑ i, algebraMap K L (c i) * y ^ (i : ℕ) := by
    have h := pb.basis.sum_repr ⟨x, hx⟩
    have h2 := congrArg (algebraMap K⟮y⟯ L) h
    rw [map_sum] at h2
    conv_lhs => rw [show x = algebraMap K⟮y⟯ L ⟨x, hx⟩ from rfl, ← h2]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [PowerBasis.basis_eq_pow, Algebra.smul_def, map_mul, map_pow,
      ← IsScalarTower.algebraMap_apply K K⟮y⟯ L]
    show _ * (algebraMap K⟮y⟯ L) (IntermediateField.adjoin.powerBasis hyK).gen ^ _ = _
    rw [IntermediateField.adjoin.powerBasis_gen, IntermediateField.AdjoinSimple.algebraMap_gen]
  by_cases hc0 : ∀ i, c i = 0
  · exact ⟨d, fun _ => 0, by simp [hxsum, hc0]⟩
  push Not at hc0
  obtain ⟨i₁, hi₁⟩ := hc0
  obtain ⟨i₀, -, hmax⟩ :=
    Finset.exists_max_image Finset.univ (fun i => V.valuation (c i)) ⟨i₁, Finset.mem_univ _⟩
  have hci₀ : c i₀ ≠ 0 := by
    intro h
    apply hi₁
    have := hmax i₁ (Finset.mem_univ _)
    rw [h, map_zero, le_zero_iff] at this
    exact (map_eq_zero _).mp this
  have he : ∀ i, c i / c i₀ ∈ V := fun i => by
    rw [← V.valuation_le_one_iff, map_div₀]
    exact div_le_one_of_le₀ (hmax i (Finset.mem_univ _)) zero_le'
  let e : Fin d → V := fun i => ⟨c i / c i₀, he i⟩
  have he₀ : e i₀ = 1 := Subtype.ext (div_self hci₀)
  let P : Polynomial V := ∑ i, C (e i) * X ^ (i : ℕ)
  have hdpos : 0 < d := Fin.pos i₀
  have hPdeg : P.natDegree < d := by
    by_cases hP0 : P = 0
    · rw [hP0, natDegree_zero]; exact hdpos
    · exact (natDegree_lt_iff_degree_lt hP0).mpr (degree_sum_fin_lt _)
  have hPcoeff : P.coeff i₀ = 1 := by
    simp only [P, finsetSum_coeff, coeff_C_mul_X_pow]
    rw [Finset.sum_eq_single i₀, if_pos rfl, he₀]
    · intro b _ hb
      rw [if_neg]
      exact fun h => hb (Fin.ext h.symm)
    · intro h; exact absurd (Finset.mem_univ _) h
  have hPbar_ne : P.map (IsLocalRing.residue V) ≠ 0 := fun h => by
    have := congrArg (fun p => p.coeff (i₀ : ℕ)) h
    simp only [coeff_map, hPcoeff, map_one, coeff_zero] at this
    exact one_ne_zero this
  have haevalP : aeval y P = ∑ i, algebraMap K L (c i / c i₀) * y ^ (i : ℕ) := by
    simp only [P, map_sum, map_mul, aeval_C, map_pow, aeval_X]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [IsScalarTower.algebraMap_apply V K L]
    rfl
  have hu : algebraMap K L (c i₀) * aeval y P = x := by
    rw [haevalP, Finset.mul_sum, hxsum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← mul_assoc, ← map_mul, mul_div_cancel₀ _ hci₀]
  suffices hcV : c i₀ ∈ V by
    refine ⟨d, fun i => ⟨c i₀, hcV⟩ * e i, ?_⟩
    rw [hxsum]
    refine Finset.sum_congr rfl fun i _ => ?_
    congr 1
    simp only [e, MulMemClass.coe_mul, mul_div_cancel₀ _ hci₀]
  by_contra hcV
  have hinv : (c i₀)⁻¹ ∈ V := (V.mem_or_inv_mem _).resolve_left hcV
  set π : V := ⟨(c i₀)⁻¹, hinv⟩ with hπdef
  have hπ : π ∈ IsLocalRing.maximalIdeal V := by
    rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
    rintro ⟨w, hw⟩
    apply hcV
    have h1 : ((w⁻¹ : Vˣ) : V) * (π : K) = 1 := by
      rw [← hw, ← MulMemClass.coe_mul, Units.inv_mul, OneMemClass.coe_one]
    have h2 : (((w⁻¹ : Vˣ) : V) : K) = c i₀ := by
      have : (π : K) = (c i₀)⁻¹ := rfl
      rw [this] at h1
      have h3 := congrArg (· * c i₀) h1
      simp only [mul_assoc, inv_mul_cancel₀ hci₀, mul_one, one_mul] at h3
      exact h3
    rw [← h2]; exact SetLike.coe_mem _
  have hux : algebraMap V L π * x = aeval y P := by
    rw [← hu, ← mul_assoc, IsScalarTower.algebraMap_apply V K L, ← map_mul]
    have : ((π : K)) * c i₀ = 1 := inv_mul_cancel₀ hci₀
    rw [show algebraMap V K π = (π : K) from rfl, this, map_one, one_mul]
  have hH : aeval y ((q.scaleRoots π).comp P) = 0 := by
    rw [aeval_comp, ← hux]
    exact scaleRoots_aeval_eq_zero hqx'
  have hg_dvd_H : minpoly V y ∣ (q.scaleRoots π).comp P := minpoly.isIntegrallyClosed_dvd hyV hH
  have hg_dvd_f : minpoly V y ∣ f := minpoly.isIntegrallyClosed_dvd hyV hfy'
  set g := minpoly V y with hg
  have hgbar_sq : Squarefree (g.map (IsLocalRing.residue V)) :=
    Squarefree.squarefree_of_dvd (Polynomial.map_dvd _ hg_dvd_f) hsq
  have hm : q.natDegree ≠ 0 := by
    intro h0
    have : q = 1 := eq_one_of_monic_natDegree_zero hq h0
    rw [this, map_one] at hqx'
    exact one_ne_zero hqx'
  have hgbar_dvd_P : g.map (IsLocalRing.residue V) ∣ P.map (IsLocalRing.residue V) := by
    have h1 : g.map (IsLocalRing.residue V) ∣ (P.map (IsLocalRing.residue V)) ^ q.natDegree := by
      have := Polynomial.map_dvd (IsLocalRing.residue V) hg_dvd_H
      rwa [map_comp, map_residue_scaleRoots V q hq π hπ, X_pow_comp] at this
    exact (hgbar_sq.dvd_pow_iff_dvd hm).mp h1
  have hg_deg : g.natDegree = d := by
    have h1 : minpoly K y = g.map (algebraMap V K) :=
      minpoly.isIntegrallyClosed_eq_field_fractions' K hyV
    show g.natDegree = (IntermediateField.adjoin.powerBasis hyK).dim
    rw [IntermediateField.adjoin.powerBasis_dim, h1, (minpoly.monic hyV).natDegree_map]
  have hgbar_deg : (g.map (IsLocalRing.residue V)).natDegree = d := by
    rw [(minpoly.monic hyV).natDegree_map]; exact hg_deg
  have hPbar_deg : (P.map (IsLocalRing.residue V)).natDegree
      < (g.map (IsLocalRing.residue V)).natDegree :=
    lt_of_le_of_lt natDegree_map_le (hgbar_deg ▸ hPdeg)
  exact hPbar_ne (eq_zero_of_dvd_of_natDegree_lt hgbar_dvd_P hPbar_deg)

end PiInfQExpansion.Dedekind
p2m_reactivate "P2MW.S_ModularCurve_CharPModel_FibreModel_coe_piInf_eq_coeffRed_of_cuspChart.PiInfQExpansion P2MW.S_ModularCurve_CharPModel_FibreModel_coe_piInf_eq_coeffRed_of_cuspChart.PiInfQExpansion.Gauss"
p2m_reactivate "P2MW.S_ModularCurve_CharPModel_FibreModel_coe_piInf_eq_coeffRed_of_cuspChart.PiInfQExpansion P2MW.S_ModularCurve_CharPModel_FibreModel_coe_piInf_eq_coeffRed_of_cuspChart.PiInfQExpansion.Gauss"

open Polynomial
open scoped IntermediateField

noncomputable section

namespace PiInfQExpansion

section Arith

variable {A k : Type*} [CommRing A] [IsLocalRing A] [Field k] (red : A →+* k)
  (ℓ : ℕ) [Fact ℓ.Prime] [CharP k ℓ]

include red in
omit [Fact ℓ.Prime] in
theorem natCast_mem_maximalIdeal : ((ℓ : ℕ) : A) ∈ IsLocalRing.maximalIdeal A := by
  have h1 : ((ℓ : ℕ) : A) ∈ RingHom.ker red := by
    rw [RingHom.mem_ker, map_natCast, CharP.cast_eq_zero]
  exact IsLocalRing.le_maximalIdeal (RingHom.ker_ne_top red) h1

include red in
theorem ker_le_maximalIdeal : RingHom.ker red ≤ IsLocalRing.maximalIdeal A :=
  IsLocalRing.le_maximalIdeal (RingHom.ker_ne_top red)

include red ℓ in

theorem intCast_notMem_maximalIdeal (n : ℤ) (hn : ((n : ℤ) : ZMod ℓ) ≠ 0) :
    ((n : ℤ) : A) ∉ IsLocalRing.maximalIdeal A := by
  intro hmem
  set m : ℤ := (((n : ZMod ℓ)⁻¹).val : ℤ) with hm
  have h1 : ((n * m : ℤ) : ZMod ℓ) = 1 := by
    rw [Int.cast_mul, hm, Int.cast_natCast, ZMod.natCast_zmod_val, mul_inv_cancel₀ hn]
  have h2 : ((ℓ : ℕ) : ℤ) ∣ n * m - 1 := by
    rw [← ZMod.intCast_zmod_eq_zero_iff_dvd, Int.cast_sub, h1, Int.cast_one, sub_self]
  obtain ⟨t, ht⟩ := h2
  have h3 : (1 : A) = (n : A) * (m : A) - ((ℓ : ℕ) : A) * (t : A) := by
    have := congrArg (fun z : ℤ => (z : A)) ht
    simp only [Int.cast_sub, Int.cast_mul, Int.cast_one, Int.cast_natCast] at this
    rw [← this]; ring
  apply (IsLocalRing.maximalIdeal A).ne_top_iff_one.mp (Ideal.IsMaximal.ne_top inferInstance)
  rw [h3]
  exact Ideal.sub_mem _ (Ideal.mul_mem_right _ _ hmem)
    (Ideal.mul_mem_right _ _ (natCast_mem_maximalIdeal red ℓ))

include red in
theorem map_ne_zero_of_map_residue_ne_zero {G : Polynomial A}
    (hG : G.map (IsLocalRing.residue A) ≠ 0) : G.map red ≠ 0 := by
  intro h
  apply hG
  ext i
  have hi := congrArg (fun p => p.coeff i) h
  simp only [coeff_map, coeff_zero] at hi ⊢
  rw [IsLocalRing.residue_eq_zero_iff]
  exact ker_le_maximalIdeal red ((RingHom.mem_ker).mpr hi)

end Arith
p2m_reactivate "P2MW.S_ModularCurve_CharPModel_FibreModel_coe_piInf_eq_coeffRed_of_cuspChart.PiInfQExpansion P2MW.S_ModularCurve_CharPModel_FibreModel_coe_piInf_eq_coeffRed_of_cuspChart.PiInfQExpansion.Gauss"

theorem intPoly_ringHom_ext {R : Type*} [Semiring R] {f g : ℤ[X] →+* R} (h : f X = g X) :
    f = g :=
  Polynomial.ringHom_ext' (RingHom.ext_int _ _) h

end PiInfQExpansion
p2m_reactivate "P2MW.S_ModularCurve_CharPModel_FibreModel_coe_piInf_eq_coeffRed_of_cuspChart.PiInfQExpansion P2MW.S_ModularCurve_CharPModel_FibreModel_coe_piInf_eq_coeffRed_of_cuspChart.PiInfQExpansion.Gauss"

namespace PiInfQExpansion

open ModularCurve ModularCurve.CharPModel ModularCurve.CharPReduction

local notation "Qb" => AlgebraicClosure ℚ
local notation "LL" => LaurentSeries (AlgebraicClosure ℚ)

variable (N : ℕ) [NeZero N]

theorem coeffEmb_jq : coeffEmb Qb jq = jqModC Qb := by
  show (jqModC ℚ).map (algebraMap ℚ Qb) = jqModC Qb
  exact map_jqModC _

theorem coeffEmb_jqN : coeffEmb Qb (qExpand ℚ N jq) = jqNModC Qb N := by
  show coeffMap (algebraMap ℚ Qb) (qExpand ℚ N jq) = qExpand Qb N (jqModC Qb)
  rw [coeffMap_qExpand]
  congr 1
  exact coeffEmb_jq

theorem coe_jBar : ((jBar N : laurentBaseChange Qb (modularFunctionFieldFull N)) : LL) = jqModC Qb :=
  coeffEmb_jq

theorem coe_jNBar :
    ((jNBar N : laurentBaseChange Qb (modularFunctionFieldFull N)) : LL) = jqNModC Qb N :=
  coeffEmb_jqN N

theorem jqModC_eq_coeffMap (K : Type*) [CommRing K] :
    jqModC K = coeffMap (Int.castRingHom K) (jqModC ℤ) :=
  jqModC_eq_map_intCast K

theorem jqNModC_eq_coeffMap (K : Type*) [CommRing K] :
    jqNModC K N = coeffMap (Int.castRingHom K) (jqNModC ℤ N) := by
  show qExpand K N (jqModC K) = coeffMap (Int.castRingHom K) (qExpand ℤ N (jqModC ℤ))
  rw [coeffMap_qExpand, ← jqModC_eq_coeffMap]

theorem jqModC_ne_zero : jqModC Qb ≠ 0 := fun h =>
  (transcendental_jqModC Qb) (h ▸ isAlgebraic_zero)

theorem mem_adjoin_adjoin (x : LL) (hx : x ∈ laurentBaseChange Qb (modularFunctionFieldFull N)) :
    x ∈ (↥Qb⟮jqModC Qb⟯)⟮jqNModC Qb N⟯ := by
  suffices h : x ∈ Qb⟮jqModC Qb, jqNModC Qb N⟯ by
    rw [← IntermediateField.adjoin_simple_adjoin_simple, IntermediateField.mem_restrictScalars] at h
    exact h
  refine laurentBaseChange_le_of_divisor_generators_mem Qb N _ (fun d _ hd => ?_) hx
  have hg : qExpand ℚ d jq ∈ IntermediateField.adjoin ℚ {jq, qExpand ℚ N jq} :=
    functionFieldGeneration N d hd inferInstance
  have hle : Subfield.closure (Set.range (algebraMap ℚ (LaurentSeries ℚ)) ∪ {jq, qExpand ℚ N jq})
      ≤ (Qb⟮jqModC Qb, jqNModC Qb N⟯.toSubfield).comap (coeffEmb Qb) := by
    rw [Subfield.closure_le]
    rintro y (⟨r, rfl⟩ | hy)
    · simp only [Subfield.coe_comap, Set.mem_preimage, SetLike.mem_coe,
        IntermediateField.mem_toSubfield]
      rw [algebraMap_laurentSeries_eq_single, coeffEmb, coeffMap_single,
        ← algebraMap_laurentSeries_eq_single]
      exact IntermediateField.algebraMap_mem _ _
    · simp only [Subfield.coe_comap, Set.mem_preimage, SetLike.mem_coe,
        IntermediateField.mem_toSubfield]
      rcases hy with rfl | hy
      · rw [coeffEmb_jq]
        exact IntermediateField.subset_adjoin _ _ (Set.mem_insert _ _)
      · rw [Set.mem_singleton_iff.mp hy, coeffEmb_jqN]
        exact IntermediateField.subset_adjoin _ _ (Set.mem_insert_of_mem _ rfl)
  exact hle hg

end PiInfQExpansion
p2m_reactivate "P2MW.S_ModularCurve_CharPModel_FibreModel_coe_piInf_eq_coeffRed_of_cuspChart.PiInfQExpansion P2MW.S_ModularCurve_CharPModel_FibreModel_coe_piInf_eq_coeffRed_of_cuspChart.PiInfQExpansion.Gauss"

namespace PiInfQExpansion

open ModularCurve ModularCurve.CharPModel ModularCurve.CharPReduction PiInfQExpansion.Gauss

local notation "Qb" => AlgebraicClosure ℚ
local notation "LL" => LaurentSeries (AlgebraicClosure ℚ)
local notation "K₀" => (AlgebraicClosure ℚ)⟮jqModC (AlgebraicClosure ℚ)⟯

theorem hJt : Transcendental Qb (jqModC Qb) := transcendental_jqModC Qb

abbrev VG (A : ValuationSubring Qb) : ValuationSubring K₀ := gaussVal (A := A) hJt

scoped instance instSMulVG (A : ValuationSubring Qb) : SMul (VG A) LL := Algebra.toSMul
scoped instance instModuleVG (A : ValuationSubring Qb) : Module (VG A) LL := Algebra.toModule
scoped instance instTowerVG (A : ValuationSubring Qb) : IsScalarTower (VG A) K₀ LL :=
  IsScalarTower.of_algebraMap_eq (fun _ => rfl)

variable (N : ℕ) [NeZero N] (A : ValuationSubring Qb)

abbrev vJ : VG A := gJ (A := A) hJt

theorem algebraMap_VG_apply (v : VG A) : algebraMap (VG A) LL v = ((v : K₀) : LL) := by
  rw [IsScalarTower.algebraMap_apply (VG A) K₀ LL]
  rfl

def fV (data : ModularPolynomialData N) : Polynomial (VG A) :=
  data.Φ.map (eval₂RingHom (Int.castRingHom (VG A)) (vJ A))

theorem fV_monic (data : ModularPolynomialData N) : (fV N A data).Monic :=
  data.monic.map _

theorem aeval_fV (data : ModularPolynomialData N) :
    aeval (jqNModC Qb N) ((fV N A data).map (algebraMap (VG A) K₀)) = 0 := by
  rw [aeval_map_algebraMap, aeval_def, fV, eval₂_map]
  have hφ : (algebraMap (VG A) LL).comp (eval₂RingHom (Int.castRingHom (VG A)) (vJ A))
      = eval₂RingHom (Int.castRingHom LL) (jqModC Qb) := by
    apply intPoly_ringHom_ext
    simp only [RingHom.comp_apply, coe_eval₂RingHom, eval₂_X]
    rw [algebraMap_VG_apply]
    exact coe_coe_gJ hJt
  rw [hφ]
  have h : (data.Φ.map (eval₂RingHom (Int.castRingHom LL) (coeffEmb Qb jq))).IsRoot
      (coeffEmb Qb (qExpand ℚ N jq)) :=
    isRoot_map_Phi_apply_jBar Qb N data LL (laurentBaseChange Qb (modularFunctionFieldFull N)).val
  rw [coeffEmb_jq, coeffEmb_jqN, IsRoot, eval_map] at h
  exact h

section Residue

variable {A}
variable {k : Type*} [Field k] (red : A →+* k) (ℓ : ℕ)

include red in
theorem natCast_mem_maximalIdeal_VG [CharP k ℓ] :
    ((ℓ : ℕ) : VG A) ∈ IsLocalRing.maximalIdeal (VG A) := by
  have : ((ℓ : ℕ) : VG A) = gConst hJt ((ℓ : ℕ) : A) := by rw [map_natCast]
  rw [this]
  exact gConst_mem_maximalIdeal hJt (natCast_mem_maximalIdeal red ℓ)

include red in
theorem charP_residueField_VG [Fact ℓ.Prime] [CharP k ℓ] :
    CharP (IsLocalRing.ResidueField (VG A)) ℓ := by
  refine (CharP.charP_iff_prime_eq_zero (Fact.out : ℓ.Prime)).mpr ?_
  rw [← map_natCast (IsLocalRing.residue (VG A)), IsLocalRing.residue_eq_zero_iff]
  exact natCast_mem_maximalIdeal_VG red ℓ

variable (A) in

def theta [CharP (IsLocalRing.ResidueField (VG A)) ℓ] :
    (ZMod ℓ)[X] →+* IsLocalRing.ResidueField (VG A) :=
  eval₂RingHom (ZMod.castHom (dvd_refl ℓ) (IsLocalRing.ResidueField (VG A)))
    (IsLocalRing.residue (VG A) (vJ A))

include red in

theorem theta_injective [Fact ℓ.Prime] [CharP k ℓ] [CharP (IsLocalRing.ResidueField (VG A)) ℓ] :
    Function.Injective (theta A ℓ) := by
  rw [injective_iff_map_eq_zero]
  intro Pt hPt
  obtain ⟨P, rfl⟩ := Polynomial.map_surjective (Int.castRingHom (ZMod ℓ))
    (ZMod.ringHom_surjective _) Pt

  have h1 : (theta A ℓ).comp (mapRingHom (Int.castRingHom (ZMod ℓ)))
      = (IsLocalRing.residue (VG A)).comp
          ((gEv (A := A) hJt).comp (mapRingHom (Int.castRingHom A))) := by
    apply intPoly_ringHom_ext
    simp [theta, gEv]
  have h2 : IsLocalRing.residue (VG A) (gEv (A := A) hJt (P.map (Int.castRingHom A))) = 0 := by
    have := RingHom.congr_fun h1 P
    simp only [RingHom.comp_apply, coe_mapRingHom] at this
    rw [← this]; exact hPt
  have h3 : (P.map (Int.castRingHom A)).map (IsLocalRing.residue A) = 0 := by
    by_contra hne
    have hu := isUnit_gEv (A := A) hJt hne
    rw [← IsLocalRing.residue_ne_zero_iff_isUnit] at hu
    exact hu h2
  ext i
  rw [coeff_map, coeff_zero]
  by_contra hi
  have hni := intCast_notMem_maximalIdeal red ℓ (P.coeff i) hi
  apply hni
  have := congrArg (fun p => p.coeff i) h3
  simp only [coeff_map, coeff_zero, eq_intCast, IsLocalRing.residue_eq_zero_iff] at this
  exact this

def Theta [Fact ℓ.Prime] [CharP k ℓ] [CharP (IsLocalRing.ResidueField (VG A)) ℓ] :
    RatFunc (ZMod ℓ) →+* IsLocalRing.ResidueField (VG A) :=
  RatFunc.liftRingHom (theta A ℓ)
    (nonZeroDivisors_le_comap_nonZeroDivisors_of_injective _ (theta_injective red ℓ))

variable (k) in

def iotaK [Fact ℓ.Prime] [CharP k ℓ] : RatFunc (ZMod ℓ) →+* RatFunc k :=
  RatFunc.liftRingHom ((algebraMap k[X] (RatFunc k)).comp (mapRingHom (ZMod.castHom (dvd_refl ℓ) k)))
    (nonZeroDivisors_le_comap_nonZeroDivisors_of_injective _
      ((RatFunc.algebraMap_injective k).comp
        (Polynomial.map_injective _ (ZMod.castHom (dvd_refl ℓ) k).injective)))

include red ℓ in

theorem squarefree_fV_map_residue [Fact ℓ.Prime] [CharP k ℓ] (data : ModularPolynomialData N)
    (hsep : (((data.Φ.map (Polynomial.mapRingHom (Int.castRingHom k))).map
      (algebraMap (Polynomial k) (RatFunc k))).Separable)) :
    Squarefree ((fV N A data).map (IsLocalRing.residue (VG A))) := by
  haveI := charP_residueField_VG red ℓ (A := A)

  set Φℓ : (RatFunc (ZMod ℓ))[X] := data.Φ.map
    ((algebraMap (ZMod ℓ)[X] (RatFunc (ZMod ℓ))).comp (mapRingHom (Int.castRingHom (ZMod ℓ))))
    with hΦℓ
  have hk : (data.Φ.map (Polynomial.mapRingHom (Int.castRingHom k))).map
      (algebraMap (Polynomial k) (RatFunc k)) = Φℓ.map (iotaK k ℓ) := by
    rw [Polynomial.map_map, hΦℓ, Polynomial.map_map]
    congr 1
    apply intPoly_ringHom_ext
    simp [iotaK]
  rw [hk] at hsep
  have hsepℓ : Φℓ.Separable := (separable_map _).mp hsep
  have hsq : Squarefree (Φℓ.map (Theta red ℓ)) := (hsepℓ.map).squarefree
  have hid : Φℓ.map (Theta red ℓ) = (fV N A data).map (IsLocalRing.residue (VG A)) := by
    rw [hΦℓ, fV, Polynomial.map_map, Polynomial.map_map]
    congr 1
    apply intPoly_ringHom_ext
    simp [Theta, theta]
  rwa [hid] at hsq

end Residue
p2m_reactivate "P2MW.S_ModularCurve_CharPModel_FibreModel_coe_piInf_eq_coeffRed_of_cuspChart.PiInfQExpansion P2MW.S_ModularCurve_CharPModel_FibreModel_coe_piInf_eq_coeffRed_of_cuspChart.PiInfQExpansion.Gauss"

theorem affineBaseInf_le_range :
    (affineBaseInf N A).map (algebraMap (laurentBaseChange Qb (modularFunctionFieldFull N)) LL)
      ≤ (algebraMap (VG A) LL).range := by
  rw [Subring.map_le_iff_le_comap, affineBaseInf, Subring.closure_le]
  rintro y (⟨a, rfl⟩ | hy)
  · refine ⟨gConst hJt a, ?_⟩
    rw [algebraMap_VG_apply, coe_coe_gConst]
    rfl
  · rw [Set.mem_singleton_iff] at hy
    subst hy
    refine ⟨gJinv hJt, ?_⟩
    rw [algebraMap_VG_apply, coe_coe_gJinv]
    show (jqModC Qb)⁻¹ = (((jBar N)⁻¹ : laurentBaseChange Qb (modularFunctionFieldFull N)) : LL)
    rw [IntermediateField.coe_inv, coe_jBar]

theorem exists_monic_aeval_eq_zero {ℓ : ℕ} [Fact ℓ.Prime] {k : Type*} [Field k] [CharP k ℓ]
    {red : A →+* k} (fm : FibreModel N A ℓ k red) (b : fm.BInf) :
    ∃ q : Polynomial (VG A), q.Monic ∧
      aeval ((b : laurentBaseChange Qb (modularFunctionFieldFull N)) : LL)
        (q.map (algebraMap (VG A) K₀)) = 0 := by
  obtain ⟨p, hp, hpb⟩ := fm.integralInf b
  set FF := laurentBaseChange Qb (modularFunctionFieldFull N)

  set p₁ : Polynomial LL := p.map ((algebraMap FF LL).comp (affineBaseInf N A).subtype) with hp₁
  have hp₁m : p₁.Monic := hp.map _
  have hp₁b : p₁.eval ((b : FF) : LL) = 0 := by
    rw [hp₁, eval_map, show ((b : FF) : LL) = algebraMap FF LL b from rfl, ← Polynomial.hom_eval₂,
      hpb, map_zero]
  have hlifts : p₁ ∈ Polynomial.lifts (algebraMap (VG A) LL) := by
    rw [lifts_iff_coeff_lifts]
    intro n
    rw [hp₁, coeff_map]
    exact affineBaseInf_le_range N A ⟨_, (p.coeff n).2, rfl⟩
  obtain ⟨q, hq, -, hqm⟩ := lifts_and_degree_eq_and_monic hlifts hp₁m
  refine ⟨q, hqm, ?_⟩
  rw [aeval_map_algebraMap, aeval_def, ← eval_map, hq, hp₁b]

end PiInfQExpansion
p2m_reactivate "P2MW.S_ModularCurve_CharPModel_FibreModel_coe_piInf_eq_coeffRed_of_cuspChart.PiInfQExpansion P2MW.S_ModularCurve_CharPModel_FibreModel_coe_piInf_eq_coeffRed_of_cuspChart.PiInfQExpansion.Gauss"

namespace PiInfQExpansion

open ModularCurve ModularCurve.CharPModel ModularCurve.CharPReduction PiInfQExpansion.Gauss

local notation "Qb" => AlgebraicClosure ℚ
local notation "LL" => LaurentSeries (AlgebraicClosure ℚ)
local notation "K₀" => (AlgebraicClosure ℚ)⟮jqModC (AlgebraicClosure ℚ)⟯

variable (N : ℕ) [NeZero N] (A : ValuationSubring Qb)

def Rst : Subring LL :=
  Subring.closure (Set.range ((algebraMap Qb LL).comp A.subtype) ∪
    {(jqModC Qb)⁻¹, jqNModC Qb N * (jqModC Qb)⁻¹ ^ N})

theorem const_mem_Rst (a : A) : algebraMap Qb LL a ∈ Rst N A :=
  Subring.subset_closure (Or.inl ⟨a, rfl⟩)

theorem inv_mem_Rst : (jqModC Qb)⁻¹ ∈ Rst N A :=
  Subring.subset_closure (Or.inr (Set.mem_insert _ _))

theorem t_mem_Rst : jqNModC Qb N * (jqModC Qb)⁻¹ ^ N ∈ Rst N A :=
  Subring.subset_closure (Or.inr (Set.mem_insert_of_mem _ rfl))

theorem evJ_inv_mem_Rst (G : Polynomial A) : evJ A (jqModC Qb)⁻¹ G ∈ Rst N A := by
  rw [evJ, coe_eval₂RingHom]
  induction G using Polynomial.induction_on' with
  | add p q hp hq => rw [eval₂_add]; exact add_mem hp hq
  | monomial n a =>
    rw [eval₂_monomial]
    exact mul_mem (const_mem_Rst N A a) (pow_mem (inv_mem_Rst N A) _)

def HasDenom (x : LL) : Prop :=
  ∃ G : Polynomial A, G.map (IsLocalRing.residue A) ≠ 0 ∧ x * evJ A (jqModC Qb)⁻¹ G ∈ Rst N A

theorem hasDenom_zero : HasDenom N A 0 :=
  ⟨1, by simp, by rw [zero_mul]; exact zero_mem _⟩

variable {N A} in
theorem hasDenom_add {x y : LL} (hx : HasDenom N A x) (hy : HasDenom N A y) :
    HasDenom N A (x + y) := by
  obtain ⟨Gx, hGx, hx⟩ := hx
  obtain ⟨Gy, hGy, hy⟩ := hy
  refine ⟨Gx * Gy, map_residue_mul_ne_zero hGx hGy, ?_⟩
  rw [map_mul, show (x + y) * (evJ A (jqModC Qb)⁻¹ Gx * evJ A (jqModC Qb)⁻¹ Gy)
      = (x * evJ A (jqModC Qb)⁻¹ Gx) * evJ A (jqModC Qb)⁻¹ Gy
        + (y * evJ A (jqModC Qb)⁻¹ Gy) * evJ A (jqModC Qb)⁻¹ Gx by ring]
  exact add_mem (mul_mem hx (evJ_inv_mem_Rst N A _)) (mul_mem hy (evJ_inv_mem_Rst N A _))

variable {N A} in
theorem hasDenom_mul_mem {x r : LL} (hx : HasDenom N A x) (hr : r ∈ Rst N A) :
    HasDenom N A (x * r) := by
  obtain ⟨G, hG, hx⟩ := hx
  exact ⟨G, hG, by rw [mul_right_comm]; exact mul_mem hx hr⟩

variable {N A} in
theorem hasDenom_sum {ι : Type*} (s : Finset ι) (f : ι → LL) (h : ∀ i ∈ s, HasDenom N A (f i)) :
    HasDenom N A (∑ i ∈ s, f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => rw [Finset.sum_empty]; exact hasDenom_zero N A
  | insert a s ha ih =>
    rw [Finset.sum_insert ha]
    exact hasDenom_add (h a (Finset.mem_insert_self _ _))
      (ih fun i hi => h i (Finset.mem_insert_of_mem hi))

variable {N A} in

theorem hasDenom_of_isGaussInt {x : LL} (hx : IsGaussInt A (jqModC Qb) x) : HasDenom N A x := by
  obtain ⟨P, Q, hQ, h⟩ := hx
  haveI : Invertible (jqModC Qb) := invertibleOfNonzero jqModC_ne_zero
  set D := max P.natDegree Q.natDegree with hD
  refine ⟨reflect D Q, ?_, ?_⟩
  · rw [← reflect_map, Ne, reflect_eq_zero_iff]; exact hQ
  · have hs : (jqModC Qb)⁻¹ = ⅟(jqModC Qb) := (invOf_eq_inv _).symm
    have hP := eval₂_reflect_mul_pow ((algebraMap Qb LL).comp A.subtype) (jqModC Qb) D P
      (le_max_left _ _)
    have hQ' := eval₂_reflect_mul_pow ((algebraMap Qb LL).comp A.subtype) (jqModC Qb) D Q
      (le_max_right _ _)
    have key : x * evJ A (jqModC Qb)⁻¹ (reflect D Q) = evJ A (jqModC Qb)⁻¹ (reflect D P) := by
      have hJD : (jqModC Qb) ^ D ≠ 0 := pow_ne_zero _ jqModC_ne_zero
      apply mul_right_cancel₀ hJD
      simp only [evJ, coe_eval₂RingHom, hs] at h ⊢
      rw [mul_assoc, hQ', hP]
      exact h
    rw [key]
    exact evJ_inv_mem_Rst N A _

theorem isGaussInt_pow_self (m : ℕ) : IsGaussInt A (jqModC Qb) ((jqModC Qb) ^ m) :=
  ⟨X ^ m, 1, by simp, by simp [evJ]⟩

theorem hasDenom_of_sum {n : ℕ} (c : Fin n → VG A) :
    HasDenom N A (∑ i, algebraMap K₀ LL (c i : K₀) * (jqNModC Qb N) ^ (i : ℕ)) := by
  apply hasDenom_sum
  intro i _
  have hJ0 : jqModC Qb ≠ 0 := jqModC_ne_zero
  have e : algebraMap K₀ LL (c i : K₀) * jqNModC Qb N ^ (i : ℕ)
      = (((c i : K₀) : LL) * (jqModC Qb) ^ (N * i))
          * (jqNModC Qb N * (jqModC Qb)⁻¹ ^ N) ^ (i : ℕ) := by
    rw [IntermediateField.algebraMap_apply, mul_pow, ← pow_mul, inv_pow, mul_mul_mul_comm,
      mul_assoc ((c i : K₀) : LL) (jqNModC Qb N ^ (i : ℕ)), mul_inv_cancel₀ (pow_ne_zero _ hJ0),
      mul_one]
  rw [e]
  exact hasDenom_mul_mem
    (hasDenom_of_isGaussInt (IsGaussInt.mul (c i).2 (isGaussInt_pow_self A _)))
    (pow_mem (t_mem_Rst N A) _)

end PiInfQExpansion
p2m_reactivate "P2MW.S_ModularCurve_CharPModel_FibreModel_coe_piInf_eq_coeffRed_of_cuspChart.PiInfQExpansion P2MW.S_ModularCurve_CharPModel_FibreModel_coe_piInf_eq_coeffRed_of_cuspChart.PiInfQExpansion.Gauss"

namespace PiInfQExpansion

open ModularCurve ModularCurve.CharPModel ModularCurve.CharPReduction PiInfQExpansion.Gauss

local notation "Qb" => AlgebraicClosure ℚ
local notation "LL" => LaurentSeries (AlgebraicClosure ℚ)
local notation "K₀" => (AlgebraicClosure ℚ)⟮jqModC (AlgebraicClosure ℚ)⟯

section Final

variable {N : ℕ} [NeZero N] {A : ValuationSubring Qb} {ℓ : ℕ} [Fact ℓ.Prime]
  {k : Type*} [Field k] [CharP k ℓ] {red : A →+* k} (fm : FibreModel N A ℓ k red)

local notation "FF" => laurentBaseChange (AlgebraicClosure ℚ) (modularFunctionFieldFull N)

def coeLL : fm.BInf →+* LL := (algebraMap FF LL).comp fm.BInf.subtype

theorem coeLL_apply (y : fm.BInf) : coeLL fm y = ((y : FF) : LL) := rfl

theorem coeLL_injective : Function.Injective (coeLL fm) :=
  fun _ _ h => Subtype.ext (Subtype.ext h)

def Bint : Subring fm.BInf := (integralCoeffs A.toSubring).comap (coeLL fm)

def phi1 : Bint fm →+* LaurentSeries k :=
  ((algebraMap (modularFunctionFieldC k N) (LaurentSeries k)).comp fm.piInf).comp (Bint fm).subtype

def phi2 : Bint fm →+* LaurentSeries k :=
  (coeffRed A.toSubring red).comp (((coeLL fm).comp (Bint fm).subtype).codRestrict _ fun y => y.2)

theorem phi1_apply (y : Bint fm) :
    phi1 fm y = ((fm.piInf y : modularFunctionFieldC k N) : LaurentSeries k) := rfl

theorem phi2_apply (y : Bint fm) :
    phi2 fm y = coeffRed A.toSubring red ⟨coeLL fm y, y.2⟩ := rfl

def Egood : Subring LL :=
  ((RingHom.eqLocus (phi1 fm) (phi2 fm)).map (Bint fm).subtype).map (coeLL fm)

theorem mem_Egood_iff {x : LL} :
    x ∈ Egood fm ↔ ∃ y : Bint fm, phi1 fm y = phi2 fm y ∧ coeLL fm y = x := by
  constructor
  · rintro ⟨z, ⟨y, hy, rfl⟩, rfl⟩
    exact ⟨y, RingHom.mem_eqLocus.mp hy, rfl⟩
  · rintro ⟨y, hy, rfl⟩
    exact ⟨y, ⟨y, RingHom.mem_eqLocus.mpr hy, rfl⟩, rfl⟩

theorem mem_Egood_of (y : fm.BInf) (h3 : coeLL fm y ∈ integralCoeffs A.toSubring)
    (h : ((fm.piInf y : modularFunctionFieldC k N) : LaurentSeries k)
      = coeffRed A.toSubring red ⟨coeLL fm y, h3⟩) :
    coeLL fm y ∈ Egood fm :=
  (mem_Egood_iff fm).mpr ⟨⟨y, h3⟩, h, rfl⟩

omit [NeZero N] [Fact ℓ.Prime] [CharP k ℓ] in
theorem coeffMap_int_mem (x : LaurentSeries ℤ) :
    coeffMap (Int.castRingHom Qb) x ∈ integralCoeffs A.toSubring :=
  fun n => intCast_mem A.toSubring (x.coeff n)

omit [NeZero N] [Fact ℓ.Prime] [CharP k ℓ] in
theorem coeffRed_coeffMap_int (x : LaurentSeries ℤ) (hx : coeffMap (Int.castRingHom Qb) x ∈
      integralCoeffs A.toSubring) :
    coeffRed A.toSubring red ⟨coeffMap (Int.castRingHom Qb) x, hx⟩
      = coeffMap (Int.castRingHom k) x := by
  ext n
  rw [coeffRed_coeff]
  show red (⟨((x.coeff n : ℤ) : Qb), intCast_mem A.toSubring _⟩ : A) = ((x.coeff n : ℤ) : k)
  rw [← map_intCast red (x.coeff n)]
  exact congrArg red (Subtype.ext (map_intCast A.subtype _).symm)

omit [Fact ℓ.Prime] [CharP k ℓ] in
theorem coeffRed_jqModC (h : jqModC Qb ∈ integralCoeffs A.toSubring) :
    coeffRed A.toSubring red ⟨jqModC Qb, h⟩ = jqModC k := by
  have h' := h
  rw [jqModC_eq_coeffMap] at h'
  have : (⟨jqModC Qb, h⟩ : integralCoeffs A.toSubring) = ⟨_, h'⟩ :=
    Subtype.ext (jqModC_eq_coeffMap Qb)
  rw [this, coeffRed_coeffMap_int, ← jqModC_eq_coeffMap]

omit [Fact ℓ.Prime] [CharP k ℓ] in
theorem coeffRed_jqNModC (h : jqNModC Qb N ∈ integralCoeffs A.toSubring) :
    coeffRed A.toSubring red ⟨jqNModC Qb N, h⟩ = jqNModC k N := by
  have h' := h
  rw [jqNModC_eq_coeffMap] at h'
  have : (⟨jqNModC Qb N, h⟩ : integralCoeffs A.toSubring) = ⟨_, h'⟩ :=
    Subtype.ext (jqNModC_eq_coeffMap N Qb)
  rw [this, coeffRed_coeffMap_int, ← jqNModC_eq_coeffMap]

omit [NeZero N] [Fact ℓ.Prime] [CharP k ℓ] in
theorem coeffRed_const (a : A) (h : algebraMap Qb LL (a : Qb) ∈ integralCoeffs A.toSubring) :
    coeffRed A.toSubring red ⟨algebraMap Qb LL (a : Qb), h⟩
      = algebraMap k (LaurentSeries k) (red a) := by
  ext n
  rw [coeffRed_coeff, algebraMap_laurentSeries_eq_single k (red a)]
  by_cases hn : n = 0
  · subst hn
    rw [HahnSeries.coeff_single_same]
    show red (⟨(algebraMap Qb LL (a : Qb)).coeff 0, h 0⟩ : A) = red a
    refine congrArg red (Subtype.ext ?_)
    show (algebraMap Qb LL (a : Qb)).coeff 0 = a
    rw [algebraMap_laurentSeries_eq_single Qb, HahnSeries.coeff_single_same]
  · rw [HahnSeries.coeff_single_of_ne hn]
    show red (⟨(algebraMap Qb LL (a : Qb)).coeff n, h n⟩ : A) = 0
    rw [← map_zero red]
    refine congrArg red (Subtype.ext ?_)
    show (algebraMap Qb LL (a : Qb)).coeff n = 0
    rw [algebraMap_laurentSeries_eq_single Qb, HahnSeries.coeff_single_of_ne hn]

omit [Fact ℓ.Prime] [CharP k ℓ] in

theorem coeffRed_inv_jqModC (h : (jqModC Qb)⁻¹ ∈ integralCoeffs A.toSubring) :
    coeffRed A.toSubring red ⟨(jqModC Qb)⁻¹, h⟩ = (jqModC k)⁻¹ := by
  apply eq_inv_of_mul_eq_one_left
  rw [← coeffRed_jqModC (red := red) (jqModC_mem_integralCoeffs _), ← map_mul]
  have : (⟨(jqModC Qb)⁻¹, h⟩ : integralCoeffs A.toSubring) * ⟨jqModC Qb, jqModC_mem_integralCoeffs _⟩
      = 1 := Subtype.ext (inv_mul_cancel₀ jqModC_ne_zero)
  rw [this, map_one]

omit [NeZero N] [Fact ℓ.Prime] [CharP k ℓ] in

theorem inv_jqModC_mem_integralCoeffs : (jqModC Qb)⁻¹ ∈ integralCoeffs A.toSubring := by

  set u : PowerSeries ℤ := PowerSeries.invOfUnit jNum 1 with hu
  have hju : jNum * u = 1 := by
    apply PowerSeries.mul_invOfUnit jNum 1
    rw [Units.val_one]
    exact constantCoeff_jNum
  set sZ : LaurentSeries ℤ := HahnSeries.single (1 : ℤ) (1 : ℤ) * HahnSeries.ofPowerSeries ℤ ℤ u
    with hsZ
  have hid : PowerSeries.map (Int.castRingHom ℤ) jNum = jNum := by
    ext n; simp
  have hprod : jqModC ℤ * sZ = 1 := by
    show HahnSeries.single (-1 : ℤ) (1 : ℤ) * HahnSeries.ofPowerSeries ℤ ℤ (PowerSeries.map
        (Int.castRingHom ℤ) jNum) * sZ = 1
    rw [hid, hsZ, mul_mul_mul_comm, HahnSeries.single_mul_single, ← map_mul, hju, map_one, mul_one]
    simp
  have hcast : (jqModC Qb)⁻¹ = coeffMap (Int.castRingHom Qb) sZ := by
    symm
    apply eq_inv_of_mul_eq_one_left
    rw [jqModC_eq_coeffMap, ← map_mul, mul_comm, hprod, map_one]
  rw [hcast]
  exact coeffMap_int_mem sZ

theorem const_mem_Egood (a : A) : algebraMap Qb LL a ∈ Egood fm := by
  have h3 : algebraMap Qb LL (a : Qb) ∈ integralCoeffs A.toSubring :=
    constSeries_mem_integralCoeffs A.toSubring ⟨a, a.2⟩
  have hco : coeLL fm ⟨constantsHom N A a, fm.constInf_mem a⟩ = algebraMap Qb LL a := rfl
  rw [← hco]
  refine mem_Egood_of fm _ h3 ?_
  rw [fm.piInf_const a]
  exact (IntermediateField.coe_algebraMap_apply _ _).trans (coeffRed_const a h3).symm

theorem inv_mem_Egood : (jqModC Qb)⁻¹ ∈ Egood fm := by
  have hco : coeLL fm ⟨(jBar N)⁻¹, fm.jInvBar_mem⟩ = (jqModC Qb)⁻¹ := by
    rw [coeLL_apply, IntermediateField.coe_inv, coe_jBar]
  have h3 : coeLL fm ⟨(jBar N)⁻¹, fm.jInvBar_mem⟩ ∈ integralCoeffs A.toSubring := by
    rw [hco]; exact inv_jqModC_mem_integralCoeffs
  rw [← hco]
  refine mem_Egood_of fm _ h3 ?_
  rw [fm.piInf_jInv, IntermediateField.coe_inv]
  have : (⟨coeLL fm ⟨(jBar N)⁻¹, fm.jInvBar_mem⟩, h3⟩ : integralCoeffs A.toSubring)
      = ⟨(jqModC Qb)⁻¹, inv_jqModC_mem_integralCoeffs⟩ := Subtype.ext hco
  rw [this, coeffRed_inv_jqModC]

theorem t_mem_Egood (hc : fm.CuspChart) : jqNModC Qb N * (jqModC Qb)⁻¹ ^ N ∈ Egood fm := by
  have hco : coeLL fm ⟨jNBar N * ((jBar N)⁻¹) ^ N, hc.tBar_mem⟩
      = jqNModC Qb N * (jqModC Qb)⁻¹ ^ N := by
    rw [coeLL_apply, IntermediateField.coe_mul, IntermediateField.coe_pow,
      IntermediateField.coe_inv, coe_jBar, coe_jNBar]
  have h3' : jqNModC Qb N * (jqModC Qb)⁻¹ ^ N ∈ integralCoeffs A.toSubring :=
    mul_mem (jqNModC_mem_integralCoeffs N _) (pow_mem inv_jqModC_mem_integralCoeffs N)
  have h3 : coeLL fm ⟨jNBar N * ((jBar N)⁻¹) ^ N, hc.tBar_mem⟩ ∈ integralCoeffs A.toSubring := by
    rw [hco]; exact h3'
  rw [← hco]
  refine mem_Egood_of fm _ h3 ?_
  rw [hc.piInf_t, IntermediateField.coe_mul, IntermediateField.coe_pow, IntermediateField.coe_inv]
  have : (⟨coeLL fm ⟨jNBar N * ((jBar N)⁻¹) ^ N, hc.tBar_mem⟩, h3⟩ : integralCoeffs A.toSubring)
      = ⟨jqNModC Qb N, jqNModC_mem_integralCoeffs N _⟩
        * ⟨(jqModC Qb)⁻¹, inv_jqModC_mem_integralCoeffs⟩ ^ N := Subtype.ext hco
  rw [this, map_mul, map_pow, coeffRed_jqNModC, coeffRed_inv_jqModC]

theorem Rst_le_Egood (hc : fm.CuspChart) : Rst N A ≤ Egood fm := by
  rw [Rst, Subring.closure_le]
  rintro x (⟨a, rfl⟩ | hx)
  · exact const_mem_Egood fm a
  · rcases hx with rfl | hx
    · exact inv_mem_Egood fm
    · rw [Set.mem_singleton_iff.mp hx]; exact t_mem_Egood fm hc

theorem coeffRed_evJ_ne_zero (G : Polynomial A) (hG : G.map (IsLocalRing.residue A) ≠ 0)
    (h3 : evJ A (jqModC Qb)⁻¹ G ∈ integralCoeffs A.toSubring) :
    coeffRed A.toSubring red ⟨evJ A (jqModC Qb)⁻¹ G, h3⟩ ≠ 0 := by

  set cA : A →+* integralCoeffs A.toSubring :=
    ((algebraMap Qb LL).comp A.subtype).codRestrict _ fun a =>
      constSeries_mem_integralCoeffs A.toSubring ⟨a, a.2⟩ with hcA
  set sI : integralCoeffs A.toSubring := ⟨(jqModC Qb)⁻¹, inv_jqModC_mem_integralCoeffs⟩
  have he : (⟨evJ A (jqModC Qb)⁻¹ G, h3⟩ : integralCoeffs A.toSubring) = eval₂ cA sI G := by
    apply Subtype.ext
    show evJ A (jqModC Qb)⁻¹ G = (integralCoeffs A.toSubring).subtype (eval₂ cA sI G)
    rw [Polynomial.hom_eval₂, evJ, coe_eval₂RingHom]
    rfl
  rw [he, Polynomial.hom_eval₂, coeffRed_inv_jqModC]
  have hc : (coeffRed A.toSubring red).comp cA = (algebraMap k (LaurentSeries k)).comp red := by
    ext a : 1
    simp only [RingHom.comp_apply]
    exact coeffRed_const a _
  rw [hc, ← eval₂_map, ← aeval_def]
  have ht : Transcendental k (jqModC k)⁻¹ := fun h =>
    transcendental_jqModC k (IsAlgebraic.inv_iff.mp h)
  intro h0
  exact map_ne_zero_of_map_residue_ne_zero red hG ((transcendental_iff.mp ht) _ h0)

theorem coe_piInf_eq_coeffRed_of_cuspChart (hc : fm.CuspChart) (data : ModularPolynomialData N)
    (hsep : (((data.Φ.map (Polynomial.mapRingHom (Int.castRingHom k))).map
      (algebraMap (Polynomial k) (RatFunc k))).Separable))
    (b : fm.BInf)
    (hmem : ((b : FF) : LL) ∈ integralCoeffs A.toSubring) :
    ((fm.piInf b : modularFunctionFieldC k N) : LaurentSeries k)
      = coeffRed A.toSubring red ⟨_, hmem⟩ := by

  obtain ⟨q, hqm, hqb⟩ := exists_monic_aeval_eq_zero N A fm b
  obtain ⟨n, c, hbc⟩ := PiInfQExpansion.Dedekind.exists_eq_sum_of_isIntegral (VG A) (jqNModC Qb N)
    (fV N A data) (fV_monic N A data) (aeval_fV N A data)
    (squarefree_fV_map_residue N red ℓ data hsep) ((b : FF) : LL)
    (mem_adjoin_adjoin N _ (b : FF).2) q hqm hqb

  obtain ⟨G, hG, hr⟩ : HasDenom N A ((b : FF) : LL) := hbc ▸ hasDenom_of_sum N A c

  have hle := Rst_le_Egood fm hc
  obtain ⟨yg, hyg, hcg⟩ := (mem_Egood_iff fm).mp (hle (evJ_inv_mem_Rst N A G))
  obtain ⟨yr, hyr, hcr⟩ := (mem_Egood_iff fm).mp (hle hr)

  let yb : Bint fm := ⟨b, hmem⟩
  have hprod : yb * yg = yr := by
    apply Subtype.ext
    apply coeLL_injective fm
    rw [MulMemClass.coe_mul, map_mul, hcr, hcg]
    rfl
  have h1 : phi1 fm yb * phi1 fm yg = phi2 fm yb * phi2 fm yg := by
    rw [← map_mul, ← map_mul, hprod, hyr]
  rw [hyg] at h1
  have hne : phi2 fm yg ≠ 0 := by
    rw [phi2_apply]
    have h3 : evJ A (jqModC Qb)⁻¹ G ∈ integralCoeffs A.toSubring := hcg ▸ yg.2
    have : (⟨coeLL fm yg, yg.2⟩ : integralCoeffs A.toSubring) = ⟨_, h3⟩ := Subtype.ext hcg
    rw [this]
    exact coeffRed_evJ_ne_zero G hG h3
  exact mul_right_cancel₀ hne h1

end Final
p2m_reactivate "P2MW.S_ModularCurve_CharPModel_FibreModel_coe_piInf_eq_coeffRed_of_cuspChart.PiInfQExpansion P2MW.S_ModularCurve_CharPModel_FibreModel_coe_piInf_eq_coeffRed_of_cuspChart.PiInfQExpansion.Gauss"

end PiInfQExpansion
p2m_reactivate "P2MW.S_ModularCurve_CharPModel_FibreModel_coe_piInf_eq_coeffRed_of_cuspChart.PiInfQExpansion P2MW.S_ModularCurve_CharPModel_FibreModel_coe_piInf_eq_coeffRed_of_cuspChart.PiInfQExpansion.Gauss"

end
p2m_reactivate "P2MW.S_ModularCurve_CharPModel_FibreModel_coe_piInf_eq_coeffRed_of_cuspChart.PiInfQExpansion P2MW.S_ModularCurve_CharPModel_FibreModel_coe_piInf_eq_coeffRed_of_cuspChart.PiInfQExpansion.Gauss"

open ModularCurve ModularCurve.CharPModel ModularCurve.CharPReduction in
theorem solution
    (N : ℕ) [NeZero N] (A : ValuationSubring (AlgebraicClosure ℚ))
    (ℓ : ℕ) [Fact ℓ.Prime] (k : Type*) [Field k] [CharP k ℓ]
    (red : A →+* k) (fm : FibreModel N A ℓ k red) (hc : fm.CuspChart)
    (data : ModularPolynomialData N)
    (hsep : (((data.Φ.map (Polynomial.mapRingHom (Int.castRingHom k))).map
      (algebraMap (Polynomial k) (RatFunc k))).Separable))
    (b : fm.BInf)
    (hmem : ((b : laurentBaseChange (AlgebraicClosure ℚ) (modularFunctionFieldFull N)) :
        LaurentSeries (AlgebraicClosure ℚ)) ∈ integralCoeffs A.toSubring) :
    ((fm.piInf b : modularFunctionFieldC k N) : LaurentSeries k)
      = coeffRed A.toSubring red ⟨_, hmem⟩ :=
  PiInfQExpansion.coe_piInf_eq_coeffRed_of_cuspChart fm hc data hsep b hmem

end S_ModularCurve_CharPModel_FibreModel_coe_piInf_eq_coeffRed_of_cuspChart
end P2MW
export P2MW.S_ModularCurve_CharPModel_FibreModel_coe_piInf_eq_coeffRed_of_cuspChart (solution)
