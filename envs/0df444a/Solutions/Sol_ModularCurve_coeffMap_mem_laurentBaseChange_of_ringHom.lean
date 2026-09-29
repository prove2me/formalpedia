-- Prove2me | solution 1 for ModularCurve.coeffMap_mem_laurentBaseChange_of_ringHom
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:11.261198+00:00
-- url     : https://prove2.me/submissions/3fae2c98-e6ac-5519-9a37-54647782cfbb

import Definitions.Def_AlgebraicCurve_Differentials
import Definitions.Def_ModularCurve_QExpansionDiff
import Definitions.Def_ModularCurve_ArithmeticGalois
import Theorems.Thm_ModularCurve_qExpansionDiffAlong_D
import Theorems.Thm_ModularCurve_qExpansionDiffAlong_smul
import Theorems.Thm_ModularCurve_finiteDimensional_adjoin_coeffEmb_jq_full
import Theorems.Thm_ModularCurve_isSeparable_adjoin_coeffEmb_jq_full
import Theorems.Thm_AlgebraicCurve_Place_ordDiff_smul
import Theorems.Thm_AlgebraicCurve_Place_ordDiff_D_nonneg
import Theorems.Thm_AlgebraicCurve_Place_ordDiff_zero
import Theorems.Thm_P2M_Dup_AlgebraicCurve_Place_ord_nonneg_of_mem
import Theorems.Thm_KaehlerDifferential_D_ne_zero_of_transcendental
import Theorems.Thm_ModularCurve_transcendental_coeffEmb_jq
import Mathlib.Analysis.Complex.Basic
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_coeffMap_mem_laurentBaseChange_of_ringHom
p2m_attr_erase "instance" "ModularCurve.instIsDomainTensorProduct AlgebraicClosure.Rat.isGalois AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.instFundamentalIdentityOfSumRamificationInertia AlgebraicCurve.Place.instIsScalarTowerResidueFieldRestrictPushforward AlgebraicCurve.Place.instAlgebraResidueFieldRestrictPushforward AlgebraicCurve.Place.instIsLocalHomRestrictInclusion AlgebraicCurve.IsCurveOver.instNontrivialKaehler AlgebraicCurve.IsCurveOver.instFreeKaehler AlgebraicCurve.IsCurveOver.toHasPrincipalDivisors AlgebraicCurve.IsCurveOver.instFiniteResidue AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation instDecEqAlgebraicClosureRat WeierstrassCurve.Affine.Point.instDistribMulActionAlgEquiv WeierstrassCurve.Affine.Point.instModuleZModTorsionBy WeierstrassCurve.Affine.Point.instSMulTorsionBy WeierstrassCurve.Affine.Point.instDistribMulActionTorsionBy WeierstrassCurve.Affine.Point.instSMulAlgEquiv WeierstrassCurve.Affine.Point.instSMulCommClassAlgEquivZModTorsionBy ModularCurve.PhiGen.instNeZeroPhiGenCosetA"
p2m_attr_erase "simp" "ModularCurve.coe_baseChangeEquiv_apply ModularCurve.baseChangeHom_tmul ModularCurve.jqNModC_one ModularCurve.coe_cuspidalDivisor₀ AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal AlgebraicCurve.Divisor.mapRestrict_single AlgebraicCurve.Divisor.pushforward_single AlgebraicCurve.Place.coe_restrictInclusion AlgebraicCurve.Place.mem_fiber AlgebraicCurve.Place.restrict_toValuationSubring AlgebraicCurve.Divisor.degree_pushforward AlgebraicCurve.Place.restrictResidueMap_residue AlgebraicCurve.Pic0.coe_pushforwardDegZeroHom AlgebraicCurve.Pic0.coe_pullbackDegZeroHom AlgebraicCurve.IsFrobeniusEndo.frobNormRingHom_apply ModularCurve.frobeniusPushforwardGeomLevelPic0_mk ModularCurve.coe_frobeniusGeomLevelEquiv_apply ModularCurve.coe_frobeniusPushforwardGeomLevelDegZero ModularCurve.heckeFibreGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusGeomLevel_apply_coe ModularCurve.frobeniusPullbackGeomLevelPic0OfIsCurveOver_mk ModularCurve.coe_heckeFibreGeomLevelDegZero ModularCurve.coe_frobeniusPullbackGeomLevelDegZero ModularCurve.frobeniusPullbackGeomLevelPic0_mk ModularCurve.frobeniusPullbackGeomLevel_single ModularCurve.heckeFibreGeomLevelPic0_mk ModularCurve.frobeniusPushforwardGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusPushforwardGeomLevel_single ModularCurve.qExpandAlgC_apply AlgebraicCurve.Place.congrEquiv_symm_apply AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply AlgebraicCurve.RationalFunctionField.deg_placeOfPoint AlgebraicCurve.Divisor.degree_pushforwardAlong"
p2m_attr_erase "simp" "AlgebraicCurve.Pic0.coe_degZeroCorrespondence AlgebraicCurve.Place.mem_fiberAlong AlgebraicCurve.coe_frobeniusPushforwardDegZero AlgebraicCurve.IsFrobeniusEndo.coe_frobeniusPullbackDegZero ModularCurve.reduceModBivar_C_X ModularCurve.laurentMap_coeff ModularCurve.reduceModBivar_X ModularCurve.laurentMap_single ModularCurve.evalAtJInt_X ModularCurve.evalAtJMod_X ModularCurve.jqNMod_one ModularCurve.aeval_heckeGen ModularCurve.coe_mTorsionGaloisRep_apply ModularCurve.eisensteinSystem_of_dvd ModularCurve.eisensteinSystem_of_not_dvd FreyPackage.mk.sizeOf_spec FreyPackage.mk.injEq WeierstrassCurve.Affine.Point.galoisRepModuleEnd_apply ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL ModularCurve.eisensteinNumerator_nineteen ModularCurve.eisensteinNumerator_seventeen"
p2m_attr_erase "simp" "ModularCurve.eisensteinNumerator_eleven ModularCurve.eisensteinNumerator_five ModularCurve.eisensteinNumerator_seven ModularCurve.eisensteinNumerator_twentythree ModularCurve.eisensteinNumerator_thirteen ModularCurve.constantCoeff_dedekindEtaUnitQ"
set_option maxHeartbeats 3200000
set_option synthInstance.maxHeartbeats 640000

set_option autoImplicit false

p2m_open "ModularCurve P2MW.S_ModularCurve_coeffMap_mem_laurentBaseChange_of_ringHom.ModularCurve AlgebraicCurve P2MW.S_ModularCurve_coeffMap_mem_laurentBaseChange_of_ringHom.AlgebraicCurve KaehlerDifferential"

private theorem thetaL_coeff_aux {R : Type*} [Field R] (f : LaurentSeries R) (n : ℤ) :
    (thetaL R f).coeff n = n • f.coeff n := by
  rw [thetaL_apply, HahnSeries.coeff_single_mul, LaurentSeries.derivative_apply,
    LaurentSeries.hasseDeriv_coeff, one_mul]
  simp

namespace ModularCurve p2m_export "ModularCurve" "thetaL thetaL_apply qExpansionDiffAlong modularFunctionFieldBar jq coeff_jq_neg_one modularFunctionFieldFull coeffMap coeffMap_coeff coeffMap_single coeffMap_coeffMap coeffMap_congr algebraMap_laurentSeries_eq_single coeffEmb coeffEmb_coeff laurentBaseChange coeffEmb_mem_laurentBaseChange mem_laurentBaseChange_iff qExpansionDiffAlong_D qExpansionDiffAlong_smul finiteDimensional_adjoin_coeffEmb_jq_full jq_mem_full isSeparable_adjoin_coeffEmb_jq_full transcendental_coeffEmb_jq" end ModularCurve
p2m_open_scoped "ModularCurve" in
private theorem ModularCurve.coeffMap_thetaL {R S : Type*} [Field R] [Field S] (σ : R →+* S) (f : LaurentSeries R) : ModularCurve.coeffMap σ (ModularCurve.thetaL R f) = ModularCurve.thetaL S (ModularCurve.coeffMap σ f) := by
  ext n
  rw [coeffMap_coeff, thetaL_coeff_aux, thetaL_coeff_aux, coeffMap_coeff, map_zsmul]

p2m_open_scoped "ModularCurve" in
private theorem ModularCurve.coeffMap_coeffEmb_of_ringHom {L₁ L₂ : Type*} [Field L₁] [Field L₂] [Algebra ℚ L₁] [Algebra ℚ L₂] (σ : L₁ →+* L₂) (x : LaurentSeries ℚ) : ModularCurve.coeffMap σ (ModularCurve.coeffEmb L₁ x) = ModularCurve.coeffEmb L₂ x := by
  show coeffMap σ (coeffMap (algebraMap ℚ L₁) x) = coeffMap (algebraMap ℚ L₂) x
  rw [coeffMap_coeffMap]
  exact coeffMap_congr (Subsingleton.elim _ _) x

p2m_open_scoped "ModularCurve" in
private theorem ModularCurve.coeffMap_mem_laurentBaseChange_of_ringHom {L₁ L₂ : Type*} [Field L₁] [Field L₂] [Algebra ℚ L₁] [Algebra ℚ L₂] (σ : L₁ →+* L₂) (F₀ : IntermediateField ℚ (LaurentSeries ℚ)) {x : LaurentSeries L₁} (hx : x ∈ ModularCurve.laurentBaseChange L₁ F₀) : ModularCurve.coeffMap σ x ∈ ModularCurve.laurentBaseChange L₂ F₀ := by
  rw [mem_laurentBaseChange_iff] at hx
  induction hx using Subfield.closure_induction with
  | mem y hy =>
      rcases hy with ⟨c, rfl⟩ | ⟨z, hz, rfl⟩
      · rw [algebraMap_laurentSeries_eq_single, coeffMap_single,
          ← algebraMap_laurentSeries_eq_single]
        exact (laurentBaseChange L₂ F₀).algebraMap_mem (σ c)
      · rw [coeffMap_coeffEmb_of_ringHom]
        exact coeffEmb_mem_laurentBaseChange L₂ hz
  | one => rw [map_one]; exact one_mem _
  | add a b _ _ ha hb => rw [map_add]; exact add_mem ha hb
  | neg a _ ha => rw [map_neg]; exact neg_mem ha
  | inv a _ ha => rw [map_inv₀]; exact inv_mem ha
  | mul a b _ _ ha hb => rw [map_mul]; exact mul_mem ha hb

p2m_open_scoped "ModularCurve" in
private theorem ModularCurve.qExpansionDiffAlong_coeffMap_smul_D_coeffMap {L₁ L₂ : Type*} [Field L₁] [Field L₂] [Algebra ℚ L₁] [Algebra ℚ L₂] (σ : L₁ →+* L₂) (F₀ : IntermediateField ℚ (LaurentSeries ℚ)) (c t : ModularCurve.laurentBaseChange L₁ F₀) : ModularCurve.qExpansionDiffAlong (K := L₂) (L := L₂) (ModularCurve.laurentBaseChange L₂ F₀).val ((⟨ModularCurve.coeffMap σ (c : LaurentSeries L₁), ModularCurve.coeffMap_mem_laurentBaseChange_of_ringHom σ F₀ c.2⟩ : ModularCurve.laurentBaseChange L₂ F₀) • KaehlerDifferential.D L₂ (ModularCurve.laurentBaseChange L₂ F₀) ⟨ModularCurve.coeffMap σ (t : LaurentSeries L₁), ModularCurve.coeffMap_mem_laurentBaseChange_of_ringHom σ F₀ t.2⟩) = ModularCurve.coeffMap σ (ModularCurve.qExpansionDiffAlong (K := L₁) (L := L₁) (ModularCurve.laurentBaseChange L₁ F₀).val (c • KaehlerDifferential.D L₁ (ModularCurve.laurentBaseChange L₁ F₀) t)) := by
  erw [qExpansionDiffAlong_smul, qExpansionDiffAlong_D,
    qExpansionDiffAlong_smul, qExpansionDiffAlong_D]
  rw [map_mul, coeffMap_thetaL]
  rfl

namespace AlgebraicCurve p2m_export "AlgebraicCurve" "regularDiffs Place Place.ordDiff_smul Place.ordDiff_D_nonneg Place.ordDiff_zero Place.ord_nonneg_of_mem" namespace Place p2m_export "AlgebraicCurve.Place" "ordDiff ext ord toValuationSubring ordDiff_smul ordDiff_D_nonneg ordDiff_zero ord_nonneg_of_mem" end AlgebraicCurve.Place
p2m_open_scoped "AlgebraicCurve AlgebraicCurve.Place" in
private theorem AlgebraicCurve.Place.ordDiff_smul_D_nonneg_of_ord_nonneg {K F : Type*} [Field K] [Field F] [Algebra K F] [CharZero K] (x : F) [FiniteDimensional (IntermediateField.adjoin K ({x} : Set F)) F] (v : AlgebraicCurve.Place K F) {c : F} (hc : 0 ≤ v.ord c) {t : F} (ht : 0 ≤ v.ord t) (hDt : KaehlerDifferential.D K F t ≠ 0) : 0 ≤ v.ordDiff (c • KaehlerDifferential.D K F t) := by
  haveI : Algebra.IsAlgebraic (IntermediateField.adjoin K ({x} : Set F)) F :=
    Algebra.IsAlgebraic.of_finite _ _
  rcases eq_or_ne c 0 with rfl | hc0
  · rw [zero_smul, Place.ordDiff_zero x]
  · rw [Place.ordDiff_smul x v hc0 hDt]
    exact add_nonneg hc (Place.ordDiff_D_nonneg x v ht)

p2m_open_scoped "ModularCurve" in
private theorem ModularCurve.ordDiff_coeffMap_smul_D_coeffEmb_jq_nonneg_of_forall_mem (N : ℕ) [NeZero N] (σ : AlgebraicClosure ℚ →+* ℂ) (c : ModularCurve.modularFunctionFieldBar N) (w : AlgebraicCurve.Place ℂ (ModularCurve.laurentBaseChange ℂ (ModularCurve.modularFunctionFieldFull N))) (hw : ∀ x : ModularCurve.modularFunctionFieldBar N, (⟨ModularCurve.coeffMap σ (x : LaurentSeries (AlgebraicClosure ℚ)), ModularCurve.coeffMap_mem_laurentBaseChange_of_ringHom σ (ModularCurve.modularFunctionFieldFull N) x.2⟩ : ModularCurve.laurentBaseChange ℂ (ModularCurve.modularFunctionFieldFull N)) ∈ w.toValuationSubring) : 0 ≤ w.ordDiff ((⟨ModularCurve.coeffMap σ (c : LaurentSeries (AlgebraicClosure ℚ)), ModularCurve.coeffMap_mem_laurentBaseChange_of_ringHom σ (ModularCurve.modularFunctionFieldFull N) c.2⟩ : ModularCurve.laurentBaseChange ℂ (ModularCurve.modularFunctionFieldFull N)) • KaehlerDifferential.D ℂ (ModularCurve.laurentBaseChange ℂ (ModularCurve.modularFunctionFieldFull N)) ⟨ModularCurve.coeffEmb ℂ ModularCurve.jq, ModularCurve.coeffEmb_mem_laurentBaseChange ℂ (ModularCurve.jq_mem_full N)⟩) := by
  haveI := finiteDimensional_adjoin_coeffEmb_jq_full ℂ N
  haveI := isSeparable_adjoin_coeffEmb_jq_full ℂ N
  have hjord : 0 ≤ w.ord
      (⟨coeffEmb ℂ jq, coeffEmb_mem_laurentBaseChange ℂ (jq_mem_full N)⟩ :
        laurentBaseChange ℂ (modularFunctionFieldFull N)) := by
    have hjeq :
        (⟨coeffEmb ℂ jq, coeffEmb_mem_laurentBaseChange ℂ (jq_mem_full N)⟩ :
            laurentBaseChange ℂ (modularFunctionFieldFull N)) =
          ⟨coeffMap σ (coeffEmb (AlgebraicClosure ℚ) jq),
            coeffMap_mem_laurentBaseChange_of_ringHom σ (modularFunctionFieldFull N)
              (coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) (jq_mem_full N))⟩ :=
      Subtype.ext (coeffMap_coeffEmb_of_ringHom σ jq).symm
    rw [hjeq]
    exact w.ord_nonneg_of_mem
      (hw ⟨coeffEmb (AlgebraicClosure ℚ) jq,
        coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) (jq_mem_full N)⟩)
  exact Place.ordDiff_smul_D_nonneg_of_ord_nonneg
    (⟨coeffEmb ℂ jq, coeffEmb_mem_laurentBaseChange ℂ (jq_mem_full N)⟩ :
      laurentBaseChange ℂ (modularFunctionFieldFull N)) w
    (w.ord_nonneg_of_mem (hw c)) hjord
    (D_ne_zero_of_transcendental ℂ
      (⟨coeffEmb ℂ jq, coeffEmb_mem_laurentBaseChange ℂ (jq_mem_full N)⟩ :
        laurentBaseChange ℂ (modularFunctionFieldFull N))
      (transcendental_coeffEmb_jq ℂ N))

section Ed2Derivative

private theorem derivative_coeff_aux {R : Type*} [CommRing R] (f : LaurentSeries R) (n : ℤ) :
    (LaurentSeries.derivative R f).coeff n = (n + 1) • f.coeff (n + 1) := by
  rw [LaurentSeries.derivative_apply, LaurentSeries.hasseDeriv_coeff]
  simp

p2m_open_scoped "ModularCurve" in
private theorem ModularCurve.coeffMap_derivative {R S : Type*} [CommRing R] [CommRing S] (σ : R →+* S) (f : LaurentSeries R) : ModularCurve.coeffMap σ (LaurentSeries.derivative R f) = LaurentSeries.derivative S (ModularCurve.coeffMap σ f) := by
  ext n
  rw [coeffMap_coeff, derivative_coeff_aux, derivative_coeff_aux, coeffMap_coeff, map_zsmul]

p2m_open_scoped "ModularCurve" in
private theorem ModularCurve.coeffMap_single_one_mul_derivative {R S : Type*} [CommRing R] [CommRing S] (σ : R →+* S) (f : LaurentSeries R) : ModularCurve.coeffMap σ ((HahnSeries.single (1 : ℤ) (1 : R) : LaurentSeries R) * LaurentSeries.derivative R f) = (HahnSeries.single (1 : ℤ) (1 : S) : LaurentSeries S) * LaurentSeries.derivative S (ModularCurve.coeffMap σ f) := by
  rw [map_mul, coeffMap_single, map_one, coeffMap_derivative]

end Ed2Derivative

section Ed2Engine4

p2m_open_scoped "ModularCurve" in
private theorem ModularCurve.qExpansionDiffAlong_coeffMap_smul_D_coeffMap_of_coe_eq {L₁ L₂ : Type*} [Field L₁] [Field L₂] [Algebra ℚ L₁] [Algebra ℚ L₂] (σ : L₁ →+* L₂) (F₀ : IntermediateField ℚ (LaurentSeries ℚ)) (c t : ModularCurve.laurentBaseChange L₁ F₀) (c' t' : ModularCurve.laurentBaseChange L₂ F₀) (hcc' : (c' : LaurentSeries L₂) = ModularCurve.coeffMap σ (c : LaurentSeries L₁)) (htt' : (t' : LaurentSeries L₂) = ModularCurve.coeffMap σ (t : LaurentSeries L₁)) : ModularCurve.qExpansionDiffAlong (K := L₂) (L := L₂) (ModularCurve.laurentBaseChange L₂ F₀).val (c' • KaehlerDifferential.D L₂ (ModularCurve.laurentBaseChange L₂ F₀) t') = ModularCurve.coeffMap σ (ModularCurve.qExpansionDiffAlong (K := L₁) (L := L₁) (ModularCurve.laurentBaseChange L₁ F₀).val (c • KaehlerDifferential.D L₁ (ModularCurve.laurentBaseChange L₁ F₀) t)) := by
  obtain rfl : c' = ⟨coeffMap σ (c : LaurentSeries L₁),
      coeffMap_mem_laurentBaseChange_of_ringHom σ F₀ c.2⟩ := Subtype.ext hcc'
  obtain rfl : t' = ⟨coeffMap σ (t : LaurentSeries L₁),
      coeffMap_mem_laurentBaseChange_of_ringHom σ F₀ t.2⟩ := Subtype.ext htt'
  exact qExpansionDiffAlong_coeffMap_smul_D_coeffMap σ F₀ c t

end Ed2Engine4

section Ed2JqCoeff

p2m_open_scoped "ModularCurve" in
private theorem ModularCurve.coeff_thetaL_coeffEmb_jq_neg_one (L : Type*) [Field L] [Algebra ℚ L] : (ModularCurve.thetaL L (ModularCurve.coeffEmb L ModularCurve.jq)).coeff (-1 : ℤ) = -1 := by
  simp [thetaL_coeff_aux, coeffEmb_coeff, coeff_jq_neg_one]

p2m_open_scoped "ModularCurve" in
private theorem ModularCurve.coeff_thetaL_coeffMap_coeffEmb_jq_neg_one {L₁ L₂ : Type*} [Field L₁] [Field L₂] [Algebra ℚ L₁] [Algebra ℚ L₂] (σ : L₁ →+* L₂) : (ModularCurve.thetaL L₂ (ModularCurve.coeffMap σ (ModularCurve.coeffEmb L₁ ModularCurve.jq))).coeff (-1 : ℤ) = -1 := by
  rw [coeffMap_coeffEmb_of_ringHom]
  exact coeff_thetaL_coeffEmb_jq_neg_one L₂

end Ed2JqCoeff

open _root_.ModularCurve _root_.P2MW.S_ModularCurve_coeffMap_mem_laurentBaseChange_of_ringHom.ModularCurve _root_.AlgebraicCurve _root_.P2MW.S_ModularCurve_coeffMap_mem_laurentBaseChange_of_ringHom.AlgebraicCurve in

theorem solution {L₁ L₂ : Type*} [Field L₁] [Field L₂] [Algebra ℚ L₁] [Algebra ℚ L₂] (σ : L₁ →+* L₂) (F₀ : IntermediateField ℚ (LaurentSeries ℚ)) {x : LaurentSeries L₁} (hx : x ∈ ModularCurve.laurentBaseChange L₁ F₀) : ModularCurve.coeffMap σ x ∈ ModularCurve.laurentBaseChange L₂ F₀ :=
  ModularCurve.coeffMap_mem_laurentBaseChange_of_ringHom σ F₀ hx

#print axioms solution

end S_ModularCurve_coeffMap_mem_laurentBaseChange_of_ringHom
end P2MW
export P2MW.S_ModularCurve_coeffMap_mem_laurentBaseChange_of_ringHom (solution)
