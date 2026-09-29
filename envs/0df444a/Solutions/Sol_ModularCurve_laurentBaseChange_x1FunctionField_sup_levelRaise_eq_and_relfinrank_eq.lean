-- Prove2me | solution 1 for ModularCurve.laurentBaseChange_x1FunctionField_sup_levelRaise_eq_and_relfinrank_eq
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.280726+00:00
-- url     : https://prove2.me/submissions/f487e58d-b54e-5d61-a837-832a5d5f9460

import Mathlib
import Definitions.Def_ModularCurve_X1
import Definitions.Def_ModularCurve_JqCoeff
import Definitions.Def_AlgebraicCurve_Repartitions
import Theorems.Thm_ModularCurve_laurentBaseChange_adjoin
import Theorems.Thm_ModularCurve_relfinrank_laurentBaseChange
import Theorems.Thm_ModularCurve_laurentBaseChange_mono
import Theorems.Thm_ModularCurve_coeffEmb_jq_mem_laurentBaseChange_x1FunctionField
import Theorems.Thm_ModularCurve_transcendental_jq
import Theorems.Thm_ModularCurve_coeffEmb_jq
import Theorems.Thm_ModularCurve_transcendental_and_finiteDimensional_adjoin_laurentBaseChange_qExpFunctionFieldC_of_coe_eq_jqModC
import Theorems.Thm_ModularCurve_x1FunctionField_mul_sup_x1FunctionField_mul_eq_of_coprime
import Theorems.Thm_ModularCurve_relfinrank_x1FunctionField_mul_eq_sq_sub_one_of_prime_of_not_dvd
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_laurentBaseChange_x1FunctionField_sup_levelRaise_eq_and_relfinrank_eq
p2m_attr_erase "instance" "ModularCurve.instIsDomainTensorProduct AlgebraicClosure.Rat.isGalois AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.instFundamentalIdentityOfSumRamificationInertia AlgebraicCurve.Place.instIsScalarTowerResidueFieldRestrictPushforward AlgebraicCurve.Place.instAlgebraResidueFieldRestrictPushforward AlgebraicCurve.Place.instIsLocalHomRestrictInclusion AlgebraicCurve.IsCurveOver.instNontrivialKaehler AlgebraicCurve.IsCurveOver.instFreeKaehler AlgebraicCurve.IsCurveOver.toHasPrincipalDivisors AlgebraicCurve.IsCurveOver.instFiniteResidue AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation instDecEqAlgebraicClosureRat WeierstrassCurve.Affine.Point.instDistribMulActionAlgEquiv WeierstrassCurve.Affine.Point.instModuleZModTorsionBy WeierstrassCurve.Affine.Point.instSMulTorsionBy WeierstrassCurve.Affine.Point.instDistribMulActionTorsionBy WeierstrassCurve.Affine.Point.instSMulAlgEquiv WeierstrassCurve.Affine.Point.instSMulCommClassAlgEquivZModTorsionBy ModularCurve.PhiGen.instNeZeroPhiGenCosetA CohCarrier.iotaDeg_range_finiteIndex CohCarrier.Gamma0Upper_finiteIndex TateModule.instModule TateModule.instSMul GaloisRepAdic.instAddCommGroup GaloisRepAdic.instFree GaloisRepAdic.instFinite GaloisRepAdic.instModule ResidualGaloisRep.instModule ResidualGaloisRep.instModuleFinite ResidualGaloisRep.instAddCommGroup WeierstrassCurve.Affine.Point.instFinite ModularCurve.instFiniteProjectiveLine ModularCurve.unimodularRowSetoid"
p2m_attr_erase "simp" "ModularCurve.coe_baseChangeEquiv_apply ModularCurve.baseChangeHom_tmul ModularCurve.qInftyPlaceBar_toValuationSubring ModularCurve.qSeriesBar_zero ModularCurve.qSeriesBar_add ModularCurve.cuspInftyFull_toValuationSubring ModularCurve.qInftyPlaceRat_toValuationSubring ModularCurve.qSeriesBar_mul ModularCurve.qSeriesBar_div ModularCurve.qSeriesBar_eq_zero_iff ModularCurve.coe_uniformizerBar ModularCurve.qSeriesBar_pow ModularCurve.cuspInfty_toValuationSubring ModularCurve.qSeriesBar_one ModularCurve.qSeriesBar_inv ModularCurve.qSeriesBar_sub ModularCurve.qSeriesBar_neg ModularCurve.coe_cuspidalDivisor₀ AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal AlgebraicCurve.Divisor.mapRestrict_single AlgebraicCurve.Divisor.pushforward_single AlgebraicCurve.Place.coe_restrictInclusion AlgebraicCurve.Place.mem_fiber AlgebraicCurve.Place.restrict_toValuationSubring AlgebraicCurve.Divisor.degree_pushforward AlgebraicCurve.Place.restrictResidueMap_residue AlgebraicCurve.Pic0.coe_pushforwardDegZeroHom AlgebraicCurve.Pic0.coe_pullbackDegZeroHom AlgebraicCurve.IsFrobeniusEndo.frobNormRingHom_apply ModularCurve.frobeniusPushforwardGeomLevelPic0_mk ModularCurve.coe_frobeniusGeomLevelEquiv_apply ModularCurve.coe_frobeniusPushforwardGeomLevelDegZero ModularCurve.heckeFibreGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusGeomLevel_apply_coe ModularCurve.frobeniusPullbackGeomLevelPic0OfIsCurveOver_mk ModularCurve.coe_heckeFibreGeomLevelDegZero"
p2m_attr_erase "simp" "ModularCurve.coe_frobeniusPullbackGeomLevelDegZero ModularCurve.frobeniusPullbackGeomLevelPic0_mk ModularCurve.frobeniusPullbackGeomLevel_single ModularCurve.heckeFibreGeomLevelPic0_mk ModularCurve.frobeniusPushforwardGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusPushforwardGeomLevel_single ModularCurve.qExpandAlgC_apply AlgebraicCurve.Place.congrEquiv_symm_apply AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply AlgebraicCurve.RationalFunctionField.deg_placeOfPoint AlgebraicCurve.Divisor.degree_pushforwardAlong AlgebraicCurve.Pic0.coe_degZeroCorrespondence AlgebraicCurve.Place.mem_fiberAlong AlgebraicCurve.coe_frobeniusPushforwardDegZero AlgebraicCurve.IsFrobeniusEndo.coe_frobeniusPullbackDegZero ModularCurve.reduceModBivar_C_X ModularCurve.laurentMap_coeff ModularCurve.reduceModBivar_X ModularCurve.laurentMap_single ModularCurve.evalAtJInt_X ModularCurve.evalAtJMod_X ModularCurve.jqNMod_one ModularCurve.aeval_heckeGen ModularCurve.coe_mTorsionGaloisRep_apply ModularCurve.eisensteinSystem_of_dvd ModularCurve.eisensteinSystem_of_not_dvd FreyPackage.mk.sizeOf_spec FreyPackage.mk.injEq WeierstrassCurve.Affine.Point.galoisRepModuleEnd_apply ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single"
p2m_attr_erase "simp" "ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL ModularCurve.eisensteinNumerator_nineteen ModularCurve.eisensteinNumerator_seventeen ModularCurve.eisensteinNumerator_eleven ModularCurve.eisensteinNumerator_five ModularCurve.eisensteinNumerator_seven ModularCurve.eisensteinNumerator_twentythree ModularCurve.eisensteinNumerator_thirteen ModularCurve.constantCoeff_dedekindEtaUnitQ ModularCurve.qExpandAlgHomC_apply WeierstrassCurve.reducePoint_zero WeierstrassCurve.Affine.Point.galoisRep_apply ModularCurve.LevelN.coe_jGen PeriodPair.weierstrassCurve_a₆ PeriodPair.weierstrassCurve_a₃ PeriodPair.weierstrassCurve_a₁ PeriodPair.ofTau_ω₂ PeriodPair.scale_ω₂ PeriodPair.ofTau_ω₁ PeriodPair.toPoint_zero PeriodPair.toPoint_of_mem PeriodPair.weierstrassCurve_a₂ PeriodPair.ofTau_lattice PeriodPair.scale_ω₁ PeriodPair.weierstrassCurve_a₄ ModularCurve.JH.torsionGaloisRep_apply CohCarrier.conjUpperMat_apply_11 CohCarrier.conjUpperMat_apply_10 CohCarrier.mem_Gamma0Upper"
p2m_attr_erase "simp" "CohCarrier.val_gamma0Units TateModule.smul_apply TateModule.coe_mulP TateModule.proj_apply TateModule.coe_add TateModule.coe_sub WeierstrassCurve.tateModuleRepOfBasis_V TateModule.coe_zero TateModule.rep_apply WeierstrassCurve.tateModuleRep_V WeierstrassCurve.tateModuleRepOfBasis_ρ_apply GaloisRep.padicIntToRingLevel_apply TateModule.coe_neg WeierstrassCurve.tateModuleRep_ρ_apply GaloisRepAdic.mk.injEq GaloisRepAdic.mk.sizeOf_spec GaloisRepAdic.Equiv.mk.sizeOf_spec GaloisRepAdic.Equiv.mk.injEq ResidualGaloisRep.mk.sizeOf_spec ResidualGaloisRep.mk.injEq ResidualGaloisRep.Equiv.mk.sizeOf_spec ResidualGaloisRep.Equiv.mk.injEq ModularCurve.ProjectiveLine.map_mk"

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 1600000
set_option maxHeartbeats 3200000

open scoped MatrixGroups

namespace LinDisjProof

open ModularCurve IntermediateField

theorem coeffEmb_rat (x : LaurentSeries ℚ) : @coeffEmb ℚ _ DivisionRing.toRatAlgebra x = x := by
  ext k
  rw [coeffEmb_coeff, eq_ratCast, Rat.cast_id]

theorem laurentBaseChange_rat (F₀ : IntermediateField ℚ (LaurentSeries ℚ)) :
    @laurentBaseChange ℚ _ DivisionRing.toRatAlgebra F₀ = F₀ := by
  show IntermediateField.adjoin ℚ (⇑(@coeffEmb ℚ _ DivisionRing.toRatAlgebra) '' (F₀ : Set (LaurentSeries ℚ))) = F₀
  have : ⇑(@coeffEmb ℚ _ DivisionRing.toRatAlgebra) '' (F₀ : Set (LaurentSeries ℚ)) = F₀ := by
    ext x
    simp only [Set.mem_image, coeffEmb_rat, exists_eq_right, SetLike.mem_coe]
  rw [this]
  exact IntermediateField.gi.l_u_eq F₀

theorem jq_mem (N : ℕ) [NeZero N] : jq ∈ x1FunctionField N := by
  have h := coeffEmb_jq_mem_laurentBaseChange_x1FunctionField ℚ N
  rwa [coeffEmb_rat, laurentBaseChange_rat] at h

theorem laurentBaseChange_sup (L : Type) [Field L] [CharZero L] (F₁ F₂ : IntermediateField ℚ (LaurentSeries ℚ)) :
    laurentBaseChange L F₁ ⊔ laurentBaseChange L F₂ = laurentBaseChange L (F₁ ⊔ F₂) := by
  have h := laurentBaseChange_adjoin L ((F₁ : Set (LaurentSeries ℚ)) ∪ F₂)
  rw [Set.image_union] at h
  have e1 : IntermediateField.adjoin ℚ ((F₁ : Set (LaurentSeries ℚ)) ∪ F₂) = F₁ ⊔ F₂ := by
    rw [show ((F₁ : Set (LaurentSeries ℚ)) ∪ F₂) = (F₁ : Set (LaurentSeries ℚ)) ⊔ (F₂ : Set (LaurentSeries ℚ)) from rfl,
      IntermediateField.gc.l_sup, IntermediateField.gi.l_u_eq, IntermediateField.gi.l_u_eq]
  have e2 : IntermediateField.adjoin L (⇑(coeffEmb L) '' (F₁ : Set (LaurentSeries ℚ)) ∪ ⇑(coeffEmb L) '' (F₂ : Set (LaurentSeries ℚ))) =
      laurentBaseChange L F₁ ⊔ laurentBaseChange L F₂ := by
    rw [show (⇑(coeffEmb L) '' (F₁ : Set (LaurentSeries ℚ)) ∪ ⇑(coeffEmb L) '' (F₂ : Set (LaurentSeries ℚ))) =
        (⇑(coeffEmb L) '' (F₁ : Set (LaurentSeries ℚ))) ⊔ (⇑(coeffEmb L) '' (F₂ : Set (LaurentSeries ℚ))) from rfl,
      IntermediateField.gc.l_sup]
    rfl
  rw [e1, e2] at h
  exact h.symm

theorem relfinrank_adjoin_coeffEmb_jq_ne_zero (L : Type) [Field L] [CharZero L] (N : ℕ) [NeZero N] :
    IntermediateField.relfinrank (IntermediateField.adjoin L ({coeffEmb L jq} : Set (LaurentSeries L)))
      (laurentBaseChange L (x1FunctionField N)) ≠ 0 := by
  classical
  show IntermediateField.relfinrank (IntermediateField.adjoin L ({coeffEmb L jq} : Set (LaurentSeries L)))
      (laurentBaseChange L (qExpFunctionFieldC ℚ (CongruenceSubgroup.Gamma1 N))) ≠ 0
  have hT : ModularGroup.T ∈ CongruenceSubgroup.Gamma1 N := by
    rw [CongruenceSubgroup.Gamma1_mem]
    simp [ModularGroup.coe_T]
  have hjN : coeffEmb L jq ∈ laurentBaseChange L (qExpFunctionFieldC ℚ (CongruenceSubgroup.Gamma1 N)) :=
    coeffEmb_jq_mem_laurentBaseChange_x1FunctionField L N
  let y : ↥(laurentBaseChange L (qExpFunctionFieldC ℚ (CongruenceSubgroup.Gamma1 N))) := ⟨coeffEmb L jq, hjN⟩
  have hy : (y : LaurentSeries L) = jqModC L := coeffEmb_jq L
  obtain ⟨-, hfd⟩ := transcendental_and_finiteDimensional_adjoin_laurentBaseChange_qExpFunctionFieldC_of_coe_eq_jqModC L
    (CongruenceSubgroup.Gamma1 N) hT y hy
  have hle : IntermediateField.adjoin L ({coeffEmb L jq} : Set (LaurentSeries L)) ≤
      laurentBaseChange L (qExpFunctionFieldC ℚ (CongruenceSubgroup.Gamma1 N)) :=
    IntermediateField.adjoin_simple_le_iff.mpr hjN

  have hLj : ∀ z : ↥(laurentBaseChange L (qExpFunctionFieldC ℚ (CongruenceSubgroup.Gamma1 N))),
      z ∈ IntermediateField.adjoin L ({y} : Set _) → ((z : LaurentSeries L)) ∈ IntermediateField.adjoin L ({coeffEmb L jq} : Set (LaurentSeries L)) := by
    intro z hz
    induction hz using IntermediateField.adjoin_induction with
    | mem z hz =>
        rw [Set.mem_singleton_iff] at hz
        subst hz
        exact IntermediateField.mem_adjoin_simple_self L (coeffEmb L jq)
    | algebraMap c => exact (IntermediateField.adjoin L ({coeffEmb L jq} : Set (LaurentSeries L))).algebraMap_mem c
    | add z w _ _ hz hw => exact add_mem hz hw
    | inv z _ hz => exact inv_mem hz
    | mul z w _ _ hz hw => exact mul_mem hz hw
  let φ : ↥(IntermediateField.adjoin L ({y} : Set _)) →+* ↥(IntermediateField.adjoin L ({coeffEmb L jq} : Set (LaurentSeries L))) :=
    { toFun := fun z => ⟨((z : ↥(laurentBaseChange L (qExpFunctionFieldC ℚ (CongruenceSubgroup.Gamma1 N)))) : LaurentSeries L), hLj z z.2⟩
      map_one' := rfl
      map_mul' := fun _ _ => rfl
      map_zero' := rfl
      map_add' := fun _ _ => rfl }
  letI : Algebra ↥(IntermediateField.adjoin L ({y} : Set _)) ↥(IntermediateField.adjoin L ({coeffEmb L jq} : Set (LaurentSeries L))) := φ.toAlgebra
  letI : Module ↥(IntermediateField.adjoin L ({y} : Set _)) ↥(IntermediateField.extendScalars hle) :=
    Module.compHom ↥(IntermediateField.extendScalars hle) φ
  haveI : IsScalarTower ↥(IntermediateField.adjoin L ({y} : Set _)) ↥(IntermediateField.adjoin L ({coeffEmb L jq} : Set (LaurentSeries L)))
      ↥(IntermediateField.extendScalars hle) :=
    ⟨fun z c v => mul_smul (φ z) c v⟩
  let e : ↥(laurentBaseChange L (qExpFunctionFieldC ℚ (CongruenceSubgroup.Gamma1 N))) ≃ₗ[↥(IntermediateField.adjoin L ({y} : Set _))]
      ↥(IntermediateField.extendScalars hle) :=
    { toFun := fun v => ⟨v.1, v.2⟩
      invFun := fun v => ⟨v.1, v.2⟩
      map_add' := fun _ _ => rfl
      map_smul' := fun z v => Subtype.ext rfl
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  haveI : Module.Finite ↥(IntermediateField.adjoin L ({y} : Set _)) ↥(IntermediateField.extendScalars hle) := Module.Finite.equiv e
  haveI : Module.Finite ↥(IntermediateField.adjoin L ({coeffEmb L jq} : Set (LaurentSeries L))) ↥(IntermediateField.extendScalars hle) :=
    Module.Finite.of_restrictScalars_finite ↥(IntermediateField.adjoin L ({y} : Set _)) _ _
  rw [IntermediateField.relfinrank_eq_finrank_of_le hle]
  exact Module.finrank_pos.ne'

theorem relfinrank_laurentBaseChange_x1FunctionField (L : Type) [Field L] [CharZero L] (a b : ℕ) [NeZero a] [NeZero b]
    (hab : x1FunctionField a ≤ x1FunctionField b) :
    IntermediateField.relfinrank (laurentBaseChange L (x1FunctionField a)) (laurentBaseChange L (x1FunctionField b)) =
      IntermediateField.relfinrank (x1FunctionField a) (x1FunctionField b) := by
  have hta := relfinrank_laurentBaseChange L (x1FunctionField a) jq (jq_mem a) transcendental_jq
  have htb := relfinrank_laurentBaseChange L (x1FunctionField b) jq (jq_mem b) transcendental_jq
  have hleQa : IntermediateField.adjoin ℚ ({jq} : Set (LaurentSeries ℚ)) ≤ x1FunctionField a :=
    IntermediateField.adjoin_simple_le_iff.mpr (jq_mem a)
  have hleLa : IntermediateField.adjoin L ({coeffEmb L jq} : Set (LaurentSeries L)) ≤ laurentBaseChange L (x1FunctionField a) :=
    IntermediateField.adjoin_simple_le_iff.mpr (coeffEmb_jq_mem_laurentBaseChange_x1FunctionField L a)
  have h1 := IntermediateField.relfinrank_mul_relfinrank hleLa (laurentBaseChange_mono L hab)
  have h2 := IntermediateField.relfinrank_mul_relfinrank hleQa hab

  rw [htb, ← h2, ← hta] at h1
  exact mul_left_cancel₀ (relfinrank_adjoin_coeffEmb_jq_ne_zero L a) h1

end LinDisjProof

open LinDisjProof in
theorem solution
    (L : Type) [Field L] [CharZero L] (M ℓ p : ℕ) [NeZero M] [NeZero p] (hM : 3 ≤ M) (hℓ : ℓ.Prime) (hℓMp : ¬ ℓ ∣ M * p) :
    ModularCurve.laurentBaseChange L (ModularCurve.x1FunctionField (M * p)) ⊔ ModularCurve.laurentBaseChange L (ModularCurve.x1FunctionField (M * ℓ)) =
        ModularCurve.laurentBaseChange L (ModularCurve.x1FunctionField (M * ℓ * p)) ∧
      IntermediateField.relfinrank (ModularCurve.laurentBaseChange L (ModularCurve.x1FunctionField (M * p))) (ModularCurve.laurentBaseChange L (ModularCurve.x1FunctionField (M * ℓ * p))) =
        IntermediateField.relfinrank (ModularCurve.laurentBaseChange L (ModularCurve.x1FunctionField (M))) (ModularCurve.laurentBaseChange L (ModularCurve.x1FunctionField (M * ℓ))) := by
  haveI : NeZero ℓ := ⟨hℓ.ne_zero⟩
  haveI : NeZero (M * p) := ⟨Nat.mul_ne_zero (NeZero.ne M) (NeZero.ne p)⟩
  haveI : NeZero (M * ℓ) := ⟨Nat.mul_ne_zero (NeZero.ne M) hℓ.ne_zero⟩
  haveI : NeZero (M * p * ℓ) := ⟨Nat.mul_ne_zero (Nat.mul_ne_zero (NeZero.ne M) (NeZero.ne p)) hℓ.ne_zero⟩
  haveI : NeZero (M * ℓ * p) := ⟨Nat.mul_ne_zero (Nat.mul_ne_zero (NeZero.ne M) hℓ.ne_zero) (NeZero.ne p)⟩
  have hℓp : ¬ ℓ ∣ p := fun h => hℓMp (dvd_mul_of_dvd_right h M)
  have hℓM : ¬ ℓ ∣ M := fun h => hℓMp (dvd_mul_of_dvd_left h p)
  have hcop : Nat.Coprime p ℓ := (Nat.coprime_comm.mp ((Nat.Prime.coprime_iff_not_dvd hℓ).mpr hℓp))
  have hMp3 : 3 ≤ M * p := le_mul_of_le_of_one_le hM (NeZero.one_le)

  have hcomp : ModularCurve.x1FunctionField (M * p) ⊔ ModularCurve.x1FunctionField (M * ℓ) = ModularCurve.x1FunctionField (M * ℓ * p) := by
    rw [ModularCurve.x1FunctionField_mul_sup_x1FunctionField_mul_eq_of_coprime M p ℓ hM hcop, mul_right_comm M p ℓ]
  have hdeg1 : IntermediateField.relfinrank (ModularCurve.x1FunctionField (M * p)) (ModularCurve.x1FunctionField (M * ℓ * p)) = ℓ ^ 2 - 1 := by
    rw [← mul_right_comm M p ℓ]
    exact ModularCurve.relfinrank_x1FunctionField_mul_eq_sq_sub_one_of_prime_of_not_dvd (M * p) ℓ hMp3 hℓ hℓMp
  have hdeg2 : IntermediateField.relfinrank (ModularCurve.x1FunctionField M) (ModularCurve.x1FunctionField (M * ℓ)) = ℓ ^ 2 - 1 :=
    ModularCurve.relfinrank_x1FunctionField_mul_eq_sq_sub_one_of_prime_of_not_dvd M ℓ hM hℓ hℓM
  refine ⟨?_, ?_⟩
  · rw [laurentBaseChange_sup, hcomp]
  · have hle1 : ModularCurve.x1FunctionField (M * p) ≤ ModularCurve.x1FunctionField (M * ℓ * p) := by
      rw [← mul_right_comm M p ℓ]
      exact ModularCurve.x1FunctionFieldC_le_of_dvd ℚ (Dvd.intro ℓ rfl)
    have hle2 : ModularCurve.x1FunctionField M ≤ ModularCurve.x1FunctionField (M * ℓ) :=
      ModularCurve.x1FunctionFieldC_le_of_dvd ℚ (Dvd.intro ℓ rfl)
    rw [relfinrank_laurentBaseChange_x1FunctionField L _ _ hle1, relfinrank_laurentBaseChange_x1FunctionField L _ _ hle2,
      hdeg1, hdeg2]

end S_ModularCurve_laurentBaseChange_x1FunctionField_sup_levelRaise_eq_and_relfinrank_eq
end P2MW
export P2MW.S_ModularCurve_laurentBaseChange_x1FunctionField_sup_levelRaise_eq_and_relfinrank_eq (solution)
