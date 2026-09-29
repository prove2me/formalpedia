-- Prove2me | solution 1 for ModularCurve.finrankAlong_heckeBetaOneBar
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.007995+00:00
-- url     : https://prove2.me/submissions/bc580468-511e-5481-b40a-df963358c2f5

import Mathlib
import Definitions.Def_ModularCurve_X1HeckeOperator
import Definitions.Def_ModularCurve_X0ModL
import Theorems.Thm_ModularCurve_finrankAlong_heckeAlphaOneBar
import Theorems.Thm_AlgebraicCurve_finrankAlong_eq_relfinrank_fieldRange
import Theorems.Thm_ModularCurve_relfinrank_qExpand_full
import Theorems.Thm_ModularCurve_relfinrank_full_eq_dedekindPsi
import Theorems.Thm_ModularCurve_dedekindPsi_mul_prime
import Theorems.Thm_ModularCurve_modularFunctionFieldFullC_le_qExpFunctionFieldC_gamma0
import Theorems.Thm_ModularCurve_JOneES_exists_transcendental_finiteDimensional_qExpFunctionFieldC
import Theorems.Thm_AlgebraicCurve_finiteDimensional_adjoin_of_transcendental
import Theorems.Thm_ModularCurve_transcendental_jqN
import Theorems.Thm_ModularCurve_relfinrank_laurentBaseChange
import Theorems.Thm_ModularCurve_coeffMap_qExpand
import Theorems.Thm_ModularCurve_laurentBaseChange_adjoin
import Theorems.Thm_ModularCurve_laurentBaseChange_mono
import Theorems.Thm_ModularCurve_qExpand_mem_laurentBaseChange
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_finrankAlong_heckeBetaOneBar
p2m_attr_erase "instance" "CohCarrier.iotaDeg_range_finiteIndex CohCarrier.Gamma0Upper_finiteIndex TateModule.instModule TateModule.instSMul GaloisRepAdic.instAddCommGroup GaloisRepAdic.instFree GaloisRepAdic.instFinite GaloisRepAdic.instModule ResidualGaloisRep.instModule ResidualGaloisRep.instModuleFinite ResidualGaloisRep.instAddCommGroup WeierstrassCurve.Affine.Point.instSMulCommClassAlgEquivZModTorsionBy instDecEqAlgebraicClosureRat WeierstrassCurve.Affine.Point.instDistribMulActionAlgEquiv WeierstrassCurve.Affine.Point.instModuleZModTorsionBy WeierstrassCurve.Affine.Point.instSMulTorsionBy WeierstrassCurve.Affine.Point.instDistribMulActionTorsionBy WeierstrassCurve.Affine.Point.instSMulAlgEquiv WeierstrassCurve.Affine.Point.instFinite ModularCurve.PhiGen.instNeZeroPhiGenCosetA ModularCurve.instIsDomainTensorProduct AlgebraicClosure.Rat.isGalois AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.IsCurveOver.instNontrivialKaehler AlgebraicCurve.IsCurveOver.instFreeKaehler AlgebraicCurve.IsCurveOver.toHasPrincipalDivisors AlgebraicCurve.IsCurveOver.instFiniteResidue AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation ModularCurve.instFiniteProjectiveLine ModularCurve.unimodularRowSetoid"
p2m_attr_erase "simp" "ModularCurve.JH.torsionGaloisRep_apply CohCarrier.conjUpperMat_apply_11 CohCarrier.conjUpperMat_apply_10 CohCarrier.mem_Gamma0Upper CohCarrier.val_gamma0Units TateModule.smul_apply TateModule.coe_mulP TateModule.proj_apply TateModule.coe_add TateModule.coe_sub WeierstrassCurve.tateModuleRepOfBasis_V TateModule.coe_zero TateModule.rep_apply WeierstrassCurve.tateModuleRep_V WeierstrassCurve.tateModuleRepOfBasis_ρ_apply GaloisRep.padicIntToRingLevel_apply TateModule.coe_neg WeierstrassCurve.tateModuleRep_ρ_apply GaloisRepAdic.mk.injEq GaloisRepAdic.mk.sizeOf_spec GaloisRepAdic.Equiv.mk.sizeOf_spec GaloisRepAdic.Equiv.mk.injEq ResidualGaloisRep.mk.sizeOf_spec ResidualGaloisRep.mk.injEq WeierstrassCurve.Affine.Point.galoisRepModuleEnd_apply FreyPackage.mk.sizeOf_spec FreyPackage.mk.injEq ResidualGaloisRep.Equiv.mk.sizeOf_spec ResidualGaloisRep.Equiv.mk.injEq ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff"
p2m_attr_erase "simp" "ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ ModularCurve.coe_baseChangeEquiv_apply ModularCurve.baseChangeHom_tmul ModularCurve.qInftyPlaceBar_toValuationSubring ModularCurve.qSeriesBar_zero ModularCurve.qSeriesBar_add ModularCurve.cuspInftyFull_toValuationSubring ModularCurve.qInftyPlaceRat_toValuationSubring ModularCurve.qSeriesBar_mul ModularCurve.qSeriesBar_div ModularCurve.qSeriesBar_eq_zero_iff ModularCurve.coe_uniformizerBar ModularCurve.qSeriesBar_pow ModularCurve.cuspInfty_toValuationSubring ModularCurve.qSeriesBar_one ModularCurve.qSeriesBar_inv ModularCurve.qSeriesBar_sub ModularCurve.qSeriesBar_neg ModularCurve.coe_cuspidalDivisor₀ AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal AlgebraicCurve.IsFrobeniusEndo.frobNormRingHom_apply ModularCurve.frobeniusPushforwardGeomLevelPic0_mk ModularCurve.coe_frobeniusGeomLevelEquiv_apply ModularCurve.coe_frobeniusPushforwardGeomLevelDegZero ModularCurve.heckeFibreGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusGeomLevel_apply_coe ModularCurve.frobeniusPullbackGeomLevelPic0OfIsCurveOver_mk ModularCurve.coe_heckeFibreGeomLevelDegZero"
p2m_attr_erase "simp" "ModularCurve.coe_frobeniusPullbackGeomLevelDegZero ModularCurve.frobeniusPullbackGeomLevelPic0_mk ModularCurve.frobeniusPullbackGeomLevel_single ModularCurve.heckeFibreGeomLevelPic0_mk ModularCurve.frobeniusPushforwardGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusPushforwardGeomLevel_single ModularCurve.qExpandAlgC_apply AlgebraicCurve.Place.congrEquiv_symm_apply AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply AlgebraicCurve.RationalFunctionField.deg_placeOfPoint AlgebraicCurve.coe_frobeniusPushforwardDegZero AlgebraicCurve.IsFrobeniusEndo.coe_frobeniusPullbackDegZero ModularCurve.reduceModBivar_C_X ModularCurve.laurentMap_coeff ModularCurve.reduceModBivar_X ModularCurve.laurentMap_single ModularCurve.evalAtJInt_X ModularCurve.evalAtJMod_X ModularCurve.jqNMod_one ModularCurve.aeval_heckeGen ModularCurve.coe_mTorsionGaloisRep_apply ModularCurve.eisensteinSystem_of_dvd ModularCurve.eisensteinSystem_of_not_dvd ModularCurve.eisensteinNumerator_nineteen ModularCurve.eisensteinNumerator_seventeen ModularCurve.eisensteinNumerator_eleven ModularCurve.eisensteinNumerator_five ModularCurve.eisensteinNumerator_seven ModularCurve.eisensteinNumerator_twentythree ModularCurve.eisensteinNumerator_thirteen ModularCurve.constantCoeff_dedekindEtaUnitQ ModularCurve.coe_towerInclBar ModularCurve.coe_towerSubstBar ModularCurve.coe_heckeBetaBarRingHom ModularCurve.coe_heckeBetaBar ModularCurve.coe_heckeAlphaBar ModularCurve.ProjectiveLine.map_mk"

set_option autoImplicit false
set_option linter.unusedSectionVars false

noncomputable section

open scoped MatrixGroups
p2m_open "ModularCurve~transcendental_jq CongruenceSubgroup IntermediateField AlgebraicCurve"

namespace DBeta

variable (M : ℕ) [NeZero M] (ℓ : ℕ) [NeZero ℓ]

abbrev Gam' : Subgroup SL(2, ℤ) := Gamma1 M ⊓ Gamma0 (M * ℓ)

scoped instance : (Gam' M ℓ).FiniteIndex := by
  haveI : NeZero (M * ℓ) := NeZero.mul
  refine Subgroup.finiteIndex_of_le (H := Gamma1 (M * ℓ)) (le_inf ?_ (Gamma1_in_Gamma0 _))
  exact Gamma1_le_of_dvd (dvd_mul_right M ℓ)

omit [NeZero M] [NeZero ℓ] in
theorem T_mem_Gam' : ModularGroup.T ∈ Gam' M ℓ := by
  refine Subgroup.mem_inf.mpr ⟨?_, ?_⟩
  · rw [Gamma1_mem]
    simp [ModularGroup.T]
  · rw [Gamma0_mem]
    simp [ModularGroup.T]

abbrev FF : IntermediateField ℚ (LaurentSeries ℚ) := x1FunctionField M
abbrev FF' : IntermediateField ℚ (LaurentSeries ℚ) := x1x0FunctionFieldC ℚ M (M * ℓ)
abbrev F0 : IntermediateField ℚ (LaurentSeries ℚ) := modularFunctionFieldFull M
abbrev F0' : IntermediateField ℚ (LaurentSeries ℚ) := modularFunctionFieldFull (M * ℓ)
abbrev B0 : IntermediateField ℚ (LaurentSeries ℚ) := (modularFunctionFieldFull M).map (qExpandₐ ℓ)
abbrev BB : IntermediateField ℚ (LaurentSeries ℚ) := (x1FunctionField M).map (qExpandₐ ℓ)

abbrev dd : ℕ := if ℓ ∣ M then ℓ else ℓ + 1

omit [NeZero M] [NeZero ℓ] in
theorem FF_le : FF M ≤ FF' M ℓ := x1FunctionFieldC_le_x1x0 ℚ M (M * ℓ)

theorem F0_le_FF : F0 M ≤ FF M := by
  rw [show F0 M = modularFunctionFieldFullC ℚ M from (modularFunctionFieldFullC_rat M).symm]
  exact (modularFunctionFieldFullC_le_qExpFunctionFieldC_gamma0 ℚ M).trans
    (qExpFunctionFieldC_mono ℚ (Gamma1_in_Gamma0 M))

theorem F0'_le_FF' : F0' M ℓ ≤ FF' M ℓ := by
  haveI : NeZero (M * ℓ) := NeZero.mul
  rw [show F0' M ℓ = modularFunctionFieldFullC ℚ (M * ℓ) from (modularFunctionFieldFullC_rat (M * ℓ)).symm]
  exact (modularFunctionFieldFullC_le_qExpFunctionFieldC_gamma0 ℚ (M * ℓ)).trans
    (qExpFunctionFieldC_mono ℚ inf_le_right)

theorem B0_le_F0' : B0 M ℓ ≤ F0' M ℓ := full_degeneracy_map_le M ℓ

theorem B0_le_BB : B0 M ℓ ≤ BB M ℓ := by
  intro x hx
  rw [IntermediateField.mem_map] at hx ⊢
  obtain ⟨y, hy, rfl⟩ := hx
  exact ⟨y, F0_le_FF M hy, rfl⟩

omit [NeZero M] in
theorem BB_le_FF' (h : HeckeBetaOneDefined M ℓ) : BB M ℓ ≤ FF' M ℓ := by
  intro x hx
  rw [IntermediateField.mem_map] at hx
  obtain ⟨y, hy, rfl⟩ := hx
  exact h y hy

theorem relfinrank_adjoin_eq_finrank {K E : Type*} [Field K] [Field E] [Algebra K E]
    (B : IntermediateField K E) (x : B) :
    relfinrank (adjoin K ({(x : E)} : Set E)) B = Module.finrank (adjoin K ({x} : Set B)) B := by
  have hc : (adjoin K ({(x : E)} : Set E)).comap B.val = adjoin K ({x} : Set B) := by
    apply le_antisymm
    · intro y hy
      change B.val y ∈ adjoin K ({(x : E)} : Set E) at hy
      have h' : (y : E) ∈ lift (adjoin K ({x} : Set B)) := by
        rw [lift_adjoin_simple]; exact hy
      exact (IntermediateField.mem_lift y).mp h'
    · rw [adjoin_le_iff, Set.singleton_subset_iff, SetLike.mem_coe]
      change B.val x ∈ adjoin K ({(x : E)} : Set E)
      exact mem_adjoin_simple_self K (x : E)
  have h := IntermediateField.finrank_comap B.val (A := adjoin K ({(x : E)} : Set E))
  rw [fieldRange_val] at h
  rw [← h]
  exact congrArg (fun C : IntermediateField K B => Module.finrank C B) hc

theorem relfinrank_adjoin_ne_zero {K E : Type*} [Field K] [Field E] [Algebra K E]
    (B : IntermediateField K E) (x : B) (h : FiniteDimensional (adjoin K ({x} : Set B)) B) :
    relfinrank (adjoin K ({(x : E)} : Set E)) B ≠ 0 := by
  rw [relfinrank_adjoin_eq_finrank]
  exact Module.finrank_pos.ne'

theorem transcendental_of_subsingleton_ratAlgebra {F : Type*} [Field F] {i₁ : Algebra ℚ F}
    (i₂ : Algebra ℚ F) {x : F} (h : @Transcendental ℚ F _ _ i₁ x) : @Transcendental ℚ F _ _ i₂ x := by
  have := Subsingleton.elim i₁ i₂; subst this; exact h

theorem isAlgebraic_of_subsingleton_ratAlgebra {F : Type*} [Field F] {i₁ : Algebra ℚ F}
    (i₂ : Algebra ℚ F) {x : F} (h : @IsAlgebraic ℚ F _ _ i₁ x) : @IsAlgebraic ℚ F _ _ i₂ x := by
  have := Subsingleton.elim i₁ i₂; subst this; exact h

theorem finiteDimensional_adjoin_of_subsingleton_ratAlgebra {F : Type*} [Field F] {i₁ : Algebra ℚ F}
    (i₂ : Algebra ℚ F) {x : F}
    (h : letI := i₁; FiniteDimensional (adjoin ℚ ({x} : Set F)) F) :
    letI := i₂; FiniteDimensional (adjoin ℚ ({x} : Set F)) F := by
  have := Subsingleton.elim i₁ i₂; subst this; exact h

theorem relfinrank_adjoin_FF'_ne_zero (t : LaurentSeries ℚ) (ht : t ∈ FF' M ℓ) (htr : Transcendental ℚ t) :
    relfinrank (adjoin ℚ ({t} : Set (LaurentSeries ℚ))) (FF' M ℓ) ≠ 0 := by
  have H : ∃ x : FF' M ℓ, Transcendental ℚ x ∧
      FiniteDimensional (adjoin ℚ ({x} : Set (FF' M ℓ))) (FF' M ℓ) :=
    ModularCurve.JOneES.exists_transcendental_finiteDimensional_qExpFunctionFieldC (Gam' M ℓ)
      (T_mem_Gam' M ℓ)
  obtain ⟨x', hxt', hfd'⟩ := H
  let y : FF' M ℓ := ⟨t, ht⟩
  have hyt : Transcendental ℚ y := fun h =>
    htr ((IntermediateField.isAlgebraic_iff (K := ℚ) (S := FF' M ℓ) (x := y)).mp
      (isAlgebraic_of_subsingleton_ratAlgebra _ h))
  haveI := hfd'
  have hfdy : FiniteDimensional (adjoin ℚ ({y} : Set (FF' M ℓ))) (FF' M ℓ) :=
    AlgebraicCurve.finiteDimensional_adjoin_of_transcendental x' hyt
  exact relfinrank_adjoin_ne_zero (FF' M ℓ) y (finiteDimensional_adjoin_of_subsingleton_ratAlgebra _ hfdy)

theorem relfinrank_ne_zero_of_tower {K E : Type*} [Field K] [Field E] [Algebra K E]
    {T A C : IntermediateField K E} (hTA : T ≤ A) (hAC : A ≤ C) (h : relfinrank T C ≠ 0) :
    relfinrank T A ≠ 0 ∧ relfinrank A C ≠ 0 := by
  have := relfinrank_mul_relfinrank hTA hAC
  rw [← this] at h
  exact ⟨left_ne_zero_of_mul h, right_ne_zero_of_mul h⟩

theorem jq_mem_F0 : jq ∈ F0 M := by
  have h := jqd_mem_full M (one_dvd M)
  rwa [qExpand_one_apply] at h

omit [NeZero M] [NeZero ℓ] in
theorem transcendental_jq : Transcendental ℚ jq := by
  have h := transcendental_jqN 1
  rwa [jqN_one] at h

theorem jqN_mem_B0 : jqN ℓ ∈ B0 M ℓ :=
  ⟨jq, jq_mem_F0 M, rfl⟩

theorem adjoin_jq_le_F0 : adjoin ℚ ({jq} : Set (LaurentSeries ℚ)) ≤ F0 M := by
  rw [adjoin_le_iff, Set.singleton_subset_iff]; exact jq_mem_F0 M

theorem F0_le_F0' : F0 M ≤ F0' M ℓ := full_degeneracy_le (dvd_mul_right M ℓ)

theorem relfinrank_F0_F0' [Fact ℓ.Prime] : relfinrank (F0 M) (F0' M ℓ) = dd M ℓ := by
  haveI : NeZero (M * ℓ) := NeZero.mul
  have h1 := relfinrank_full_eq_dedekindPsi M
  have h2 := relfinrank_full_eq_dedekindPsi (M * ℓ)
  have t := relfinrank_mul_relfinrank (adjoin_jq_le_F0 M) (F0_le_F0' M ℓ)
  rw [h1, h2, dedekindPsi_mul_prime M ℓ Fact.out, mul_comm] at t

  have hψ : dedekindPsi M ≠ 0 := by
    rw [← h1]
    exact (relfinrank_ne_zero_of_tower (adjoin_jq_le_F0 M) ((F0_le_FF M).trans (FF_le M ℓ))
      (relfinrank_adjoin_FF'_ne_zero M ℓ jq ((F0_le_FF M).trans (FF_le M ℓ) (jq_mem_F0 M))
        transcendental_jq)).1
  exact Nat.eq_of_mul_eq_mul_right (Nat.pos_of_ne_zero hψ) t

theorem relfinrank_B0_F0' [Fact ℓ.Prime] : relfinrank (B0 M ℓ) (F0' M ℓ) = dd M ℓ :=
  relfinrank_qExpand_full M ℓ

theorem relfinrank_B0_BB : relfinrank (B0 M ℓ) (BB M ℓ) = relfinrank (F0 M) (FF M) :=
  IntermediateField.relfinrank_map_map (F0 M) (FF M) (qExpandₐ ℓ)

section BaseChange

variable (L : Type*) [Field L] [Algebra ℚ L]

theorem relfinrank_lbc_lbc {A C : IntermediateField ℚ (LaurentSeries ℚ)} (hAC : A ≤ C)
    (x : LaurentSeries ℚ) (hx : x ∈ A) (htr : Transcendental ℚ x)
    (hfin : relfinrank (adjoin ℚ ({x} : Set (LaurentSeries ℚ))) C ≠ 0) :
    relfinrank (laurentBaseChange L A) (laurentBaseChange L C) = relfinrank A C := by
  have h1 := ModularCurve.relfinrank_laurentBaseChange L A x hx htr
  have h2 := ModularCurve.relfinrank_laurentBaseChange L C x (hAC hx) htr
  have hxle : adjoin ℚ ({x} : Set (LaurentSeries ℚ)) ≤ A := by
    rw [adjoin_le_iff, Set.singleton_subset_iff]; exact hx
  have hxLle : adjoin L ({coeffEmb L x} : Set (LaurentSeries L)) ≤ laurentBaseChange L A := by
    rw [adjoin_le_iff, Set.singleton_subset_iff]; exact coeffEmb_mem_laurentBaseChange L hx
  have tQ := relfinrank_mul_relfinrank hxle hAC
  have tL := relfinrank_mul_relfinrank hxLle (laurentBaseChange_mono L hAC)
  have hA0 : relfinrank (adjoin ℚ ({x} : Set (LaurentSeries ℚ))) A ≠ 0 :=
    (relfinrank_ne_zero_of_tower hxle hAC hfin).1
  rw [h1, h2, ← tQ] at tL
  exact Nat.eq_of_mul_eq_mul_left (Nat.pos_of_ne_zero hA0) tL

def qExpandAlg (n : ℕ) [NeZero n] : LaurentSeries L →ₐ[L] LaurentSeries L :=
  { qExpand L n with
    commutes' := fun a => by
      show qExpand L n (algebraMap L (LaurentSeries L) a) = algebraMap L (LaurentSeries L) a
      rw [algebraMap_laurentSeries_eq_single, qExpand_single, mul_zero] }

omit [NeZero M] [NeZero ℓ] [Algebra ℚ L] in
@[scoped simp] theorem qExpandAlg_apply (n : ℕ) [NeZero n] (x : LaurentSeries L) : qExpandAlg L n x = qExpand L n x := rfl

omit [NeZero M] in

theorem laurentBaseChange_map_qExpand (A : IntermediateField ℚ (LaurentSeries ℚ)) :
    laurentBaseChange L (A.map (qExpandₐ ℓ)) = (laurentBaseChange L A).map (qExpandAlg L ℓ) := by
  rw [laurentBaseChange, laurentBaseChange, IntermediateField.adjoin_map, IntermediateField.coe_map, Set.image_image,
    Set.image_image]
  congr 1
  refine Set.image_congr fun y _ => ?_
  show coeffMap (algebraMap ℚ L) (qExpand ℚ ℓ y) = qExpand L ℓ (coeffMap (algebraMap ℚ L) y)
  exact coeffMap_qExpand _ _ _

omit [NeZero M] in

theorem fieldRange_heckeBetaOneBar (h : HeckeBetaOneDefined M ℓ) :
    ((laurentBaseChange L (FF' M ℓ)).val.comp (heckeBetaOneBar L M ℓ)).fieldRange =
      (laurentBaseChange L (FF M)).map (qExpandAlg L ℓ) := by
  ext x
  rw [AlgHom.mem_fieldRange, IntermediateField.mem_map]
  constructor
  · rintro ⟨y, rfl⟩
    refine ⟨(y : LaurentSeries L), y.2, ?_⟩
    rw [qExpandAlg_apply, AlgHom.comp_apply, ← coe_heckeBetaOneBar M ℓ h y]
    rfl
  · rintro ⟨z, hz, rfl⟩
    refine ⟨⟨z, hz⟩, ?_⟩
    rw [qExpandAlg_apply, AlgHom.comp_apply, ← coe_heckeBetaOneBar M ℓ h ⟨z, hz⟩]
    rfl

end BaseChange

section Assembly

variable [Fact ℓ.Prime]

omit [Fact ℓ.Prime] in
theorem fieldRange_val_comp_inclusion {K E : Type*} [Field K] [Field E] [Algebra K E]
    {A B : IntermediateField K E} (hAB : A ≤ B) :
    (B.val.comp (IntermediateField.inclusion hAB)).fieldRange = A := by
  ext x
  constructor
  · rintro ⟨a, rfl⟩
    exact a.2
  · intro hx
    exact ⟨⟨x, hx⟩, rfl⟩

omit [Fact ℓ.Prime] in

theorem finrankAlong_inclusion {K E : Type*} [Field K] [Field E] [Algebra K E]
    {A B : IntermediateField K E} (hAB : A ≤ B) :
    finrankAlong K (IntermediateField.inclusion hAB) = relfinrank A B := by
  rw [AlgebraicCurve.finrankAlong_eq_relfinrank_fieldRange, fieldRange_val_comp_inclusion]

omit [Fact ℓ.Prime] in

theorem finrankAlong_heckeAlphaOneBar_eq (L : Type*) [Field L] [Algebra ℚ L] :
    finrankAlong L (heckeAlphaOneBar L M ℓ) = relfinrank (laurentBaseChange L (FF M)) (laurentBaseChange L (FF' M ℓ)) := by
  have hle : laurentBaseChange L (FF M) ≤ laurentBaseChange L (FF' M ℓ) := laurentBaseChange_mono L (FF_le M ℓ)
  rw [heckeAlphaOneBar_eq_inclusion M ℓ hle]
  exact finrankAlong_inclusion hle

theorem relfinrank_FF_FF' (L : Type*) [Field L] [Algebra ℚ L] : relfinrank (FF M) (FF' M ℓ) = dd M ℓ := by
  have hα := (finrankAlong_heckeAlphaOneBar_eq M ℓ L).symm.trans (ModularCurve.finrankAlong_heckeAlphaOneBar L M ℓ)
  rwa [relfinrank_lbc_lbc L (FF_le M ℓ) jq (F0_le_FF M (jq_mem_F0 M)) transcendental_jq
    (relfinrank_adjoin_FF'_ne_zero M ℓ jq ((F0_le_FF M).trans (FF_le M ℓ) (jq_mem_F0 M)) transcendental_jq)] at hα

theorem relfinrank_F0'_FF'_eq (L : Type*) [Field L] [Algebra ℚ L] :
    relfinrank (F0' M ℓ) (FF' M ℓ) = relfinrank (F0 M) (FF M) ∧
    relfinrank (F0 M) (FF M) ≠ 0 := by
  have t1 := relfinrank_mul_relfinrank (F0_le_FF M) (FF_le M ℓ)
  have t2 := relfinrank_mul_relfinrank (F0_le_F0' M ℓ) (F0'_le_FF' M ℓ)
  rw [relfinrank_FF_FF' M ℓ L] at t1
  rw [relfinrank_F0_F0', ← t1, mul_comm] at t2
  have hd : 0 < dd M ℓ := by
    have := (Fact.out : ℓ.Prime).pos
    unfold dd; split_ifs <;> omega
  refine ⟨Nat.eq_of_mul_eq_mul_right hd t2, ?_⟩
  have hF0 : relfinrank (adjoin ℚ ({jq} : Set (LaurentSeries ℚ))) (FF' M ℓ) ≠ 0 :=
    relfinrank_adjoin_FF'_ne_zero M ℓ jq ((F0_le_FF M).trans (FF_le M ℓ) (jq_mem_F0 M)) transcendental_jq
  have h' := (relfinrank_ne_zero_of_tower (adjoin_jq_le_F0 M) ((F0_le_FF M).trans (FF_le M ℓ)) hF0).2
  exact (relfinrank_ne_zero_of_tower (F0_le_FF M) (FF_le M ℓ) h').1

theorem relfinrank_BB_FF' (L : Type*) [Field L] [Algebra ℚ L] (h : HeckeBetaOneDefined M ℓ) :
    relfinrank (BB M ℓ) (FF' M ℓ) = dd M ℓ := by
  obtain ⟨hc, hc0⟩ := relfinrank_F0'_FF'_eq M ℓ L
  have s1 := relfinrank_mul_relfinrank (B0_le_BB M ℓ) (BB_le_FF' M ℓ h)
  have s2 := relfinrank_mul_relfinrank (B0_le_F0' M ℓ) (F0'_le_FF' M ℓ)
  rw [relfinrank_B0_BB] at s1
  rw [relfinrank_B0_F0', hc, ← s1, mul_comm] at s2
  exact (Nat.eq_of_mul_eq_mul_left (Nat.pos_of_ne_zero hc0) s2).symm

theorem main (L : Type*) [Field L] [Algebra ℚ L] (h : HeckeBetaOneDefined M ℓ) :
    finrankAlong L (heckeBetaOneBar L M ℓ) = dd M ℓ := by
  have e1 := AlgebraicCurve.finrankAlong_eq_relfinrank_fieldRange (laurentBaseChange L (FF M))
    (laurentBaseChange L (FF' M ℓ)) (heckeBetaOneBar L M ℓ)
  have e2 := fieldRange_heckeBetaOneBar M ℓ L h
  have e3 : relfinrank ((laurentBaseChange L (FF M)).map (qExpandAlg L ℓ)) (laurentBaseChange L (FF' M ℓ)) =
      dd M ℓ := by
    rw [← laurentBaseChange_map_qExpand,
      relfinrank_lbc_lbc L (BB_le_FF' M ℓ h) (jqN ℓ) (B0_le_BB M ℓ (jqN_mem_B0 M ℓ)) (transcendental_jqN ℓ)
        (relfinrank_adjoin_FF'_ne_zero M ℓ _ (F0'_le_FF' M ℓ (B0_le_F0' M ℓ (jqN_mem_B0 M ℓ))) (transcendental_jqN ℓ))]
    exact relfinrank_BB_FF' M ℓ L h
  rw [← e2] at e3
  exact e1.trans e3

end Assembly

end DBeta
p2m_reactivate "P2MW.S_ModularCurve_finrankAlong_heckeBetaOneBar.DBeta"

end
p2m_reactivate "P2MW.S_ModularCurve_finrankAlong_heckeBetaOneBar.DBeta"

theorem solution (L : Type*) [Field L] [Algebra ℚ L]
    (M : ℕ) [NeZero M] (ℓ : ℕ) [Fact ℓ.Prime] (h : ModularCurve.HeckeBetaOneDefined M ℓ) :
    AlgebraicCurve.finrankAlong L (ModularCurve.heckeBetaOneBar L M ℓ) =
      if ℓ ∣ M then ℓ else ℓ + 1 :=
  DBeta.main M ℓ L h

end S_ModularCurve_finrankAlong_heckeBetaOneBar
end P2MW
export P2MW.S_ModularCurve_finrankAlong_heckeBetaOneBar (solution)
