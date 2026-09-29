-- Prove2me | solution 1 for ModularCurve.x1FunctionField_mul_sup_x1FunctionField_mul_eq_of_coprime
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.620212+00:00
-- url     : https://prove2.me/submissions/3a2ab56f-a2f9-5912-be89-dfe16f3b4ccd

import Mathlib
import Definitions.Def_ModularCurve_LevelNFunctionField
import Definitions.Def_ModularCurve_X1
import Definitions.Def_ModularCurve_JqCoeff
import Theorems.Thm_ModularCurve_LevelN_isDomain_ring
import Theorems.Thm_ModularCurve_LevelN_exists_monoidHom_algEquiv_fixedField_eq_adjoin
import Theorems.Thm_ModularCurve_LevelN_exists_algHom_laurentBaseChange_apply_eq_qExpand
import Theorems.Thm_ModularCurve_exists_ringHom_laurentBaseChange_qExpFunctionFieldC_levelN_qExpansion
import Theorems.Thm_ModularCurve_finrank_adjoin_jqModC_laurentBaseChange_qExpFunctionFieldC_gamma1_eq_index
import Theorems.Thm_ModularCurve_jqModC_mem_intFormRatiosC
import Theorems.Thm_ModularCurve_laurentBaseChange_adjoin
import Theorems.Thm_ModularCurve_relfinrank_laurentBaseChange
import Theorems.Thm_ModularCurve_transcendental_jq
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_x1FunctionField_mul_sup_x1FunctionField_mul_eq_of_coprime
p2m_attr_erase "instance" "CohCarrier.iotaDeg_range_finiteIndex CohCarrier.Gamma0Upper_finiteIndex TateModule.instModule TateModule.instSMul GaloisRepAdic.instAddCommGroup GaloisRepAdic.instFree GaloisRepAdic.instFinite GaloisRepAdic.instModule ResidualGaloisRep.instModule ResidualGaloisRep.instModuleFinite ResidualGaloisRep.instAddCommGroup WeierstrassCurve.Affine.Point.instSMulCommClassAlgEquivZModTorsionBy instDecEqAlgebraicClosureRat WeierstrassCurve.Affine.Point.instDistribMulActionAlgEquiv WeierstrassCurve.Affine.Point.instModuleZModTorsionBy WeierstrassCurve.Affine.Point.instSMulTorsionBy WeierstrassCurve.Affine.Point.instDistribMulActionTorsionBy WeierstrassCurve.Affine.Point.instSMulAlgEquiv WeierstrassCurve.Affine.Point.instFinite ModularCurve.instIsDomainTensorProduct AlgebraicClosure.Rat.isGalois AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.instFundamentalIdentityOfSumRamificationInertia AlgebraicCurve.Place.instIsScalarTowerResidueFieldRestrictPushforward AlgebraicCurve.Place.instAlgebraResidueFieldRestrictPushforward AlgebraicCurve.Place.instIsLocalHomRestrictInclusion AlgebraicCurve.IsCurveOver.instNontrivialKaehler AlgebraicCurve.IsCurveOver.instFreeKaehler AlgebraicCurve.IsCurveOver.toHasPrincipalDivisors AlgebraicCurve.IsCurveOver.instFiniteResidue AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation ModularCurve.PhiGen.instNeZeroPhiGenCosetA ModularCurve.instFiniteProjectiveLine ModularCurve.unimodularRowSetoid"
p2m_attr_erase "simp" "ModularCurve.JH.torsionGaloisRep_apply CohCarrier.conjUpperMat_apply_11 CohCarrier.conjUpperMat_apply_10 CohCarrier.mem_Gamma0Upper CohCarrier.val_gamma0Units TateModule.smul_apply TateModule.coe_mulP TateModule.proj_apply TateModule.coe_add TateModule.coe_sub WeierstrassCurve.tateModuleRepOfBasis_V TateModule.coe_zero TateModule.rep_apply WeierstrassCurve.tateModuleRep_V WeierstrassCurve.tateModuleRepOfBasis_ρ_apply GaloisRep.padicIntToRingLevel_apply TateModule.coe_neg WeierstrassCurve.tateModuleRep_ρ_apply GaloisRepAdic.mk.injEq GaloisRepAdic.mk.sizeOf_spec GaloisRepAdic.Equiv.mk.sizeOf_spec GaloisRepAdic.Equiv.mk.injEq ResidualGaloisRep.mk.sizeOf_spec ResidualGaloisRep.mk.injEq WeierstrassCurve.Affine.Point.galoisRepModuleEnd_apply FreyPackage.mk.sizeOf_spec FreyPackage.mk.injEq ResidualGaloisRep.Equiv.mk.sizeOf_spec ResidualGaloisRep.Equiv.mk.injEq ModularCurve.qExpandAlgHomC_apply ModularCurve.coe_baseChangeEquiv_apply ModularCurve.baseChangeHom_tmul ModularCurve.qInftyPlaceBar_toValuationSubring ModularCurve.qSeriesBar_zero ModularCurve.qSeriesBar_add ModularCurve.cuspInftyFull_toValuationSubring ModularCurve.qInftyPlaceRat_toValuationSubring ModularCurve.qSeriesBar_mul ModularCurve.qSeriesBar_div ModularCurve.qSeriesBar_eq_zero_iff"
p2m_attr_erase "simp" "ModularCurve.coe_uniformizerBar ModularCurve.qSeriesBar_pow ModularCurve.cuspInfty_toValuationSubring ModularCurve.qSeriesBar_one ModularCurve.qSeriesBar_inv ModularCurve.qSeriesBar_sub ModularCurve.qSeriesBar_neg ModularCurve.coe_cuspidalDivisor₀ AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal AlgebraicCurve.Divisor.mapRestrict_single AlgebraicCurve.Divisor.pushforward_single AlgebraicCurve.Place.coe_restrictInclusion AlgebraicCurve.Place.mem_fiber AlgebraicCurve.Place.restrict_toValuationSubring AlgebraicCurve.Divisor.degree_pushforward AlgebraicCurve.Place.restrictResidueMap_residue AlgebraicCurve.Pic0.coe_pushforwardDegZeroHom AlgebraicCurve.Pic0.coe_pullbackDegZeroHom AlgebraicCurve.IsFrobeniusEndo.frobNormRingHom_apply ModularCurve.frobeniusPushforwardGeomLevelPic0_mk ModularCurve.coe_frobeniusGeomLevelEquiv_apply ModularCurve.coe_frobeniusPushforwardGeomLevelDegZero ModularCurve.heckeFibreGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusGeomLevel_apply_coe ModularCurve.frobeniusPullbackGeomLevelPic0OfIsCurveOver_mk ModularCurve.coe_heckeFibreGeomLevelDegZero ModularCurve.coe_frobeniusPullbackGeomLevelDegZero ModularCurve.frobeniusPullbackGeomLevelPic0_mk ModularCurve.frobeniusPullbackGeomLevel_single ModularCurve.heckeFibreGeomLevelPic0_mk ModularCurve.frobeniusPushforwardGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusPushforwardGeomLevel_single ModularCurve.qExpandAlgC_apply AlgebraicCurve.Place.congrEquiv_symm_apply AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal AlgebraicCurve.Place.congrRingEquiv_toValuationSubring"
p2m_attr_erase "simp" "AlgebraicCurve.Place.congrEquiv_apply AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply AlgebraicCurve.RationalFunctionField.deg_placeOfPoint AlgebraicCurve.Divisor.degree_pushforwardAlong AlgebraicCurve.Pic0.coe_degZeroCorrespondence AlgebraicCurve.Place.mem_fiberAlong AlgebraicCurve.coe_frobeniusPushforwardDegZero AlgebraicCurve.IsFrobeniusEndo.coe_frobeniusPullbackDegZero ModularCurve.reduceModBivar_C_X ModularCurve.laurentMap_coeff ModularCurve.reduceModBivar_X ModularCurve.laurentMap_single ModularCurve.evalAtJInt_X ModularCurve.evalAtJMod_X ModularCurve.jqNMod_one ModularCurve.aeval_heckeGen ModularCurve.coe_mTorsionGaloisRep_apply ModularCurve.eisensteinSystem_of_dvd ModularCurve.eisensteinSystem_of_not_dvd ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL ModularCurve.eisensteinNumerator_nineteen"
p2m_attr_erase "simp" "ModularCurve.eisensteinNumerator_seventeen ModularCurve.eisensteinNumerator_eleven ModularCurve.eisensteinNumerator_five ModularCurve.eisensteinNumerator_seven ModularCurve.eisensteinNumerator_twentythree ModularCurve.eisensteinNumerator_thirteen ModularCurve.constantCoeff_dedekindEtaUnitQ WeierstrassCurve.reducePoint_zero WeierstrassCurve.Affine.Point.galoisRep_apply ModularCurve.ProjectiveLine.map_mk"

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 1600000
set_option maxHeartbeats 3200000

open scoped MatrixGroups IntermediateField
open Polynomial

namespace CompQ

section PM

variable {G : Type*} [Group G]

theorem mem_or_mul_mem_of_mem_sup_zpowers (H : Subgroup G) {z : G} (hz : z ∈ Subgroup.center G)
    (hz2 : z * z = 1) {g : G} (hg : g ∈ H ⊔ Subgroup.zpowers z) : g ∈ H ∨ g * z ∈ H := by
  have hcomm : ∀ g : G, g * z = z * g := fun g => (Subgroup.mem_center_iff.mp hz g)
  let K : Subgroup G :=
    { carrier := {g | g ∈ H ∨ g * z ∈ H}
      one_mem' := Or.inl H.one_mem
      mul_mem' := by
        rintro x y (hx | hx) (hy | hy)
        · exact Or.inl (H.mul_mem hx hy)
        · refine Or.inr ?_
          rw [mul_assoc]
          exact H.mul_mem hx hy
        · refine Or.inr ?_
          rw [mul_assoc, hcomm y, ← mul_assoc]
          exact H.mul_mem hx hy
        · refine Or.inl ?_
          have : x * y = (x * z) * (y * z) := by
            rw [mul_assoc, ← mul_assoc z, ← hcomm y, mul_assoc y, hz2, mul_one]
          rw [this]
          exact H.mul_mem hx hy
      inv_mem' := by
        rintro x (hx | hx)
        · exact Or.inl (H.inv_mem hx)
        · refine Or.inr ?_
          have hzinv : z⁻¹ = z := inv_eq_of_mul_eq_one_right hz2
          have : x⁻¹ * z = (x * z)⁻¹ := by rw [mul_inv_rev, hzinv, hcomm]
          rw [this]
          exact H.inv_mem hx }
  have hle : H ⊔ Subgroup.zpowers z ≤ K := by
    refine sup_le (fun g hg => Or.inl hg) ?_
    rw [Subgroup.zpowers_le]
    exact Or.inr (by rw [hz2]; exact H.one_mem)
  exact hle hg

end PM

theorem negOne_mem_center : (-1 : SL(2, ℤ)) ∈ Subgroup.center SL(2, ℤ) := by
  rw [Subgroup.mem_center_iff]
  intro g
  rw [mul_neg_one, neg_one_mul]

theorem mem_sup_zpowers_negOne_iff (Γ : Subgroup SL(2, ℤ)) (x : SL(2, ℤ)) :
    x ∈ Γ ⊔ Subgroup.zpowers (-1 : SL(2, ℤ)) ↔ x ∈ Γ ∨ -x ∈ Γ := by
  constructor
  · intro hx
    rcases mem_or_mul_mem_of_mem_sup_zpowers Γ negOne_mem_center (by rw [neg_one_mul, neg_neg]) hx with h | h
    · exact Or.inl h
    · right; rwa [mul_neg_one] at h
  · rintro (h | h)
    · exact Subgroup.mem_sup_left h
    · have : x = -x * (-1 : SL(2, ℤ)) := by rw [mul_neg_one, neg_neg]
      rw [this]
      exact Subgroup.mul_mem _ (Subgroup.mem_sup_left h) (Subgroup.mem_sup_right (Subgroup.mem_zpowers _))

theorem dvd_and_dvd_iff (M a b : ℕ) (hM : M ≠ 0) (hab : Nat.Coprime a b) (k : ℤ) :
    ((M * a : ℕ) : ℤ) ∣ k ∧ ((M * b : ℕ) : ℤ) ∣ k ↔ ((M * a * b : ℕ) : ℤ) ∣ k := by
  push_cast
  constructor
  · rintro ⟨⟨u, hu⟩, hb⟩
    rw [hu, mul_assoc] at hb
    have hb' : (b : ℤ) ∣ (a : ℤ) * u :=
      (mul_dvd_mul_iff_left (by exact_mod_cast hM : (M : ℤ) ≠ 0)).mp hb
    have hcop : IsCoprime (b : ℤ) (a : ℤ) := Nat.isCoprime_iff_coprime.mpr hab.symm
    obtain ⟨w, hw⟩ := hcop.dvd_of_dvd_mul_left (by rwa [mul_comm] at hb')
    refine ⟨w, ?_⟩
    rw [hu, hw]
    ring
  · intro h
    exact ⟨dvd_trans ⟨b, by ring⟩ h, dvd_trans ⟨a, by ring⟩ h⟩

theorem intCast_eq_one_iff (n : ℕ) (k : ℤ) : ((k : ZMod n) = 1) ↔ (n : ℤ) ∣ k - 1 := by
  rw [show (1 : ZMod n) = ((1 : ℤ) : ZMod n) by norm_cast, ZMod.intCast_eq_intCast_iff_dvd_sub]
  rw [dvd_sub_comm]

theorem intCast_eq_zero_iff (n : ℕ) (k : ℤ) : ((k : ZMod n) = 0) ↔ (n : ℤ) ∣ k :=
  ZMod.intCast_zmod_eq_zero_iff_dvd k n

theorem gamma1_inf_gamma1_eq (M a b : ℕ) (hM : M ≠ 0) (hab : Nat.Coprime a b) :
    CongruenceSubgroup.Gamma1 (M * a) ⊓ CongruenceSubgroup.Gamma1 (M * b) =
      CongruenceSubgroup.Gamma1 (M * a * b) := by
  ext A
  simp only [Subgroup.mem_inf, CongruenceSubgroup.Gamma1_mem, intCast_eq_one_iff, intCast_eq_zero_iff,
    ← dvd_and_dvd_iff M a b hM hab]
  tauto

theorem not_mem_and_neg_mem (M a b : ℕ) (hM : 3 ≤ M) {x : SL(2, ℤ)}
    (ha : x ∈ CongruenceSubgroup.Gamma1 (M * a)) (hb : -x ∈ CongruenceSubgroup.Gamma1 (M * b)) : False := by
  rw [CongruenceSubgroup.Gamma1_mem] at ha hb
  obtain ⟨ha0, -, -⟩ := ha
  obtain ⟨hb0, -, -⟩ := hb
  rw [intCast_eq_one_iff] at ha0 hb0
  rw [Matrix.SpecialLinearGroup.coe_neg, Matrix.neg_apply] at hb0
  have h1 : (M : ℤ) ∣ (x : Matrix (Fin 2) (Fin 2) ℤ) 0 0 - 1 := dvd_trans ⟨a, by push_cast; ring⟩ ha0
  have h2 : (M : ℤ) ∣ -(x : Matrix (Fin 2) (Fin 2) ℤ) 0 0 - 1 := dvd_trans ⟨b, by push_cast; ring⟩ hb0
  have h3 : (M : ℤ) ∣ 2 := by
    have := dvd_sub h1 h2
    have e : (x : Matrix (Fin 2) (Fin 2) ℤ) 0 0 - 1 - (-(x : Matrix (Fin 2) (Fin 2) ℤ) 0 0 - 1) =
        2 * (x : Matrix (Fin 2) (Fin 2) ℤ) 0 0 := by ring
    rw [e] at this

    have h4 : (M : ℤ) ∣ 2 * ((x : Matrix (Fin 2) (Fin 2) ℤ) 0 0 - 1) := dvd_mul_of_dvd_right h1 2
    have := dvd_sub this h4
    have e2 : 2 * (x : Matrix (Fin 2) (Fin 2) ℤ) 0 0 - 2 * ((x : Matrix (Fin 2) (Fin 2) ℤ) 0 0 - 1) = 2 := by ring
    rwa [e2] at this
  have h5 : (M : ℤ) ≤ 2 := Int.le_of_dvd (by norm_num) h3
  omega

theorem gamma1_sup_inf_gamma1_sup_eq (M a b : ℕ) (hM : 3 ≤ M) (hab : Nat.Coprime a b) :
    (CongruenceSubgroup.Gamma1 (M * a) ⊔ Subgroup.zpowers (-1 : SL(2, ℤ))) ⊓
        (CongruenceSubgroup.Gamma1 (M * b) ⊔ Subgroup.zpowers (-1 : SL(2, ℤ))) =
      CongruenceSubgroup.Gamma1 (M * a * b) ⊔ Subgroup.zpowers (-1 : SL(2, ℤ)) := by
  have hM0 : M ≠ 0 := by omega
  have hinf := gamma1_inf_gamma1_eq M a b hM0 hab
  ext x
  rw [Subgroup.mem_inf, mem_sup_zpowers_negOne_iff, mem_sup_zpowers_negOne_iff, mem_sup_zpowers_negOne_iff,
    ← hinf, Subgroup.mem_inf, Subgroup.mem_inf]
  constructor
  · rintro ⟨ha | ha, hb | hb⟩
    · exact Or.inl ⟨ha, hb⟩
    · exact (not_mem_and_neg_mem M a b hM ha hb).elim
    · exact (not_mem_and_neg_mem M b a hM hb ha).elim
    · exact Or.inr ⟨ha, hb⟩
  · rintro (⟨ha, hb⟩ | ⟨ha, hb⟩)
    · exact ⟨Or.inl ha, Or.inl hb⟩
    · exact ⟨Or.inr ha, Or.inr hb⟩

theorem map_inf_map_eq {H : Type*} [Group H] (σ : SL(2, ℤ) →* H) (M a b : ℕ) (hM : 3 ≤ M) (hab : Nat.Coprime a b)
    (hker : σ.ker ≤ CongruenceSubgroup.Gamma1 (M * b) ⊔ Subgroup.zpowers (-1 : SL(2, ℤ))) :
    (CongruenceSubgroup.Gamma1 (M * a) ⊔ Subgroup.zpowers (-1 : SL(2, ℤ))).map σ ⊓
        (CongruenceSubgroup.Gamma1 (M * b) ⊔ Subgroup.zpowers (-1 : SL(2, ℤ))).map σ =
      (CongruenceSubgroup.Gamma1 (M * a * b) ⊔ Subgroup.zpowers (-1 : SL(2, ℤ))).map σ := by
  rw [← gamma1_sup_inf_gamma1_sup_eq M a b hM hab]
  apply le_antisymm
  · rintro y ⟨⟨g, hg, rfl⟩, ⟨h, hh, hgh⟩⟩
    refine ⟨g, ⟨hg, ?_⟩, rfl⟩

    have hk : g * h⁻¹ ∈ σ.ker := by
      rw [MonoidHom.mem_ker, map_mul, map_inv, ← hgh, mul_inv_cancel]
    have : g = g * h⁻¹ * h := by rw [inv_mul_cancel_right]
    rw [this]
    exact Subgroup.mul_mem _ (hker hk) hh
  · exact Subgroup.map_inf_le _ _ _

theorem sup_eq_of_fixingSubgroup_inf_eq {F E : Type*} [Field F] [Field E] [Algebra F E]
    [FiniteDimensional F E] [IsGalois F E] (K₁ K₂ K₃ : IntermediateField F E)
    (h : K₁.fixingSubgroup ⊓ K₂.fixingSubgroup = K₃.fixingSubgroup) : K₁ ⊔ K₂ = K₃ := by
  rw [← IsGalois.fixedField_fixingSubgroup (K₁ ⊔ K₂), IntermediateField.fixingSubgroup_sup, h,
    IsGalois.fixedField_fixingSubgroup]

theorem fixedField_inf {F E : Type*} [Field F] [Field E] [Algebra F E]
    [FiniteDimensional F E] [IsGalois F E] (H₁ H₂ : Subgroup (E ≃ₐ[F] E)) :
    IntermediateField.fixedField (H₁ ⊓ H₂) = IntermediateField.fixedField H₁ ⊔ IntermediateField.fixedField H₂ := by
  symm
  apply sup_eq_of_fixingSubgroup_inf_eq
  rw [IntermediateField.fixingSubgroup_fixedField, IntermediateField.fixingSubgroup_fixedField,
    IntermediateField.fixingSubgroup_fixedField]

end CompQ

namespace CompQ

noncomputable abbrev red (L : ℕ) : SL(2, ℤ) →* SL(2, ZMod L) :=
  Matrix.SpecialLinearGroup.map (Int.castRingHom (ZMod L))

theorem red_ker (L : ℕ) : (red L).ker = CongruenceSubgroup.Gamma L := rfl

theorem red_apply (L : ℕ) (g : SL(2, ℤ)) (i j : Fin 2) :
    (red L g) i j = ((g i j : ℤ) : ZMod L) := rfl

theorem red_eq_red_T_zpow_of_mem_gamma1 (L : ℕ) {γ : SL(2, ℤ)} (hγ : γ ∈ CongruenceSubgroup.Gamma1 L) :
    red L γ = red L (ModularGroup.T ^ (γ 0 1)) := by
  rw [CongruenceSubgroup.Gamma1_mem] at hγ
  obtain ⟨h00, h11, h10⟩ := hγ
  ext i j
  rw [red_apply, red_apply]
  fin_cases i <;> fin_cases j
  · simpa [ModularGroup.coe_T_zpow] using h00
  · simp [ModularGroup.coe_T_zpow]
  · simpa [ModularGroup.coe_T_zpow] using h10
  · simpa [ModularGroup.coe_T_zpow] using h11

theorem T_zpow_mem_gamma1 (N : ℕ) (m : ℤ) : ModularGroup.T ^ m ∈ CongruenceSubgroup.Gamma1 N := by
  rw [CongruenceSubgroup.Gamma1_mem]
  simp [ModularGroup.coe_T_zpow]

theorem gamma1_le_gamma1_of_dvd {L N : ℕ} (h : L ∣ N) : CongruenceSubgroup.Gamma1 N ≤ CongruenceSubgroup.Gamma1 L := by
  intro A hA
  rw [CongruenceSubgroup.Gamma1_mem] at hA ⊢
  obtain ⟨h00, h11, h10⟩ := hA
  refine ⟨?_, ?_, ?_⟩
  · have := congrArg (ZMod.castHom h (ZMod L)) h00
    rwa [map_intCast, map_one] at this
  · have := congrArg (ZMod.castHom h (ZMod L)) h11
    rwa [map_intCast, map_one] at this
  · have := congrArg (ZMod.castHom h (ZMod L)) h10
    rwa [map_intCast, map_zero] at this

theorem map_red_gamma1_eq {L N : ℕ} (h : L ∣ N) :
    (CongruenceSubgroup.Gamma1 N).map (red L) = (CongruenceSubgroup.Gamma1 L).map (red L) := by
  apply le_antisymm (Subgroup.map_mono (gamma1_le_gamma1_of_dvd h))
  rintro _ ⟨γ, hγ, rfl⟩
  exact ⟨ModularGroup.T ^ (γ 0 1), T_zpow_mem_gamma1 N _, (red_eq_red_T_zpow_of_mem_gamma1 L hγ).symm⟩

theorem Gamma_le_gamma1 (L : ℕ) : CongruenceSubgroup.Gamma L ≤ CongruenceSubgroup.Gamma1 L := by
  intro A hA
  rw [CongruenceSubgroup.Gamma_mem] at hA
  rw [CongruenceSubgroup.Gamma1_mem]
  exact ⟨hA.1, hA.2.2.2, hA.2.2.1⟩

theorem conj_comp_conj {G : Type*} [Group G] (a b : G) :
    (MulAut.conj a).toMonoidHom.comp (MulAut.conj b).toMonoidHom = (MulAut.conj (a * b)).toMonoidHom := by
  ext g
  show a * (b * g * b⁻¹) * a⁻¹ = a * b * g * (a * b)⁻¹
  group

theorem conj_one_toMonoidHom {G : Type*} [Group G] : (MulAut.conj (1 : G)).toMonoidHom = MonoidHom.id G := by
  ext g
  show 1 * g * 1⁻¹ = g
  group

theorem map_conj_comm {G H : Type*} [Group G] [Group H] (f : G →* H) (δ : G) (S : Subgroup G) :
    (S.map (MulAut.conj δ).toMonoidHom).map f = (S.map f).map (MulAut.conj (f δ)).toMonoidHom := by
  rw [Subgroup.map_map, Subgroup.map_map]
  congr 1
  ext g
  show f (δ * g * δ⁻¹) = f δ * f g * (f δ)⁻¹
  rw [map_mul, map_mul, map_inv]

theorem eq_map_conj_of_le {H : Type*} [Group H] [Finite H] (A : Subgroup H) (h : H)
    (hle : A ≤ A.map (MulAut.conj h).toMonoidHom) : A = A.map (MulAut.conj h).toMonoidHom := by
  apply Subgroup.eq_of_le_of_card_ge hle
  rw [Subgroup.card_map_of_injective (MulAut.conj h).injective]

theorem map_conj_gamma1_sup_eq_of_le {L N : ℕ} [NeZero L] (h : L ∣ N) (δ : SL(2, ℤ))
    (hle : CongruenceSubgroup.Gamma1 N ⊔ Subgroup.zpowers (-1 : SL(2, ℤ)) ≤
      (CongruenceSubgroup.Gamma1 L ⊔ Subgroup.zpowers (-1 : SL(2, ℤ))).map (MulAut.conj δ).toMonoidHom) :
    (CongruenceSubgroup.Gamma1 L ⊔ Subgroup.zpowers (-1 : SL(2, ℤ))).map (MulAut.conj δ).toMonoidHom =
      CongruenceSubgroup.Gamma1 L ⊔ Subgroup.zpowers (-1 : SL(2, ℤ)) := by
  set S := CongruenceSubgroup.Gamma1 L ⊔ Subgroup.zpowers (-1 : SL(2, ℤ)) with hS
  set SN := CongruenceSubgroup.Gamma1 N ⊔ Subgroup.zpowers (-1 : SL(2, ℤ)) with hSN
  set π := red L with hπ
  set A := S.map π with hA

  have hAN : SN.map π = A := by
    rw [hSN, hA, hS, Subgroup.map_sup, Subgroup.map_sup, map_red_gamma1_eq h]

  have hker : π.ker ≤ S := by
    rw [hπ, red_ker]
    exact (Gamma_le_gamma1 L).trans le_sup_left
  have hcomap : (A).comap π = S := by
    rw [hA, Subgroup.comap_map_eq, sup_eq_left.mpr hker]

  have h1 : A ≤ A.map (MulAut.conj (π δ)).toMonoidHom := by
    calc A = SN.map π := hAN.symm
      _ ≤ (S.map (MulAut.conj δ).toMonoidHom).map π := Subgroup.map_mono hle
      _ = (S.map π).map (MulAut.conj (π δ)).toMonoidHom := map_conj_comm π δ S
      _ = A.map (MulAut.conj (π δ)).toMonoidHom := by rw [hA]
  have h2 : A = A.map (MulAut.conj (π δ)).toMonoidHom := eq_map_conj_of_le A (π δ) h1
  have h3 : A.map (MulAut.conj (π δ⁻¹)).toMonoidHom = A := by
    conv_lhs => rw [h2]
    rw [Subgroup.map_map, conj_comp_conj, ← map_mul, inv_mul_cancel, map_one, conj_one_toMonoidHom, Subgroup.map_id]

  have hsub : ∀ ε : SL(2, ℤ), A.map (MulAut.conj (π ε)).toMonoidHom = A →
      S.map (MulAut.conj ε).toMonoidHom ≤ S := by
    intro ε hε
    calc S.map (MulAut.conj ε).toMonoidHom
        ≤ ((S.map (MulAut.conj ε).toMonoidHom).map π).comap π := Subgroup.le_comap_map _ _
      _ = (A.map (MulAut.conj (π ε)).toMonoidHom).comap π := by rw [map_conj_comm, ← hA]
      _ = S := by rw [hε, hcomap]
  have hle1 : S.map (MulAut.conj δ).toMonoidHom ≤ S := hsub δ h2.symm
  have hle2 : S.map (MulAut.conj δ⁻¹).toMonoidHom ≤ S := hsub δ⁻¹ h3
  apply le_antisymm hle1

  have : S = (S.map (MulAut.conj δ⁻¹).toMonoidHom).map (MulAut.conj δ).toMonoidHom := by
    rw [Subgroup.map_map, conj_comp_conj, mul_inv_cancel, conj_one_toMonoidHom, Subgroup.map_id]
  conv_lhs => rw [this]
  exact Subgroup.map_mono hle2

end CompQ

namespace CompQ

theorem sup_eq_of_fixingSubgroup_inf_eq' {F E : Type*} [Field F] [Field E] [Algebra F E]
    [FiniteDimensional F E] [IsGalois F E] {K₁ K₂ K₃ : IntermediateField F E}
    (h : K₁.fixingSubgroup ⊓ K₂.fixingSubgroup = K₃.fixingSubgroup) : K₁ ⊔ K₂ = K₃ := by
  rw [← IsGalois.fixedField_fixingSubgroup (K₁ ⊔ K₂), IntermediateField.fixingSubgroup_sup, h,
    IsGalois.fixedField_fixingSubgroup]

section GaloisCore

variable {k K : Type*} [Field k] [Field K] [Algebra k K]
variable {G₀ : Type*} [Group G₀] (σ : G₀ →* (K ≃ₐ[k] K)) (F₀ : IntermediateField k K)
  (hfixed : IntermediateField.fixedField σ.range = F₀)

include hfixed in
theorem apply_eq_of_mem_base (γ : G₀) {c : K} (hc : c ∈ F₀) : σ γ c = c := by
  rw [← hfixed, IntermediateField.mem_fixedField_iff] at hc
  exact hc _ ⟨γ, rfl⟩

def rebase (γ : G₀) : K ≃ₐ[F₀] K :=
  { (σ γ).toRingEquiv with
    commutes' := fun c => apply_eq_of_mem_base σ F₀ hfixed γ c.2 }

theorem rebase_apply (γ : G₀) (x : K) : rebase σ F₀ hfixed γ x = σ γ x := rfl

def rebaseHom : G₀ →* (K ≃ₐ[F₀] K) where
  toFun := rebase σ F₀ hfixed
  map_one' := by
    ext x
    rw [rebase_apply, map_one]
    rfl
  map_mul' a b := by
    ext x
    rw [rebase_apply, map_mul, AlgEquiv.mul_apply, AlgEquiv.mul_apply, rebase_apply, rebase_apply]

theorem rebaseHom_apply (γ : G₀) (x : K) : rebaseHom σ F₀ hfixed γ x = σ γ x := rfl

theorem ker_rebaseHom : (rebaseHom σ F₀ hfixed).ker = σ.ker := by
  ext γ
  rw [MonoidHom.mem_ker, MonoidHom.mem_ker, AlgEquiv.ext_iff, AlgEquiv.ext_iff]
  simp only [rebaseHom_apply, AlgEquiv.one_apply]

theorem card_map_rebaseHom_mul_index (S : Subgroup G₀) (hS : σ.ker ≤ S) [σ.ker.FiniteIndex] :
    Nat.card (S.map (rebaseHom σ F₀ hfixed)) * S.index = σ.ker.index := by
  rw [← MonoidHom.restrict_range, ← Subgroup.index_ker, MonoidHom.ker_restrict, ker_rebaseHom]
  exact Subgroup.relIndex_mul_index hS

variable [FiniteDimensional F₀ K]

theorem finrank_fixedField_map (hdeg : Module.finrank F₀ K = σ.ker.index) [σ.ker.FiniteIndex]
    (S : Subgroup G₀) (hS : σ.ker ≤ S) :
    Module.finrank F₀ (IntermediateField.fixedField (S.map (rebaseHom σ F₀ hfixed))) = S.index := by
  haveI : S.FiniteIndex := Subgroup.finiteIndex_of_le hS
  set H := S.map (rebaseHom σ F₀ hfixed)
  have h1 : Module.finrank F₀ (IntermediateField.fixedField H) * Module.finrank (IntermediateField.fixedField H) K =
      Module.finrank F₀ K := Module.finrank_mul_finrank _ _ _
  rw [IntermediateField.finrank_fixedField_eq_card, hdeg, ← card_map_rebaseHom_mul_index σ F₀ hfixed S hS,
    mul_comm (Nat.card H)] at h1
  have hH : Nat.card H ≠ 0 := Nat.card_pos.ne'
  exact Nat.eq_of_mul_eq_mul_right (Nat.pos_of_ne_zero hH) h1

theorem extendScalars_eq_fixedField (hdeg : Module.finrank F₀ K = σ.ker.index) [σ.ker.FiniteIndex]
    (S : Subgroup G₀) (hS : σ.ker ≤ S) (W : IntermediateField k K) (hW : F₀ ≤ W)
    (hdegW : IntermediateField.relfinrank F₀ W = S.index)
    (hfix : ∀ γ ∈ S, ∀ w ∈ W, σ γ w = w) :
    IntermediateField.extendScalars hW = IntermediateField.fixedField (S.map (rebaseHom σ F₀ hfixed)) := by
  apply IntermediateField.eq_of_le_of_finrank_eq
  · intro w hw
    rw [IntermediateField.mem_fixedField_iff]
    rintro _ ⟨γ, hγ, rfl⟩
    exact hfix γ hγ w hw
  · rw [finrank_fixedField_map σ F₀ hfixed hdeg S hS, ← hdegW, IntermediateField.relfinrank_eq_finrank_of_le hW]

omit [FiniteDimensional F₀ K] in

theorem ker_le_map_conj (S : Subgroup G₀) (hS : σ.ker ≤ S) (δ : G₀) :
    σ.ker ≤ S.map (MulAut.conj δ).toMonoidHom := by
  intro g hg
  refine ⟨δ⁻¹ * g * δ, hS ?_, by show δ * (δ⁻¹ * g * δ) * δ⁻¹ = g; group⟩
  rw [MonoidHom.mem_ker] at hg ⊢
  rw [map_mul, map_mul, hg, mul_one, ← map_mul, inv_mul_cancel, map_one]

omit [FiniteDimensional F₀ K] in
theorem index_map_conj (S : Subgroup G₀) (δ : G₀) : (S.map (MulAut.conj δ).toMonoidHom).index = S.index :=
  Subgroup.index_map_of_bijective (MulAut.conj δ).bijective S

theorem extendScalars_eq_fixedField_conj (hdeg : Module.finrank F₀ K = σ.ker.index) [σ.ker.FiniteIndex]
    (S : Subgroup G₀) (hS : σ.ker ≤ S) (W : IntermediateField k K) (hW : F₀ ≤ W)
    (hdegW : IntermediateField.relfinrank F₀ W = S.index) (δ : G₀)
    (hfix : ∀ γ ∈ S, ∀ w ∈ W, σ (δ * γ * δ⁻¹) w = w) :
    IntermediateField.extendScalars hW =
      IntermediateField.fixedField ((S.map (MulAut.conj δ).toMonoidHom).map (rebaseHom σ F₀ hfixed)) := by
  apply extendScalars_eq_fixedField σ F₀ hfixed hdeg _ (ker_le_map_conj σ S hS δ) W hW
  · rw [index_map_conj]; exact hdegW
  · rintro _ ⟨γ, hγ, rfl⟩ w hw
    exact hfix γ hγ w hw

omit [FiniteDimensional F₀ K] in

theorem le_of_map_le_map {S T : Subgroup G₀} (hT : σ.ker ≤ T)
    (h : S.map (rebaseHom σ F₀ hfixed) ≤ T.map (rebaseHom σ F₀ hfixed)) : S ≤ T := by
  have := Subgroup.comap_mono (f := rebaseHom σ F₀ hfixed) h
  rw [Subgroup.comap_map_eq, Subgroup.comap_map_eq, ker_rebaseHom, sup_eq_left.mpr hT] at this
  exact le_sup_left.trans this

variable [IsGalois F₀ K]

include hfixed in

theorem sup_eq_of_galois (hdeg : Module.finrank F₀ K = σ.ker.index) [σ.ker.FiniteIndex]
    (Sa Sb Sab : Subgroup G₀) (hka : σ.ker ≤ Sa) (hkb : σ.ker ≤ Sb) (hSab : Sa ⊓ Sb = Sab)
    (hreal_a : ∀ δ : G₀, Sab ≤ Sa.map (MulAut.conj δ).toMonoidHom → Sa.map (MulAut.conj δ).toMonoidHom = Sa)
    (hreal_b : ∀ δ : G₀, Sab ≤ Sb.map (MulAut.conj δ).toMonoidHom → Sb.map (MulAut.conj δ).toMonoidHom = Sb)
    (Wa Wb Wab : IntermediateField k K) (ha : F₀ ≤ Wa) (hb : F₀ ≤ Wb) (hab : F₀ ≤ Wab)
    (haab : Wa ≤ Wab) (hbab : Wb ≤ Wab)
    (hdega : IntermediateField.relfinrank F₀ Wa = Sa.index) (hdegb : IntermediateField.relfinrank F₀ Wb = Sb.index)
    (hdegab : IntermediateField.relfinrank F₀ Wab = Sab.index)
    (hfixab : ∀ γ ∈ Sab, ∀ w ∈ Wab, σ γ w = w)
    (hfixa : ∃ δ : G₀, ∀ γ ∈ Sa, ∀ w ∈ Wa, σ (δ * γ * δ⁻¹) w = w)
    (hfixb : ∃ δ : G₀, ∀ γ ∈ Sb, ∀ w ∈ Wb, σ (δ * γ * δ⁻¹) w = w) :
    Wa ⊔ Wb = Wab := by
  set rb := rebaseHom σ F₀ hfixed with hrb
  have hkab : σ.ker ≤ Sab := by rw [← hSab]; exact le_inf hka hkb

  have hWab : IntermediateField.extendScalars hab = IntermediateField.fixedField (Sab.map rb) :=
    extendScalars_eq_fixedField σ F₀ hfixed hdeg Sab hkab Wab hab hdegab hfixab
  obtain ⟨δa, hδa⟩ := hfixa
  obtain ⟨δb, hδb⟩ := hfixb
  have hWa' := extendScalars_eq_fixedField_conj σ F₀ hfixed hdeg Sa hka Wa ha hdega δa hδa
  have hWb' := extendScalars_eq_fixedField_conj σ F₀ hfixed hdeg Sb hkb Wb hb hdegb δb hδb

  have key : ∀ (S : Subgroup G₀) (hS : σ.ker ≤ S) (W : IntermediateField k K) (hW : F₀ ≤ W) (hWab' : W ≤ Wab) (δ : G₀)
      (hreal : Sab ≤ S.map (MulAut.conj δ).toMonoidHom → S.map (MulAut.conj δ).toMonoidHom = S)
      (hWfix : IntermediateField.extendScalars hW =
        IntermediateField.fixedField ((S.map (MulAut.conj δ).toMonoidHom).map rb)),
      IntermediateField.extendScalars hW = IntermediateField.fixedField (S.map rb) := by
    intro S hS W hW hWab' δ hreal hWfix
    have hle : IntermediateField.extendScalars hW ≤ IntermediateField.extendScalars hab :=
      (IntermediateField.extendScalars_le_extendScalars_iff _ _).mpr hWab'
    rw [hWfix, hWab, IntermediateField.le_iff_le, IntermediateField.fixingSubgroup_fixedField] at hle
    have hle' : Sab ≤ S.map (MulAut.conj δ).toMonoidHom :=
      le_of_map_le_map σ F₀ hfixed (ker_le_map_conj σ S hS δ) hle
    rw [hWfix, hreal hle']
  have hWa : IntermediateField.extendScalars ha = IntermediateField.fixedField (Sa.map rb) :=
    key Sa hka Wa ha haab δa (hreal_a δa) hWa'
  have hWb : IntermediateField.extendScalars hb = IntermediateField.fixedField (Sb.map rb) :=
    key Sb hkb Wb hb hbab δb (hreal_b δb) hWb'

  have hsup : IntermediateField.extendScalars ha ⊔ IntermediateField.extendScalars hb = IntermediateField.extendScalars hab := by
    apply sup_eq_of_fixingSubgroup_inf_eq'
    rw [hWa, hWb, hWab, IntermediateField.fixingSubgroup_fixedField, IntermediateField.fixingSubgroup_fixedField,
      IntermediateField.fixingSubgroup_fixedField]

    rw [← hSab]
    apply le_antisymm
    · rintro y ⟨⟨g, hg, rfl⟩, ⟨h, hh, hgh⟩⟩
      refine ⟨g, ⟨hg, ?_⟩, rfl⟩
      have hk : g * h⁻¹ ∈ σ.ker := by
        rw [← ker_rebaseHom σ F₀ hfixed, MonoidHom.mem_ker, map_mul, map_inv, ← hgh, mul_inv_cancel]
      have : g = g * h⁻¹ * h := by rw [inv_mul_cancel_right]
      rw [this]
      exact Subgroup.mul_mem _ (hkb hk) hh
    · exact Subgroup.map_inf_le _ _ _

  have := congrArg (IntermediateField.restrictScalars k) hsup
  rw [← IntermediateField.restrictScalars_sup, IntermediateField.extendScalars_restrictScalars,
    IntermediateField.extendScalars_restrictScalars, IntermediateField.extendScalars_restrictScalars] at this
  exact this

end GaloisCore

end CompQ

noncomputable def CompQ.N3.qExpandAlgHom (L : Type*) [Field L] (N : ℕ) [NeZero N] :
    LaurentSeries L →ₐ[L] LaurentSeries L :=
  AlgHom.mk' (ModularCurve.qExpand L N) (fun c x => by
    rw [Algebra.smul_def, Algebra.smul_def, map_mul, LaurentSeries.algebraMap_apply,
      ModularCurve.qExpand_C])

theorem CompQ.N3.qExpandAlgHom_apply (L : Type*) [Field L] (N : ℕ) [NeZero N] (x : LaurentSeries L) :
    CompQ.N3.qExpandAlgHom L N x = ModularCurve.qExpand L N x := rfl

theorem CompQ.N3.exists_apply_eq_apply_smul
    {F K L : Type*} [Field F] [Field K] [Algebra F K] [Field L] [Algebra F L]
    (H : Subgroup (K ≃ₐ[F] K)) [Finite H] (E E' : K →ₐ[F] L)
    (hagree : ∀ c ∈ IntermediateField.fixedField H, E c = E' c) (x : K) :
    ∃ h : H, E' x = E ((h : K ≃ₐ[F] K) x) := by
  classical
  haveI : Fintype H := Fintype.ofFinite H
  set Q : K[X] := ∏ h : H, (X - C ((h : K ≃ₐ[F] K) x)) with hQ

  have hfix : ∀ i, Q.coeff i ∈ IntermediateField.fixedField H := by
    intro i
    rw [IntermediateField.mem_fixedField_iff]
    intro g hg
    have hmap : Q.map (g : K →+* K) = Q := by
      rw [hQ, Polynomial.map_prod]
      simp only [Polynomial.map_sub, Polynomial.map_X, Polynomial.map_C, RingHom.coe_coe]
      exact Fintype.prod_bijective (fun h : H => (⟨g, hg⟩ : H) * h) (Group.mulLeft_bijective _)
        _ _ fun h => rfl
    have := congrArg (fun P : K[X] => P.coeff i) hmap
    simpa only [Polynomial.coeff_map, RingHom.coe_coe] using this

  have hmapEE' : Q.map (E : K →+* L) = Q.map (E' : K →+* L) := by
    ext i
    rw [Polynomial.coeff_map, Polynomial.coeff_map, RingHom.coe_coe, RingHom.coe_coe]
    exact hagree _ (hfix i)

  have hQx : Q.eval x = 0 := by
    rw [hQ, eval_prod]
    exact Finset.prod_eq_zero (Finset.mem_univ (1 : H)) (by simp)
  have hroot : (Q.map (E : K →+* L)).eval (E' x) = 0 := by
    have h0 : Polynomial.eval₂ (E' : K →+* L) ((E' : K →+* L) x) Q = 0 := by
      rw [Polynomial.eval₂_hom, hQx, map_zero]
    rw [hmapEE', Polynomial.eval_map]
    simpa only [RingHom.coe_coe] using h0

  have hfac : Q.map (E : K →+* L) = ∏ h : H, (X - C (E ((h : K ≃ₐ[F] K) x))) := by
    rw [hQ, Polynomial.map_prod]
    simp only [Polynomial.map_sub, Polynomial.map_X, Polynomial.map_C, RingHom.coe_coe]
  rw [hfac, eval_prod, Finset.prod_eq_zero_iff] at hroot
  obtain ⟨h, -, hh⟩ := hroot
  refine ⟨h, ?_⟩
  simpa [sub_eq_zero] using hh

theorem CompQ.N3.exists_algHom_comp_eq
    {F K L : Type*} [Field F] [Field K] [Algebra F K] [Field L] [Algebra F L]
    (H : Subgroup (K ≃ₐ[F] K)) [Finite H] (E E' : K →ₐ[F] L)
    (hagree : ∀ c ∈ IntermediateField.fixedField H, E c = E' c) :
    ∃ g : K →ₐ[F] K, ∀ x, E (g x) = E' x := by
  have hmem : ∀ x, E' x ∈ E.range := by
    intro x
    obtain ⟨h, hh⟩ := CompQ.N3.exists_apply_eq_apply_smul H E E' hagree x
    exact ⟨_, hh.symm⟩
  refine ⟨(AlgEquiv.ofInjectiveField E).symm.toAlgHom.comp (E'.codRestrict E.range hmem), fun x => ?_⟩
  have h1 := AlgEquiv.ofInjective_apply E (RingHom.injective (E : K →+* L))
    ((AlgEquiv.ofInjectiveField E).symm (E'.codRestrict E.range hmem x))
  show E ((AlgEquiv.ofInjectiveField E).symm (E'.codRestrict E.range hmem x)) = E' x
  rw [← h1]
  show (((AlgEquiv.ofInjectiveField E) ((AlgEquiv.ofInjectiveField E).symm
    (E'.codRestrict E.range hmem x))) : L) = E' x
  rw [AlgEquiv.apply_symm_apply]
  rfl

namespace CompQ

p2m_open "ModularCurve~coeffEmb_jq"

section Concrete

variable {K : Type*} [Field K] [Algebra ℂ K]

theorem E_inj (E : K →ₐ[ℂ] LaurentSeries ℂ) : Function.Injective E := RingHom.injective (E : K →+* LaurentSeries ℂ)

theorem coeffMap_coeffEmb (ι : AlgebraicClosure ℚ →+* ℂ) (x : LaurentSeries ℚ) :
    coeffMap ι (coeffEmb (AlgebraicClosure ℚ) x) = coeffEmb ℂ x := by
  rw [coeffEmb, coeffEmb, coeffMap_coeffMap]
  exact coeffMap_congr (RingHom.ext_rat _ _) x

theorem jq_mem (Γ : Subgroup SL(2, ℤ)) : jq ∈ qExpFunctionFieldC ℚ Γ := by
  have h := jqModC_mem_intFormRatiosC ℚ Γ
  rw [jqModC_rat] at h
  exact intFormRatiosC_subset ℚ Γ h

theorem coeffEmb_jq (L : Type*) [Field L] [Algebra ℚ L] : coeffEmb L jq = jqModC L := by
  show (jqModC ℚ).map (algebraMap ℚ L) = jqModC L
  exact map_jqModC (algebraMap ℚ L)

theorem laurentBaseChange_le_of_forall {F : IntermediateField ℚ (LaurentSeries ℚ)}
    {P : IntermediateField ℂ (LaurentSeries ℂ)} (h : ∀ x ∈ F, coeffEmb ℂ x ∈ P) :
    laurentBaseChange ℂ F ≤ P := by
  rw [laurentBaseChange, IntermediateField.adjoin_le_iff]
  rintro _ ⟨x, hx, rfl⟩
  exact h x hx

theorem fieldRange_le_fieldRange (N : ℕ) [NeZero N] (E : K →ₐ[ℂ] LaurentSeries ℂ)
    {F F' : IntermediateField ℚ (LaurentSeries ℚ)} (hFF' : F ≤ F')
    (Ψ : laurentBaseChange ℂ F →ₐ[ℂ] K) (hΨ : ∀ u, E (Ψ u) = qExpand ℂ N (u : LaurentSeries ℂ))
    (Ψ' : laurentBaseChange ℂ F' →ₐ[ℂ] K) (hΨ' : ∀ u, E (Ψ' u) = qExpand ℂ N (u : LaurentSeries ℂ)) :
    Ψ.fieldRange ≤ Ψ'.fieldRange := by
  rintro _ ⟨u, rfl⟩
  have hle : laurentBaseChange ℂ F ≤ laurentBaseChange ℂ F' := by
    rw [laurentBaseChange, laurentBaseChange]
    exact IntermediateField.adjoin.mono ℂ _ _ (Set.image_mono hFF')
  refine ⟨⟨u, hle u.2⟩, E_inj E ?_⟩
  show E (Ψ' ⟨u, hle u.2⟩) = E (Ψ u)
  rw [hΨ, hΨ']

theorem apply_j_eq (N : ℕ) [NeZero N] (E : K →ₐ[ℂ] LaurentSeries ℂ) (jK : K) (hEj : E jK = qExpand ℂ N (jqModC ℂ))
    {F : IntermediateField ℚ (LaurentSeries ℚ)} (hj : jq ∈ F)
    (Ψ : laurentBaseChange ℂ F →ₐ[ℂ] K) (hΨ : ∀ u, E (Ψ u) = qExpand ℂ N (u : LaurentSeries ℂ)) :
    Ψ ⟨coeffEmb ℂ jq, coeffEmb_mem_laurentBaseChange ℂ hj⟩ = jK := by
  apply E_inj E
  rw [hΨ, hEj]
  show qExpand ℂ N (coeffEmb ℂ jq) = _
  rw [coeffEmb_jq]

theorem fieldRange_le_fixedField (N : ℕ) [NeZero N] (E : K →ₐ[ℂ] LaurentSeries ℂ)
    (σ : SL(2, ℤ) →* (K ≃ₐ[ℂ] K)) (S : Subgroup SL(2, ℤ))
    {F : IntermediateField ℚ (LaurentSeries ℚ)}
    (Ψ : laurentBaseChange ℂ F →ₐ[ℂ] K)
    (hgen : ∀ x (hx : x ∈ F), ∀ γ ∈ S,
      σ γ (Ψ ⟨coeffEmb ℂ x, coeffEmb_mem_laurentBaseChange ℂ hx⟩) = Ψ ⟨coeffEmb ℂ x, coeffEmb_mem_laurentBaseChange ℂ hx⟩) :
    ∀ γ ∈ S, ∀ w ∈ Ψ.fieldRange, σ γ w = w := by

  set FF : IntermediateField ℂ K := IntermediateField.fixedField (S.map σ) with hFF

  have hle : laurentBaseChange ℂ F ≤ (FF.comap Ψ).map (laurentBaseChange ℂ F).val := by
    apply laurentBaseChange_le_of_forall
    intro x hx
    refine ⟨⟨coeffEmb ℂ x, coeffEmb_mem_laurentBaseChange ℂ hx⟩, ?_, rfl⟩
    show Ψ _ ∈ FF
    rw [hFF, IntermediateField.mem_fixedField_iff]
    rintro _ ⟨γ, hγ, rfl⟩
    exact hgen x hx γ hγ
  intro γ hγ w hw
  obtain ⟨u, rfl⟩ := hw
  have hu : (u : LaurentSeries ℂ) ∈ (FF.comap Ψ).map (laurentBaseChange ℂ F).val := hle u.2
  obtain ⟨u', hu', hu'eq⟩ := hu
  have : u' = u := Subtype.ext hu'eq
  subst this
  have hmem : Ψ u' ∈ FF := hu'
  rw [hFF, IntermediateField.mem_fixedField_iff] at hmem
  exact hmem _ ⟨γ, hγ, rfl⟩

theorem relfinrank_map_map' {F E E' : Type*} [Field F] [Field E] [Field E'] [Algebra F E] [Algebra F E']
    (A B : IntermediateField F E) (f : E →ₐ[F] E') :
    IntermediateField.relfinrank (A.map f) (B.map f) = IntermediateField.relfinrank A B := by
  show Subfield.relfinrank _ _ = Subfield.relfinrank _ _
  rw [IntermediateField.toSubfield_map, IntermediateField.toSubfield_map]
  exact Subfield.relfinrank_map_map _ _ (f : E →+* E')

theorem relfinrank_adjoin_fieldRange (L N : ℕ) [NeZero L] [NeZero N] (E : K →ₐ[ℂ] LaurentSeries ℂ) (jK : K)
    (hEj : E jK = qExpand ℂ N (jqModC ℂ))
    (Ψ : laurentBaseChange ℂ (qExpFunctionFieldC ℚ (CongruenceSubgroup.Gamma1 L)) →ₐ[ℂ] K)
    (hΨ : ∀ u, E (Ψ u) = qExpand ℂ N (u : LaurentSeries ℂ)) :
    IntermediateField.relfinrank ℂ⟮jK⟯ Ψ.fieldRange =
      (CongruenceSubgroup.Gamma1 L ⊔ Subgroup.zpowers (-1 : SL(2, ℤ))).index := by
  set y : laurentBaseChange ℂ (qExpFunctionFieldC ℚ (CongruenceSubgroup.Gamma1 L)) :=
    ⟨coeffEmb ℂ jq, coeffEmb_mem_laurentBaseChange ℂ (jq_mem _)⟩ with hy_def
  have hy : (y : LaurentSeries ℂ) = jqModC ℂ := coeffEmb_jq ℂ
  have hΨy : Ψ y = jK := apply_j_eq N E jK hEj (jq_mem _) Ψ hΨ
  have h1 : ℂ⟮jK⟯ = (ℂ⟮y⟯).map Ψ := by
    rw [IntermediateField.adjoin_map, Set.image_singleton, hΨy]
  rw [h1, AlgHom.fieldRange_eq_map, relfinrank_map_map', IntermediateField.relfinrank_eq_finrank_of_le le_top,
    IntermediateField.extendScalars_top, IntermediateField.finrank_top']
  exact finrank_adjoin_jqModC_laurentBaseChange_qExpFunctionFieldC_gamma1_eq_index ℂ L y hy

theorem adjoin_le_fieldRange (N : ℕ) [NeZero N] (E : K →ₐ[ℂ] LaurentSeries ℂ) (jK : K)
    (hEj : E jK = qExpand ℂ N (jqModC ℂ)) {F : IntermediateField ℚ (LaurentSeries ℚ)} (hj : jq ∈ F)
    (Ψ : laurentBaseChange ℂ F →ₐ[ℂ] K) (hΨ : ∀ u, E (Ψ u) = qExpand ℂ N (u : LaurentSeries ℂ)) :
    ℂ⟮jK⟯ ≤ Ψ.fieldRange := by
  rw [IntermediateField.adjoin_simple_le_iff, ← apply_j_eq N E jK hEj hj Ψ hΨ]
  exact ⟨_, rfl⟩

variable (σ : SL(2, ℤ) →* (K ≃ₐ[ℂ] K)) (jK : K)
  (hfixed : IntermediateField.fixedField σ.range = ℂ⟮jK⟯)

include hfixed in

theorem agree_on_fixedField (E E' : K →ₐ[ℂ] LaurentSeries ℂ) (hj : E jK = E' jK) :
    ∀ c ∈ IntermediateField.fixedField σ.range, E c = E' c := by
  intro c hc
  rw [hfixed] at hc
  obtain ⟨p, q, rfl⟩ := (IntermediateField.mem_adjoin_simple_iff ℂ c).mp hc
  have key : ∀ (φ : K →ₐ[ℂ] LaurentSeries ℂ) (r : ℂ[X]), φ (aeval jK r) = aeval (φ jK) r :=
    fun φ r => (Polynomial.aeval_algHom_apply φ jK r).symm
  rw [map_div₀, map_div₀, key E, key E, key E', key E', hj]

include hfixed in

theorem exists_align [σ.ker.FiniteIndex] [FiniteDimensional ℂ⟮jK⟯ K] [IsGalois ℂ⟮jK⟯ K]
    (hdeg : Module.finrank ℂ⟮jK⟯ K = σ.ker.index)
    (E E' : K →ₐ[ℂ] LaurentSeries ℂ) (hj : E jK = E' jK) :
    ∃ δ : SL(2, ℤ), ∀ x : K, E (σ δ x) = E' x := by
  classical
  haveI : Finite σ.range := Finite.of_equiv _ (QuotientGroup.quotientKerEquivRange σ).toEquiv
  obtain ⟨g, hg⟩ := CompQ.N3.exists_algHom_comp_eq σ.range E E' (agree_on_fixedField σ jK hfixed E E' hj)

  have hgfix : ∀ c ∈ ℂ⟮jK⟯, g c = c := by
    intro c hc
    apply E_inj E
    rw [hg]
    exact (agree_on_fixedField σ jK hfixed E E' hj c (hfixed ▸ hc)).symm

  let gF : K →ₐ[ℂ⟮jK⟯] K := { g.toRingHom with commutes' := fun c => hgfix c c.2 }
  have hgF : ∀ x, gF x = g x := fun _ => rfl
  haveI : Algebra.IsAlgebraic ℂ⟮jK⟯ K := Algebra.IsAlgebraic.of_finite _ _
  let gE : K ≃ₐ[ℂ⟮jK⟯] K := AlgEquiv.ofBijective gF (Algebra.IsAlgebraic.algHom_bijective gF)
  have hgE : ∀ x, gE x = g x := fun _ => rfl

  set rb := rebaseHom σ ℂ⟮jK⟯ hfixed with hrb
  have hrange : rb.range = ⊤ := by
    haveI : Finite (K ≃ₐ[ℂ⟮jK⟯] K) := inferInstance
    apply Subgroup.eq_top_of_card_eq
    have h1 := card_map_rebaseHom_mul_index σ ℂ⟮jK⟯ hfixed ⊤ le_top
    rw [Subgroup.index_top, mul_one, ← MonoidHom.range_eq_map, ← hdeg, ← IsGalois.card_aut_eq_finrank] at h1
    exact h1
  have hmem : gE ∈ rb.range := by rw [hrange]; exact Subgroup.mem_top _
  obtain ⟨δ, hδ⟩ := hmem
  refine ⟨δ, fun x => ?_⟩
  have : σ δ x = g x := by
    rw [← hgE, ← hδ]
    rfl
  rw [this, hg]

end Concrete

end CompQ

namespace CompQ

p2m_open "ModularCurve~coeffEmb_jq"

theorem Gamma_le_Gamma1 (N : ℕ) : CongruenceSubgroup.Gamma N ≤ CongruenceSubgroup.Gamma1 N := Gamma_le_gamma1 N

theorem T_mem_Gamma1 (N : ℕ) : ModularGroup.T ∈ CongruenceSubgroup.Gamma1 N := by
  simpa using T_zpow_mem_gamma1 N 1

scoped instance instIsDomainLevelNRing (N : ℕ) [NeZero N] : IsDomain (LevelN.ring N) := LevelN.isDomain_ring N

abbrev KN (N : ℕ) [NeZero N] : Type := FractionRing (LevelN.ring N)

theorem sigma_neg {K : Type*} [Field K] [Algebra ℂ K] (σ : SL(2, ℤ) →* (K ≃ₐ[ℂ] K))
    (h1 : (-1 : SL(2, ℤ)) ∈ σ.ker) (γ : SL(2, ℤ)) : σ (-γ) = σ γ := by
  have : -γ = -1 * γ := by rw [neg_one_mul]
  rw [this, map_mul, (MonoidHom.mem_ker).mp h1, one_mul]

theorem fix_sup {K : Type*} [Field K] [Algebra ℂ K] (σ : SL(2, ℤ) →* (K ≃ₐ[ℂ] K))
    (h1 : (-1 : SL(2, ℤ)) ∈ σ.ker) (Γ : Subgroup SL(2, ℤ)) (y : K) (hy : ∀ γ ∈ Γ, σ γ y = y) :
    ∀ γ ∈ Γ ⊔ Subgroup.zpowers (-1 : SL(2, ℤ)), σ γ y = y := by
  intro γ hγ
  rcases (mem_sup_zpowers_negOne_iff Γ γ).mp hγ with h | h
  · exact hy γ h
  · rw [← sigma_neg σ h1]
    exact hy _ h

theorem laurentBaseChange_sup_eq (M a b : ℕ) [NeZero M] [NeZero a] [NeZero b] (hM : 3 ≤ M) (hab : Nat.Coprime a b) :
    laurentBaseChange ℂ (qExpFunctionFieldC ℚ (CongruenceSubgroup.Gamma1 (M * a))) ⊔
        laurentBaseChange ℂ (qExpFunctionFieldC ℚ (CongruenceSubgroup.Gamma1 (M * b))) =
      laurentBaseChange ℂ (qExpFunctionFieldC ℚ (CongruenceSubgroup.Gamma1 (M * a * b))) := by
  classical
  set N := M * a * b with hN
  haveI : NeZero (M * a) := ⟨Nat.mul_ne_zero (NeZero.ne M) (NeZero.ne a)⟩
  haveI : NeZero (M * b) := ⟨Nat.mul_ne_zero (NeZero.ne M) (NeZero.ne b)⟩
  haveI : NeZero N := ⟨Nat.mul_ne_zero (Nat.mul_ne_zero (NeZero.ne M) (NeZero.ne a)) (NeZero.ne b)⟩
  have hdvd_a : M * a ∣ N := dvd_mul_right _ _
  have hdvd_b : M * b ∣ N := ⟨a, by rw [hN]; ring⟩

  obtain ⟨hst, σ, hσ, hker, hfixed, htr, hfin, hdeg, hgal⟩ :=
    LevelN.exists_monoidHom_algEquiv_fixedField_eq_adjoin N (KN N)
  set jK : KN N := algebraMap (LevelN.ring N) (KN N) (LevelN.jGen N) with hjK
  haveI := hfin
  haveI := hgal
  haveI hkerfi : σ.ker.FiniteIndex := by rw [hker]; exact Subgroup.finiteIndex_of_le le_sup_left
  have hneg1 : (-1 : SL(2, ℤ)) ∈ σ.ker := by rw [hker]; exact Subgroup.mem_sup_right (Subgroup.mem_zpowers _)
  haveI : Algebra.IsAlgebraic ℚ (AlgebraicClosure ℚ) := AlgebraicClosure.isAlgebraic ℚ
  let ι : AlgebraicClosure ℚ →+* ℂ := (IsAlgClosed.lift (R := ℚ) (S := AlgebraicClosure ℚ) (M := ℂ)).toRingHom

  obtain ⟨Φ, E, hEj, hEΦ, -, -, hΦfix⟩ :=
    exists_ringHom_laurentBaseChange_qExpFunctionFieldC_levelN_qExpansion N (CongruenceSubgroup.Gamma1 N)
      (Gamma_le_Gamma1 N) (T_mem_Gamma1 N) ι (KN N)
  have hΦfix' : ∀ γ ∈ CongruenceSubgroup.Gamma1 N, ∀ u, σ γ (Φ u) = Φ u := fun γ hγ u =>
    hΦfix γ hγ (fun G hG => hst γ⁻¹ G hG) (σ γ) (fun G hG => hσ γ G hG) u

  obtain ⟨Ψa, hΨa⟩ := LevelN.exists_algHom_laurentBaseChange_apply_eq_qExpand N (KN N) σ hker hfixed E hEj
    (CongruenceSubgroup.Gamma1 (M * a)) ((Gamma_le_Gamma1 N).trans (gamma1_le_gamma1_of_dvd hdvd_a)) (T_mem_Gamma1 _)
  obtain ⟨Ψb, hΨb⟩ := LevelN.exists_algHom_laurentBaseChange_apply_eq_qExpand N (KN N) σ hker hfixed E hEj
    (CongruenceSubgroup.Gamma1 (M * b)) ((Gamma_le_Gamma1 N).trans (gamma1_le_gamma1_of_dvd hdvd_b)) (T_mem_Gamma1 _)
  obtain ⟨Ψab, hΨab⟩ := LevelN.exists_algHom_laurentBaseChange_apply_eq_qExpand N (KN N) σ hker hfixed E hEj
    (CongruenceSubgroup.Gamma1 N) (Gamma_le_Gamma1 N) (T_mem_Gamma1 _)

  set Z : Subgroup SL(2, ℤ) := Subgroup.zpowers (-1 : SL(2, ℤ)) with hZ
  set Sa := CongruenceSubgroup.Gamma1 (M * a) ⊔ Z with hSa
  set Sb := CongruenceSubgroup.Gamma1 (M * b) ⊔ Z with hSb
  set Sab := CongruenceSubgroup.Gamma1 N ⊔ Z with hSab
  have hka : σ.ker ≤ Sa := by
    rw [hker]; exact sup_le_sup_right ((Gamma_le_Gamma1 N).trans (gamma1_le_gamma1_of_dvd hdvd_a)) _
  have hkb : σ.ker ≤ Sb := by
    rw [hker]; exact sup_le_sup_right ((Gamma_le_Gamma1 N).trans (gamma1_le_gamma1_of_dvd hdvd_b)) _
  have hSab' : Sa ⊓ Sb = Sab := gamma1_sup_inf_gamma1_sup_eq M a b hM hab
  have hdeg' : Module.finrank ℂ⟮jK⟯ (KN N) = σ.ker.index := by rw [hker]; exact hdeg

  have hK : Ψa.fieldRange ⊔ Ψb.fieldRange = Ψab.fieldRange := by
    refine sup_eq_of_galois σ ℂ⟮jK⟯ hfixed hdeg' Sa Sb Sab hka hkb hSab'
      (fun δ h => map_conj_gamma1_sup_eq_of_le hdvd_a δ h) (fun δ h => map_conj_gamma1_sup_eq_of_le hdvd_b δ h)
      Ψa.fieldRange Ψb.fieldRange Ψab.fieldRange
      (adjoin_le_fieldRange N E jK hEj (jq_mem _) Ψa hΨa)
      (adjoin_le_fieldRange N E jK hEj (jq_mem _) Ψb hΨb)
      (adjoin_le_fieldRange N E jK hEj (jq_mem _) Ψab hΨab)
      (fieldRange_le_fieldRange N E (qExpFunctionFieldC_mono ℚ (gamma1_le_gamma1_of_dvd hdvd_a)) Ψa hΨa Ψab hΨab)
      (fieldRange_le_fieldRange N E (qExpFunctionFieldC_mono ℚ (gamma1_le_gamma1_of_dvd hdvd_b)) Ψb hΨb Ψab hΨab)
      (relfinrank_adjoin_fieldRange (M * a) N E jK hEj Ψa hΨa)
      (relfinrank_adjoin_fieldRange (M * b) N E jK hEj Ψb hΨb)
      (relfinrank_adjoin_fieldRange N N E jK hEj Ψab hΨab) ?_ ?_ ?_
    ·
      apply fieldRange_le_fixedField N E σ Sab Ψab
      intro x hx
      have hgen : Ψab ⟨coeffEmb ℂ x, coeffEmb_mem_laurentBaseChange ℂ hx⟩ =
          Φ ⟨coeffEmb (AlgebraicClosure ℚ) x, coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) hx⟩ := by
        apply E_inj E
        rw [hΨab, hEΦ]
        show qExpand ℂ N (coeffEmb ℂ x) = qExpand ℂ N (coeffMap ι (coeffEmb (AlgebraicClosure ℚ) x))
        rw [coeffMap_coeffEmb]
      rw [hgen]
      exact fix_sup σ hneg1 _ _ (fun γ hγ => hΦfix' γ hγ _)
    ·
      obtain ⟨Φa, Ea, hEaj, hEaΦa, -, -, hΦafix⟩ :=
        exists_ringHom_laurentBaseChange_qExpFunctionFieldC_levelN_qExpansion N (CongruenceSubgroup.Gamma1 (M * a))
          ((Gamma_le_Gamma1 N).trans (gamma1_le_gamma1_of_dvd hdvd_a)) (T_mem_Gamma1 _) ι (KN N)
      have hΦafix' : ∀ γ ∈ CongruenceSubgroup.Gamma1 (M * a), ∀ u, σ γ (Φa u) = Φa u := fun γ hγ u =>
        hΦafix γ hγ (fun G hG => hst γ⁻¹ G hG) (σ γ) (fun G hG => hσ γ G hG) u
      obtain ⟨δ, hδ⟩ := exists_align σ jK hfixed hdeg' E Ea (by rw [hEj, hEaj])
      refine ⟨δ, ?_⟩
      have := fieldRange_le_fixedField N E (σ.comp (MulAut.conj δ).toMonoidHom) Sa Ψa (by
        intro x hx
        have hgen : Ψa ⟨coeffEmb ℂ x, coeffEmb_mem_laurentBaseChange ℂ hx⟩ =
            σ δ (Φa ⟨coeffEmb (AlgebraicClosure ℚ) x, coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) hx⟩) := by
          apply E_inj E
          rw [hΨa, hδ, hEaΦa]
          show qExpand ℂ N (coeffEmb ℂ x) = qExpand ℂ N (coeffMap ι (coeffEmb (AlgebraicClosure ℚ) x))
          rw [coeffMap_coeffEmb]
        rw [hgen]
        apply fix_sup (σ.comp (MulAut.conj δ).toMonoidHom)
        · show δ * -1 * δ⁻¹ ∈ σ.ker
          rw [mul_neg_one, neg_mul, mul_inv_cancel]; exact hneg1
        · intro γ hγ
          show σ (δ * γ * δ⁻¹) (σ δ (Φa _)) = σ δ (Φa _)
          rw [map_mul, map_mul, map_inv, AlgEquiv.mul_apply, AlgEquiv.mul_apply, AlgEquiv.aut_inv,
            AlgEquiv.symm_apply_apply,
            hΦafix' γ hγ])
      intro γ hγ w hw
      exact this γ hγ w hw
    ·
      obtain ⟨Φb, Eb, hEbj, hEbΦb, -, -, hΦbfix⟩ :=
        exists_ringHom_laurentBaseChange_qExpFunctionFieldC_levelN_qExpansion N (CongruenceSubgroup.Gamma1 (M * b))
          ((Gamma_le_Gamma1 N).trans (gamma1_le_gamma1_of_dvd hdvd_b)) (T_mem_Gamma1 _) ι (KN N)
      have hΦbfix' : ∀ γ ∈ CongruenceSubgroup.Gamma1 (M * b), ∀ u, σ γ (Φb u) = Φb u := fun γ hγ u =>
        hΦbfix γ hγ (fun G hG => hst γ⁻¹ G hG) (σ γ) (fun G hG => hσ γ G hG) u
      obtain ⟨δ, hδ⟩ := exists_align σ jK hfixed hdeg' E Eb (by rw [hEj, hEbj])
      refine ⟨δ, ?_⟩
      have := fieldRange_le_fixedField N E (σ.comp (MulAut.conj δ).toMonoidHom) Sb Ψb (by
        intro x hx
        have hgen : Ψb ⟨coeffEmb ℂ x, coeffEmb_mem_laurentBaseChange ℂ hx⟩ =
            σ δ (Φb ⟨coeffEmb (AlgebraicClosure ℚ) x, coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) hx⟩) := by
          apply E_inj E
          rw [hΨb, hδ, hEbΦb]
          show qExpand ℂ N (coeffEmb ℂ x) = qExpand ℂ N (coeffMap ι (coeffEmb (AlgebraicClosure ℚ) x))
          rw [coeffMap_coeffEmb]
        rw [hgen]
        apply fix_sup (σ.comp (MulAut.conj δ).toMonoidHom)
        · show δ * -1 * δ⁻¹ ∈ σ.ker
          rw [mul_neg_one, neg_mul, mul_inv_cancel]; exact hneg1
        · intro γ hγ
          show σ (δ * γ * δ⁻¹) (σ δ (Φb _)) = σ δ (Φb _)
          rw [map_mul, map_mul, map_inv, AlgEquiv.mul_apply, AlgEquiv.mul_apply, AlgEquiv.aut_inv,
            AlgEquiv.symm_apply_apply,
            hΦbfix' γ hγ])
      intro γ hγ w hw
      exact this γ hγ w hw

  set Q := CompQ.N3.qExpandAlgHom ℂ N with hQ
  have hmapE : ∀ {F : IntermediateField ℚ (LaurentSeries ℚ)} (Ψ : laurentBaseChange ℂ F →ₐ[ℂ] KN N)
      (hΨ : ∀ u, E (Ψ u) = qExpand ℂ N (u : LaurentSeries ℂ)),
      Ψ.fieldRange.map E = (laurentBaseChange ℂ F).map Q := by
    intro F Ψ hΨ
    have hcomp : E.comp Ψ = Q.comp (laurentBaseChange ℂ F).val := AlgHom.ext fun u => by
      show E (Ψ u) = Q ((laurentBaseChange ℂ F).val u)
      rw [hΨ, CompQ.N3.qExpandAlgHom_apply]
      rfl
    calc Ψ.fieldRange.map E = ((⊤ : IntermediateField ℂ _).map Ψ).map E := by rw [AlgHom.fieldRange_eq_map]
      _ = (⊤ : IntermediateField ℂ _).map (E.comp Ψ) := IntermediateField.map_map _ _ _
      _ = (E.comp Ψ).fieldRange := (AlgHom.fieldRange_eq_map _).symm
      _ = (Q.comp (laurentBaseChange ℂ F).val).fieldRange := by rw [hcomp]; try rfl
      _ = (laurentBaseChange ℂ F).map Q := IntermediateField.fieldRange_comp_val _ _
  have h2 := congrArg (IntermediateField.map E) hK
  rw [IntermediateField.map_sup, hmapE Ψa hΨa, hmapE Ψb hΨb, hmapE Ψab hΨab, ← IntermediateField.map_sup] at h2
  exact IntermediateField.map_injective Q h2

end CompQ
p2m_reactivate "P2MW.S_ModularCurve_x1FunctionField_mul_sup_x1FunctionField_mul_eq_of_coprime.CompQ"

namespace CompQ

p2m_open "ModularCurve~coeffEmb_jq"

theorem relfinrank_adjoin_jq (M : ℕ) [NeZero M] :
    IntermediateField.relfinrank (IntermediateField.adjoin ℚ ({jq} : Set (LaurentSeries ℚ)))
        (qExpFunctionFieldC ℚ (CongruenceSubgroup.Gamma1 M)) =
      (CongruenceSubgroup.Gamma1 M ⊔ Subgroup.zpowers (-1 : SL(2, ℤ))).index := by
  classical
  set K := AlgebraicClosure ℚ
  set F₀ := qExpFunctionFieldC ℚ (CongruenceSubgroup.Gamma1 M) with hF₀
  rw [← relfinrank_laurentBaseChange K F₀ jq (jq_mem (CongruenceSubgroup.Gamma1 M)) transcendental_jq]
  have hymem : coeffEmb K jq ∈ laurentBaseChange K F₀ := coeffEmb_mem_laurentBaseChange K (jq_mem _)
  set y : ↥(laurentBaseChange K F₀) := ⟨coeffEmb K jq, hymem⟩ with hy_def
  have hy : (y : LaurentSeries K) = jqModC K := coeffEmb_jq K
  have hA : IntermediateField.adjoin K ({coeffEmb K jq} : Set (LaurentSeries K)) =
      (IntermediateField.adjoin K ({y} : Set ↥(laurentBaseChange K F₀))).map (laurentBaseChange K F₀).val := by
    have h := IntermediateField.adjoin_map (F := K) ({y} : Set ↥(laurentBaseChange K F₀)) (laurentBaseChange K F₀).val
    rw [Set.image_singleton] at h
    exact h.symm
  have hcomap : (IntermediateField.adjoin K ({coeffEmb K jq} : Set (LaurentSeries K))).comap (laurentBaseChange K F₀).val =
      IntermediateField.adjoin K ({y} : Set ↥(laurentBaseChange K F₀)) := by
    rw [hA, IntermediateField.comap_map]
  have h1 := IntermediateField.finrank_comap (IntermediateField.adjoin K ({coeffEmb K jq} : Set (LaurentSeries K)))
    (laurentBaseChange K F₀).val
  rw [IntermediateField.fieldRange_val, hcomap] at h1
  rw [← h1]
  exact finrank_adjoin_jqModC_laurentBaseChange_qExpFunctionFieldC_gamma1_eq_index K M y hy

theorem laurentBaseChange_sup (Γ Γ' : Subgroup SL(2, ℤ)) :
    laurentBaseChange ℂ (qExpFunctionFieldC ℚ Γ ⊔ qExpFunctionFieldC ℚ Γ') =
      laurentBaseChange ℂ (qExpFunctionFieldC ℚ Γ) ⊔ laurentBaseChange ℂ (qExpFunctionFieldC ℚ Γ') := by
  show laurentBaseChange ℂ (IntermediateField.adjoin ℚ (intFormRatiosC ℚ Γ) ⊔ IntermediateField.adjoin ℚ (intFormRatiosC ℚ Γ')) =
    laurentBaseChange ℂ (IntermediateField.adjoin ℚ (intFormRatiosC ℚ Γ)) ⊔
      laurentBaseChange ℂ (IntermediateField.adjoin ℚ (intFormRatiosC ℚ Γ'))
  rw [← IntermediateField.adjoin_union, laurentBaseChange_adjoin, laurentBaseChange_adjoin, laurentBaseChange_adjoin,
    Set.image_union, IntermediateField.adjoin_union]

theorem eq_of_laurentBaseChange_eq (A : IntermediateField ℚ (LaurentSeries ℚ)) (L : ℕ) [NeZero L]
    (hjA : jq ∈ A) (hAB : A ≤ qExpFunctionFieldC ℚ (CongruenceSubgroup.Gamma1 L))
    (h : laurentBaseChange ℂ A = laurentBaseChange ℂ (qExpFunctionFieldC ℚ (CongruenceSubgroup.Gamma1 L))) :
    A = qExpFunctionFieldC ℚ (CongruenceSubgroup.Gamma1 L) := by
  set B := qExpFunctionFieldC ℚ (CongruenceSubgroup.Gamma1 L) with hB
  have hjB : jq ∈ B := jq_mem _
  have hA := relfinrank_laurentBaseChange ℂ A jq hjA transcendental_jq
  have hB' := relfinrank_laurentBaseChange ℂ B jq hjB transcendental_jq
  rw [h] at hA
  have heq : IntermediateField.relfinrank ℚ⟮jq⟯ A = IntermediateField.relfinrank ℚ⟮jq⟯ B := by rw [← hA, ← hB']
  have h01 : ℚ⟮jq⟯ ≤ A := IntermediateField.adjoin_simple_le_iff.mpr hjA
  have htower := IntermediateField.relfinrank_mul_relfinrank h01 hAB
  have hpos : 0 < IntermediateField.relfinrank ℚ⟮jq⟯ B := by
    rw [hB, relfinrank_adjoin_jq L]
    haveI : (CongruenceSubgroup.Gamma1 L ⊔ Subgroup.zpowers (-1 : SL(2, ℤ))).FiniteIndex :=
      Subgroup.finiteIndex_of_le (le_sup_left : CongruenceSubgroup.Gamma1 L ≤ _)
    exact Nat.pos_of_ne_zero Subgroup.FiniteIndex.index_ne_zero
  rw [heq] at htower
  have h1 : IntermediateField.relfinrank A B = 1 := by
    have : IntermediateField.relfinrank ℚ⟮jq⟯ B * IntermediateField.relfinrank A B =
        IntermediateField.relfinrank ℚ⟮jq⟯ B * 1 := by rw [mul_one]; exact htower
    exact Nat.eq_of_mul_eq_mul_left hpos this
  exact le_antisymm hAB (IntermediateField.relfinrank_eq_one_iff.mp h1)

end CompQ
p2m_reactivate "P2MW.S_ModularCurve_x1FunctionField_mul_sup_x1FunctionField_mul_eq_of_coprime.CompQ"

namespace CompQ
p2m_open "ModularCurve~coeffEmb_jq"

theorem main_q (M a b : ℕ) [NeZero M] [NeZero a] [NeZero b] (hM : 3 ≤ M) (hab : Nat.Coprime a b) :
    qExpFunctionFieldC ℚ (CongruenceSubgroup.Gamma1 (M * a)) ⊔ qExpFunctionFieldC ℚ (CongruenceSubgroup.Gamma1 (M * b)) =
      qExpFunctionFieldC ℚ (CongruenceSubgroup.Gamma1 (M * a * b)) := by
  haveI : NeZero (M * a * b) := ⟨Nat.mul_ne_zero (Nat.mul_ne_zero (NeZero.ne M) (NeZero.ne a)) (NeZero.ne b)⟩
  set Fa := qExpFunctionFieldC ℚ (CongruenceSubgroup.Gamma1 (M * a)) with hFa
  set Fb := qExpFunctionFieldC ℚ (CongruenceSubgroup.Gamma1 (M * b)) with hFb
  have hle_a : Fa ≤ Fa ⊔ Fb := le_sup_left
  have hjA : jq ∈ Fa ⊔ Fb := hle_a (jq_mem _)
  have hAB : Fa ⊔ Fb ≤ qExpFunctionFieldC ℚ (CongruenceSubgroup.Gamma1 (M * a * b)) :=
    sup_le (qExpFunctionFieldC_mono ℚ (gamma1_le_gamma1_of_dvd (dvd_mul_right _ _)))
      (qExpFunctionFieldC_mono ℚ (gamma1_le_gamma1_of_dvd ⟨a, by ring⟩))
  have hC : laurentBaseChange ℂ (Fa ⊔ Fb) = laurentBaseChange ℂ (qExpFunctionFieldC ℚ (CongruenceSubgroup.Gamma1 (M * a * b))) := by
    rw [hFa, hFb, laurentBaseChange_sup]
    exact laurentBaseChange_sup_eq M a b hM hab
  exact eq_of_laurentBaseChange_eq _ (M * a * b) hjA hAB hC

end CompQ
p2m_reactivate "P2MW.S_ModularCurve_x1FunctionField_mul_sup_x1FunctionField_mul_eq_of_coprime.CompQ"

theorem solution
    (M a b : ℕ) [NeZero M] [NeZero a] [NeZero b] (hM : 3 ≤ M) (hab : Nat.Coprime a b) :
    ModularCurve.x1FunctionField (M * a) ⊔ ModularCurve.x1FunctionField (M * b) =
      ModularCurve.x1FunctionField (M * a * b) :=
  CompQ.main_q M a b hM hab

end S_ModularCurve_x1FunctionField_mul_sup_x1FunctionField_mul_eq_of_coprime
end P2MW
export P2MW.S_ModularCurve_x1FunctionField_mul_sup_x1FunctionField_mul_eq_of_coprime (solution)
