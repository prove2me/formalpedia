-- Prove2me | solution 1 for ModularCurve.exists_isDiamondPullbackModL_bot_forall_coe_mem_gammaH_iff
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.007995+00:00
-- url     : https://prove2.me/submissions/a6ab3234-41a7-52b0-9827-f0b3879c28d7

import Mathlib
import Definitions.Def_ModularCurve_X1
import Definitions.Def_ModularCurve_JqCoeff
import Definitions.Def_CohCarrier_Level
import Definitions.Def_ModularCurve_XH
import Definitions.Def_ModularCurve_XHDiamondModL
import Definitions.Def_ModularCurve_X0ModL
import Theorems.Thm_ModularCurve_exists_isDiamondPullbackModL_bot_of_natCast_ne_zero
import Theorems.Thm_ModularCurve_finiteDimensional_and_finrank_adjoin_jqModC_qExpFunctionFieldC_le_index
import Theorems.Thm_ModularCurve_exists_gamma1_eisenstein_isIntegralQExp_and_slash_eq
import Theorems.Thm_ModularCurve_finrank_adjoin_jqModC_modularFunctionFieldFullC_eq_dedekindPsi
import Theorems.Thm_ModularCurve_Gamma0_index
import Theorems.Thm_ModularCurve_qExpand_image_intFormRatiosC_subset
import Theorems.Thm_ModularCurve_jqModC_mem_intFormRatiosC
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_exists_isDiamondPullbackModL_bot_forall_coe_mem_gammaH_iff
p2m_attr_erase "instance" "CohCarrier.HeckeData.V_isScalarTower CohCarrier.HeckeData.opSubalgebra_isMulCommutative CohCarrier.HeckeData.mTheta_isPrime ModularCurve.instIsDomainTensorProduct AlgebraicClosure.Rat.isGalois AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.instFundamentalIdentityOfSumRamificationInertia AlgebraicCurve.Place.instIsScalarTowerResidueFieldRestrictPushforward AlgebraicCurve.Place.instAlgebraResidueFieldRestrictPushforward AlgebraicCurve.Place.instIsLocalHomRestrictInclusion AlgebraicCurve.IsCurveOver.instNontrivialKaehler AlgebraicCurve.IsCurveOver.instFreeKaehler AlgebraicCurve.IsCurveOver.toHasPrincipalDivisors AlgebraicCurve.IsCurveOver.instFiniteResidue AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation ModularCurve.PhiGen.instNeZeroPhiGenCosetA ModularCurve.instFiniteProjectiveLine ModularCurve.unimodularRowSetoid"
p2m_attr_erase "simp" "ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL CohCarrier.Gen.dia.sizeOf_spec CohCarrier.Gen.U.injEq CohCarrier.Gen.T.sizeOf_spec CohCarrier.Gen.U.sizeOf_spec CohCarrier.Gen.T.injEq CohCarrier.Gen.dia.injEq CohCarrier.HeckeData.mk.sizeOf_spec CohCarrier.HeckeData.opAlgHom_X CohCarrier.HeckeData.toMLₒ_apply CohCarrier.HeckeData.mk.injEq CohCarrier.frickeH1L_apply CohCarrier.frickeMat_apply_10 CohCarrier.frickeEquiv_symm_apply CohCarrier.frickeMat_apply_01 CohCarrier.coe_frickeHom CohCarrier.frickeMat_apply_00 CohCarrier.frickeMat_apply_11 CohCarrier.frickeEquiv_apply CohCarrier.frickeH1_apply WeierstrassCurve.reducePoint_zero WeierstrassCurve.Affine.Point.galoisRep_apply ModularCurve.coe_baseChangeEquiv_apply ModularCurve.baseChangeHom_tmul ModularCurve.qInftyPlaceBar_toValuationSubring ModularCurve.qSeriesBar_zero ModularCurve.qSeriesBar_add ModularCurve.cuspInftyFull_toValuationSubring ModularCurve.qInftyPlaceRat_toValuationSubring ModularCurve.qSeriesBar_mul ModularCurve.qSeriesBar_div ModularCurve.qSeriesBar_eq_zero_iff"
p2m_attr_erase "simp" "ModularCurve.coe_uniformizerBar ModularCurve.qSeriesBar_pow ModularCurve.cuspInfty_toValuationSubring ModularCurve.qSeriesBar_one ModularCurve.qSeriesBar_inv ModularCurve.qSeriesBar_sub ModularCurve.qSeriesBar_neg ModularCurve.coe_cuspidalDivisor₀ AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal AlgebraicCurve.Divisor.mapRestrict_single AlgebraicCurve.Divisor.pushforward_single AlgebraicCurve.Place.coe_restrictInclusion AlgebraicCurve.Place.mem_fiber AlgebraicCurve.Place.restrict_toValuationSubring AlgebraicCurve.Divisor.degree_pushforward AlgebraicCurve.Place.restrictResidueMap_residue AlgebraicCurve.Pic0.coe_pushforwardDegZeroHom AlgebraicCurve.Pic0.coe_pullbackDegZeroHom AlgebraicCurve.IsFrobeniusEndo.frobNormRingHom_apply ModularCurve.frobeniusPushforwardGeomLevelPic0_mk ModularCurve.coe_frobeniusGeomLevelEquiv_apply ModularCurve.coe_frobeniusPushforwardGeomLevelDegZero ModularCurve.heckeFibreGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusGeomLevel_apply_coe ModularCurve.frobeniusPullbackGeomLevelPic0OfIsCurveOver_mk ModularCurve.coe_heckeFibreGeomLevelDegZero ModularCurve.coe_frobeniusPullbackGeomLevelDegZero ModularCurve.frobeniusPullbackGeomLevelPic0_mk ModularCurve.frobeniusPullbackGeomLevel_single ModularCurve.heckeFibreGeomLevelPic0_mk ModularCurve.frobeniusPushforwardGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusPushforwardGeomLevel_single ModularCurve.qExpandAlgC_apply AlgebraicCurve.Place.congrEquiv_symm_apply AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal AlgebraicCurve.Place.congrRingEquiv_toValuationSubring"
p2m_attr_erase "simp" "AlgebraicCurve.Place.congrEquiv_apply AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply AlgebraicCurve.RationalFunctionField.deg_placeOfPoint AlgebraicCurve.Divisor.degree_pushforwardAlong AlgebraicCurve.Pic0.coe_degZeroCorrespondence AlgebraicCurve.Place.mem_fiberAlong AlgebraicCurve.coe_frobeniusPushforwardDegZero AlgebraicCurve.IsFrobeniusEndo.coe_frobeniusPullbackDegZero ModularCurve.reduceModBivar_C_X ModularCurve.laurentMap_coeff ModularCurve.reduceModBivar_X ModularCurve.laurentMap_single ModularCurve.evalAtJInt_X ModularCurve.evalAtJMod_X ModularCurve.jqNMod_one ModularCurve.aeval_heckeGen ModularCurve.coe_mTorsionGaloisRep_apply ModularCurve.eisensteinSystem_of_dvd ModularCurve.eisensteinSystem_of_not_dvd ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ ModularCurve.eisensteinNumerator_nineteen ModularCurve.eisensteinNumerator_seventeen ModularCurve.eisensteinNumerator_eleven ModularCurve.eisensteinNumerator_five ModularCurve.eisensteinNumerator_seven ModularCurve.eisensteinNumerator_twentythree ModularCurve.eisensteinNumerator_thirteen ModularCurve.constantCoeff_dedekindEtaUnitQ ModularCurve.ProjectiveLine.map_mk"

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option synthInstance.maxHeartbeats 1600000
set_option maxHeartbeats 6400000

noncomputable section

p2m_open "UpperHalfPlane ModularForm CongruenceSubgroup Function HahnSeries ModularCurve~IsCusp IntermediateField CohCarrier"

open scoped MatrixGroups ModularForm Manifold

namespace P2MKcDiaGal

local notation "Γᴳ(" M ", " H ")" =>
  ((CohCarrier.GammaH M H : Subgroup SL(2, ℤ)) : Subgroup (GL (Fin 2) ℝ))

local notation "Γ₁ᴳ(" M ")" => ((Gamma1 M : Subgroup SL(2, ℤ)) : Subgroup (GL (Fin 2) ℝ))

section Prelim

variable (M : ℕ) (H : Subgroup (ZMod M)ˣ)

theorem T_mem_Gamma1 : ModularGroup.T ∈ Gamma1 M := by
  simp [Gamma1_mem, ModularGroup.T]

theorem one_mem_strictPeriods_one : (1 : ℝ) ∈ (Γ₁ᴳ(M)).strictPeriods := by
  rw [Subgroup.strictPeriods_eq_zmultiples_one_of_T_mem (T_mem_Gamma1 M)]
  exact AddSubgroup.mem_zmultiples 1

theorem one_mem_strictPeriods_H : (1 : ℝ) ∈ (Γᴳ(M, H)).strictPeriods := by
  rw [Subgroup.strictPeriods_eq_zmultiples_one_of_T_mem (translation_mem_GammaH M H)]
  exact AddSubgroup.mem_zmultiples 1

scoped instance finiteIndex_GammaH [NeZero M] : (CohCarrier.GammaH M H).FiniteIndex :=
  Subgroup.finiteIndex_of_le (Gamma1_le_GammaH M H)

theorem Gamma1_le_H : Γ₁ᴳ(M) ≤ Γᴳ(M, H) := Subgroup.map_mono (Gamma1_le_GammaH M H)

theorem bot_le_H : Γᴳ(M, ⊥) ≤ Γᴳ(M, H) := Subgroup.map_mono (GammaH_mono bot_le)

theorem le_Gamma0 : Γᴳ(M, H) ≤ ((Gamma0 M : Subgroup SL(2, ℤ)) : Subgroup (GL (Fin 2) ℝ)) :=
  Subgroup.map_mono (GammaH_le_Gamma0 H)

variable {M H}

theorem coe_finset_sum {Γ : Subgroup (GL (Fin 2) ℝ)} {k : ℤ} {ι : Type*} (s : Finset ι)
    (F : ι → ModularForm Γ k) : (⇑(∑ i ∈ s, F i) : ℍ → ℂ) = ∑ i ∈ s, (⇑(F i) : ℍ → ℂ) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, ModularForm.coe_add, ih]

theorem qExpansion_finset_sum {ι : Type*} (s : Finset ι) (F : ι → ModularForm Γ₁ᴳ(M) 4) :
    qExpansion 1 (⇑(∑ i ∈ s, F i)) = ∑ i ∈ s, qExpansion 1 (⇑(F i)) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [qExpansion_zero]
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha, ModularForm.coe_add,
      ModularForm.qExpansion_add one_pos (one_mem_strictPeriods_one M) (F a) (∑ i ∈ s, F i), ih]

theorem finset_sum_slash {k : ℤ} {ι : Type*} (s : Finset ι) (F : ι → ℍ → ℂ) (γ : SL(2, ℤ)) :
    (∑ i ∈ s, F i) ∣[k] γ = ∑ i ∈ s, (F i ∣[k] γ) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [SlashAction.zero_slash]
  | insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, SlashAction.add_slash, ih]

theorem isIntegralQExp_E4 : IsIntegralQExp (E₄ : ℍ → ℂ) eisenstein4 := by
  rw [isIntegralQExp_iff]
  intro n
  rw [EisensteinSeries.E_qExpansion_coeff (by norm_num) (by decide) n, eisenstein4, PowerSeries.coeff_mk]
  split_ifs with h
  · simp
  · rw [show _root_.bernoulli 4 = -1 / 30 by decide +kernel, ArithmeticFunction.sigma_apply]
    push_cast
    ring

variable (M H) in

def E4H : ModularForm Γᴳ(M, H) 4 := restrictForm (Subgroup.map_le_range _ _) E₄

theorem coe_E4H : (⇑(E4H M H) : ℍ → ℂ) = E₄ := rfl

theorem isIntegralQExp_E4H : IsIntegralQExp (⇑(E4H M H)) eisenstein4 := isIntegralQExp_E4

theorem E4H_slash (γ : SL(2, ℤ)) : (⇑(E4H M H) : ℍ → ℂ) ∣[(4 : ℤ)] γ = ⇑(E4H M H) := by
  rw [coe_E4H, ModularForm.SL_slash]
  exact SlashInvariantFormClass.slash_action_eq E₄ _ ⟨γ, rfl⟩

theorem intSeriesC_eisenstein4_ne_zero (K : Type*) [Field K] : intSeriesC K eisenstein4 ≠ 0 := by
  intro h
  have h1 : eisenstein4.map (Int.castRingHom K) = 0 :=
    HahnSeries.ofPowerSeries_injective (h.trans (map_zero _).symm)
  have := congrArg (PowerSeries.coeff 0) h1
  rw [PowerSeries.coeff_map, map_zero, eisenstein4, PowerSeries.coeff_mk, if_pos rfl, map_one] at this
  exact one_ne_zero this

theorem mem_sup_zpowers_neg_one_iff (u : (ZMod M)ˣ) :
    u ∈ H ⊔ Subgroup.zpowers (-1) ↔ u ∈ H ∨ -u ∈ H := by
  constructor
  · intro hu
    rw [Subgroup.mem_sup] at hu
    obtain ⟨y, hy, z, hz, rfl⟩ := hu
    rw [Subgroup.mem_zpowers_iff] at hz
    obtain ⟨n, rfl⟩ := hz
    rcases Int.even_or_odd n with hn | hn
    · left; rw [hn.neg_one_zpow, mul_one]; exact hy
    · right; rw [hn.neg_one_zpow, mul_neg_one, neg_neg]; exact hy
  · rintro (h | h)
    · exact Subgroup.mem_sup_left h
    · have : u = -u * -1 := by rw [mul_neg_one, neg_neg]
      rw [this]
      exact Subgroup.mul_mem _ (Subgroup.mem_sup_left h)
        (Subgroup.mem_sup_right (Subgroup.mem_zpowers _))

theorem neg_mem_Gamma0 {γ : SL(2, ℤ)} (h : γ ∈ Gamma0 M) : -γ ∈ Gamma0 M := by
  rw [Gamma0_mem] at h ⊢
  simp [h]

theorem gamma0Units_neg (γ : SL(2, ℤ)) (h : γ ∈ Gamma0 M) :
    gamma0Units M ⟨-γ, neg_mem_Gamma0 h⟩ = -gamma0Units M ⟨γ, h⟩ := by
  ext
  simp [Gamma0Map]

theorem mem_or_neg_mem_of_mem_GammaH_sup (γ : SL(2, ℤ))
    (hγ : γ ∈ GammaH M (H ⊔ Subgroup.zpowers (-1))) : γ ∈ GammaH M H ∨ -γ ∈ GammaH M H := by
  obtain ⟨hγ0, hγH⟩ := mem_GammaH_iff.mp hγ
  rcases (mem_sup_zpowers_neg_one_iff _).mp hγH with h | h
  · exact Or.inl (mem_GammaH_iff.mpr ⟨hγ0, h⟩)
  · refine Or.inr (mem_GammaH_iff.mpr ⟨neg_mem_Gamma0 hγ0, ?_⟩)
    rw [gamma0Units_neg]
    exact h

def sgn (k : ℤ) : ℤ := if Even k then 1 else -1

theorem sgn_ne_zero (K : Type*) [Field K] (k : ℤ) : (sgn k : K) ≠ 0 := by
  unfold sgn
  split_ifs
  · simp
  · rw [Int.cast_neg, Int.cast_one]; exact neg_ne_zero.mpr one_ne_zero

theorem slash_neg_one {k : ℤ} (F : ℍ → ℂ) : F ∣[k] (-1 : SL(2, ℤ)) = ((sgn k : ℤ) : ℂ) • F := by
  funext τ
  rw [Pi.smul_apply, smul_eq_mul, ModularForm.SL_slash_apply]
  have h1 : (-1 : SL(2, ℤ)) • τ = τ := by
    have : (-1 : SL(2, ℤ)) • τ = (1 : SL(2, ℤ)) • τ := by simp
    rw [this, one_smul]
  have h2 : denom (-1 : SL(2, ℤ)) τ = -1 := by
    simp [denom]
  rw [h1, h2]
  unfold sgn
  rcases Int.even_or_odd k with hk | hk
  · rw [if_pos hk, (Even.neg hk).neg_one_zpow, Int.cast_one, one_mul, mul_one]
  · rw [if_neg (Int.not_even_iff_odd.mpr hk), (Odd.neg hk).neg_one_zpow, Int.cast_neg, Int.cast_one]
    ring

theorem isIntegralQExp_intCast_smul {a : ℤ} {f : ModularForm Γᴳ(M, H) a} {p : PowerSeries ℤ}
    (hf : IsIntegralQExp f p) (c : ℤ) :
    IsIntegralQExp (⇑((c : ℝ) • f)) (PowerSeries.C c * p) := by
  have h1 : (⇑((c : ℝ) • f) : ℍ → ℂ) = (c : ℂ) • (⇑f : ℍ → ℂ) := by
    rw [ModularForm.coe_smul]
    funext τ
    simp only [Pi.smul_apply, Complex.real_smul, smul_eq_mul, Complex.ofReal_intCast]
  rw [IsIntegralQExp, h1, ModularForm.qExpansion_smul one_pos (one_mem_strictPeriods_H M H) (c : ℂ) f, ← hf,
    map_mul, PowerSeries.map_C, eq_intCast, PowerSeries.smul_eq_C_mul]

theorem coe_intCast_smul {a : ℤ} (c : ℤ) (f : ModularForm Γᴳ(M, H) a) :
    (⇑((c : ℝ) • f) : ℍ → ℂ) = (c : ℂ) • (⇑f : ℍ → ℂ) := by
  rw [ModularForm.coe_smul]
  funext τ
  simp only [Pi.smul_apply, Complex.real_smul, smul_eq_mul, Complex.ofReal_intCast]

theorem intSeriesC_C_mul (K : Type*) [Field K] (c : ℤ) (p : PowerSeries ℤ) :
    intSeriesC K (PowerSeries.C c * p) = HahnSeries.C (c : K) * intSeriesC K p := by
  rw [intSeriesC_mul, intSeriesC, PowerSeries.map_C, eq_intCast, HahnSeries.ofPowerSeries_C]

end Prelim

section Witness

variable (M : ℕ) [NeZero M]

def G4 : ZMod M → ModularForm Γ₁ᴳ(M) ((4 : ℕ) : ℤ) :=
  (exists_gamma1_eisenstein_isIntegralQExp_and_slash_eq M 4 (by norm_num)).choose

def a4 (c : ZMod M) : PowerSeries ℤ :=
  PowerSeries.mk fun n : ℕ =>
    (∑ m ∈ n.divisors with ((n / m : ℕ) : ZMod M) = c, (m : ℤ) ^ (4 - 1)) +
      (-1) ^ 4 * ∑ m ∈ n.divisors with ((n / m : ℕ) : ZMod M) = -c, (m : ℤ) ^ (4 - 1)

theorem G4_int (c : ZMod M) (hc : c ≠ 0) : IsIntegralQExp (⇑(G4 M c)) (a4 M c) :=
  (exists_gamma1_eisenstein_isIntegralQExp_and_slash_eq M 4 (by norm_num)).choose_spec.1 c hc

theorem G4_slash (c : ZMod M) (γ : SL(2, ℤ)) (hγ : γ ∈ Gamma0 M) :
    (⇑(G4 M c) : ℍ → ℂ) ∣[((4 : ℕ) : ℤ)] γ = ⇑(G4 M (c * ((γ 0 0 : ℤ) : ZMod M))) :=
  (exists_gamma1_eisenstein_isIntegralQExp_and_slash_eq M 4 (by norm_num)).choose_spec.2 c γ hγ

def FS (S : Finset (ZMod M)) : ModularForm Γ₁ᴳ(M) ((4 : ℕ) : ℤ) :=
  (2 : ℝ)⁻¹ • ∑ c ∈ S, G4 M c

def bS (S : Finset (ZMod M)) : PowerSeries ℤ :=
  PowerSeries.mk fun n : ℕ => ∑ m ∈ n.divisors with ((n / m : ℕ) : ZMod M) ∈ S, (m : ℤ) ^ 3

theorem coe_FS (S : Finset (ZMod M)) :
    (⇑(FS M S) : ℍ → ℂ) = (2 : ℂ)⁻¹ • ∑ c ∈ S, (⇑(G4 M c) : ℍ → ℂ) := by
  rw [FS, ModularForm.coe_smul, coe_finset_sum]
  funext τ
  simp only [Pi.smul_apply, Complex.real_smul, Complex.ofReal_inv, Complex.ofReal_ofNat, smul_eq_mul]

theorem FS_slash (S : Finset (ZMod M)) (γ : SL(2, ℤ)) (hγ : γ ∈ Gamma0 M) :
    (⇑(FS M S) : ℍ → ℂ) ∣[((4 : ℕ) : ℤ)] γ = ⇑(FS M (S.image (· * ((γ 0 0 : ℤ) : ZMod M)))) := by
  classical
  have hunit : IsUnit ((γ 0 0 : ℤ) : ZMod M) := by
    have h := Gamma0_d_mul_a M ⟨γ, hγ⟩
    exact IsUnit.of_mul_eq_one _ (by rw [mul_comm]; exact h)
  have hinj : Function.Injective (fun c : ZMod M => c * ((γ 0 0 : ℤ) : ZMod M)) :=
    fun c c' h => hunit.mul_left_injective h
  rw [coe_FS, coe_FS, ModularForm.SL_smul_slash, finset_sum_slash,
    Finset.sum_image (fun c _ c' _ h => hinj h)]
  congr 1
  exact Finset.sum_congr rfl fun c _ => G4_slash M c γ hγ

theorem sum_a4_eq (S : Finset (ZMod M)) (hsymm : ∀ c ∈ S, -c ∈ S) :
    ∑ c ∈ S, a4 M c = PowerSeries.C (2 : ℤ) * bS M S := by
  classical
  ext n
  rw [map_sum, PowerSeries.coeff_C_mul, bS, PowerSeries.coeff_mk]
  simp only [a4, PowerSeries.coeff_mk]
  rw [Finset.sum_add_distrib]
  have h1 : ∑ c ∈ S, ∑ m ∈ n.divisors with ((n / m : ℕ) : ZMod M) = c, (m : ℤ) ^ (4 - 1)
      = ∑ m ∈ n.divisors with ((n / m : ℕ) : ZMod M) ∈ S, (m : ℤ) ^ 3 :=
    Finset.sum_fiberwise_eq_sum_filter _ _ _ _
  have h2 : ∑ c ∈ S, (-1) ^ 4 * ∑ m ∈ n.divisors with ((n / m : ℕ) : ZMod M) = -c, (m : ℤ) ^ (4 - 1)
      = ∑ m ∈ n.divisors with ((n / m : ℕ) : ZMod M) ∈ S, (m : ℤ) ^ 3 := by
    have e : ∀ c ∈ S, (-1 : ℤ) ^ 4 * ∑ m ∈ n.divisors with ((n / m : ℕ) : ZMod M) = -c, (m : ℤ) ^ (4 - 1)
        = ∑ m ∈ n.divisors with -(((n / m : ℕ) : ZMod M)) = c, (m : ℤ) ^ 3 := by
      intro c _
      rw [show ((-1 : ℤ) ^ 4) = 1 by norm_num, one_mul]
      refine Finset.sum_congr ?_ fun _ _ => rfl
      ext m
      simp only [Finset.mem_filter, neg_eq_iff_eq_neg]
    rw [Finset.sum_congr rfl e, Finset.sum_fiberwise_eq_sum_filter]
    refine Finset.sum_congr ?_ fun _ _ => rfl
    ext m
    simp only [Finset.mem_filter, and_congr_right_iff]
    intro _
    constructor
    · intro h; simpa using hsymm _ h
    · intro h; exact hsymm _ h
  rw [h1, h2, two_mul]

theorem FS_int (S : Finset (ZMod M)) (h0 : ∀ c ∈ S, c ≠ 0) (hsymm : ∀ c ∈ S, -c ∈ S) :
    IsIntegralQExp (⇑(FS M S)) (bS M S) := by
  classical
  have hsum : qExpansion 1 (⇑(∑ c ∈ S, G4 M c)) = (PowerSeries.C (2 : ℤ) * bS M S).map (Int.castRingHom ℂ) := by
    rw [qExpansion_finset_sum, ← sum_a4_eq M S hsymm, map_sum]
    exact Finset.sum_congr rfl fun c hc => (G4_int M c (h0 c hc)).symm
  have hcoe : (⇑(FS M S) : ℍ → ℂ) = (2 : ℂ)⁻¹ • (⇑(∑ c ∈ S, G4 M c) : ℍ → ℂ) := by
    rw [coe_FS, coe_finset_sum]
  rw [IsIntegralQExp, hcoe, ModularForm.qExpansion_smul one_pos (one_mem_strictPeriods_one M) _
    (∑ c ∈ S, G4 M c), hsum, map_mul, PowerSeries.map_C, eq_intCast, PowerSeries.smul_eq_C_mul,
    ← mul_assoc, ← map_mul, Int.cast_ofNat, inv_mul_cancel₀ (two_ne_zero), map_one, one_mul]

theorem coeff_one_bS (S : Finset (ZMod M)) :
    PowerSeries.coeff 1 (bS M S) = if (1 : ZMod M) ∈ S then 1 else 0 := by
  classical
  rw [bS, PowerSeries.coeff_mk, Nat.divisors_one]
  rw [Finset.filter_singleton]
  simp only [Nat.div_self Nat.one_pos, Nat.cast_one]
  split_ifs <;> simp

end Witness

section Cosets

open Classical in

def cosetSet (M : ℕ) [NeZero M] (H : Subgroup (ZMod M)ˣ) (a : (ZMod M)ˣ) : Finset (ZMod M) :=
  Finset.univ.filter fun c : ZMod M => ∃ u : (ZMod M)ˣ, (u : ZMod M) = c ∧ u * a⁻¹ ∈ H ⊔ Subgroup.zpowers (-1)

variable {M : ℕ} [NeZero M] {H : Subgroup (ZMod M)ˣ}

abbrev Hpm (H : Subgroup (ZMod M)ˣ) : Subgroup (ZMod M)ˣ := H ⊔ Subgroup.zpowers (-1)

theorem neg_one_mem_Hpm : (-1 : (ZMod M)ˣ) ∈ Hpm H :=
  Subgroup.mem_sup_right (Subgroup.mem_zpowers _)

theorem le_Hpm : H ≤ Hpm H := le_sup_left

theorem mem_cosetSet {a : (ZMod M)ˣ} {c : ZMod M} :
    c ∈ cosetSet M H a ↔ ∃ u : (ZMod M)ˣ, (u : ZMod M) = c ∧ u * a⁻¹ ∈ Hpm H := by
  simp [cosetSet]

theorem coe_mem_cosetSet {a u : (ZMod M)ˣ} : (u : ZMod M) ∈ cosetSet M H a ↔ u * a⁻¹ ∈ Hpm H := by
  rw [mem_cosetSet]
  constructor
  · rintro ⟨u', hu', h⟩
    rw [Units.ext hu'] at h
    exact h
  · intro h; exact ⟨u, rfl, h⟩

theorem cosetSet_symm {a : (ZMod M)ˣ} {c : ZMod M} (hc : c ∈ cosetSet M H a) : -c ∈ cosetSet M H a := by
  rw [mem_cosetSet] at hc ⊢
  obtain ⟨u, rfl, hu⟩ := hc
  refine ⟨-u, by simp, ?_⟩
  have : -u * a⁻¹ = (u * a⁻¹) * (-1) := by simp [mul_comm]
  rw [this]
  exact mul_mem hu neg_one_mem_Hpm

theorem cosetSet_ne_zero (hM : Nontrivial (ZMod M)) {a : (ZMod M)ˣ} {c : ZMod M}
    (hc : c ∈ cosetSet M H a) : c ≠ 0 := by
  rw [mem_cosetSet] at hc
  obtain ⟨u, rfl, _⟩ := hc
  exact u.ne_zero

theorem one_mem_cosetSet_iff {a : (ZMod M)ˣ} : (1 : ZMod M) ∈ cosetSet M H a ↔ a ∈ Hpm H := by
  rw [← Units.val_one, coe_mem_cosetSet, one_mul]
  exact inv_mem_iff

theorem cosetSet_image_mul (a b : (ZMod M)ˣ) :
    (cosetSet M H a).image (· * (b : ZMod M)) = cosetSet M H (a * b) := by
  ext c
  simp only [Finset.mem_image, mem_cosetSet]
  constructor
  · rintro ⟨c', ⟨u, rfl, hu⟩, rfl⟩
    refine ⟨u * b, by simp, ?_⟩
    rwa [mul_inv_rev, ← mul_assoc, mul_assoc u, mul_inv_cancel, mul_one]
  · rintro ⟨u, rfl, hu⟩
    refine ⟨(u * b⁻¹ : (ZMod M)ˣ), ⟨u * b⁻¹, rfl, ?_⟩, by simp⟩
    rwa [mul_inv_rev, ← mul_assoc] at hu

theorem cosetSet_mul_of_mem (a : (ZMod M)ˣ) {h : (ZMod M)ˣ} (hh : h ∈ Hpm H) :
    cosetSet M H (a * h) = cosetSet M H a := by
  ext c
  simp only [mem_cosetSet]
  refine exists_congr fun u => and_congr_right fun _ => ?_
  have e : u * (a * h)⁻¹ = (u * a⁻¹) * h⁻¹ := by rw [mul_inv_rev, mul_comm h⁻¹, mul_assoc]
  rw [e]
  constructor
  · intro hmem
    have := mul_mem hmem hh
    rwa [inv_mul_cancel_right] at this
  · intro hmem
    exact mul_mem hmem (inv_mem hh)

def unitOf (γ : SL(2, ℤ)) (hγ : γ ∈ Gamma0 M) : (ZMod M)ˣ := (gamma0Units M ⟨γ, hγ⟩)⁻¹

theorem coe_unitOf (γ : SL(2, ℤ)) (hγ : γ ∈ Gamma0 M) : (unitOf γ hγ : ZMod M) = ((γ 0 0 : ℤ) : ZMod M) :=
  rfl

theorem unitOf_mem_of_mem_GammaH {γ : SL(2, ℤ)} (h : γ ∈ GammaH M H) :
    unitOf γ (GammaH_le_Gamma0 H h) ∈ Hpm H := by
  obtain ⟨hγ0, hγH⟩ := mem_GammaH_iff.mp h
  exact inv_mem (le_Hpm hγH)

theorem mem_GammaH_of_unitOf_mem {γ : SL(2, ℤ)} (hγ : γ ∈ Gamma0 M) (h : unitOf γ hγ ∈ Hpm H) :
    γ ∈ GammaH M (Hpm H) :=
  mem_GammaH_iff.mpr ⟨hγ, by simpa [unitOf] using inv_mem h⟩

def liftH (f : ModularForm Γ₁ᴳ(M) ((4 : ℕ) : ℤ))
    (hf : ∀ γ ∈ GammaH M H, (⇑f : ℍ → ℂ) ∣[((4 : ℕ) : ℤ)] γ = ⇑f) : ModularForm Γᴳ(M, H) ((4 : ℕ) : ℤ) where
  toFun := f
  slash_action_eq' A hA := by
    obtain ⟨γ, hγ, rfl⟩ := hA
    have := hf γ hγ
    rwa [ModularForm.SL_slash] at this
  holo' := f.holo'
  bdd_at_cusps' {c} hc := by
    have hc' : IsCusp c Γ₁ᴳ(M) := by
      rw [Subgroup.IsArithmetic.isCusp_iff_isCusp_SL2Z] at hc ⊢
      exact hc
    exact f.bdd_at_cusps' hc'

@[scoped simp] theorem coe_liftH (f : ModularForm Γ₁ᴳ(M) ((4 : ℕ) : ℤ))
    (hf : ∀ γ ∈ GammaH M H, (⇑f : ℍ → ℂ) ∣[((4 : ℕ) : ℤ)] γ = ⇑f) : (⇑(liftH f hf) : ℍ → ℂ) = f := rfl

theorem FS_cosetSet_invariant (a : (ZMod M)ˣ) (γ : SL(2, ℤ)) (hγ : γ ∈ GammaH M H) :
    (⇑(FS M (cosetSet M H a)) : ℍ → ℂ) ∣[((4 : ℕ) : ℤ)] γ = ⇑(FS M (cosetSet M H a)) := by
  have hγ0 : γ ∈ Gamma0 M := GammaH_le_Gamma0 H hγ
  rw [FS_slash M _ γ hγ0, ← coe_unitOf γ hγ0, cosetSet_image_mul,
    cosetSet_mul_of_mem a (unitOf_mem_of_mem_GammaH hγ)]

variable (M H) in

def W (a : (ZMod M)ˣ) : ModularForm Γᴳ(M, H) ((4 : ℕ) : ℤ) :=
  liftH (FS M (cosetSet M H a)) (FS_cosetSet_invariant a)

theorem coe_W (a : (ZMod M)ˣ) : (⇑(W M H a) : ℍ → ℂ) = ⇑(FS M (cosetSet M H a)) := rfl

theorem W_slash (a : (ZMod M)ˣ) (γ : SL(2, ℤ)) (hγ : γ ∈ Gamma0 M) :
    (⇑(W M H a) : ℍ → ℂ) ∣[((4 : ℕ) : ℤ)] γ = ⇑(W M H (a * unitOf γ hγ)) := by
  rw [coe_W, coe_W, FS_slash M _ γ hγ, ← coe_unitOf γ hγ, cosetSet_image_mul]

theorem W_int (hM : Nontrivial (ZMod M)) (a : (ZMod M)ˣ) :
    IsIntegralQExp (⇑(W M H a)) (bS M (cosetSet M H a)) := by
  rw [coe_W]
  exact FS_int M _ (fun c hc => cosetSet_ne_zero hM hc) (fun c hc => cosetSet_symm hc)

variable (M H) in

def Wb (a : (ZMod M)ˣ) : ModularForm Γᴳ(M, ⊥) ((4 : ℕ) : ℤ) := restrictForm (bot_le_H M H) (W M H a)

theorem coe_Wb (a : (ZMod M)ˣ) : (⇑(Wb M H a) : ℍ → ℂ) = ⇑(W M H a) := rfl

end Cosets

section Fields

variable (K : Type*) [Field K] (M : ℕ)

abbrev Fb : IntermediateField K (LaurentSeries K) := qExpFunctionFieldC K (GammaH M ⊥)

scoped instance instFieldFb : Field (Fb K M) := inferInstance
scoped instance instAlgebraFb : Algebra K (Fb K M) := inferInstance

theorem Fb_eq : Fb K M = qExpFunctionFieldC K (GammaH M ⊥) := rfl

abbrev FH (H : Subgroup (ZMod M)ˣ) : IntermediateField K (LaurentSeries K) := qExpFunctionFieldC K (GammaH M H)

variable {K M}

theorem FH_le (H : Subgroup (ZMod M)ˣ) : FH K M H ≤ Fb K M := qExpFunctionFieldC_mono K (GammaH_mono bot_le)

def fixedIF (e : Fb K M ≃ₐ[K] Fb K M) : IntermediateField K (Fb K M) where
  carrier := {y | e y = y}
  mul_mem' {a b} ha hb := by
    simp only [Set.mem_setOf_eq, map_mul] at *; rw [ha, hb]
  one_mem' := map_one e
  add_mem' {a b} ha hb := by
    simp only [Set.mem_setOf_eq, map_add] at *; rw [ha, hb]
  zero_mem' := map_zero e
  algebraMap_mem' c := e.commutes c
  inv_mem' x hx := by
    simp only [Set.mem_setOf_eq, map_inv₀] at *; rw [hx]

theorem apply_eq_self_of_coe_mem_adjoin (e : Fb K M ≃ₐ[K] Fb K M) (S : Set (LaurentSeries K))
    (hSF : S ⊆ (Fb K M : Set (LaurentSeries K)))
    (hS : ∀ s (hs : s ∈ S), e ⟨s, hSF hs⟩ = ⟨s, hSF hs⟩) (y : Fb K M)
    (hy : (y : LaurentSeries K) ∈ IntermediateField.adjoin K S) : e y = y := by
  have hle : IntermediateField.adjoin K S ≤ IntermediateField.lift (fixedIF e) := by
    rw [adjoin_le_iff]
    intro s hs
    exact (mem_lift (⟨s, hSF hs⟩ : Fb K M)).mpr (hS s hs)
  exact (mem_lift y).mp (hle hy)

variable [NeZero M]

theorem intFormRatiosC_subset_Fb (H : Subgroup (ZMod M)ˣ) :
    intFormRatiosC K (GammaH M H) ⊆ (Fb K M : Set (LaurentSeries K)) :=
  fun s hs => FH_le H (intFormRatiosC_subset K _ hs)

theorem apply_eq_self_of_coe_mem_FH (ρ : Gamma0 M →* (Fb K M ≃ₐ[K] Fb K M))
    (hρ : IsDiamondPullbackModL K M ⊥ ρ) {H : Subgroup (ZMod M)ˣ} (γ : Gamma0 M)
    (hγ : (γ : SL(2, ℤ)) ∈ GammaH M H) (y : Fb K M) (hy : (y : LaurentSeries K) ∈ FH K M H) :
    ρ γ y = y := by
  refine apply_eq_self_of_coe_mem_adjoin (ρ γ) (intFormRatiosC K (GammaH M H))
    (intFormRatiosC_subset_Fb H) (fun s hs => ?_) y hy
  obtain ⟨k, f, g, pf, pg, hf, hg, hg0, rfl⟩ := hs
  set f' : ModularForm Γᴳ(M, ⊥) k := restrictForm (bot_le_H M H) f
  set g' : ModularForm Γᴳ(M, ⊥) k := restrictForm (bot_le_H M H) g
  have ef : (⇑f' : ℍ → ℂ) = (⇑f' : ℍ → ℂ) ∣[k] (γ : SL(2, ℤ)) := by
    rw [ModularForm.SL_slash]
    exact (SlashInvariantFormClass.slash_action_eq f _ (Subgroup.mem_map_of_mem _ hγ)).symm
  have eg : (⇑g' : ℍ → ℂ) = (⇑g' : ℍ → ℂ) ∣[k] (γ : SL(2, ℤ)) := by
    rw [ModularForm.SL_slash]
    exact (SlashInvariantFormClass.slash_action_eq g _ (Subgroup.mem_map_of_mem _ hγ)).symm
  exact Subtype.ext (hρ γ k f' g' f' g' pf pg pf pg hf hg hf hg ef eg hg0 ⟨_, _⟩ rfl)

theorem rho_eq_one_of_mem_bot (ρ : Gamma0 M →* (Fb K M ≃ₐ[K] Fb K M))
    (hρ : IsDiamondPullbackModL K M ⊥ ρ) (γ : Gamma0 M) (hγ : (γ : SL(2, ℤ)) ∈ GammaH M ⊥) :
    ρ γ = 1 :=
  AlgEquiv.ext fun y => apply_eq_self_of_coe_mem_FH ρ hρ γ hγ y y.2

def negOne : Gamma0 M := ⟨-1, neg_mem_Gamma0 (one_mem _)⟩

theorem rho_negOne (ρ : Gamma0 M →* (Fb K M ≃ₐ[K] Fb K M)) (hρ : IsDiamondPullbackModL K M ⊥ ρ) :
    ρ negOne = 1 := by
  refine AlgEquiv.ext fun y => ?_
  refine apply_eq_self_of_coe_mem_adjoin (ρ negOne) (intFormRatiosC K (GammaH M ⊥))
    (intFormRatiosC_subset_Fb ⊥) (fun s hs => ?_) y y.2
  obtain ⟨k, f, g, pf, pg, hf, hg, hg0, rfl⟩ := hs
  set f₁ : ModularForm Γᴳ(M, ⊥) k := (sgn k : ℝ) • f
  set g₁ : ModularForm Γᴳ(M, ⊥) k := (sgn k : ℝ) • g
  have hf₁ : IsIntegralQExp (⇑f₁) (PowerSeries.C (sgn k) * pf) := isIntegralQExp_intCast_smul hf _
  have hg₁ : IsIntegralQExp (⇑g₁) (PowerSeries.C (sgn k) * pg) := isIntegralQExp_intCast_smul hg _
  have ef : (⇑f₁ : ℍ → ℂ) = (⇑f : ℍ → ℂ) ∣[k] ((negOne : Gamma0 M) : SL(2, ℤ)) := by
    show (⇑f₁ : ℍ → ℂ) = (⇑f : ℍ → ℂ) ∣[k] (-1 : SL(2, ℤ))
    rw [slash_neg_one, coe_intCast_smul]
  have eg : (⇑g₁ : ℍ → ℂ) = (⇑g : ℍ → ℂ) ∣[k] ((negOne : Gamma0 M) : SL(2, ℤ)) := by
    show (⇑g₁ : ℍ → ℂ) = (⇑g : ℍ → ℂ) ∣[k] (-1 : SL(2, ℤ))
    rw [slash_neg_one, coe_intCast_smul]
  have hx : intSeriesC K pf / intSeriesC K pg =
      intSeriesC K (PowerSeries.C (sgn k) * pf) / intSeriesC K (PowerSeries.C (sgn k) * pg) := by
    rw [intSeriesC_C_mul, intSeriesC_C_mul, mul_div_mul_left _ _ (HahnSeries.C_ne_zero (sgn_ne_zero K k))]
  exact Subtype.ext (hρ negOne k f g f₁ g₁ pf pg _ _ hf hg hf₁ hg₁ ef eg hg0 ⟨_, _⟩ hx)

theorem rho_neg (ρ : Gamma0 M →* (Fb K M ≃ₐ[K] Fb K M)) (hρ : IsDiamondPullbackModL K M ⊥ ρ)
    (γ : Gamma0 M) : ρ ⟨-(γ : SL(2, ℤ)), neg_mem_Gamma0 γ.2⟩ = ρ γ := by
  have : (⟨-(γ : SL(2, ℤ)), neg_mem_Gamma0 γ.2⟩ : Gamma0 M) = negOne * γ := Subtype.ext (by simp [negOne])
  rw [this, map_mul, rho_negOne ρ hρ, one_mul]

theorem rho_eq_one_of_mem_sup (ρ : Gamma0 M →* (Fb K M ≃ₐ[K] Fb K M))
    (hρ : IsDiamondPullbackModL K M ⊥ ρ) (γ : Gamma0 M)
    (hγ : (γ : SL(2, ℤ)) ∈ GammaH M (Hpm ⊥)) : ρ γ = 1 := by
  rcases mem_or_neg_mem_of_mem_GammaH_sup _ hγ with h | h
  · exact rho_eq_one_of_mem_bot ρ hρ γ h
  · rw [← rho_neg ρ hρ γ]
    exact rho_eq_one_of_mem_bot ρ hρ _ h

theorem apply_eq_self_of_mem_sup (ρ : Gamma0 M →* (Fb K M ≃ₐ[K] Fb K M))
    (hρ : IsDiamondPullbackModL K M ⊥ ρ) {H : Subgroup (ZMod M)ˣ} (y : Fb K M)
    (hy : ∀ γ : Gamma0 M, (γ : SL(2, ℤ)) ∈ GammaH M H → ρ γ y = y)
    (γ : Gamma0 M) (hγ : (γ : SL(2, ℤ)) ∈ GammaH M (Hpm H)) : ρ γ y = y := by
  rcases mem_or_neg_mem_of_mem_GammaH_sup _ hγ with h | h
  · exact hy γ h
  · rw [← rho_neg ρ hρ γ]
    exact hy _ h

end Fields

section Separation

variable {K : Type*} [Field K] {M : ℕ} [NeZero M] {H : Subgroup (ZMod M)ˣ}

theorem mem_GammaH_sup_of_forall_apply_eq (ρ : Gamma0 M →* (Fb K M ≃ₐ[K] Fb K M))
    (hρ : IsDiamondPullbackModL K M ⊥ ρ) (γ : Gamma0 M)
    (hfix : ∀ y : Fb K M, (y : LaurentSeries K) ∈ FH K M H → ρ γ y = y) :
    (γ : SL(2, ℤ)) ∈ GammaH M (Hpm H) := by
  classical

  by_cases htop : Hpm H = ⊤
  · exact mem_GammaH_of_unitOf_mem γ.2 (by rw [htop]; exact Subgroup.mem_top _)

  have hM : Nontrivial (ZMod M) := by
    by_contra hnt
    apply htop
    haveI : Subsingleton (ZMod M) := not_nontrivial_iff_subsingleton.mp hnt
    haveI : Subsingleton (ZMod M)ˣ := ⟨fun x y => Units.ext (Subsingleton.elim _ _)⟩
    exact eq_top_iff.mpr fun x _ => by rw [Subsingleton.elim x 1]; exact one_mem _
  by_contra hnot
  have hd : unitOf (γ : SL(2, ℤ)) γ.2 ∉ Hpm H := fun h => hnot (mem_GammaH_of_unitOf_mem γ.2 h)

  set a : (ZMod M)ˣ := unitOf (γ : SL(2, ℤ)) γ.2 with ha
  have hf : IsIntegralQExp (⇑(Wb M H 1)) (bS M (cosetSet M H 1)) := W_int hM 1
  have hf₁ : IsIntegralQExp (⇑(Wb M H (1 * a))) (bS M (cosetSet M H (1 * a))) := W_int hM (1 * a)
  have ef : (⇑(Wb M H (1 * a)) : ℍ → ℂ) = (⇑(Wb M H 1) : ℍ → ℂ) ∣[((4 : ℕ) : ℤ)] (γ : SL(2, ℤ)) :=
    (W_slash 1 (γ : SL(2, ℤ)) γ.2).symm
  have eg : (⇑(E4H M ⊥) : ℍ → ℂ) = (⇑(E4H M ⊥) : ℍ → ℂ) ∣[((4 : ℕ) : ℤ)] (γ : SL(2, ℤ)) :=
    (E4H_slash (γ : SL(2, ℤ))).symm
  have hg0 : intSeriesC K eisenstein4 ≠ 0 := intSeriesC_eisenstein4_ne_zero _

  have hxH : intSeriesC K (bS M (cosetSet M H (1 * a))) / intSeriesC K eisenstein4 ∈ FH K M H :=
    div_mem_qExpFunctionFieldC (W M H (1 * a)) (E4H M H) hf₁ isIntegralQExp_E4H hg0
  have hxmem : intSeriesC K (bS M (cosetSet M H (1 * a))) / intSeriesC K eisenstein4 ∈ Fb K M :=
    FH_le H hxH
  have key := hρ γ ((4 : ℕ) : ℤ) (Wb M H 1) (E4H M ⊥) (Wb M H (1 * a)) (E4H M ⊥)
    (bS M (cosetSet M H 1)) eisenstein4 (bS M (cosetSet M H (1 * a))) eisenstein4
    hf isIntegralQExp_E4H hf₁ isIntegralQExp_E4H ef eg hg0 ⟨_, hxmem⟩ rfl
  have e2 := congrArg (fun z : Fb K M => (z : LaurentSeries K)) (hfix ⟨_, hxmem⟩ hxH)
  replace key := e2.symm.trans key
  change intSeriesC K (bS M (cosetSet M H (1 * a))) / intSeriesC K eisenstein4 =
    intSeriesC K (bS M (cosetSet M H 1)) / intSeriesC K eisenstein4 at key
  rw [div_left_inj' hg0] at key

  have hcoeff := congrArg (fun z : LaurentSeries K => z.coeff 1) key
  simp only [intSeriesC] at hcoeff
  rw [show (1 : ℤ) = ((1 : ℕ) : ℤ) from rfl, HahnSeries.ofPowerSeries_apply_coeff,
    HahnSeries.ofPowerSeries_apply_coeff, PowerSeries.coeff_map, PowerSeries.coeff_map,
    coeff_one_bS, coeff_one_bS, one_mul, if_neg (mt one_mem_cosetSet_iff.mp hd),
    if_pos (one_mem_cosetSet_iff.mpr (one_mem _))] at hcoeff
  simp at hcoeff

theorem mem_GammaH_sup_bot_of_eq_one (ρ : Gamma0 M →* (Fb K M ≃ₐ[K] Fb K M))
    (hρ : IsDiamondPullbackModL K M ⊥ ρ) (γ : Gamma0 M) (hγ : ρ γ = 1) :
    (γ : SL(2, ℤ)) ∈ GammaH M (Hpm ⊥) :=
  mem_GammaH_sup_of_forall_apply_eq ρ hρ γ (fun y _ => by rw [hγ]; rfl)

end Separation

section Invariants

section Transport

variable {K L : Type*} [Field K] [Field L] [Algebra K L]

theorem adjoin_simple_eq_comap (E : IntermediateField K L) (x : E) :
    IntermediateField.adjoin K ({x} : Set E) =
      (IntermediateField.adjoin K ({(x : L)} : Set L)).comap (IntermediateField.val E) := by
  apply IntermediateField.lift_injective
  erw [IntermediateField.lift_adjoin_simple]
  change _ = ((IntermediateField.adjoin K ({(x : L)} : Set L)).comap E.val).map E.val
  rw [IntermediateField.map_comap_eq, IntermediateField.fieldRange_val, inf_eq_left.mpr]
  exact IntermediateField.adjoin_le_iff.mpr (Set.singleton_subset_iff.mpr x.2)

theorem finrank_adjoin_simple_eq_relfinrank (E : IntermediateField K L) (x : E) :
    Module.finrank (IntermediateField.adjoin K ({x} : Set E)) E =
      IntermediateField.relfinrank (IntermediateField.adjoin K ({(x : L)} : Set L)) E := by
  rw [adjoin_simple_eq_comap, IntermediateField.finrank_comap, IntermediateField.fieldRange_val]

theorem finrank_eq_relfinrank_lift (E : IntermediateField K L) (A' : IntermediateField K E) :
    Module.finrank A' E = IntermediateField.relfinrank (IntermediateField.lift A') E := by
  have h : (IntermediateField.lift A').comap (IntermediateField.val E) = A' :=
    IntermediateField.comap_map _ _
  conv_lhs => rw [← h]
  rw [IntermediateField.finrank_comap, IntermediateField.fieldRange_val]

end Transport

variable {K : Type*} [Field K] {M : ℕ} [NeZero M]

theorem qExpand_jqModC_mem (d : ℕ) [NeZero d] (hd : d ∣ M) :
    qExpand K d (jqModC K) ∈ intFormRatiosC K (Gamma0 M) := by
  have hsub := qExpand_image_intFormRatiosC_subset K (Γ := ⊤) (Γ' := Gamma0 M)
    (Subgroup.mem_top _) d (by
      intro γ hγ
      have hc : (M : ℤ) ∣ γ 1 0 := by
        rw [Gamma0_mem] at hγ
        exact (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp hγ
      obtain ⟨c, hc⟩ := (Int.natCast_dvd_natCast.mpr hd |>.trans hc : (d : ℤ) ∣ γ 1 0)
      refine ⟨⟨!![γ 0 0, (d : ℤ) * γ 0 1; c, γ 1 1], ?_⟩, Subgroup.mem_top _, ?_, ?_, ?_, ?_⟩
      · rw [Matrix.det_fin_two_of]
        have := γ.det_coe
        rw [Matrix.det_fin_two, hc] at this
        linear_combination this
      all_goals simp [hc])
  exact hsub ⟨jqModC K, jqModC_mem_intFormRatiosC K ⊤, rfl⟩

theorem full_le_F0 : modularFunctionFieldFullC K M ≤ qExpFunctionFieldC K (Gamma0 M) := by
  rw [modularFunctionFieldFullC, adjoin_le_iff]
  rintro y ⟨d, hne, hd, rfl⟩
  haveI := hne
  exact intFormRatiosC_subset K _ (qExpand_jqModC_mem d hd)

theorem F0_le_FH (H : Subgroup (ZMod M)ˣ) : qExpFunctionFieldC K (Gamma0 M) ≤ FH K M H :=
  qExpFunctionFieldC_mono K (GammaH_le_Gamma0 H)

theorem full_le_FH (H : Subgroup (ZMod M)ˣ) : modularFunctionFieldFullC K M ≤ FH K M H :=
  full_le_F0.trans (F0_le_FH H)

theorem apply_eq_self_of_coe_mem_F0 (ρ : Gamma0 M →* (Fb K M ≃ₐ[K] Fb K M))
    (hρ : IsDiamondPullbackModL K M ⊥ ρ) (γ : Gamma0 M) (y : Fb K M)
    (hy : (y : LaurentSeries K) ∈ qExpFunctionFieldC K (Gamma0 M)) : ρ γ y = y := by
  have hy' : (y : LaurentSeries K) ∈ FH K M ⊤ := by
    have e : FH K M ⊤ = qExpFunctionFieldC K (Gamma0 M) := by rw [FH, GammaH_top]
    rw [e]; exact hy
  have hγ : (γ : SL(2, ℤ)) ∈ GammaH M ⊤ := by rw [GammaH_top]; exact γ.2
  exact apply_eq_self_of_coe_mem_FH ρ hρ γ hγ y hy'

theorem mem_or_neg_mem_bot (γ : SL(2, ℤ)) (hγ : γ ∈ GammaH M (Hpm (⊥ : Subgroup (ZMod M)ˣ))) :
    γ ∈ GammaH M ⊥ ∨ -γ ∈ GammaH M ⊥ :=
  mem_or_neg_mem_of_mem_GammaH_sup γ hγ

theorem lift_fixedField_range_eq_full (hM : (M : K) ≠ 0) (ρ : Gamma0 M →* (Fb K M ≃ₐ[K] Fb K M))
    (hρ : IsDiamondPullbackModL K M ⊥ ρ) :
    IntermediateField.lift (IntermediateField.fixedField ρ.range) = modularFunctionFieldFullC K M := by
  classical

  set Hp : Subgroup (ZMod M)ˣ := Hpm ⊥ with hHp
  set K' : Subgroup (Gamma0 M) := (GammaH M Hp).subgroupOf (Gamma0 M) with hK'
  haveI : (GammaH M Hp).FiniteIndex := finiteIndex_GammaH M Hp
  haveI hK'fi : K'.FiniteIndex := inferInstance
  have hK'le : K' ≤ ρ.ker := fun γ hγ => by
    rw [MonoidHom.mem_ker]
    exact rho_eq_one_of_mem_sup ρ hρ γ (Subgroup.mem_subgroupOf.mp hγ)
  have hkerle : ρ.ker ≤ K' := fun γ hγ =>
    Subgroup.mem_subgroupOf.mpr (mem_GammaH_sup_bot_of_eq_one ρ hρ γ ((MonoidHom.mem_ker).mp hγ))
  have hker : ρ.ker = K' := le_antisymm hkerle hK'le
  haveI : ρ.ker.FiniteIndex := Subgroup.finiteIndex_of_le hK'le
  set G : Subgroup (Fb K M ≃ₐ[K] Fb K M) := ρ.range with hG
  have hcardG : Nat.card G = K'.index := by rw [← hker]; exact (Subgroup.index_ker ρ).symm
  haveI : Finite G := Nat.finite_of_card_ne_zero (by rw [hcardG]; exact Subgroup.FiniteIndex.index_ne_zero)
  haveI : Fintype G := Fintype.ofFinite G
  have hK'pos : 0 < K'.index := Nat.pos_of_ne_zero Subgroup.FiniteIndex.index_ne_zero
  have hK'index : K'.index * (Gamma0 M).index = (GammaH M Hp).index :=
    Subgroup.relIndex_mul_index (GammaH_le_Gamma0 Hp)

  have hArtin : Module.finrank (IntermediateField.fixedField G) (Fb K M) = Nat.card G := by
    rw [Nat.card_eq_fintype_card]
    exact FixedPoints.finrank_eq_card G (Fb K M)

  set J : IntermediateField K (LaurentSeries K) :=
    IntermediateField.adjoin K ({jqModC K} : Set (LaurentSeries K)) with hJ
  set Φ : IntermediateField K (LaurentSeries K) := modularFunctionFieldFullC K M with hΦ
  set Fx : IntermediateField K (LaurentSeries K) :=
    IntermediateField.lift (IntermediateField.fixedField G) with hFx
  have hJΦ : J ≤ Φ := IntermediateField.adjoin_simple_le_iff.mpr (jqModC_mem_full K M)
  have hΦFx : Φ ≤ Fx := by
    intro y hy
    have hyF : y ∈ Fb K M := FH_le ⊥ (full_le_FH ⊥ hy)
    have : (⟨y, hyF⟩ : Fb K M) ∈ IntermediateField.fixedField G := by
      rw [IntermediateField.mem_fixedField_iff]
      rintro e ⟨γ, rfl⟩
      exact apply_eq_self_of_coe_mem_F0 ρ hρ γ ⟨y, hyF⟩ (full_le_F0 hy)
    exact (IntermediateField.mem_lift (⟨y, hyF⟩ : Fb K M)).mpr this
  have hFxF : Fx ≤ Fb K M := IntermediateField.lift_le _

  have hψ : IntermediateField.relfinrank J Φ = dedekindPsi M := by
    have e1 := finrank_adjoin_simple_eq_relfinrank (K := K) (modularFunctionFieldFullC K M)
      ⟨jqModC K, jqModC_mem_full K M⟩
    have e2 := finrank_adjoin_jqModC_modularFunctionFieldFullC_eq_dedekindPsi K M hM
    exact e1.symm.trans e2
  have hFxdeg : IntermediateField.relfinrank Fx (Fb K M) = Nat.card G := by
    have e := finrank_eq_relfinrank_lift (K := K) (Fb K M) (IntermediateField.fixedField G)
    exact e.symm.trans hArtin

  set x₀ : Fb K M := ⟨jqModC K, intFormRatiosC_subset K _ (jqModC_mem_intFormRatiosC K _)⟩ with hx₀
  have hx₀' : (x₀ : LaurentSeries K) = jqModC K := rfl
  obtain ⟨hfin, hle⟩ := finiteDimensional_and_finrank_adjoin_jqModC_qExpFunctionFieldC_le_index K
    (GammaH M ⊥) (translation_mem_GammaH M ⊥) (GammaH M Hp) (GammaH_mono le_Hpm) mem_or_neg_mem_bot x₀ hx₀'
  haveI := hfin
  have htarget : Module.finrank (IntermediateField.adjoin K ({x₀} : Set (Fb K M))) (Fb K M)
      = IntermediateField.relfinrank J (Fb K M) := by
    have e := finrank_adjoin_simple_eq_relfinrank (K := K) (Fb K M) x₀
    rw [hx₀'] at e
    exact e
  have htower : IntermediateField.relfinrank J (Fb K M)
      = dedekindPsi M * (IntermediateField.relfinrank Φ Fx * Nat.card G) := by
    rw [← IntermediateField.relfinrank_mul_relfinrank hJΦ (hΦFx.trans hFxF),
      ← IntermediateField.relfinrank_mul_relfinrank hΦFx hFxF, hψ, hFxdeg]

  have hpos : 0 < Module.finrank (IntermediateField.adjoin K ({x₀} : Set (Fb K M))) (Fb K M) :=
    Module.finrank_pos
  rw [htarget, htower] at hpos
  have hmid : 1 ≤ IntermediateField.relfinrank Φ Fx := by
    rcases Nat.eq_zero_or_pos (IntermediateField.relfinrank Φ Fx) with h0 | h0
    · rw [h0, zero_mul, mul_zero] at hpos; exact absurd hpos (lt_irrefl 0)
    · exact h0
  have hψpos : 0 < dedekindPsi M := by
    rcases Nat.eq_zero_or_pos (dedekindPsi M) with h0 | h0
    · rw [h0, zero_mul] at hpos; exact absurd hpos (lt_irrefl 0)
    · exact h0

  rw [htarget, htower, ← hK'index, Gamma0_index, ← hcardG] at hle
  have hr : IntermediateField.relfinrank Φ Fx ≤ 1 := by
    have h1 : dedekindPsi M * (IntermediateField.relfinrank Φ Fx * Nat.card G) ≤
        dedekindPsi M * (1 * Nat.card G) := by rw [one_mul, mul_comm (dedekindPsi M) (Nat.card G)]; exact hle
    have h2 := Nat.le_of_mul_le_mul_left h1 hψpos
    exact Nat.le_of_mul_le_mul_right h2 (by rw [hcardG]; exact hK'pos)
  have hr1 : IntermediateField.relfinrank Φ Fx = 1 := le_antisymm hr hmid
  exact le_antisymm ((IntermediateField.relfinrank_eq_one_iff).mp hr1) hΦFx

theorem coe_mem_FH_of_forall_apply_eq (hM : (M : K) ≠ 0) (ρ : Gamma0 M →* (Fb K M ≃ₐ[K] Fb K M))
    (hρ : IsDiamondPullbackModL K M ⊥ ρ) (H : Subgroup (ZMod M)ˣ) (y : Fb K M)
    (hy : ∀ γ : Gamma0 M, ρ γ y = y) : (y : LaurentSeries K) ∈ FH K M H := by
  have hyfix : y ∈ IntermediateField.fixedField ρ.range := by
    rw [IntermediateField.mem_fixedField_iff]
    rintro e ⟨γ, rfl⟩
    exact hy γ
  have h1 : (y : LaurentSeries K) ∈ IntermediateField.lift (IntermediateField.fixedField ρ.range) :=
    (IntermediateField.mem_lift y).mpr hyfix
  rw [lift_fixedField_range_eq_full hM ρ hρ] at h1
  exact full_le_FH H h1

end Invariants

section Galois

variable {K : Type*} [Field K] {M : ℕ} [NeZero M]

variable (K) in

def FHin (H : Subgroup (ZMod M)ˣ) : IntermediateField K (Fb K M) :=
  (FH K M H).comap (IntermediateField.val (Fb K M))

theorem mem_FHin {H : Subgroup (ZMod M)ˣ} {y : Fb K M} : y ∈ FHin K H ↔ (y : LaurentSeries K) ∈ FH K M H :=
  Iff.rfl

theorem coe_mem_FH_of_forall_GammaH (hM : (M : K) ≠ 0) (ρ : Gamma0 M →* (Fb K M ≃ₐ[K] Fb K M))
    (hρ : IsDiamondPullbackModL K M ⊥ ρ) (H : Subgroup (ZMod M)ˣ) (y : Fb K M)
    (hy : ∀ γ : Gamma0 M, (γ : SL(2, ℤ)) ∈ GammaH M H → ρ γ y = y) :
    (y : LaurentSeries K) ∈ FH K M H := by
  classical

  set G : Subgroup (Fb K M ≃ₐ[K] Fb K M) := ρ.range with hG
  haveI : (GammaH M (Hpm ⊥)).FiniteIndex := finiteIndex_GammaH M _
  have hK'le : (GammaH M (Hpm ⊥)).subgroupOf (Gamma0 M) ≤ ρ.ker := fun γ hγ => by
    rw [MonoidHom.mem_ker]
    exact rho_eq_one_of_mem_sup ρ hρ γ (Subgroup.mem_subgroupOf.mp hγ)
  haveI : ρ.ker.FiniteIndex := Subgroup.finiteIndex_of_le hK'le
  haveI : Finite G := Nat.finite_of_card_ne_zero (by
    rw [← Subgroup.index_ker ρ]; exact Subgroup.FiniteIndex.index_ne_zero)

  let B : Subfield (Fb K M) := FixedPoints.subfield G (Fb K M)
  haveI : IsGalois B (Fb K M) := IsGalois.of_fixed_field (Fb K M) G
  haveI : FiniteDimensional B (Fb K M) := inferInstance

  have hEA : ∀ b : Fb K M, (∀ g : G, (g : Fb K M ≃ₐ[K] Fb K M) b = b) → b ∈ FHin K H := by
    intro b hb
    exact mem_FHin.mpr (coe_mem_FH_of_forall_apply_eq hM ρ hρ H b (fun γ => hb ⟨ρ γ, ⟨γ, rfl⟩⟩))
  let A' : IntermediateField B (Fb K M) :=
    { (FHin K H).toSubalgebra.toSubsemiring with
      carrier := (FHin K H : Set (Fb K M))
      algebraMap_mem' := fun b => hEA (b : Fb K M) (fun g => b.2 g)
      inv_mem' := fun x hx => (FHin K H).inv_mem hx }
  have hGal := IsGalois.fixedField_fixingSubgroup A'

  have hyfix : y ∈ IntermediateField.fixedField (IntermediateField.fixingSubgroup A') := by
    rw [IntermediateField.mem_fixedField_iff]
    intro τ hτ
    obtain ⟨g, rfl⟩ := FixedPoints.toAlgAut_surjective G (Fb K M) τ
    obtain ⟨γ, hγ⟩ : ∃ γ : Gamma0 M, ρ γ = (g : Fb K M ≃ₐ[K] Fb K M) := g.2
    have hfixA : ∀ a : Fb K M, (a : LaurentSeries K) ∈ FH K M H → ρ γ a = a := by
      intro a ha
      have := hτ ⟨a, show a ∈ FHin K H from mem_FHin.mpr ha⟩
      rw [hγ]
      first | exact this | simpa using this | (simp only [AlgEquiv.smul_def] at this; exact this)
    have hmem : (γ : SL(2, ℤ)) ∈ GammaH M (Hpm H) := mem_GammaH_sup_of_forall_apply_eq ρ hρ γ hfixA
    have := apply_eq_self_of_mem_sup ρ hρ y hy γ hmem
    rw [hγ] at this
    first | exact this | simpa using this | (change _ = _; exact this)
  rw [hGal] at hyfix
  exact mem_FHin.mp hyfix

end Galois

end P2MKcDiaGal
p2m_reactivate "P2MW.S_ModularCurve_exists_isDiamondPullbackModL_bot_forall_coe_mem_gammaH_iff.P2MKcDiaGal"

open P2MKcDiaGal in
universe u in
set_option synthInstance.maxHeartbeats 1600000 in

theorem solution
    (K : Type u) [Field K] [IsAlgClosed K] (M : ℕ) [NeZero M] (hM : (M : K) ≠ 0) :
    ∃ ρ : CongruenceSubgroup.Gamma0 M →*
        (qExpFunctionFieldC K (CohCarrier.GammaH M ⊥) ≃ₐ[K]
          qExpFunctionFieldC K (CohCarrier.GammaH M ⊥)),
      IsDiamondPullbackModL K M ⊥ ρ ∧
      ∀ (H : Subgroup (ZMod M)ˣ) (y : qExpFunctionFieldC K (CohCarrier.GammaH M ⊥)),
        (y : LaurentSeries K) ∈ qExpFunctionFieldC K (CohCarrier.GammaH M H) ↔
          ∀ γ : CongruenceSubgroup.Gamma0 M, (γ : SL(2, ℤ)) ∈ CohCarrier.GammaH M H → ρ γ y = y := by
  obtain ⟨ρ, hρ⟩ := ModularCurve.exists_isDiamondPullbackModL_bot_of_natCast_ne_zero K M hM
  refine ⟨ρ, hρ, fun H y => ⟨fun hy γ hγ => ?_, fun h => ?_⟩⟩
  · exact apply_eq_self_of_coe_mem_FH (K := K) (M := M) ρ hρ γ hγ y hy
  · exact coe_mem_FH_of_forall_GammaH (K := K) (M := M) hM ρ hρ H y h

end
p2m_reactivate "P2MW.S_ModularCurve_exists_isDiamondPullbackModL_bot_forall_coe_mem_gammaH_iff.P2MKcDiaGal"

end S_ModularCurve_exists_isDiamondPullbackModL_bot_forall_coe_mem_gammaH_iff
end P2MW
export P2MW.S_ModularCurve_exists_isDiamondPullbackModL_bot_forall_coe_mem_gammaH_iff (solution)
