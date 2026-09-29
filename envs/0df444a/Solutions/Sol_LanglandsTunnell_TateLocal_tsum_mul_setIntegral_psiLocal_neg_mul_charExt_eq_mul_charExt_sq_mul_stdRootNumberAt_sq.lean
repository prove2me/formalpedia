-- Prove2me | solution 1 for LanglandsTunnell.TateLocal.tsum_mul_setIntegral_psiLocal_neg_mul_charExt_eq_mul_charExt_sq_mul_stdRootNumberAt_sq
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:08.670037+00:00
-- url     : https://prove2.me/submissions/ca8e72cd-8a03-504d-83c6-b41d7518f5e1

import Definitions.Def_LanglandsTunnell_StandardLocalConstantsAt
import Theorems.Thm_LanglandsTunnell_TateLocal_tateFourier_indicator_setOf_valued_sub_le
import Theorems.Thm_LanglandsTunnell_TateLocal_modulus_adicCompletion_eq_nnnorm
import Theorems.Thm_LanglandsTunnell_TateLocal_forall_eq_one_and_exists_ne_one_of_addCharLevel
import Theorems.Thm_LanglandsTunnell_TateLocal_psiLocal_eq_one_of_mem_integers
import Theorems.Thm_LanglandsTunnell_TateLocal_psiLocal_ne_one
import Theorems.Thm_LanglandsTunnell_TateLocal_setIntegral_addChar_mul_charExt_eq_zero_of_valued_ne
import Theorems.Thm_LanglandsTunnell_TateLocal_setIntegral_addChar_mul_charExt_mul_setIntegral_inv_mul_pow_eq
import Theorems.Thm_LanglandsTunnell_TateLocal_localZeta_tateFourier_stdTestFunAt
import Theorems.Thm_LanglandsTunnell_TateLocal_localZeta_stdTestFunAt_eq_real_image_higherUnitsAt
import Theorems.Thm_LanglandsTunnell_TateLocal_selfDualHaarAt_real_image_higherUnitsAt
import Theorems.Thm_LanglandsTunnell_TateLocal_selfDualHaarAt_real_integers_mul_real_setOf_valued_le_exp_addCharLevel
import Theorems.Thm_LanglandsTunnell_TateLocal_measureReal_setOf_valued_le_exp
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.NormNum
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_LanglandsTunnell_TateLocal_tsum_mul_setIntegral_psiLocal_neg_mul_charExt_eq_mul_charExt_sq_mul_stdRootNumberAt_sq
p2m_attr_erase "instance" "instFiniteResidueFieldAdicCompletionRingOfIntegersWithZeroMultiplicativeInt_definitions NumberField.instCompactSpaceAdicCompletionIntegers Rat.adicCompletion.locallyCompactSpace NumberField.instFiniteResidueFieldAdicCompletionIntegers instWeaklyLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions instCountableOfNumberField_definitions IsDedekindDomain.HeightOneSpectrum.Extension.instAlgebraSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersValEqUnder IsDedekindDomain.HeightOneSpectrum.Extension.instAlgebraSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersValEqUnder_1 IsDedekindDomain.HeightOneSpectrum.instMulActionHomClassAlgHomTensorProductAdicCompletionForallValEqUnder_definitions IsDedekindDomain.HeightOneSpectrum.Extension.instAlgebraAdicCompletionValEqUnder IsDedekindDomain.HeightOneSpectrum.adicCompletion.instFiniteForallValEqUnderOfFiniteDimensional_definitions IsDedekindDomain.HeightOneSpectrum.instIsBiscalarSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersTensorProductCoeAlgHomTensorAdicCompletionIntegersTo IsDedekindDomain.HeightOneSpectrum.Extension.instContinuousSMulAdicCompletionValEqUnder IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsModuleTopology IsDedekindDomain.HeightOneSpectrum.Extension.instFiniteSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersValEqUnderOfFiniteDimensional IsDedekindDomain.HeightOneSpectrum.adicCompletion.instFiniteValEqUnderOfFiniteDimensional_definitions instIsBiscalarTensorProductCoeAlgHomBaseChange_of_algebraMap IsDedekindDomain.HeightOneSpectrum.instIsScalarTowerSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersValEqUnder_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsModuleTopologyPi Submodule.instIsTopologicalModuleSubtypeMem Pi.instTopologicalModule IsTopologicalModule.toContinuousSMul IsTopologicalModule.toContinuousAdd instFunLike SemialgHomClass.toSemilinearMapClass instCoeTCSemialgHom SemialgHomClass.toRingHomClass SemialgHomClass.instSemialgHom"
p2m_attr_erase "simp" "SemialgHom.baseChange_of_algebraMap_tmul_left SemialgHom.baseChangeRightOfAlgebraMap_apply Pi.semialgHomPi_apply Pi.semialgHom_apply Module.Basis.rightBaseChange_apply LinearEquiv.coe_mulLeft LinearEquiv.coe_mulRight WithVal.semialgebraMap_toFun_ofVal Module.Basis.rightBaseChange_repr IsDedekindDomain.HeightOneSpectrum.adicCompletionIntegers.tensorCoe_tmul IsDedekindDomain.HeightOneSpectrum.tensorAdicCompletionIntegersTo_tmul SemialgHom.baseChangeRightOfAlgebraMap_coe IsDedekindDomain.HeightOneSpectrum.adicCompletion.integerBaseChangeLinearEquiv_tmul_apply SemialgHom.baseChange_of_algebraMap_tmul_right IsLocalization.map_moduleTensorEquiv_symm_tmul IsLocalization.leftModuleTensorEquiv_apply IsLocalization.moduleLid_symm_apply IsLocalization.leftModuleTensorEquiv_symm_apply IsLocalization.map_moduleTensorEquiv_tmul IsModuleTopology.continuousLinearEquiv_apply AlgEquiv.extendScalars_symm_apply IsModuleTopology.Module.Basis.equivFun_homeo_symm_apply IsModuleTopology.Module.Basis.equivFun_homeo_apply IsModuleTopology.continuousAlgEquivOfIsBiscalar_apply AlgEquiv.extendScalars_apply IsModuleTopology.continuousLinearEquiv_symm_apply SemialgHom.restrictScalars_toFun SemialgHom.mk.sizeOf_spec SemialgHom.mk.injEq SemialgHom.coe_coe coe_mk TensorProduct.RightActions.smul_def TensorProduct.RightActions.Module.TensorProduct.comm_symm_apply_tmul TensorProduct.RightActions.LinearMap.baseChange_id TensorProduct.RightActions.algebraMap_eval TensorProduct.RightActions.Module.TensorProduct.comm_apply_tmul TensorProduct.RightActions.Algebra.TensorProduct.comm_symm_apply_tmul TensorProduct.RightActions.Algebra.TensorProduct.comm_apply_tmul"

set_option autoImplicit false

open IsDedekindDomain NumberField NumberField.AdelicLevel NumberField.StandardAddChar

open MeasureTheory

noncomputable section

open MeasureTheory IsDedekindDomain NumberField NumberField.AdelicLevel NumberField.StandardAddChar
open scoped NNReal ENNReal Pointwise

namespace LanglandsTunnell
p2m_export "LanglandsTunnell" "TateLocal.forall_eq_one_and_exists_ne_one_of_addCharLevel TateLocal.psiLocal_eq_one_of_mem_integers TateLocal.psiLocal_ne_one TateLocal.setIntegral_addChar_mul_charExt_eq_zero_of_valued_ne TateLocal.setIntegral_addChar_mul_charExt_mul_setIntegral_inv_mul_pow_eq TateLocal.localZeta_tateFourier_stdTestFunAt TateLocal.localZeta_stdTestFunAt_eq_real_image_higherUnitsAt TateLocal.selfDualHaarAt_real_image_higherUnitsAt TateLocal.selfDualHaarAt_real_integers_mul_real_setOf_valued_le_exp_addCharLevel TateLocal.measureReal_setOf_valued_le_exp"
namespace TateLocal
p2m_export "LanglandsTunnell.TateLocal" "addCharLevel localBorel borelSpace_localBorel integersPositiveCompacts selfDualHaarAt stdTestFunAt stdRootNumberAt higherUnitsAt mem_higherUnitsAt_iff HasConductorExponentAt hasConductorExponentAt_unique localEpsilonAt localEpsilonAt_of_not_hasConductorExponentAt_zero modulus modulus_coe_units tateFourier charExt charExt_zero charExt_of_ne_zero localGammaAt tateFourier_indicator_setOf_valued_sub_le modulus_adicCompletion_eq_nnnorm forall_eq_one_and_exists_ne_one_of_addCharLevel psiLocal_eq_one_of_mem_integers psiLocal_ne_one setIntegral_addChar_mul_charExt_eq_zero_of_valued_ne setIntegral_addChar_mul_charExt_mul_setIntegral_inv_mul_pow_eq localZeta_tateFourier_stdTestFunAt localZeta_stdTestFunAt_eq_real_image_higherUnitsAt selfDualHaarAt_real_image_higherUnitsAt selfDualHaarAt_real_integers_mul_real_setOf_valued_le_exp_addCharLevel measureReal_setOf_valued_le_exp"
namespace Ws47Ramified
p2m_open "LanglandsTunnell.TateLocal LanglandsTunnell"

section Generic

theorem preimage_mul_left_eq_smul {F : Type*} [Field F] (u : Fˣ) (s : Set F) :
    (fun x => (u : F) * x) ⁻¹' s = u⁻¹ • s := by
  ext x
  rw [Set.mem_preimage, Set.mem_smul_set_iff_inv_smul_mem, inv_inv, Units.smul_def, smul_eq_mul]

theorem charExt_units_mul {F : Type*} [Field F] (χ : Fˣ →* ℂˣ) (u : Fˣ) (y : F) :
    charExt χ ((u : F) * y) = (χ u : ℂ) * charExt χ y := by
  by_cases hy : y = 0
  · simp [hy]
  · have hne : (u : F) * y ≠ 0 := mul_ne_zero u.ne_zero hy
    rw [charExt_of_ne_zero χ hne, charExt_of_ne_zero χ hy, ← Units.val_mul, ← map_mul]
    congr 2
    ext
    simp

theorem tateFourier_indicator_one {F : Type*} [Field F] [MeasurableSpace F] (ψ : AddChar F ℂ)
    (μ : Measure F) {S : Set F} (hS : MeasurableSet S) (x : F) :
    tateFourier ψ μ (S.indicator fun _ => (1 : ℂ)) x = ∫ y in S, ψ (y * x) ∂μ := by
  rw [tateFourier, ← integral_indicator hS]
  congr 1
  funext y
  by_cases hy : y ∈ S <;> simp [hy]

variable {F : Type*} [Field F] [TopologicalSpace F] [IsTopologicalRing F] [LocallyCompactSpace F]
  [MeasurableSpace F] [BorelSpace F]

theorem map_mul_left_eq_smul (μ : Measure F) [μ.IsAddHaarMeasure] [μ.Regular] (u : Fˣ) :
    Measure.map (fun x => (u : F) * x) μ = ((modulus (u : F) : ℝ≥0∞)⁻¹) • μ := by
  ext s hs
  rw [Measure.map_apply (measurable_const_mul _) hs, preimage_mul_left_eq_smul,
    Measure.smul_apply, smul_eq_mul, ← distribHaarChar_mul μ u⁻¹ s, map_inv, modulus_coe_units,
    ENNReal.coe_inv distribHaarChar_pos.ne']

theorem map_mul_left_of_modulus_eq_one (μ : Measure F) [μ.IsAddHaarMeasure] [μ.Regular] {u : Fˣ}
    (hu : modulus (u : F) = 1) : Measure.map (fun x => (u : F) * x) μ = μ := by
  rw [map_mul_left_eq_smul μ u, hu, ENNReal.coe_one, inv_one, one_smul]

theorem integral_comp_mul_left_of_modulus_eq_one (μ : Measure F) [μ.IsAddHaarMeasure] [μ.Regular]
    {u : Fˣ} (hu : modulus (u : F) = 1) (Φ : F → ℂ) :
    ∫ y, Φ y ∂μ = ∫ y, Φ ((u : F) * y) ∂μ := by
  calc ∫ y, Φ y ∂μ = ∫ y, Φ y ∂(Measure.map (fun x => (u : F) * x) μ) := by
        rw [map_mul_left_of_modulus_eq_one μ hu]
    _ = ∫ y, Φ ((u : F) * y) ∂μ := by
        rw [← MeasurableEquiv.coe_mulLeft₀ u.ne_zero, integral_map_equiv]; rfl

theorem setIntegral_comp_mul_left_of_modulus_eq_one (μ : Measure F) [μ.IsAddHaarMeasure] [μ.Regular]
    {u : Fˣ} (hu : modulus (u : F) = 1) (Φ : F → ℂ) {S : Set F} (hS : MeasurableSet S) :
    ∫ y in S, Φ y ∂μ = ∫ y in (fun y => (u : F) * y) ⁻¹' S, Φ ((u : F) * y) ∂μ := by
  have hpre : MeasurableSet ((fun y => (u : F) * y) ⁻¹' S) := (measurable_const_mul (u : F)) hS
  rw [← integral_indicator hS, ← integral_indicator hpre,
    integral_comp_mul_left_of_modulus_eq_one μ hu (S.indicator Φ)]
  congr 1

theorem setIntegral_mul_charExt_eq_zero (μ : Measure F) [μ.IsAddHaarMeasure] [μ.Regular] {S : Set F}
    (hSm : MeasurableSet S) (g : F → ℂ) (χ : Fˣ →* ℂˣ) {u₁ : Fˣ} (hu₁ : modulus (u₁ : F) = 1)
    (hχ : χ u₁ ≠ 1) (hS : ∀ y, (u₁ : F) * y ∈ S ↔ y ∈ S) (hg : ∀ y ∈ S, g ((u₁ : F) * y) = g y) :
    ∫ y in S, g y * charExt χ y ∂μ = 0 := by
  set Φ : F → ℂ := S.indicator fun y => g y * charExt χ y with hΦdef
  have hΦ : ∀ y, Φ ((u₁ : F) * y) = (χ u₁ : ℂ) * Φ y := by
    intro y
    by_cases hy : y ∈ S
    · rw [hΦdef, Set.indicator_of_mem ((hS y).mpr hy), Set.indicator_of_mem hy, hg y hy,
        charExt_units_mul]
      ring
    · rw [hΦdef, Set.indicator_of_notMem (fun h => hy ((hS y).mp h)), Set.indicator_of_notMem hy,
        mul_zero]
  have hI : ∫ y, Φ y ∂μ = (χ u₁ : ℂ) * ∫ y, Φ y ∂μ := by
    calc ∫ y, Φ y ∂μ = ∫ y, Φ ((u₁ : F) * y) ∂μ := integral_comp_mul_left_of_modulus_eq_one μ hu₁ Φ
      _ = ∫ y, (χ u₁ : ℂ) * Φ y ∂μ := by simp_rw [hΦ]
      _ = (χ u₁ : ℂ) * ∫ y, Φ y ∂μ := integral_const_mul _ _
  have h1 : (1 - (χ u₁ : ℂ)) * ∫ y, Φ y ∂μ = 0 := by
    rw [sub_mul, one_mul, sub_eq_zero]; exact hI
  have hne : (χ u₁ : ℂ) ≠ 1 := fun h => hχ (Units.val_eq_one.mp h)
  rcases mul_eq_zero.mp h1 with h | h
  · exact absurd (sub_eq_zero.mp h).symm hne
  · rwa [hΦdef, integral_indicator hSm] at h

end Generic

section Kv

variable {K : Type} [Field K] [NumberField K] (v : HeightOneSpectrum (𝓞 K))

theorem valued_uniformizerUnit_zpow (m : ℤ) :
    Valued.v ((uniformizerUnit K v ^ m : (v.adicCompletion K)ˣ) : v.adicCompletion K)
      = WithZero.exp (-m) := by
  rw [Units.val_zpow_eq_zpow_val, map_zpow₀, valued_uniformizerUnit, ← WithZero.exp_zsmul]
  congr 1
  simp

theorem norm_eq_zpow_of_valued {x : v.adicCompletion K} {m : ℤ} (hx : Valued.v x = WithZero.exp m) :
    ‖x‖ = (Ideal.absNorm v.asIdeal : ℝ) ^ m := by
  rw [NumberField.FinitePlace.norm_def, hx,
    show (WithZero.exp m) = ((Multiplicative.ofAdd m : Multiplicative ℤ) : WithZero (Multiplicative ℤ))
      from rfl,
    WithZeroMulInt.toNNReal_neg_apply _ WithZero.coe_ne_zero, WithZero.unzero_coe, toAdd_ofAdd,
    NNReal.coe_zpow, NNReal.coe_natCast]

theorem coe_modulus_of_valued {x : v.adicCompletion K} {m : ℤ} (hx : Valued.v x = WithZero.exp m) :
    (modulus x : ℝ) = (Ideal.absNorm v.asIdeal : ℝ) ^ m := by
  rw [modulus_adicCompletion_eq_nnnorm K v x, coe_nnnorm, norm_eq_zpow_of_valued v hx]

theorem modulus_eq_one_of_valued {u : v.adicCompletion K} (hu : Valued.v u = 1) : modulus u = 1 := by
  rw [← NNReal.coe_inj, NNReal.coe_one, coe_modulus_of_valued v (m := 0) (by rw [hu, WithZero.exp_zero]),
    zpow_zero]

theorem valued_neg_one : Valued.v (-1 : v.adicCompletion K) = 1 := by
  rw [Valuation.map_neg, map_one]

theorem isClosed_ball (k : ℤ) : IsClosed {x : v.adicCompletion K | Valued.v x ≤ WithZero.exp k} := by
  have ht : ((uniformizerUnit K v ^ (-k) : (v.adicCompletion K)ˣ) : v.adicCompletion K) ≠ 0 :=
    Units.ne_zero _
  have h := isClosed_setOf_valued_le v _ ht
  rw [valued_uniformizerUnit_zpow, neg_neg] at h
  exact h

theorem isOpen_ball (k : ℤ) : IsOpen {x : v.adicCompletion K | Valued.v x ≤ WithZero.exp k} := by
  have ht : ((uniformizerUnit K v ^ (-k) : (v.adicCompletion K)ˣ) : v.adicCompletion K) ≠ 0 :=
    Units.ne_zero _
  have h := isOpen_setOf_valued_le v _ ht
  rw [valued_uniformizerUnit_zpow, neg_neg] at h
  exact h

theorem coe_integers_eq :
    (v.adicCompletionIntegers K : Set (v.adicCompletion K)) = {x | Valued.v x ≤ WithZero.exp 0} := by
  ext x
  rw [WithZero.exp_zero]
  exact HeightOneSpectrum.mem_adicCompletionIntegers (𝓞 K) K v

theorem isCompact_integers : IsCompact (v.adicCompletionIntegers K : Set (v.adicCompletion K)) :=
  isCompact_iff_compactSpace.mpr (show CompactSpace (v.adicCompletionIntegers K) from inferInstance)

theorem isCompact_ball_zero : IsCompact {x : v.adicCompletion K | Valued.v x ≤ WithZero.exp 0} := by
  rw [← coe_integers_eq]
  exact isCompact_integers v

theorem continuous_addChar_of_level (ψ : AddChar (v.adicCompletion K) ℂ) (n : ℤ)
    (hψn : ∀ x : v.adicCompletion K, Valued.v x ≤ WithZero.exp n → ψ x = 1) : Continuous ψ := by
  refine continuous_iff_continuousAt.mpr fun x => ?_
  have hmem : (fun y => y - x) ⁻¹' {h : v.adicCompletion K | Valued.v h ≤ WithZero.exp n} ∈ nhds x := by
    refine ((isOpen_ball v n).preimage (continuous_id.sub continuous_const)).mem_nhds ?_
    show Valued.v (x - x) ≤ WithZero.exp n
    rw [sub_self, map_zero]
    exact zero_le'
  have hev : (fun _ => ψ x) =ᶠ[nhds x] (ψ : v.adicCompletion K → ℂ) := by
    refine Filter.mem_of_superset hmem fun y hy => ?_
    show ψ x = ψ y
    rw [show ψ y = ψ (x + (y - x)) by rw [add_sub_cancel], AddChar.map_add_eq_mul, hψn _ hy, mul_one]
  exact continuousAt_const.congr hev

theorem units_set_eq_diff :
    {u : v.adicCompletion K | Valued.v u = 1}
      = {y : v.adicCompletion K | Valued.v y ≤ WithZero.exp (-(0 : ℤ))}
          \ {y : v.adicCompletion K | Valued.v y ≤ WithZero.exp (-(1 : ℤ))} := by
  ext y
  simp only [Set.mem_setOf_eq, Set.mem_diff, neg_zero]
  constructor
  · intro hy
    refine ⟨by rw [hy, WithZero.exp_zero], fun h => ?_⟩
    rw [hy, ← WithZero.exp_zero, WithZero.exp_le_exp] at h
    omega
  · rintro ⟨h1, h2⟩
    have hne : Valued.v y ≠ 0 := fun h0 => h2 (by rw [h0]; exact zero_le')
    obtain ⟨m, hm⟩ : ∃ m : ℤ, Valued.v y = WithZero.exp m := ⟨_, (WithZero.exp_log hne).symm⟩
    rw [hm, WithZero.exp_le_exp] at h1 h2
    rw [hm, ← WithZero.exp_zero]
    congr 1
    omega

theorem isClosed_units_set : IsClosed {u : v.adicCompletion K | Valued.v u = 1} := by
  rw [units_set_eq_diff]
  exact (isClosed_ball v _).sdiff (isOpen_ball v _)

theorem units_set_subset_ball_zero :
    {u : v.adicCompletion K | Valued.v u = 1} ⊆ {x : v.adicCompletion K | Valued.v x ≤ WithZero.exp 0} := by
  intro u hu
  have hu' : Valued.v u = 1 := hu
  show Valued.v u ≤ WithZero.exp 0
  rw [hu', WithZero.exp_zero]

theorem isCompact_units_set : IsCompact {u : v.adicCompletion K | Valued.v u = 1} :=
  (isCompact_ball_zero v).of_isClosed_subset (isClosed_units_set v) (units_set_subset_ball_zero v)

theorem measurableSet_units_set [MeasurableSpace (v.adicCompletion K)] [BorelSpace (v.adicCompletion K)] :
    MeasurableSet {u : v.adicCompletion K | Valued.v u = 1} :=
  (isClosed_units_set v).measurableSet

theorem preimage_mul_units_set {c : v.adicCompletion K} (hc : Valued.v c = 1) :
    (fun y => c * y) ⁻¹' {u : v.adicCompletion K | Valued.v u = 1} = {u : v.adicCompletion K | Valued.v u = 1} := by
  ext y
  simp only [Set.mem_preimage, Set.mem_setOf_eq, map_mul, hc, one_mul]

theorem exp_mul_le_iff {k m r : ℤ} (hr : k + r = m) (X : WithZero (Multiplicative ℤ)) :
    WithZero.exp k * X ≤ WithZero.exp m ↔ X ≤ WithZero.exp r := by
  by_cases hX : X = 0
  · subst hX
    rw [mul_zero]
    exact ⟨fun _ => zero_le', fun _ => zero_le'⟩
  · obtain ⟨j, rfl⟩ : ∃ j : ℤ, X = WithZero.exp j := ⟨_, (WithZero.exp_log hX).symm⟩
    rw [← WithZero.exp_add, WithZero.exp_le_exp, WithZero.exp_le_exp]
    omega

theorem sub_one_ball_subset_units_set {a : ℕ} (ha : 1 ≤ a) :
    {x : v.adicCompletion K | Valued.v (x - 1) ≤ WithZero.exp (-(a : ℤ))}
      ⊆ {u : v.adicCompletion K | Valued.v u = 1} := by
  intro x hx
  have hx' : Valued.v (x - 1) ≤ WithZero.exp (-(a : ℤ)) := hx
  have hlt : Valued.v (x - 1) < Valued.v (1 : v.adicCompletion K) := by
    rw [map_one, ← WithZero.exp_zero]
    exact hx'.trans_lt (WithZero.exp_lt_exp.mpr (by omega))
  have h := Valuation.map_eq_of_sub_lt _ hlt
  rw [map_one] at h
  exact h

theorem isClosed_sub_one_ball (k : ℤ) :
    IsClosed {x : v.adicCompletion K | Valued.v (x - 1) ≤ WithZero.exp k} :=
  (isClosed_ball v k).preimage (continuous_id.sub continuous_const)

theorem isOpen_sub_one_ball (k : ℤ) :
    IsOpen {x : v.adicCompletion K | Valued.v (x - 1) ≤ WithZero.exp k} :=
  (isOpen_ball v k).preimage (continuous_id.sub continuous_const)

theorem isClosed_add_one_ball (k : ℤ) :
    IsClosed {x : v.adicCompletion K | Valued.v (x + 1) ≤ WithZero.exp k} :=
  (isClosed_ball v k).preimage (continuous_id.add continuous_const)

theorem preimage_neg_one_mul (e : WithZero (Multiplicative ℤ)) :
    (fun y => (((-1 : (v.adicCompletion K)ˣ)) : v.adicCompletion K) * y) ⁻¹'
        ({u : v.adicCompletion K | Valued.v u = 1} ∩ {w : v.adicCompletion K | Valued.v (w + 1) ≤ e})
      = {u : v.adicCompletion K | Valued.v u = 1} ∩ {x : v.adicCompletion K | Valued.v (x - 1) ≤ e} := by
  ext y
  simp only [Set.mem_preimage, Set.mem_inter_iff, Set.mem_setOf_eq, Units.val_neg, Units.val_one, neg_mul,
    one_mul, Valuation.map_neg]
  rw [show -y + 1 = -(y - 1) by ring, Valuation.map_neg]

theorem charExt_eq_of_valued_sub_le {χ : (v.adicCompletion K)ˣ →* ℂˣ} {a : ℕ}
    (hχ : ∀ u ∈ higherUnitsAt K v a, χ u = 1) {y₀ y : v.adicCompletion K} (hy₀ : y₀ ≠ 0)
    (h : Valued.v (y - y₀) ≤ Valued.v y₀ * WithZero.exp (-((a + 1 : ℕ) : ℤ))) :
    charExt χ y = charExt χ y₀ := by
  have hv0 : Valued.v y₀ ≠ 0 := (Valuation.ne_zero_iff _).mpr hy₀
  obtain ⟨m₀, hm₀⟩ : ∃ m : ℤ, Valued.v y₀ = WithZero.exp m := ⟨_, (WithZero.exp_log hv0).symm⟩
  have h' : Valued.v (y - y₀) ≤ WithZero.exp (m₀ + -((a + 1 : ℕ) : ℤ)) := by
    rwa [hm₀, ← WithZero.exp_add] at h
  have hlt : Valued.v (y - y₀) < Valued.v y₀ := by
    refine h'.trans_lt ?_
    rw [hm₀, WithZero.exp_lt_exp]
    omega
  have hyy : Valued.v y = Valued.v y₀ := Valuation.map_eq_of_sub_lt _ hlt
  have hy : y ≠ 0 := (Valuation.ne_zero_iff _).mp (by rw [hyy]; exact hv0)
  set u : (v.adicCompletion K)ˣ := Units.mk0 y hy * (Units.mk0 y₀ hy₀)⁻¹ with hu
  have huval : (u : v.adicCompletion K) = y * y₀⁻¹ := by simp [hu]
  have humem : u ∈ higherUnitsAt K v a := by
    refine ⟨?_, Or.inr ?_⟩
    · rw [huval, map_mul, map_inv₀, hyy, mul_inv_cancel₀ hv0]
    · have hsub : (u : v.adicCompletion K) - 1 = y₀⁻¹ * (y - y₀) := by
        rw [huval, mul_sub, inv_mul_cancel₀ hy₀, mul_comm y₀⁻¹ y]
      rw [hsub, map_mul, map_inv₀, hm₀, ← WithZero.exp_neg]
      calc WithZero.exp (-m₀) * Valued.v (y - y₀)
          ≤ WithZero.exp (-m₀) * WithZero.exp (m₀ + -((a + 1 : ℕ) : ℤ)) := mul_le_mul_right h' _
        _ = WithZero.exp (-((a + 1 : ℕ) : ℤ)) := by rw [← WithZero.exp_add]; congr 1; omega
        _ ≤ WithZero.exp (-(a : ℤ)) := WithZero.exp_le_exp.mpr (by push_cast; omega)
  have hmk : Units.mk0 y hy = u * Units.mk0 y₀ hy₀ := by rw [hu, inv_mul_cancel_right]
  rw [charExt_of_ne_zero χ hy, charExt_of_ne_zero χ hy₀, hmk, map_mul, hχ u humem, one_mul]

theorem continuousOn_charExt {χ : (v.adicCompletion K)ˣ →* ℂˣ} {a : ℕ}
    (hχ : ∀ u ∈ higherUnitsAt K v a, χ u = 1) :
    ContinuousOn (charExt χ) ({0}ᶜ : Set (v.adicCompletion K)) := by
  intro y₀ hy₀
  have hy₀' : y₀ ≠ 0 := hy₀
  set t : v.adicCompletion K :=
    y₀ * ((uniformizerUnit K v ^ ((a + 1 : ℕ) : ℤ) : (v.adicCompletion K)ˣ) : v.adicCompletion K) with ht
  have ht0 : t ≠ 0 := mul_ne_zero hy₀' (Units.ne_zero _)
  have hvt : Valued.v t = Valued.v y₀ * WithZero.exp (-((a + 1 : ℕ) : ℤ)) := by
    rw [ht, map_mul, valued_uniformizerUnit_zpow]
  have hmem : (fun y => y - y₀) ⁻¹' {h : v.adicCompletion K | Valued.v h ≤ Valued.v t} ∈ nhds y₀ := by
    refine ((isOpen_setOf_valued_le v t ht0).preimage (continuous_id.sub continuous_const)).mem_nhds ?_
    show Valued.v (y₀ - y₀) ≤ Valued.v t
    rw [sub_self, map_zero]
    exact zero_le'
  have hev : charExt χ =ᶠ[nhdsWithin y₀ {0}ᶜ] fun _ => charExt χ y₀ :=
    Filter.mem_of_superset (mem_nhdsWithin_of_mem_nhds hmem) fun y hy =>
      charExt_eq_of_valued_sub_le v hχ hy₀' (by rw [← hvt]; exact hy)
  exact (continuousWithinAt_const.congr_of_eventuallyEq hev
    (by simp : charExt χ y₀ = (fun _ => charExt χ y₀) y₀))

theorem continuousOn_charExt_units_set {χ : (v.adicCompletion K)ˣ →* ℂˣ} {a : ℕ}
    (hχ : ∀ u ∈ higherUnitsAt K v a, χ u = 1) :
    ContinuousOn (charExt χ) {u : v.adicCompletion K | Valued.v u = 1} := by
  refine (continuousOn_charExt v hχ).mono fun u hu => ?_
  have hu' : Valued.v u = 1 := hu
  simp only [Set.mem_compl_iff, Set.mem_singleton_iff]
  exact (Valuation.ne_zero_iff _).mp (by rw [hu']; exact one_ne_zero)

theorem integrableOn_charExt_units_set [MeasurableSpace (v.adicCompletion K)]
    [BorelSpace (v.adicCompletion K)] (μ : Measure (v.adicCompletion K)) [μ.IsAddHaarMeasure]
    {χ : (v.adicCompletion K)ˣ →* ℂˣ} {a : ℕ} (hχ : ∀ u ∈ higherUnitsAt K v a, χ u = 1) :
    IntegrableOn (charExt χ) {u : v.adicCompletion K | Valued.v u = 1} μ :=
  (continuousOn_charExt_units_set v hχ).integrableOn_compact (isCompact_units_set v)

theorem charExt_eq_one_of_mem {χ : (v.adicCompletion K)ˣ →* ℂˣ} {a : ℕ}
    (hχ : ∀ u ∈ higherUnitsAt K v a, χ u = 1) {y : v.adicCompletion K}
    (hy : y ∈ {u : v.adicCompletion K | Valued.v u = 1}
      ∩ {x : v.adicCompletion K | Valued.v (x - 1) ≤ WithZero.exp (-(a : ℤ))}) :
    charExt χ y = 1 := by
  obtain ⟨hy1, hya⟩ := hy
  have hy1' : Valued.v y = 1 := hy1
  have hy0 : y ≠ 0 := (Valuation.ne_zero_iff _).mp (by rw [hy1']; exact one_ne_zero)
  have hmem : Units.mk0 y hy0 ∈ higherUnitsAt K v a := by
    refine (mem_higherUnitsAt_iff K v).mpr ⟨?_, Or.inr ?_⟩
    · rw [Units.val_mk0]; exact hy1'
    · rw [Units.val_mk0]; exact hya
  rw [charExt_of_ne_zero χ hy0, hχ _ hmem, Units.val_one]

theorem exists_unit_of_hasConductorExponentAt {χ : (v.adicCompletion K)ˣ →* ℂˣ} {a : ℕ} (ha : 1 ≤ a)
    (hχ : HasConductorExponentAt K v χ a) {j : ℕ} (hj : 1 ≤ j) :
    ∃ u₁ : (v.adicCompletion K)ˣ, Valued.v (u₁ : v.adicCompletion K) = 1 ∧
      Valued.v ((u₁ : v.adicCompletion K) - 1) ≤ WithZero.exp (-((a - j : ℕ) : ℤ)) ∧ χ⁻¹ u₁ ≠ 1 := by
  obtain ⟨u₁, hmem, hne⟩ := hχ.2 (a - j) (by omega)
  obtain ⟨hval, hball⟩ := (mem_higherUnitsAt_iff K v).mp hmem
  refine ⟨u₁, hval, ?_, by rwa [MonoidHom.inv_apply, inv_ne_one]⟩
  rcases hball with h0 | h
  · rw [h0, Nat.cast_zero, neg_zero, WithZero.exp_zero]
    calc Valued.v ((u₁ : v.adicCompletion K) - 1)
        ≤ max (Valued.v (u₁ : v.adicCompletion K)) (Valued.v (1 : v.adicCompletion K)) :=
          Valuation.map_sub _ _ _
      _ = 1 := by rw [hval, map_one, max_self]
  · exact h

theorem valued_mul_sub_one_le {e : WithZero (Multiplicative ℤ)} {u y : v.adicCompletion K}
    (hu : Valued.v u = 1) (hu1 : Valued.v (u - 1) ≤ e) (hy1 : Valued.v (y - 1) ≤ e) :
    Valued.v (u * y - 1) ≤ e := by
  have hsplit : u * y - 1 = u * (y - 1) + (u - 1) := by ring
  rw [hsplit]
  refine (Valuation.map_add _ _ _).trans (max_le ?_ hu1)
  rw [map_mul, hu, one_mul]
  exact hy1

theorem valued_inv_sub_one_le {e : WithZero (Multiplicative ℤ)} {u₁ : (v.adicCompletion K)ˣ}
    (hu : Valued.v (u₁ : v.adicCompletion K) = 1)
    (hu1 : Valued.v ((u₁ : v.adicCompletion K) - 1) ≤ e) :
    Valued.v (((u₁⁻¹ : (v.adicCompletion K)ˣ) : v.adicCompletion K) - 1) ≤ e := by
  have hsplit : ((u₁⁻¹ : (v.adicCompletion K)ˣ) : v.adicCompletion K) - 1
      = ((u₁⁻¹ : (v.adicCompletion K)ˣ) : v.adicCompletion K) * -((u₁ : v.adicCompletion K) - 1) := by
    rw [mul_neg, mul_sub, mul_one, Units.inv_mul, neg_sub]
  have hinv : Valued.v ((u₁⁻¹ : (v.adicCompletion K)ˣ) : v.adicCompletion K) = 1 := by
    rw [Units.val_inv_eq_inv_val, map_inv₀, hu, inv_one]
  rw [hsplit, map_mul, hinv, one_mul, Valuation.map_neg]
  exact hu1

theorem mul_mem_inter_iff {e : WithZero (Multiplicative ℤ)} {u₁ : (v.adicCompletion K)ˣ}
    (hu : Valued.v (u₁ : v.adicCompletion K) = 1) (hu1 : Valued.v ((u₁ : v.adicCompletion K) - 1) ≤ e)
    (y : v.adicCompletion K) :
    (u₁ : v.adicCompletion K) * y ∈ {u : v.adicCompletion K | Valued.v u = 1}
        ∩ {x : v.adicCompletion K | Valued.v (x - 1) ≤ e}
      ↔ y ∈ {u : v.adicCompletion K | Valued.v u = 1} ∩ {x : v.adicCompletion K | Valued.v (x - 1) ≤ e} := by
  simp only [Set.mem_inter_iff, Set.mem_setOf_eq, map_mul, hu, one_mul]
  constructor
  · rintro ⟨hy, hy1⟩
    refine ⟨hy, ?_⟩
    have hinv := valued_inv_sub_one_le v hu hu1
    have hinvval : Valued.v ((u₁⁻¹ : (v.adicCompletion K)ˣ) : v.adicCompletion K) = 1 := by
      rw [Units.val_inv_eq_inv_val, map_inv₀, hu, inv_one]
    have h := valued_mul_sub_one_le v hinvval hinv hy1
    rwa [← mul_assoc, Units.inv_mul, one_mul] at h
  · rintro ⟨hy, hy1⟩
    exact ⟨hy, valued_mul_sub_one_le v hu hu1 hy1⟩

theorem setIntegral_charExt_ball [MeasurableSpace (v.adicCompletion K)] [BorelSpace (v.adicCompletion K)]
    (μ : Measure (v.adicCompletion K)) [μ.IsAddHaarMeasure] {χ : (v.adicCompletion K)ˣ →* ℂˣ} {a : ℕ}
    (ha : 1 ≤ a) (hχ : ∀ u ∈ higherUnitsAt K v a, χ u = 1) :
    ∫ y in {u : v.adicCompletion K | Valued.v u = 1}
        ∩ {x : v.adicCompletion K | Valued.v (x - 1) ≤ WithZero.exp (-(a : ℤ))}, charExt χ y ∂μ
      = ((μ.real {x : v.adicCompletion K | Valued.v (x - 1) ≤ WithZero.exp (-(a : ℤ))} : ℝ) : ℂ) := by
  have hS : MeasurableSet ({u : v.adicCompletion K | Valued.v u = 1}
      ∩ {x : v.adicCompletion K | Valued.v (x - 1) ≤ WithZero.exp (-(a : ℤ))}) :=
    (measurableSet_units_set v).inter (isClosed_sub_one_ball v _).measurableSet
  rw [setIntegral_congr_fun hS (fun y hy => charExt_eq_one_of_mem v hχ hy), setIntegral_const,
    Set.inter_eq_right.mpr (sub_one_ball_subset_units_set v ha), Complex.real_smul, mul_one]

theorem setIntegral_charExt_inv_ball_pred_eq_zero [MeasurableSpace (v.adicCompletion K)]
    [BorelSpace (v.adicCompletion K)] (μ : Measure (v.adicCompletion K)) [μ.IsAddHaarMeasure]
    {χ : (v.adicCompletion K)ˣ →* ℂˣ} {a : ℕ} (ha : 1 ≤ a) (hχ : HasConductorExponentAt K v χ a) :
    ∫ y in {u : v.adicCompletion K | Valued.v u = 1}
        ∩ {x : v.adicCompletion K | Valued.v (x - 1) ≤ WithZero.exp (-((a - 1 : ℕ) : ℤ))},
          charExt χ⁻¹ y ∂μ = 0 := by
  obtain ⟨u₁, hu₁, hu₁', hne⟩ := exists_unit_of_hasConductorExponentAt v ha hχ (j := 1) le_rfl
  have hS : MeasurableSet ({u : v.adicCompletion K | Valued.v u = 1}
      ∩ {x : v.adicCompletion K | Valued.v (x - 1) ≤ WithZero.exp (-((a - 1 : ℕ) : ℤ))}) :=
    (measurableSet_units_set v).inter (isClosed_sub_one_ball v _).measurableSet
  have h := setIntegral_mul_charExt_eq_zero μ hS (fun _ => (1 : ℂ)) χ⁻¹ (modulus_eq_one_of_valued v hu₁) hne
    (mul_mem_inter_iff v hu₁ hu₁') (fun _ _ => rfl)
  simpa only [one_mul] using h

theorem setIntegral_ball_addChar [MeasurableSpace (v.adicCompletion K)] [BorelSpace (v.adicCompletion K)]
    (μ : Measure (v.adicCompletion K)) [μ.IsAddHaarMeasure] (ψ : AddChar (v.adicCompletion K) ℂ) (n : ℤ)
    (hψn : ∀ x : v.adicCompletion K, Valued.v x ≤ WithZero.exp n → ψ x = 1)
    (hψn' : ∃ x : v.adicCompletion K, Valued.v x ≤ WithZero.exp (n + 1) ∧ ψ x ≠ 1) (m : ℤ)
    (x : v.adicCompletion K) :
    ∫ y in {y : v.adicCompletion K | Valued.v y ≤ WithZero.exp (-m)}, ψ (y * x) ∂μ
      = if Valued.v x ≤ WithZero.exp (n + m)
          then ((μ.real {y : v.adicCompletion K | Valued.v y ≤ WithZero.exp (-m)} : ℝ) : ℂ) else 0 := by
  have h := tateFourier_indicator_setOf_valued_sub_le K v μ ψ n hψn hψn' 0 m x
  simp only [sub_zero, zero_mul, AddChar.map_zero_eq_one, one_mul] at h
  rw [tateFourier_indicator_one ψ μ (isClosed_ball v (-m)).measurableSet x] at h
  rw [h]
  by_cases hx : Valued.v x ≤ WithZero.exp (n + m) <;>
    simp only [Set.indicator_apply, Set.mem_setOf_eq, hx, ite_true, ite_false, mul_one, mul_zero]

theorem setIntegral_units_addChar [MeasurableSpace (v.adicCompletion K)] [BorelSpace (v.adicCompletion K)]
    (μ : Measure (v.adicCompletion K)) [μ.IsAddHaarMeasure] (ψ : AddChar (v.adicCompletion K) ℂ) (n : ℤ)
    (hψn : ∀ x : v.adicCompletion K, Valued.v x ≤ WithZero.exp n → ψ x = 1)
    (hψn' : ∃ x : v.adicCompletion K, Valued.v x ≤ WithZero.exp (n + 1) ∧ ψ x ≠ 1)
    (x : v.adicCompletion K) :
    ∫ y in {u : v.adicCompletion K | Valued.v u = 1}, ψ (y * x) ∂μ
      = (if Valued.v x ≤ WithZero.exp (n + 0)
            then ((μ.real {y : v.adicCompletion K | Valued.v y ≤ WithZero.exp (-(0 : ℤ))} : ℝ) : ℂ) else 0)
        - (if Valued.v x ≤ WithZero.exp (n + 1)
            then ((μ.real {y : v.adicCompletion K | Valued.v y ≤ WithZero.exp (-(1 : ℤ))} : ℝ) : ℂ) else 0) := by
  have hψc : Continuous ψ := continuous_addChar_of_level v ψ n hψn
  have hsub : {y : v.adicCompletion K | Valued.v y ≤ WithZero.exp (-(1 : ℤ))}
      ⊆ {y : v.adicCompletion K | Valued.v y ≤ WithZero.exp (-(0 : ℤ))} := by
    intro y hy
    have hy' : Valued.v y ≤ WithZero.exp (-(1 : ℤ)) := hy
    show Valued.v y ≤ WithZero.exp (-(0 : ℤ))
    exact hy'.trans (WithZero.exp_le_exp.mpr (by omega))
  have hint : IntegrableOn (fun y : v.adicCompletion K => ψ (y * x))
      {y : v.adicCompletion K | Valued.v y ≤ WithZero.exp (-(0 : ℤ))} μ := by
    refine (hψc.comp (continuous_id.mul continuous_const)).continuousOn.integrableOn_compact ?_
    rw [neg_zero]
    exact isCompact_ball_zero v
  rw [units_set_eq_diff, setIntegral_diff (isClosed_ball v _).measurableSet hint hsub,
    setIntegral_ball_addChar v μ ψ n hψn hψn' 0 x, setIntegral_ball_addChar v μ ψ n hψn hψn' 1 x]

theorem integrable_uncurry [MeasurableSpace (v.adicCompletion K)] [BorelSpace (v.adicCompletion K)]
    (μ : Measure (v.adicCompletion K)) [μ.IsAddHaarMeasure] {ψ : AddChar (v.adicCompletion K) ℂ}
    (hψc : Continuous ψ) {χ : (v.adicCompletion K)ˣ →* ℂˣ} {a : ℕ} (hχ : ∀ u ∈ higherUnitsAt K v a, χ u = 1)
    (t : v.adicCompletion K) :
    Integrable
      (Function.uncurry fun u' w : v.adicCompletion K => ψ (u' * (t * (w + 1))) * charExt χ w)
      ((μ.restrict {u : v.adicCompletion K | Valued.v u = 1}).prod
        (μ.restrict {u : v.adicCompletion K | Valued.v u = 1})) := by
  haveI : SecondCountableTopology (v.adicCompletion K) := UniformSpace.secondCountable_of_separable _
  rw [Measure.prod_restrict]
  refine ContinuousOn.integrableOn_compact ((isCompact_units_set v).prod (isCompact_units_set v)) ?_
  show ContinuousOn (fun p : v.adicCompletion K × v.adicCompletion K =>
    ψ (p.1 * (t * (p.2 + 1))) * charExt χ p.2) _
  refine ContinuousOn.mul ?_ ?_
  · exact (hψc.comp (continuous_fst.mul (continuous_const.mul (continuous_snd.add continuous_const)))).continuousOn
  · refine (continuousOn_charExt_units_set v hχ).comp continuous_snd.continuousOn ?_
    intro p hp
    exact hp.2

theorem gauss_mul_term [MeasurableSpace (v.adicCompletion K)] [BorelSpace (v.adicCompletion K)]
    (μ : Measure (v.adicCompletion K)) [μ.IsAddHaarMeasure] (ψ : AddChar (v.adicCompletion K) ℂ)
    (χ : (v.adicCompletion K)ˣ →* ℂˣ) (t : v.adicCompletion K) {u' : v.adicCompletion K}
    (hu' : Valued.v u' = 1) :
    (∫ u in {u : v.adicCompletion K | Valued.v u = 1}, ψ (t * u) * charExt χ⁻¹ u ∂μ)
        * (ψ (t * u') * charExt χ u')
      = ∫ w in {u : v.adicCompletion K | Valued.v u = 1}, ψ (u' * (t * (w + 1))) * charExt χ⁻¹ w ∂μ := by
  have hu'0 : u' ≠ 0 := (Valuation.ne_zero_iff _).mp (by rw [hu']; exact one_ne_zero)
  obtain ⟨c, rfl⟩ : ∃ c : (v.adicCompletion K)ˣ, (c : v.adicCompletion K) = u' :=
    ⟨Units.mk0 u' hu'0, Units.val_mk0 hu'0⟩
  have hmod : modulus (c : v.adicCompletion K) = 1 := modulus_eq_one_of_valued v hu'
  rw [setIntegral_comp_mul_left_of_modulus_eq_one μ hmod (fun u => ψ (t * u) * charExt χ⁻¹ u)
      (measurableSet_units_set v), preimage_mul_units_set v hu', ← integral_mul_const]
  refine setIntegral_congr_fun (measurableSet_units_set v) fun w _ => ?_
  have hχc : charExt χ (c : v.adicCompletion K) = (χ c : ℂ) := by
    rw [charExt_of_ne_zero χ c.ne_zero, Units.mk0_val]
  have hχχ : (χ⁻¹ c : ℂ) * (χ c : ℂ) = 1 := by
    rw [MonoidHom.inv_apply, Units.val_inv_eq_inv_val, inv_mul_cancel₀ (Units.ne_zero _)]
  have hψ : ψ (t * ((c : v.adicCompletion K) * w)) * ψ (t * (c : v.adicCompletion K))
      = ψ ((c : v.adicCompletion K) * (t * (w + 1))) := by
    rw [← AddChar.map_add_eq_mul]
    congr 1
    ring
  show ψ (t * ((c : v.adicCompletion K) * w)) * charExt χ⁻¹ ((c : v.adicCompletion K) * w)
      * (ψ (t * (c : v.adicCompletion K)) * charExt χ (c : v.adicCompletion K))
    = ψ ((c : v.adicCompletion K) * (t * (w + 1))) * charExt χ⁻¹ w
  rw [charExt_units_mul, hχc]
  linear_combination (charExt χ⁻¹ w * ((χ⁻¹ c : ℂ) * (χ c : ℂ))) * hψ
    + (ψ ((c : v.adicCompletion K) * (t * (w + 1))) * charExt χ⁻¹ w) * hχχ

theorem gauss_mul_gauss [MeasurableSpace (v.adicCompletion K)] [BorelSpace (v.adicCompletion K)]
    (μ : Measure (v.adicCompletion K)) [μ.IsAddHaarMeasure] (ψ : AddChar (v.adicCompletion K) ℂ) (n : ℤ)
    (hψn : ∀ x : v.adicCompletion K, Valued.v x ≤ WithZero.exp n → ψ x = 1)
    (hψn' : ∃ x : v.adicCompletion K, Valued.v x ≤ WithZero.exp (n + 1) ∧ ψ x ≠ 1)
    {χ : (v.adicCompletion K)ˣ →* ℂˣ} {a : ℕ} (ha : 1 ≤ a) (hχ : HasConductorExponentAt K v χ a)
    {t : v.adicCompletion K} (hvt : Valued.v t = WithZero.exp (n + a)) :
    (∫ u in {u : v.adicCompletion K | Valued.v u = 1}, ψ (t * u) * charExt χ⁻¹ u ∂μ)
        * (∫ u in {u : v.adicCompletion K | Valued.v u = 1}, ψ (t * u) * charExt χ u ∂μ)
      = (χ⁻¹ (-1 : (v.adicCompletion K)ˣ) : ℂ)
          * ((μ.real {y : v.adicCompletion K | Valued.v y ≤ WithZero.exp (-(0 : ℤ))} : ℝ) : ℂ)
          * ((μ.real {x : v.adicCompletion K | Valued.v (x - 1) ≤ WithZero.exp (-(a : ℤ))} : ℝ) : ℂ) := by
  have hχ1 : ∀ u ∈ higherUnitsAt K v a, χ⁻¹ u = 1 := fun u hu => by
    rw [MonoidHom.inv_apply, hχ.1 u hu, inv_one]
  have hψc : Continuous ψ := continuous_addChar_of_level v ψ n hψn
  have hU0m : MeasurableSet {u : v.adicCompletion K | Valued.v u = 1} := measurableSet_units_set v

  have hAB : (∫ u in {u : v.adicCompletion K | Valued.v u = 1}, ψ (t * u) * charExt χ⁻¹ u ∂μ)
        * (∫ u in {u : v.adicCompletion K | Valued.v u = 1}, ψ (t * u) * charExt χ u ∂μ)
      = ∫ u' in {u : v.adicCompletion K | Valued.v u = 1},
          ∫ w in {u : v.adicCompletion K | Valued.v u = 1}, ψ (u' * (t * (w + 1))) * charExt χ⁻¹ w ∂μ ∂μ := by
    rw [← integral_const_mul]
    exact setIntegral_congr_fun hU0m fun u' hu' => gauss_mul_term v μ ψ χ t hu'

  have hC : (∫ u' in {u : v.adicCompletion K | Valued.v u = 1},
          ∫ w in {u : v.adicCompletion K | Valued.v u = 1}, ψ (u' * (t * (w + 1))) * charExt χ⁻¹ w ∂μ ∂μ)
      = ∫ w in {u : v.adicCompletion K | Valued.v u = 1},
          ∫ u' in {u : v.adicCompletion K | Valued.v u = 1}, ψ (u' * (t * (w + 1))) * charExt χ⁻¹ w ∂μ ∂μ :=
    integral_integral_swap (integrable_uncurry v μ hψc hχ1 t)

  have hDE : ∀ w : v.adicCompletion K,
      (∫ u' in {u : v.adicCompletion K | Valued.v u = 1}, ψ (u' * (t * (w + 1))) * charExt χ⁻¹ w ∂μ)
        = ((μ.real {y : v.adicCompletion K | Valued.v y ≤ WithZero.exp (-(0 : ℤ))} : ℝ) : ℂ)
              * {w : v.adicCompletion K | Valued.v (w + 1) ≤ WithZero.exp (-(a : ℤ))}.indicator
                  (charExt χ⁻¹) w
            - ((μ.real {y : v.adicCompletion K | Valued.v y ≤ WithZero.exp (-(1 : ℤ))} : ℝ) : ℂ)
              * {w : v.adicCompletion K | Valued.v (w + 1) ≤ WithZero.exp (-((a - 1 : ℕ) : ℤ))}.indicator
                  (charExt χ⁻¹) w := by
    intro w
    rw [integral_mul_const, setIntegral_units_addChar v μ ψ n hψn hψn' (t * (w + 1))]
    have h0 : Valued.v (t * (w + 1)) ≤ WithZero.exp (n + 0) ↔ Valued.v (w + 1) ≤ WithZero.exp (-(a : ℤ)) := by
      rw [map_mul, hvt]
      exact exp_mul_le_iff (by omega) _
    have h1 : Valued.v (t * (w + 1)) ≤ WithZero.exp (n + 1)
        ↔ Valued.v (w + 1) ≤ WithZero.exp (-((a - 1 : ℕ) : ℤ)) := by
      rw [map_mul, hvt]
      exact exp_mul_le_iff (by omega) _
    simp only [Set.indicator_apply, Set.mem_setOf_eq]
    by_cases hq0 : Valued.v (w + 1) ≤ WithZero.exp (-(a : ℤ)) <;>
      by_cases hq1 : Valued.v (w + 1) ≤ WithZero.exp (-((a - 1 : ℕ) : ℤ)) <;>
      simp only [h0, h1, hq0, hq1, if_true, if_false] <;> ring

  have hint : Integrable (charExt χ⁻¹) (μ.restrict {u : v.adicCompletion K | Valued.v u = 1}) :=
    integrableOn_charExt_units_set v μ hχ1
  have hBa : MeasurableSet {w : v.adicCompletion K | Valued.v (w + 1) ≤ WithZero.exp (-(a : ℤ))} :=
    (isClosed_add_one_ball v _).measurableSet
  have hBb : MeasurableSet {w : v.adicCompletion K | Valued.v (w + 1) ≤ WithZero.exp (-((a - 1 : ℕ) : ℤ))} :=
    (isClosed_add_one_ball v _).measurableSet
  have hneg : modulus (((-1 : (v.adicCompletion K)ˣ)) : v.adicCompletion K) = 1 := by
    rw [Units.val_neg, Units.val_one]
    exact modulus_eq_one_of_valued v (valued_neg_one v)
  have hsubA : (∫ w in {u : v.adicCompletion K | Valued.v u = 1}
          ∩ {w : v.adicCompletion K | Valued.v (w + 1) ≤ WithZero.exp (-(a : ℤ))}, charExt χ⁻¹ w ∂μ)
      = (χ⁻¹ (-1 : (v.adicCompletion K)ˣ) : ℂ) * ∫ y in {u : v.adicCompletion K | Valued.v u = 1}
          ∩ {x : v.adicCompletion K | Valued.v (x - 1) ≤ WithZero.exp (-(a : ℤ))}, charExt χ⁻¹ y ∂μ := by
    rw [setIntegral_comp_mul_left_of_modulus_eq_one μ hneg (charExt χ⁻¹) (hU0m.inter hBa),
      preimage_neg_one_mul v]
    simp_rw [charExt_units_mul]
    exact integral_const_mul _ _
  have hsubB : (∫ w in {u : v.adicCompletion K | Valued.v u = 1}
          ∩ {w : v.adicCompletion K | Valued.v (w + 1) ≤ WithZero.exp (-((a - 1 : ℕ) : ℤ))},
            charExt χ⁻¹ w ∂μ)
      = (χ⁻¹ (-1 : (v.adicCompletion K)ˣ) : ℂ) * ∫ y in {u : v.adicCompletion K | Valued.v u = 1}
          ∩ {x : v.adicCompletion K | Valued.v (x - 1) ≤ WithZero.exp (-((a - 1 : ℕ) : ℤ))},
            charExt χ⁻¹ y ∂μ := by
    rw [setIntegral_comp_mul_left_of_modulus_eq_one μ hneg (charExt χ⁻¹) (hU0m.inter hBb),
      preimage_neg_one_mul v]
    simp_rw [charExt_units_mul]
    exact integral_const_mul _ _
  rw [hAB, hC, setIntegral_congr_fun hU0m (fun w _ => hDE w),
    integral_sub ((hint.indicator hBa).const_mul _) ((hint.indicator hBb).const_mul _),
    integral_const_mul, integral_const_mul, setIntegral_indicator hBa, setIntegral_indicator hBb, hsubA, hsubB,
    setIntegral_charExt_ball v μ ha hχ1, setIntegral_charExt_inv_ball_pred_eq_zero v μ ha hχ, mul_zero, mul_zero,
    sub_zero]
  ring

theorem gauss_ne_zero [MeasurableSpace (v.adicCompletion K)] [BorelSpace (v.adicCompletion K)]
    (μ : Measure (v.adicCompletion K)) [μ.IsAddHaarMeasure] (ψ : AddChar (v.adicCompletion K) ℂ) (n : ℤ)
    (hψn : ∀ x : v.adicCompletion K, Valued.v x ≤ WithZero.exp n → ψ x = 1)
    (hψn' : ∃ x : v.adicCompletion K, Valued.v x ≤ WithZero.exp (n + 1) ∧ ψ x ≠ 1)
    {χ : (v.adicCompletion K)ˣ →* ℂˣ} {a : ℕ} (ha : 1 ≤ a) (hχ : HasConductorExponentAt K v χ a)
    {t : v.adicCompletion K} (hvt : Valued.v t = WithZero.exp (n + a)) :
    (∫ u in {u : v.adicCompletion K | Valued.v u = 1}, ψ (t * u) * charExt χ⁻¹ u ∂μ) ≠ 0 := by
  intro h0
  have h := gauss_mul_gauss v μ ψ n hψn hψn' ha hχ hvt
  rw [h0, zero_mul] at h
  have hc0 : ((μ.real {y : v.adicCompletion K | Valued.v y ≤ WithZero.exp (-(0 : ℤ))} : ℝ) : ℂ) ≠ 0 := by
    rw [Complex.ofReal_ne_zero, neg_zero]
    refine (measureReal_ne_zero_iff (isCompact_ball_zero v).measure_lt_top.ne).mpr ?_
    refine ((isOpen_ball v 0).measure_pos (μ := μ) ⟨0, ?_⟩).ne'
    show Valued.v (0 : v.adicCompletion K) ≤ WithZero.exp 0
    rw [map_zero]
    exact zero_le'
  have hSa : ((μ.real {x : v.adicCompletion K | Valued.v (x - 1) ≤ WithZero.exp (-(a : ℤ))} : ℝ) : ℂ) ≠ 0 := by
    rw [Complex.ofReal_ne_zero]
    have hfin : μ {x : v.adicCompletion K | Valued.v (x - 1) ≤ WithZero.exp (-(a : ℤ))} ≠ ⊤ :=
      ((measure_mono ((sub_one_ball_subset_units_set v ha).trans (units_set_subset_ball_zero v))).trans_lt
        (isCompact_ball_zero v).measure_lt_top).ne
    refine (measureReal_ne_zero_iff hfin).mpr ?_
    refine ((isOpen_sub_one_ball v _).measure_pos (μ := μ) ⟨1, ?_⟩).ne'
    show Valued.v ((1 : v.adicCompletion K) - 1) ≤ WithZero.exp (-(a : ℤ))
    rw [sub_self, map_zero]
    exact zero_le'
  exact mul_ne_zero (mul_ne_zero (Units.ne_zero _) hc0) hSa h.symm

theorem isAddHaarMeasure_selfDualHaarAt :
    letI := localBorel K v
    (selfDualHaarAt K v).IsAddHaarMeasure := by
  letI := localBorel K v
  haveI : BorelSpace (v.adicCompletion K) := borelSpace_localBorel K v
  set c : ℝ≥0 := (Ideal.absNorm v.asIdeal : ℝ≥0) ^ (-(addCharLevel (psiLocal K v) : ℝ) / 2) with hc
  have hc0 : c ≠ 0 := by
    rw [hc]
    exact (NNReal.rpow_pos (by exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr v.ne_bot))).ne'
  have hdef : selfDualHaarAt K v = (c : ℝ≥0∞) • Measure.addHaarMeasure (integersPositiveCompacts K v) := rfl
  rw [hdef]
  exact Measure.IsAddHaarMeasure.smul _ (by exact_mod_cast hc0) ENNReal.coe_ne_top

end Kv

end LanglandsTunnell.TateLocal.Ws47Ramified

end

section ShellSmall
open MeasureTheory IsDedekindDomain NumberField NumberField.AdelicLevel NumberField.StandardAddChar
p2m_open "LanglandsTunnell.TateLocal P2MW.S_LanglandsTunnell_TateLocal_tsum_mul_setIntegral_psiLocal_neg_mul_charExt_eq_mul_charExt_sq_mul_stdRootNumberAt_sq.LanglandsTunnell.TateLocal P2MW.S_LanglandsTunnell_TateLocal_tsum_mul_setIntegral_psiLocal_neg_mul_charExt_eq_mul_charExt_sq_mul_stdRootNumberAt_sq.LanglandsTunnell.TateLocal.Ws47Ramified"
open scoped NNReal ENNReal

variable {K : Type} [Field K] [NumberField K] (v : HeightOneSpectrum (𝓞 K))

theorem Ws47.setIntegral_units_addChar_mul_charExt_inv_eq_zero_of_lt
    [MeasurableSpace (v.adicCompletion K)] [BorelSpace (v.adicCompletion K)]
    (μ : Measure (v.adicCompletion K)) [μ.IsAddHaarMeasure] (ψ : AddChar (v.adicCompletion K) ℂ) (n : ℤ)
    (hψn : ∀ x : v.adicCompletion K, Valued.v x ≤ WithZero.exp n → ψ x = 1)
    {χ : (v.adicCompletion K)ˣ →* ℂˣ} {a : ℕ} (ha : 1 ≤ a) (hχ : HasConductorExponentAt K v χ a)
    {t : v.adicCompletion K} {k : ℤ} (hvt : Valued.v t = WithZero.exp k) (hk : k < n + a) :
    ∫ u in {u : v.adicCompletion K | Valued.v u = 1}, ψ (t * u) * charExt χ⁻¹ u ∂μ = 0 := by

  obtain ⟨u₁, hu₁, hu₁', hne⟩ :=
    exists_unit_of_hasConductorExponentAt v ha hχ (j := a - (k - n).toNat) (by omega)
  have hm : k - ((a - (a - (k - n).toNat) : ℕ) : ℤ) ≤ n := by
    have := Int.self_le_toNat (k - n)
    omega
  refine setIntegral_mul_charExt_eq_zero μ (measurableSet_units_set v) (fun y => ψ (t * y)) χ⁻¹
    (modulus_eq_one_of_valued v hu₁) hne (fun y => ?_) (fun y hy => ?_)
  ·
    simp only [Set.mem_setOf_eq, map_mul, hu₁, one_mul]
  ·
    have hy1 : Valued.v y = 1 := hy
    have hsplit : t * ((u₁ : v.adicCompletion K) * y) = t * y + t * ((u₁ : v.adicCompletion K) - 1) * y := by ring
    have hsmall : Valued.v (t * ((u₁ : v.adicCompletion K) - 1) * y) ≤ WithZero.exp n := by
      rw [map_mul, map_mul, hvt, hy1, mul_one]
      calc WithZero.exp k * Valued.v ((u₁ : v.adicCompletion K) - 1)
          ≤ WithZero.exp k * WithZero.exp (-((a - (a - (k - n).toNat) : ℕ) : ℤ)) := mul_le_mul_right hu₁' _
        _ = WithZero.exp (k + -((a - (a - (k - n).toNat) : ℕ) : ℤ)) := (WithZero.exp_add _ _).symm
        _ ≤ WithZero.exp n := WithZero.exp_le_exp.mpr (by omega)
    show ψ (t * ((u₁ : v.adicCompletion K) * y)) = ψ (t * y)
    rw [hsplit, AddChar.map_add_eq_mul, hψn _ hsmall, mul_one]

end ShellSmall

section ShellLarge
open MeasureTheory IsDedekindDomain NumberField NumberField.AdelicLevel NumberField.StandardAddChar
p2m_open "LanglandsTunnell.TateLocal P2MW.S_LanglandsTunnell_TateLocal_tsum_mul_setIntegral_psiLocal_neg_mul_charExt_eq_mul_charExt_sq_mul_stdRootNumberAt_sq.LanglandsTunnell.TateLocal P2MW.S_LanglandsTunnell_TateLocal_tsum_mul_setIntegral_psiLocal_neg_mul_charExt_eq_mul_charExt_sq_mul_stdRootNumberAt_sq.LanglandsTunnell.TateLocal.Ws47Ramified"
open scoped NNReal ENNReal

variable {K : Type} [Field K] [NumberField K] (v : HeightOneSpectrum (𝓞 K))

theorem Ws47.setIntegral_units_addChar_mul_charExt_inv_eq_zero_of_le
    [MeasurableSpace (v.adicCompletion K)] [BorelSpace (v.adicCompletion K)]
    (μ : Measure (v.adicCompletion K)) [μ.IsAddHaarMeasure] (ψ : AddChar (v.adicCompletion K) ℂ) (n : ℤ)
    (hψn' : ∃ x : v.adicCompletion K, Valued.v x ≤ WithZero.exp (n + 1) ∧ ψ x ≠ 1)
    {χ : (v.adicCompletion K)ˣ →* ℂˣ} {a : ℕ} (ha : 1 ≤ a) (hχ1 : ∀ u ∈ higherUnitsAt K v a, χ u = 1)
    {t : v.adicCompletion K} {k : ℤ} (hvt : Valued.v t = WithZero.exp k) (hk : n + a + 1 ≤ k) :
    ∫ u in {u : v.adicCompletion K | Valued.v u = 1}, ψ (t * u) * charExt χ⁻¹ u ∂μ = 0 := by
  obtain ⟨x, hx, hψx⟩ := hψn'
  have ht0 : t ≠ 0 := by
    intro h; rw [h, map_zero] at hvt; exact WithZero.coe_ne_zero hvt.symm
  set z : v.adicCompletion K := x / t with hz
  have htz : t * z = x := by rw [hz, mul_div_cancel₀ _ ht0]
  have hvz : Valued.v z ≤ WithZero.exp (-(a : ℤ)) := by
    rw [hz, map_div₀, hvt, div_eq_mul_inv, ← WithZero.exp_neg]
    calc Valued.v x * WithZero.exp (-k)
        ≤ WithZero.exp (n + 1) * WithZero.exp (-k) := by gcongr
      _ = WithZero.exp (n + 1 + -k) := (WithZero.exp_add _ _).symm
      _ ≤ WithZero.exp (-(a : ℤ)) := WithZero.exp_le_exp.mpr (by omega)
  have hvz1 : Valued.v z < 1 := by
    refine lt_of_le_of_lt hvz ?_
    rw [← WithZero.exp_zero, WithZero.exp_lt_exp]; omega

  set S : Set (v.adicCompletion K) := {u | Valued.v u = 1} with hS
  have hSm : MeasurableSet S := measurableSet_units_set v
  have hmemS : ∀ u : v.adicCompletion K, u + z ∈ S ↔ u ∈ S := by
    intro u
    simp only [hS, Set.mem_setOf_eq]
    constructor
    · intro h
      have : u = (u + z) + (-z) := by ring
      rw [this]
      refine le_antisymm ?_ ?_
      · refine (Valuation.map_add _ _ _).trans ?_
        rw [h, Valuation.map_neg, max_eq_left hvz1.le]
      ·
        by_contra hlt
        push Not at hlt
        have h1 : Valued.v ((u + z + -z) + z) ≤ max (Valued.v (u + z + -z)) (Valued.v z) := Valuation.map_add _ _ _
        rw [show u + z + -z + z = u + z by ring, h] at h1
        exact absurd h1 (not_le.mpr (max_lt hlt hvz1))
    · intro h
      rw [Valuation.map_add_eq_of_lt_left _ (by rwa [h]), h]
  have hchar : ∀ u ∈ S, charExt χ⁻¹ (u + z) = charExt χ⁻¹ u := by
    intro u hu
    have hu1 : Valued.v u = 1 := hu
    have hu0 : u ≠ 0 := by intro h; rw [h, map_zero] at hu1; exact zero_ne_one hu1
    have he1 : Valued.v (1 + z / u) = 1 := by
      rw [Valuation.map_add_eq_of_lt_left _ ?_, map_one]
      rw [map_one, map_div₀, hu1, div_one]; exact hvz1
    have he0 : (1 + z / u) ≠ 0 := by intro h; rw [h, map_zero] at he1; exact zero_ne_one he1
    have hmem : Units.mk0 (1 + z / u) he0 ∈ higherUnitsAt K v a := by
      refine (mem_higherUnitsAt_iff K v).mpr ⟨he1, Or.inr ?_⟩
      show Valued.v ((1 + z / u) - 1) ≤ WithZero.exp (-(a : ℤ))
      rw [add_sub_cancel_left, map_div₀, hu1, div_one]; exact hvz
    have hsplit : u + z = ((Units.mk0 (1 + z / u) he0 : (v.adicCompletion K)ˣ) : v.adicCompletion K) * u := by
      rw [Units.val_mk0]; field_simp
    rw [hsplit, charExt_units_mul, MonoidHom.inv_apply, hχ1 _ hmem, inv_one, Units.val_one, one_mul]

  set F : v.adicCompletion K → ℂ := fun u => ψ (t * u) * charExt χ⁻¹ u with hF
  have hI : ∫ u in S, F u ∂μ = ψ x * ∫ u in S, F u ∂μ := by
    calc ∫ u in S, F u ∂μ = ∫ u, S.indicator F u ∂μ := (integral_indicator hSm).symm
      _ = ∫ u, S.indicator F (u + z) ∂μ := (integral_add_right_eq_self _ z).symm
      _ = ∫ u, S.indicator (fun u => ψ x * F u) u ∂μ := by
          congr 1; funext u
          by_cases hu : u ∈ S
          · rw [Set.indicator_of_mem ((hmemS u).mpr hu), Set.indicator_of_mem hu, hF]
            simp only
            rw [mul_add, htz, AddChar.map_add_eq_mul, hchar u hu]; ring
          · rw [Set.indicator_of_notMem (fun h => hu ((hmemS u).mp h)), Set.indicator_of_notMem hu]
      _ = ψ x * ∫ u in S, F u ∂μ := by rw [integral_indicator hSm, integral_const_mul]
  have : (1 - ψ x) * ∫ u in S, F u ∂μ = 0 := by linear_combination hI
  rcases mul_eq_zero.mp this with h | h
  · exact absurd (sub_eq_zero.mp h).symm hψx
  · exact h

end ShellLarge

open MeasureTheory IsDedekindDomain NumberField NumberField.StandardAddChar
p2m_open "LanglandsTunnell.TateLocal P2MW.S_LanglandsTunnell_TateLocal_tsum_mul_setIntegral_psiLocal_neg_mul_charExt_eq_mul_charExt_sq_mul_stdRootNumberAt_sq.LanglandsTunnell.TateLocal P2MW.S_LanglandsTunnell_TateLocal_tsum_mul_setIntegral_psiLocal_neg_mul_charExt_eq_mul_charExt_sq_mul_stdRootNumberAt_sq.LanglandsTunnell.TateLocal.Ws47Ramified"

namespace Ws47
namespace Shell

variable {K : Type} [Field K] [NumberField K] (v : HeightOneSpectrum (𝓞 K))

theorem hasConductorExponentAt_of_eq_inv {χ χ' : (v.adicCompletion K)ˣ →* ℂˣ} {f : ℕ}
    (hχ : HasConductorExponentAt K v χ f)
    (hχ' : ∀ u : (v.adicCompletion K)ˣ, Valued.v (u : v.adicCompletion K) = 1 → χ' u = (χ u)⁻¹) :
    HasConductorExponentAt K v χ' f := by
  refine ⟨fun u hu => ?_, fun m hm => ?_⟩
  · rw [hχ' u hu.1, hχ.1 u hu, inv_one]
  · obtain ⟨u, hu, hne⟩ := hχ.2 m hm
    exact ⟨u, hu, by rw [hχ' u hu.1]; exact fun h => hne (inv_eq_one.mp h)⟩

private theorem _root_.Ws47.Shell.valued_zpow_mul (ϖ : v.adicCompletionIntegers K)
    (hϖ : Valued.v (algebraMap (v.adicCompletionIntegers K) (v.adicCompletion K) ϖ) = WithZero.exp (-1 : ℤ))
    {y : v.adicCompletion K} {e : ℤ} (hy : Valued.v y = WithZero.exp e) (m : ℤ) :
    Valued.v (algebraMap (v.adicCompletionIntegers K) (v.adicCompletion K) ϖ ^ m * y) = WithZero.exp (e - m) := by
  rw [map_mul, map_zpow₀, hϖ, hy, ← WithZero.exp_zsmul, ← WithZero.exp_add]
  congr 1
  simp only [smul_eq_mul, mul_neg, mul_one]
  ring

p2m_export "Ws47.Shell" "valued_zpow_mul"

private theorem _root_.Ws47.Shell.tsum_shell_eq_single [MeasurableSpace (v.adicCompletion K)] [BorelSpace (v.adicCompletion K)]
    (μ : Measure (v.adicCompletion K)) [μ.IsAddHaarMeasure] (ψ : AddChar (v.adicCompletion K) ℂ) (n : ℤ)
    (hψn : ∀ x : v.adicCompletion K, Valued.v x ≤ WithZero.exp n → ψ x = 1)
    (hψn' : ∃ x : v.adicCompletion K, Valued.v x ≤ WithZero.exp (n + 1) ∧ ψ x ≠ 1)
    (η : (v.adicCompletion K)ˣ →* ℂˣ) (f : ℕ) (hf : 1 ≤ f) (hη : HasConductorExponentAt K v η f)
    (ϖ : v.adicCompletionIntegers K)
    (hϖ : Valued.v (algebraMap (v.adicCompletionIntegers K) (v.adicCompletion K) ϖ) = WithZero.exp (-1 : ℤ))
    (y : v.adicCompletion K) (e : ℤ) (hy : Valued.v y = WithZero.exp e) (a : ℤ → ℂ) (τ : ℂ) :
    (∑' m : ℤ, a m * τ ^ m *
        ((∫ u in {u : v.adicCompletion K | Valued.v u = 1},
            ψ (algebraMap (v.adicCompletionIntegers K) (v.adicCompletion K) ϖ ^ m * y * u) * charExt η u ∂μ)
          / ((μ.real {u : v.adicCompletion K | Valued.v u = 1} : ℝ) : ℂ)))
      = a (e - n - f) * τ ^ (e - n - f) *
        ((∫ u in {u : v.adicCompletion K | Valued.v u = 1},
            ψ (algebraMap (v.adicCompletionIntegers K) (v.adicCompletion K) ϖ ^ (e - n - f) * y * u) * charExt η u ∂μ)
          / ((μ.real {u : v.adicCompletion K | Valued.v u = 1} : ℝ) : ℂ)) := by
  refine tsum_eq_single (e - n - f) fun m hm => ?_
  have hval : Valued.v (algebraMap (v.adicCompletionIntegers K) (v.adicCompletion K) ϖ ^ m * y)
      ≠ WithZero.exp (n + f) := by
    rw [valued_zpow_mul v ϖ hϖ hy m]
    intro h
    have := WithZero.exp_injective h
    omega
  rw [LanglandsTunnell.TateLocal.setIntegral_addChar_mul_charExt_eq_zero_of_valued_ne K v μ ψ n hψn hψn' η f hf hη
    _ hval, zero_div, mul_zero]

p2m_export "Ws47.Shell" "tsum_shell_eq_single"

theorem setIntegral_units_neg_mul [MeasurableSpace (v.adicCompletion K)] [BorelSpace (v.adicCompletion K)]
    (μ : Measure (v.adicCompletion K)) [μ.IsAddHaarMeasure] (ψ : AddChar (v.adicCompletion K) ℂ)
    (χ' : (v.adicCompletion K)ˣ →* ℂˣ) (c : v.adicCompletion K) :
    (∫ u in {u : v.adicCompletion K | Valued.v u = 1}, ψ (-c * u) * charExt χ' u ∂μ)
      = ((χ' (-1) : ℂˣ) : ℂ) * ∫ u in {u : v.adicCompletion K | Valued.v u = 1}, ψ (c * u) * charExt χ' u ∂μ := by
  have hmod : modulus (((-1 : (v.adicCompletion K)ˣ) : (v.adicCompletion K)ˣ) : v.adicCompletion K) = 1 := by
    rw [Units.val_neg, Units.val_one]
    exact modulus_eq_one_of_valued v (valued_neg_one v)

  rw [setIntegral_comp_mul_left_of_modulus_eq_one μ hmod (fun u => ψ (c * u) * charExt χ' u)
      (measurableSet_units_set v)]
  rw [Units.val_neg, Units.val_one, preimage_mul_units_set v (valued_neg_one v), ← integral_const_mul]
  have hsq : ((χ' (-1) : ℂˣ) : ℂ) ^ 2 = 1 := by
    rw [← Units.val_pow_eq_pow_val, ← map_pow, neg_one_sq, map_one, Units.val_one]
  refine setIntegral_congr_fun (measurableSet_units_set v) fun u _ => ?_
  have hneg : charExt χ' ((-1 : v.adicCompletion K) * u) = ((χ' (-1) : ℂˣ) : ℂ) * charExt χ' u := by
    have := charExt_units_mul χ' (-1) u
    rwa [Units.val_neg, Units.val_one] at this
  show ψ (-c * u) * charExt χ' u = ((χ' (-1) : ℂˣ) : ℂ) * (ψ (c * (-1 * u)) * charExt χ' (-1 * u))
  rw [hneg, show c * (-1 * u) = -c * u by ring,
    show ((χ' (-1) : ℂˣ) : ℂ) * (ψ (-c * u) * (((χ' (-1) : ℂˣ) : ℂ) * charExt χ' u))
      = ((χ' (-1) : ℂˣ) : ℂ) ^ 2 * (ψ (-c * u) * charExt χ' u) by ring, hsq, one_mul]

theorem chi'_neg_one_mul_charExt_neg_one {χ χ' : (v.adicCompletion K)ˣ →* ℂˣ}
    (hχ' : ∀ u : (v.adicCompletion K)ˣ, Valued.v (u : v.adicCompletion K) = 1 → χ' u = (χ u)⁻¹) :
    ((χ' (-1) : ℂˣ) : ℂ) * charExt χ (-1) = 1 := by
  have hm1 : (-1 : v.adicCompletion K) ≠ 0 := neg_ne_zero.mpr one_ne_zero
  have hu : Units.mk0 (-1 : v.adicCompletion K) hm1 = -1 := Units.ext rfl
  have hval : Valued.v (((-1 : (v.adicCompletion K)ˣ)) : v.adicCompletion K) = 1 := by
    rw [Units.val_neg, Units.val_one]; exact valued_neg_one v
  rw [charExt_of_ne_zero χ hm1, hu, hχ' _ hval, ← Units.val_mul, inv_mul_cancel, Units.val_one]

theorem gauss_mul_gauss_neg [MeasurableSpace (v.adicCompletion K)] [BorelSpace (v.adicCompletion K)]
    (μ : Measure (v.adicCompletion K)) [μ.IsAddHaarMeasure] (ψ : AddChar (v.adicCompletion K) ℂ) (n : ℤ)
    (hψn : ∀ x : v.adicCompletion K, Valued.v x ≤ WithZero.exp n → ψ x = 1)
    (hψn' : ∃ x : v.adicCompletion K, Valued.v x ≤ WithZero.exp (n + 1) ∧ ψ x ≠ 1)
    (χ : (v.adicCompletion K)ˣ →* ℂˣ) (f : ℕ) (hf : 1 ≤ f) (hχ : HasConductorExponentAt K v χ f)
    (χ' : (v.adicCompletion K)ˣ →* ℂˣ)
    (hχ' : ∀ u : (v.adicCompletion K)ˣ, Valued.v (u : v.adicCompletion K) = 1 → χ' u = (χ u)⁻¹)
    (c : v.adicCompletion K) (hc : Valued.v c = WithZero.exp (n + f)) :
    (∫ u in {u : v.adicCompletion K | Valued.v u = 1}, ψ (c * u) * charExt χ u ∂μ) *
        (∫ u in {u : v.adicCompletion K | Valued.v u = 1}, ψ (-c * u) * charExt χ' u ∂μ) *
        (Ideal.absNorm v.asIdeal : ℂ) ^ f
      = ((μ.real (v.adicCompletionIntegers K : Set (v.adicCompletion K)) : ℝ) : ℂ) ^ 2 := by

  have hagree : (∫ u in {u : v.adicCompletion K | Valued.v u = 1}, ψ (c * u) * charExt χ' u ∂μ)
      = ∫ u in {u : v.adicCompletion K | Valued.v u = 1}, ψ (c * u) * charExt χ⁻¹ u ∂μ := by
    refine setIntegral_congr_fun (measurableSet_units_set v) fun u hu => ?_
    have hu0 : u ≠ 0 := (Valuation.ne_zero_iff _).mp (by rw [hu]; exact one_ne_zero)
    rw [charExt_of_ne_zero χ' hu0, charExt_of_ne_zero χ⁻¹ hu0, MonoidHom.inv_apply,
      hχ' _ (by rw [Units.val_mk0]; exact hu)]
  have hrow := LanglandsTunnell.TateLocal.setIntegral_addChar_mul_charExt_mul_setIntegral_inv_mul_pow_eq
    K v μ ψ n hψn hψn' χ f hf hχ c hc
  rw [setIntegral_units_neg_mul v μ ψ χ' c, hagree]
  calc (∫ u in {u : v.adicCompletion K | Valued.v u = 1}, ψ (c * u) * charExt χ u ∂μ) *
        (((χ' (-1) : ℂˣ) : ℂ) * ∫ u in {u : v.adicCompletion K | Valued.v u = 1}, ψ (c * u) * charExt χ⁻¹ u ∂μ) *
        (Ideal.absNorm v.asIdeal : ℂ) ^ f
      = ((χ' (-1) : ℂˣ) : ℂ) *
          ((∫ u in {u : v.adicCompletion K | Valued.v u = 1}, ψ (c * u) * charExt χ u ∂μ) *
            (∫ u in {u : v.adicCompletion K | Valued.v u = 1}, ψ (c * u) * charExt χ⁻¹ u ∂μ) *
            (Ideal.absNorm v.asIdeal : ℂ) ^ f) := by ring
    _ = ((χ' (-1) : ℂˣ) : ℂ) * (charExt χ (-1) *
          ((μ.real (v.adicCompletionIntegers K : Set (v.adicCompletion K)) : ℝ) : ℂ) ^ 2) := by rw [hrow]
    _ = (((χ' (-1) : ℂˣ) : ℂ) * charExt χ (-1)) *
          ((μ.real (v.adicCompletionIntegers K : Set (v.adicCompletion K)) : ℝ) : ℂ) ^ 2 := by ring
    _ = _ := by rw [chi'_neg_one_mul_charExt_neg_one v hχ', one_mul]

end Ws47.Shell

namespace LanglandsTunnell
p2m_export "LanglandsTunnell" "TateLocal.forall_eq_one_and_exists_ne_one_of_addCharLevel TateLocal.psiLocal_eq_one_of_mem_integers TateLocal.psiLocal_ne_one TateLocal.setIntegral_addChar_mul_charExt_eq_zero_of_valued_ne TateLocal.setIntegral_addChar_mul_charExt_mul_setIntegral_inv_mul_pow_eq TateLocal.localZeta_tateFourier_stdTestFunAt TateLocal.localZeta_stdTestFunAt_eq_real_image_higherUnitsAt TateLocal.selfDualHaarAt_real_image_higherUnitsAt TateLocal.selfDualHaarAt_real_integers_mul_real_setOf_valued_le_exp_addCharLevel TateLocal.measureReal_setOf_valued_le_exp"
namespace TateLocal
p2m_export "LanglandsTunnell.TateLocal" "addCharLevel localBorel borelSpace_localBorel integersPositiveCompacts selfDualHaarAt stdTestFunAt stdRootNumberAt higherUnitsAt mem_higherUnitsAt_iff HasConductorExponentAt hasConductorExponentAt_unique localEpsilonAt localEpsilonAt_of_not_hasConductorExponentAt_zero modulus modulus_coe_units tateFourier charExt charExt_zero charExt_of_ne_zero localGammaAt tateFourier_indicator_setOf_valued_sub_le modulus_adicCompletion_eq_nnnorm forall_eq_one_and_exists_ne_one_of_addCharLevel psiLocal_eq_one_of_mem_integers psiLocal_ne_one setIntegral_addChar_mul_charExt_eq_zero_of_valued_ne setIntegral_addChar_mul_charExt_mul_setIntegral_inv_mul_pow_eq localZeta_tateFourier_stdTestFunAt localZeta_stdTestFunAt_eq_real_image_higherUnitsAt selfDualHaarAt_real_image_higherUnitsAt selfDualHaarAt_real_integers_mul_real_setOf_valued_le_exp_addCharLevel measureReal_setOf_valued_le_exp"
namespace Ws47Shell
p2m_open "LanglandsTunnell.TateLocal LanglandsTunnell"

open MeasureTheory IsDedekindDomain NumberField NumberField.StandardAddChar
p2m_open "LanglandsTunnell.TateLocal P2MW.S_LanglandsTunnell_TateLocal_tsum_mul_setIntegral_psiLocal_neg_mul_charExt_eq_mul_charExt_sq_mul_stdRootNumberAt_sq.LanglandsTunnell.TateLocal P2MW.S_LanglandsTunnell_TateLocal_tsum_mul_setIntegral_psiLocal_neg_mul_charExt_eq_mul_charExt_sq_mul_stdRootNumberAt_sq.LanglandsTunnell.TateLocal.Ws47Ramified"
open scoped NNReal ENNReal

variable {K : Type} [Field K] [NumberField K] (v : HeightOneSpectrum (𝓞 K))

theorem psiLocal_level_data :
    (∀ x : v.adicCompletion K, Valued.v x ≤ WithZero.exp (addCharLevel (psiLocal K v)) → psiLocal K v x = 1) ∧
      ∃ x : v.adicCompletion K, Valued.v x ≤ WithZero.exp (addCharLevel (psiLocal K v) + 1) ∧ psiLocal K v x ≠ 1 :=
  LanglandsTunnell.TateLocal.forall_eq_one_and_exists_ne_one_of_addCharLevel K v (psiLocal K v)
    ⟨0, fun x hx => LanglandsTunnell.TateLocal.psiLocal_eq_one_of_mem_integers K v x
      ((HeightOneSpectrum.mem_adicCompletionIntegers (𝓞 K) K v).mpr (by simpa using hx))⟩
    (LanglandsTunnell.TateLocal.psiLocal_ne_one K v)

private theorem _root_.LanglandsTunnell.TateLocal.Ws47Shell.tsum_shell_eq_single (η : (v.adicCompletion K)ˣ →* ℂˣ) (f : ℕ) (hf : 1 ≤ f)
    (hη : HasConductorExponentAt K v η f)
    (ϖ : v.adicCompletionIntegers K)
    (hϖ : Valued.v (algebraMap (v.adicCompletionIntegers K) (v.adicCompletion K) ϖ) = WithZero.exp (-1 : ℤ))
    (y : v.adicCompletion K) (e : ℤ) (hy : Valued.v y = WithZero.exp e) (a : ℤ → ℂ) (t : ℂ) :
    letI := localBorel K v
    (∑' m : ℤ, a m * t ^ m *
        ((∫ u in {u : v.adicCompletion K | Valued.v u = 1},
            psiLocal K v (algebraMap (v.adicCompletionIntegers K) (v.adicCompletion K) ϖ ^ m * y * u)
              * charExt η u ∂(selfDualHaarAt K v))
          / (((selfDualHaarAt K v).real {u : v.adicCompletion K | Valued.v u = 1} : ℝ) : ℂ)))
      = a (e - addCharLevel (psiLocal K v) - f) * t ^ (e - addCharLevel (psiLocal K v) - f) *
        ((∫ u in {u : v.adicCompletion K | Valued.v u = 1},
            psiLocal K v (algebraMap (v.adicCompletionIntegers K) (v.adicCompletion K) ϖ
                ^ (e - addCharLevel (psiLocal K v) - f) * y * u)
              * charExt η u ∂(selfDualHaarAt K v))
          / (((selfDualHaarAt K v).real {u : v.adicCompletion K | Valued.v u = 1} : ℝ) : ℂ)) := by
  letI := localBorel K v
  haveI : BorelSpace (v.adicCompletion K) := borelSpace_localBorel K v
  haveI := isAddHaarMeasure_selfDualHaarAt v
  obtain ⟨hψn, hψn'⟩ := psiLocal_level_data v
  exact Ws47.Shell.tsum_shell_eq_single v (selfDualHaarAt K v) (psiLocal K v) _ hψn hψn' η f hf hη ϖ hϖ y e hy a t

p2m_export "LanglandsTunnell.TateLocal.Ws47Shell" "tsum_shell_eq_single"

theorem setIntegral_units_charExt_congr [MeasurableSpace (v.adicCompletion K)] [BorelSpace (v.adicCompletion K)]
    (μ : Measure (v.adicCompletion K)) (χ χ' : (v.adicCompletion K)ˣ →* ℂˣ)
    (hχ' : ∀ u : (v.adicCompletion K)ˣ, Valued.v (u : v.adicCompletion K) = 1 → χ' u = (χ u)⁻¹)
    (Φ : v.adicCompletion K → ℂ) :
    ∫ u in {u : v.adicCompletion K | Valued.v u = 1}, Φ u * charExt χ' u ∂μ = ∫ u in {u : v.adicCompletion K | Valued.v u = 1}, Φ u * charExt χ⁻¹ u ∂μ := by
  refine setIntegral_congr_fun (measurableSet_units_set v) fun u hu => ?_
  have hu0 : u ≠ 0 := (Valuation.ne_zero_iff _).mp (by rw [hu]; exact one_ne_zero)
  show Φ u * charExt χ' u = Φ u * charExt χ⁻¹ u
  rw [charExt_of_ne_zero χ' hu0, charExt_of_ne_zero χ⁻¹ hu0, MonoidHom.inv_apply,
    hχ' _ (by rw [Units.val_mk0]; exact hu)]

theorem setIntegral_units_comp_neg [MeasurableSpace (v.adicCompletion K)] [BorelSpace (v.adicCompletion K)]
    (μ : Measure (v.adicCompletion K)) [μ.IsAddHaarMeasure] (η : (v.adicCompletion K)ˣ →* ℂˣ)
    (Φ : v.adicCompletion K → ℂ) :
    ∫ u in {u : v.adicCompletion K | Valued.v u = 1}, Φ (-u) * charExt η u ∂μ = charExt η (-1) * ∫ u in {u : v.adicCompletion K | Valued.v u = 1}, Φ u * charExt η u ∂μ := by
  have hmod : modulus (((-1 : (v.adicCompletion K)ˣ) : (v.adicCompletion K)ˣ) : v.adicCompletion K) = 1 := by
    rw [Units.val_neg, Units.val_one]
    exact modulus_eq_one_of_valued v (valued_neg_one v)
  have hm1 : (-1 : v.adicCompletion K) ≠ 0 := neg_ne_zero.mpr one_ne_zero
  have hu1 : Units.mk0 (-1 : v.adicCompletion K) hm1 = -1 := Units.ext rfl
  have hce : charExt η (-1) = ((η (-1) : ℂˣ) : ℂ) := by rw [charExt_of_ne_zero η hm1, hu1]
  have hsq : ((η (-1) : ℂˣ) : ℂ) ^ 2 = 1 := by
    rw [← Units.val_pow_eq_pow_val, ← map_pow, neg_one_sq, map_one, Units.val_one]
  rw [setIntegral_comp_mul_left_of_modulus_eq_one μ hmod (fun u => Φ (-u) * charExt η u)
      (measurableSet_units_set v)]
  rw [Units.val_neg, Units.val_one, preimage_mul_units_set v (valued_neg_one v), ← integral_const_mul]
  refine setIntegral_congr_fun (measurableSet_units_set v) fun u _ => ?_
  have hneg : charExt η ((-1 : v.adicCompletion K) * u) = ((η (-1) : ℂˣ) : ℂ) * charExt η u := by
    have := charExt_units_mul η (-1) u
    rwa [Units.val_neg, Units.val_one] at this
  show Φ (-(-1 * u)) * charExt η (-1 * u) = charExt η (-1) * (Φ u * charExt η u)
  rw [hneg, hce, show -(-1 * u) = u by ring]
  ring

theorem gauss_product_selfDual (χ : (v.adicCompletion K)ˣ →* ℂˣ) (f : ℕ) (hf : 1 ≤ f)
    (hχ : HasConductorExponentAt K v χ f) (c : v.adicCompletion K)
    (hc : Valued.v c = WithZero.exp (addCharLevel (psiLocal K v) + f)) :
    letI := localBorel K v
    (∫ u in {u : v.adicCompletion K | Valued.v u = 1}, psiLocal K v (c * u) * charExt χ u ∂(selfDualHaarAt K v)) *
          (∫ u in {u : v.adicCompletion K | Valued.v u = 1}, psiLocal K v (c * u) * charExt χ⁻¹ u ∂(selfDualHaarAt K v)) *
        (Ideal.absNorm v.asIdeal : ℂ) ^ f =
      charExt χ (-1) *
        (((selfDualHaarAt K v).real (v.adicCompletionIntegers K : Set (v.adicCompletion K)) : ℝ) : ℂ) ^ 2 := by
  letI := localBorel K v
  haveI : BorelSpace (v.adicCompletion K) := borelSpace_localBorel K v
  haveI := isAddHaarMeasure_selfDualHaarAt v
  obtain ⟨hψn, hψn'⟩ := psiLocal_level_data v
  exact LanglandsTunnell.TateLocal.setIntegral_addChar_mul_charExt_mul_setIntegral_inv_mul_pow_eq
    K v (selfDualHaarAt K v) (psiLocal K v) _ hψn hψn' χ f hf hχ c hc

private theorem _root_.LanglandsTunnell.TateLocal.Ws47Shell.hasConductorExponentAt_of_eq_inv {χ χ' : (v.adicCompletion K)ˣ →* ℂˣ} {f : ℕ}
    (hχ : HasConductorExponentAt K v χ f)
    (hχ' : ∀ u : (v.adicCompletion K)ˣ, Valued.v (u : v.adicCompletion K) = 1 → χ' u = (χ u)⁻¹) :
    HasConductorExponentAt K v χ' f :=
  Ws47.Shell.hasConductorExponentAt_of_eq_inv v hχ hχ'

p2m_export "LanglandsTunnell.TateLocal.Ws47Shell" "hasConductorExponentAt_of_eq_inv"
theorem hasConductorExponentAt_inv_e2 {χ : (v.adicCompletion K)ˣ →* ℂˣ} {f : ℕ}
    (hχ : HasConductorExponentAt K v χ f) : HasConductorExponentAt K v χ⁻¹ f :=
  Ws47.Shell.hasConductorExponentAt_of_eq_inv v hχ fun u _ => by rw [MonoidHom.inv_apply]

end LanglandsTunnell.TateLocal.Ws47Shell

namespace LanglandsTunnell
p2m_export "LanglandsTunnell" "TateLocal.forall_eq_one_and_exists_ne_one_of_addCharLevel TateLocal.psiLocal_eq_one_of_mem_integers TateLocal.psiLocal_ne_one TateLocal.setIntegral_addChar_mul_charExt_eq_zero_of_valued_ne TateLocal.setIntegral_addChar_mul_charExt_mul_setIntegral_inv_mul_pow_eq TateLocal.localZeta_tateFourier_stdTestFunAt TateLocal.localZeta_stdTestFunAt_eq_real_image_higherUnitsAt TateLocal.selfDualHaarAt_real_image_higherUnitsAt TateLocal.selfDualHaarAt_real_integers_mul_real_setOf_valued_le_exp_addCharLevel TateLocal.measureReal_setOf_valued_le_exp"
namespace TateLocal
p2m_export "LanglandsTunnell.TateLocal" "addCharLevel localBorel borelSpace_localBorel integersPositiveCompacts selfDualHaarAt stdTestFunAt stdRootNumberAt higherUnitsAt mem_higherUnitsAt_iff HasConductorExponentAt hasConductorExponentAt_unique localEpsilonAt localEpsilonAt_of_not_hasConductorExponentAt_zero modulus modulus_coe_units tateFourier charExt charExt_zero charExt_of_ne_zero localGammaAt tateFourier_indicator_setOf_valued_sub_le modulus_adicCompletion_eq_nnnorm forall_eq_one_and_exists_ne_one_of_addCharLevel psiLocal_eq_one_of_mem_integers psiLocal_ne_one setIntegral_addChar_mul_charExt_eq_zero_of_valued_ne setIntegral_addChar_mul_charExt_mul_setIntegral_inv_mul_pow_eq localZeta_tateFourier_stdTestFunAt localZeta_stdTestFunAt_eq_real_image_higherUnitsAt selfDualHaarAt_real_image_higherUnitsAt selfDualHaarAt_real_integers_mul_real_setOf_valued_le_exp_addCharLevel measureReal_setOf_valued_le_exp"
namespace Ws47Shell
p2m_open "LanglandsTunnell.TateLocal LanglandsTunnell"

p2m_open "LanglandsTunnell.TateLocal P2MW.S_LanglandsTunnell_TateLocal_tsum_mul_setIntegral_psiLocal_neg_mul_charExt_eq_mul_charExt_sq_mul_stdRootNumberAt_sq.LanglandsTunnell.TateLocal P2MW.S_LanglandsTunnell_TateLocal_tsum_mul_setIntegral_psiLocal_neg_mul_charExt_eq_mul_charExt_sq_mul_stdRootNumberAt_sq.LanglandsTunnell.TateLocal.Ws47Ramified"
open scoped NNReal ENNReal

variable {K : Type} [Field K] [NumberField K] (v : HeightOneSpectrum (𝓞 K))

theorem setIntegral_units_comp_mul_unit [MeasurableSpace (v.adicCompletion K)] [BorelSpace (v.adicCompletion K)]
    (μ : Measure (v.adicCompletion K)) [μ.IsAddHaarMeasure] (η : (v.adicCompletion K)ˣ →* ℂˣ)
    (w : v.adicCompletion K) (hw : Valued.v w = 1) (Φ : v.adicCompletion K → ℂ) :
    ∫ u in {u : v.adicCompletion K | Valued.v u = 1}, Φ (w * u) * charExt η u ∂μ = (charExt η w)⁻¹ * ∫ u in {u : v.adicCompletion K | Valued.v u = 1}, Φ u * charExt η u ∂μ := by
  have hw0 : w ≠ 0 := fun h => by rw [h, map_zero] at hw; exact zero_ne_one hw
  obtain ⟨wu, rfl⟩ : ∃ wu : (v.adicCompletion K)ˣ, (wu : v.adicCompletion K) = w := ⟨Units.mk0 w hw0, Units.val_mk0 hw0⟩
  have hmod : modulus (wu : v.adicCompletion K) = 1 := modulus_eq_one_of_valued v hw
  have key := setIntegral_comp_mul_left_of_modulus_eq_one μ hmod (fun y => Φ y * charExt η y)
    (measurableSet_units_set v)
  rw [preimage_mul_units_set v hw] at key

  have e : (fun y => Φ ((wu : v.adicCompletion K) * y) * charExt η ((wu : v.adicCompletion K) * y)) =
      fun y => (η wu : ℂ) * (Φ ((wu : v.adicCompletion K) * y) * charExt η y) := by
    funext y; rw [charExt_units_mul]; ring
  rw [e, integral_const_mul] at key
  have hne : (η wu : ℂ) ≠ 0 := Units.ne_zero _
  rw [charExt_of_ne_zero η wu.ne_zero, show Units.mk0 (wu : v.adicCompletion K) wu.ne_zero = wu from Units.mk0_val wu wu.ne_zero,
    key, ← mul_assoc, inv_mul_cancel₀ hne, one_mul]

theorem stdRootNumberAt_eq (χ : (v.adicCompletion K)ˣ →* ℂˣ) (f : ℕ) (hf : 1 ≤ f)
    (hχ : HasConductorExponentAt K v χ f)
    (hs : ‖(χ⁻¹ (uniformizerUnit K v) : ℂ) * (Ideal.absNorm v.asIdeal : ℂ) ^ (-(1 - (1 / 2 : ℂ)))‖ < 1) :
    letI := localBorel K v
    stdRootNumberAt K v χ
      = (χ (uniformizerUnit K v) : ℂ) ^ (addCharLevel (psiLocal K v) + f : ℤ)
          * ((((Ideal.absNorm v.asIdeal : ℝ) ^ (addCharLevel (psiLocal K v) + f : ℤ) : ℝ) : ℂ)) ^ (1 - (1 / 2 : ℂ))
          * ∫ u in {u : v.adicCompletion K | Valued.v u = 1},
              psiLocal K v
                  (((uniformizerUnit K v ^ (-(addCharLevel (psiLocal K v) + f : ℤ)) : (v.adicCompletion K)ˣ) :
                      v.adicCompletion K) * u)
                * charExt χ⁻¹ u ∂(selfDualHaarAt K v) := by
  letI := localBorel K v
  haveI : BorelSpace (v.adicCompletion K) := borelSpace_localBorel K v
  haveI : (selfDualHaarAt K v).IsAddHaarMeasure := isAddHaarMeasure_selfDualHaarAt v
  have hnot0 : ¬ HasConductorExponentAt K v χ 0 := fun h0 => by
    have := hasConductorExponentAt_unique K v h0 hχ; omega
  have hnum := LanglandsTunnell.TateLocal.localZeta_tateFourier_stdTestFunAt K v χ f hf hχ (1 / 2) hs
  have hden := LanglandsTunnell.TateLocal.localZeta_stdTestFunAt_eq_real_image_higherUnitsAt K v χ f hf hχ (1 / 2)
  have hmass := LanglandsTunnell.TateLocal.selfDualHaarAt_real_image_higherUnitsAt K v f hf
  have hN0 : (Ideal.absNorm v.asIdeal : ℝ) ≠ 0 :=
    Nat.cast_ne_zero.mpr (Ideal.absNorm_eq_zero_iff.not.mpr v.ne_bot)
  have hNpos : (0 : ℝ) < (Ideal.absNorm v.asIdeal : ℝ) := by positivity
  have hM0 : (((selfDualHaarAt K v).real
      (((↑) : (v.adicCompletion K)ˣ → v.adicCompletion K) '' higherUnitsAt K v f) : ℝ) : ℂ) ≠ 0 := by
    rw [hmass]
    exact_mod_cast (mul_pos (zpow_pos hNpos _) (Real.rpow_pos_of_pos hNpos _)).ne'
  show localEpsilonAt K v (selfDualHaarAt K v) (psiLocal K v) (stdTestFunAt K v χ) χ (1 / 2) = _
  rw [localEpsilonAt_of_not_hasConductorExponentAt_zero K v _ _ _ hnot0, localGammaAt, hnum, hden]
  field_simp

theorem selfDual_real_integers_sq_mul_zpow :
    letI := localBorel K v
    (((selfDualHaarAt K v).real (v.adicCompletionIntegers K : Set (v.adicCompletion K)) : ℝ) : ℂ) ^ 2
        * (Ideal.absNorm v.asIdeal : ℂ) ^ (addCharLevel (psiLocal K v)) = 1 := by
  letI := localBorel K v
  haveI : BorelSpace (v.adicCompletion K) := borelSpace_localBorel K v
  haveI : (selfDualHaarAt K v).IsAddHaarMeasure := isAddHaarMeasure_selfDualHaarAt v
  have h92 := LanglandsTunnell.TateLocal.selfDualHaarAt_real_integers_mul_real_setOf_valued_le_exp_addCharLevel K v
  have hfb := LanglandsTunnell.TateLocal.measureReal_setOf_valued_le_exp K v (selfDualHaarAt K v)
    (addCharLevel (psiLocal K v))
  rw [hfb] at h92

  have hN0 : (Ideal.absNorm v.asIdeal : ℝ) ≠ 0 :=
    Nat.cast_ne_zero.mpr (Ideal.absNorm_eq_zero_iff.not.mpr v.ne_bot)
  have h' : ((selfDualHaarAt K v).real (v.adicCompletionIntegers K : Set (v.adicCompletion K))) ^ 2
      * (Ideal.absNorm v.asIdeal : ℝ) ^ (addCharLevel (psiLocal K v)) = 1 := by
    rw [← h92]; ring
  have := congrArg (fun r : ℝ => (r : ℂ)) h'
  push_cast at this
  exact this

theorem cpow_one_sub_half_sq (r : ℝ) (hr : 0 ≤ r) : (((r : ℂ)) ^ (1 - (1 / 2 : ℂ))) ^ 2 = (r : ℂ) := by
  rw [show (1 - (1 / 2 : ℂ)) = ((2 : ℕ) : ℂ)⁻¹ by norm_num]
  exact Complex.cpow_nat_inv_pow _ two_ne_zero

theorem hasConductorExponentAt_inv {χ : (v.adicCompletion K)ˣ →* ℂˣ} {f : ℕ}
    (hχ : HasConductorExponentAt K v χ f) : HasConductorExponentAt K v χ⁻¹ f := by
  refine ⟨fun u hu => by rw [MonoidHom.inv_apply, hχ.1 u hu, inv_one], fun m hm => ?_⟩
  obtain ⟨u, hu, hne⟩ := hχ.2 m hm
  exact ⟨u, hu, fun h => hne (inv_eq_one.mp (by rwa [MonoidHom.inv_apply] at h))⟩

theorem charExt_inv (χ : (v.adicCompletion K)ˣ →* ℂˣ) (y : v.adicCompletion K) :
    charExt χ⁻¹ y = (charExt χ y)⁻¹ := by
  by_cases hy : y = 0
  · rw [hy, charExt_zero, charExt_zero, inv_zero]
  · rw [charExt_of_ne_zero _ hy, charExt_of_ne_zero _ hy, MonoidHom.inv_apply, Units.val_inv_eq_inv_val]

theorem charExt_inv_neg_one (χ : (v.adicCompletion K)ˣ →* ℂˣ) :
    charExt χ⁻¹ (-1 : v.adicCompletion K) = charExt χ (-1) := by
  have hm1 : (-1 : v.adicCompletion K) ≠ 0 := neg_ne_zero.mpr one_ne_zero
  have hu : Units.mk0 (-1 : v.adicCompletion K) hm1 = -1 := Units.ext rfl
  rw [charExt_inv, charExt_of_ne_zero χ hm1, hu]
  have hsq : χ (-1 : (v.adicCompletion K)ˣ) * χ (-1) = 1 := by
    rw [← map_mul, neg_one_mul, neg_neg, map_one]
  rw [← Units.val_inv_eq_inv_val, inv_eq_of_mul_eq_one_right hsq]

theorem valued_zpow_mul {ϖ : v.adicCompletionIntegers K}
    (hϖ : Valued.v (algebraMap (v.adicCompletionIntegers K) (v.adicCompletion K) ϖ) = WithZero.exp (-1 : ℤ))
    {y : v.adicCompletion K} {e : ℤ} (hy : Valued.v y = WithZero.exp e) (m : ℤ) :
    Valued.v (algebraMap (v.adicCompletionIntegers K) (v.adicCompletion K) ϖ ^ m * y) = WithZero.exp (e - m) := by
  rw [map_mul, map_zpow₀, hϖ, hy, ← WithZero.exp_zsmul, ← WithZero.exp_add]
  congr 1
  simp only [smul_eq_mul, mul_neg, mul_one]
  ring

theorem algebra_core (a t t' K P Nn Nf I J M χm1 cw cwi μUi : ℂ)
    (hcw : cw * cwi = 1) (hP : P ^ 2 = Nn * Nf) (hE3 : I * J * Nf = χm1 * M ^ 2) (hL6 : M ^ 2 * Nn = 1) :
    a * t' * (χm1 * J * μUi) * t * K ^ 2 = a * t * (I * μUi) * t' * cw ^ 2 * (K * P * (cwi * J)) ^ 2 := by
  set C := a * t * t' * K ^ 2 * J * μUi with hC
  linear_combination (-(C * P ^ 2 * I * J * (cw * cwi + 1))) * hcw + (-(C * I * J)) * hP
    + (-(C * Nn)) * hE3 + (-(C * χm1)) * hL6

end LanglandsTunnell.TateLocal.Ws47Shell

open _root_.LanglandsTunnell.TateLocal _root_.P2MW.S_LanglandsTunnell_TateLocal_tsum_mul_setIntegral_psiLocal_neg_mul_charExt_eq_mul_charExt_sq_mul_stdRootNumberAt_sq.LanglandsTunnell.TateLocal in
theorem solution
    (K : Type) [Field K] [NumberField K] (v : HeightOneSpectrum (𝓞 K))
    (χ : (v.adicCompletion K)ˣ →* ℂˣ) (f : ℕ) (hf : 1 ≤ f) (hχ : HasConductorExponentAt K v χ f)
    (χ' : (v.adicCompletion K)ˣ →* ℂˣ)
    (hχ' : ∀ u : (v.adicCompletion K)ˣ, Valued.v (u : v.adicCompletion K) = 1 → χ' u = (χ u)⁻¹)
    (ϖ : v.adicCompletionIntegers K)
    (hϖ : Valued.v (algebraMap (v.adicCompletionIntegers K) (v.adicCompletion K) ϖ) = WithZero.exp (-1 : ℤ))
    (x : v.adicCompletion K) (e : ℤ) (hx : Valued.v x = WithZero.exp e)
    (a : ℤ → ℂ) (t t' : ℂ)
    (hs : ‖(χ⁻¹ (uniformizerUnit K v) : ℂ) * (Ideal.absNorm v.asIdeal : ℂ) ^ (-(1 - (1 / 2 : ℂ)))‖ < 1) :
    letI := localBorel K v
    (∑' m : ℤ, a m * t' ^ m *
          ((∫ u in {u : v.adicCompletion K | Valued.v u = 1},
              psiLocal K v (algebraMap (v.adicCompletionIntegers K) (v.adicCompletion K) ϖ ^ m * -x * u)
                * charExt χ' u ∂(selfDualHaarAt K v))
            / (((selfDualHaarAt K v).real
                  {u : v.adicCompletion K | Valued.v u = 1} : ℝ) : ℂ)))
        * t ^ (e - addCharLevel (psiLocal K v) - f)
        * ((χ (uniformizerUnit K v) : ℂˣ) : ℂ) ^ (2 * (addCharLevel (psiLocal K v) + f))
      = (∑' m : ℤ, a m * t ^ m *
            ((∫ u in {u : v.adicCompletion K | Valued.v u = 1},
                psiLocal K v (algebraMap (v.adicCompletionIntegers K) (v.adicCompletion K) ϖ ^ m * x * u)
                  * charExt χ u ∂(selfDualHaarAt K v))
              / (((selfDualHaarAt K v).real
                    {u : v.adicCompletion K | Valued.v u = 1} : ℝ) : ℂ)))
          * t' ^ (e - addCharLevel (psiLocal K v) - f)
          * charExt χ
              (algebraMap (v.adicCompletionIntegers K) (v.adicCompletion K) ϖ ^ (e - addCharLevel (psiLocal K v) - f)
                * x
                * ((uniformizerUnit K v ^ (addCharLevel (psiLocal K v) + f : ℤ) : (v.adicCompletion K)ˣ) :
                    v.adicCompletion K)) ^ 2
          * stdRootNumberAt K v χ ^ 2 := by
  letI := localBorel K v
  haveI : BorelSpace (v.adicCompletion K) := borelSpace_localBorel K v
  haveI : (selfDualHaarAt K v).IsAddHaarMeasure := Ws47Ramified.isAddHaarMeasure_selfDualHaarAt v

  set n : ℤ := addCharLevel (psiLocal K v) with hn
  set ϖK : v.adicCompletion K := algebraMap (v.adicCompletionIntegers K) (v.adicCompletion K) ϖ with hϖK
  set m₀ : ℤ := e - n - f with hm₀
  set μU : ℂ := (((selfDualHaarAt K v).real {u : v.adicCompletion K | Valued.v u = 1} : ℝ) : ℂ) with hμU
  have hχinv : HasConductorExponentAt K v χ⁻¹ f := Ws47Shell.hasConductorExponentAt_inv v hχ

  have hL : (∑' m : ℤ, a m * t' ^ m *
        ((∫ u in {u : v.adicCompletion K | Valued.v u = 1}, psiLocal K v (ϖK ^ m * -x * u) * charExt χ' u ∂(selfDualHaarAt K v)) / μU))
      = ∑' m : ℤ, a m * t' ^ m *
        ((∫ u in {u : v.adicCompletion K | Valued.v u = 1}, psiLocal K v (ϖK ^ m * -x * u) * charExt χ⁻¹ u ∂(selfDualHaarAt K v)) / μU) :=
    tsum_congr fun m => by rw [Ws47Shell.setIntegral_units_charExt_congr v (selfDualHaarAt K v) χ χ' hχ']
  have hnegx : Valued.v (-x) = WithZero.exp e := by rw [Valuation.map_neg, hx]
  have E1L := Ws47Shell.tsum_shell_eq_single v χ⁻¹ f hf hχinv ϖ hϖ (-x) e hnegx a t'
  have E1R := Ws47Shell.tsum_shell_eq_single v χ f hf hχ ϖ hϖ x e hx a t

  set c : v.adicCompletion K := ϖK ^ m₀ * x with hc
  have hneg : (∫ u in {u : v.adicCompletion K | Valued.v u = 1}, psiLocal K v (ϖK ^ m₀ * -x * u) * charExt χ⁻¹ u ∂(selfDualHaarAt K v))
      = charExt χ (-1) * ∫ u in {u : v.adicCompletion K | Valued.v u = 1}, psiLocal K v (c * u) * charExt χ⁻¹ u ∂(selfDualHaarAt K v) := by
    have e1 : (fun u => psiLocal K v (ϖK ^ m₀ * -x * u) * charExt χ⁻¹ u)
        = fun u => (fun u' => psiLocal K v (c * u')) (-u) * charExt χ⁻¹ u := by
      funext u; simp only [hc]; ring_nf
    have E2 := Ws47Shell.setIntegral_units_comp_neg v (selfDualHaarAt K v) χ⁻¹ (fun u' => psiLocal K v (c * u'))
    rw [Ws47Shell.charExt_inv_neg_one v] at E2
    rw [e1]
    exact E2

  have hcv : Valued.v c = WithZero.exp (n + f) := by
    rw [hc, Ws47Shell.valued_zpow_mul v hϖ hx, hm₀]; congr 1; ring
  have E3 := Ws47Shell.gauss_product_selfDual v χ f hf hχ c hcv

  have E5 := Ws47Shell.stdRootNumberAt_eq v χ f hf hχ hs
  set w : v.adicCompletion K := c * ((uniformizerUnit K v ^ (n + f : ℤ) : (v.adicCompletion K)ˣ) : v.adicCompletion K)
    with hw
  have hwv : Valued.v w = 1 := by
    rw [hw, map_mul, hcv, Ws47Ramified.valued_uniformizerUnit_zpow, ← WithZero.exp_add]
    convert WithZero.exp_zero using 2; ring
  have hw0 : w ≠ 0 := fun h => by rw [h, map_zero] at hwv; exact zero_ne_one hwv
  have hG0 : (∫ u in {u : v.adicCompletion K | Valued.v u = 1}, psiLocal K v
        (((uniformizerUnit K v ^ (-(n + f : ℤ)) : (v.adicCompletion K)ˣ) : v.adicCompletion K) * u)
          * charExt χ⁻¹ u ∂(selfDualHaarAt K v))
      = (charExt χ w)⁻¹ * ∫ u in {u : v.adicCompletion K | Valued.v u = 1}, psiLocal K v (c * u) * charExt χ⁻¹ u ∂(selfDualHaarAt K v) := by
    have L4 := Ws47Shell.setIntegral_units_comp_mul_unit v (selfDualHaarAt K v) χ⁻¹ w hwv
      (fun y => psiLocal K v (((uniformizerUnit K v ^ (-(n + f : ℤ)) : (v.adicCompletion K)ˣ) : v.adicCompletion K) * y))

    have e2 : (fun u => psiLocal K v (c * u) * charExt χ⁻¹ u) = fun u =>
        psiLocal K v (((uniformizerUnit K v ^ (-(n + f : ℤ)) : (v.adicCompletion K)ˣ) : v.adicCompletion K) * (w * u))
          * charExt χ⁻¹ u := by
      funext u; congr 2; rw [hw, zpow_neg, Units.val_inv_eq_inv_val]; field_simp
    rw [e2, L4, Ws47Shell.charExt_inv v, inv_inv, ← mul_assoc, inv_mul_cancel₀ ?_, one_mul]
    rw [charExt_of_ne_zero χ hw0]; exact Units.ne_zero _

  rw [hL, E1L, E1R, hneg, E5, hG0]
  have hcw0 : charExt χ w ≠ 0 := by rw [charExt_of_ne_zero χ hw0]; exact Units.ne_zero _
  have hP := Ws47Shell.cpow_one_sub_half_sq ((Ideal.absNorm v.asIdeal : ℝ) ^ (n + f : ℤ)) (by positivity)
  have hN0 : (Ideal.absNorm v.asIdeal : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (Ideal.absNorm_eq_zero_iff.not.mpr v.ne_bot)
  have hP' : (((((Ideal.absNorm v.asIdeal : ℝ) ^ (n + f : ℤ) : ℝ) : ℂ)) ^ (1 - (1 / 2 : ℂ))) ^ 2
      = (Ideal.absNorm v.asIdeal : ℂ) ^ n * (Ideal.absNorm v.asIdeal : ℂ) ^ (f : ℤ) := by
    rw [hP]; push_cast; rw [zpow_add₀ hN0]
  have hL6 := Ws47Shell.selfDual_real_integers_sq_mul_zpow v
  have hE3' : (∫ u in {u : v.adicCompletion K | Valued.v u = 1}, psiLocal K v (c * u) * charExt χ u ∂(selfDualHaarAt K v)) *
      (∫ u in {u : v.adicCompletion K | Valued.v u = 1}, psiLocal K v (c * u) * charExt χ⁻¹ u ∂(selfDualHaarAt K v)) *
      (Ideal.absNorm v.asIdeal : ℂ) ^ (f : ℤ) = charExt χ (-1) *
        (((selfDualHaarAt K v).real (v.adicCompletionIntegers K : Set (v.adicCompletion K)) : ℝ) : ℂ) ^ 2 := by
    rw [zpow_natCast]; exact E3
  have hK : ((χ (uniformizerUnit K v) : ℂˣ) : ℂ) ^ (2 * (n + f)) = (((χ (uniformizerUnit K v) : ℂˣ) : ℂ) ^ (n + f : ℤ)) ^ 2 := by
    rw [mul_comm, zpow_mul]; norm_cast
  rw [hK, div_eq_mul_inv, div_eq_mul_inv]
  exact Ws47Shell.algebra_core (a m₀) (t ^ m₀) (t' ^ m₀) _ _ _ _ _ _ _ _ _ _ _
    (mul_inv_cancel₀ hcw0) hP' hE3' hL6

end S_LanglandsTunnell_TateLocal_tsum_mul_setIntegral_psiLocal_neg_mul_charExt_eq_mul_charExt_sq_mul_stdRootNumberAt_sq
end P2MW
export P2MW.S_LanglandsTunnell_TateLocal_tsum_mul_setIntegral_psiLocal_neg_mul_charExt_eq_mul_charExt_sq_mul_stdRootNumberAt_sq (solution)
