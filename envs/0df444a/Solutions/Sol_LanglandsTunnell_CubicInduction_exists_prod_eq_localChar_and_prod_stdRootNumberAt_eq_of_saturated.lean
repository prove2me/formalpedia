-- Prove2me | solution 1 for LanglandsTunnell.CubicInduction.exists_prod_eq_localChar_and_prod_stdRootNumberAt_eq_of_saturated
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:08.353894+00:00
-- url     : https://prove2.me/submissions/57cfe985-07f3-520d-b90a-8e04f30bcd11

import Definitions.Def_LanglandsTunnell_CubicInduction_AutomorphyDatum31
import Definitions.Def_LanglandsTunnell_CubicInduction_MirabolicMajorant
import Definitions.Def_LanglandsTunnell_CubicLambda

import Definitions.Def_LanglandsTunnell_StandardLocalConstantsAt
import Theorems.Thm_LanglandsTunnell_TateLocal_exists_continuous_hasConductorExponentAt
import Theorems.Thm_LanglandsTunnell_TateLocal_stdRootNumberAt_mul_of_hasConductorExponentAt_zero
import Theorems.Thm_LanglandsTunnell_TateLocal_psiLocal_ne_one
import Theorems.Thm_LanglandsTunnell_TateLocal_norm_stdRootNumberAt_eq_one
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_LanglandsTunnell_CubicInduction_exists_prod_eq_localChar_and_prod_stdRootNumberAt_eq_of_saturated
p2m_attr_erase "instance" "instFiniteResidueFieldAdicCompletionRingOfIntegersWithZeroMultiplicativeInt_definitions NumberField.instCompactSpaceAdicCompletionIntegers Rat.adicCompletion.locallyCompactSpace NumberField.instFiniteResidueFieldAdicCompletionIntegers instWeaklyLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions instCountableOfNumberField_definitions IsDedekindDomain.HeightOneSpectrum.Extension.instAlgebraSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersValEqUnder IsDedekindDomain.HeightOneSpectrum.Extension.instAlgebraSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersValEqUnder_1 IsDedekindDomain.HeightOneSpectrum.instMulActionHomClassAlgHomTensorProductAdicCompletionForallValEqUnder_definitions IsDedekindDomain.HeightOneSpectrum.Extension.instAlgebraAdicCompletionValEqUnder IsDedekindDomain.HeightOneSpectrum.adicCompletion.instFiniteForallValEqUnderOfFiniteDimensional_definitions IsDedekindDomain.HeightOneSpectrum.instIsBiscalarSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersTensorProductCoeAlgHomTensorAdicCompletionIntegersTo IsDedekindDomain.HeightOneSpectrum.Extension.instContinuousSMulAdicCompletionValEqUnder IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsModuleTopology IsDedekindDomain.HeightOneSpectrum.Extension.instFiniteSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersValEqUnderOfFiniteDimensional IsDedekindDomain.HeightOneSpectrum.adicCompletion.instFiniteValEqUnderOfFiniteDimensional_definitions instIsBiscalarTensorProductCoeAlgHomBaseChange_of_algebraMap IsDedekindDomain.HeightOneSpectrum.instIsScalarTowerSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersValEqUnder_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsModuleTopologyPi Submodule.instIsTopologicalModuleSubtypeMem Pi.instTopologicalModule IsTopologicalModule.toContinuousSMul IsTopologicalModule.toContinuousAdd instFunLike SemialgHomClass.toSemilinearMapClass instCoeTCSemialgHom SemialgHomClass.toRingHomClass SemialgHomClass.instSemialgHom"
p2m_attr_erase "simp" "SemialgHom.baseChange_of_algebraMap_tmul_left SemialgHom.baseChangeRightOfAlgebraMap_apply Pi.semialgHomPi_apply Pi.semialgHom_apply Module.Basis.rightBaseChange_apply LinearEquiv.coe_mulLeft LinearEquiv.coe_mulRight WithVal.semialgebraMap_toFun_ofVal Module.Basis.rightBaseChange_repr IsDedekindDomain.HeightOneSpectrum.adicCompletionIntegers.tensorCoe_tmul IsDedekindDomain.HeightOneSpectrum.tensorAdicCompletionIntegersTo_tmul SemialgHom.baseChangeRightOfAlgebraMap_coe IsDedekindDomain.HeightOneSpectrum.adicCompletion.integerBaseChangeLinearEquiv_tmul_apply SemialgHom.baseChange_of_algebraMap_tmul_right IsLocalization.map_moduleTensorEquiv_symm_tmul IsLocalization.leftModuleTensorEquiv_apply IsLocalization.moduleLid_symm_apply IsLocalization.leftModuleTensorEquiv_symm_apply IsLocalization.map_moduleTensorEquiv_tmul IsModuleTopology.continuousLinearEquiv_apply AlgEquiv.extendScalars_symm_apply IsModuleTopology.Module.Basis.equivFun_homeo_symm_apply IsModuleTopology.Module.Basis.equivFun_homeo_apply IsModuleTopology.continuousAlgEquivOfIsBiscalar_apply AlgEquiv.extendScalars_apply IsModuleTopology.continuousLinearEquiv_symm_apply SemialgHom.restrictScalars_toFun SemialgHom.mk.sizeOf_spec SemialgHom.mk.injEq SemialgHom.coe_coe coe_mk TensorProduct.RightActions.smul_def TensorProduct.RightActions.Module.TensorProduct.comm_symm_apply_tmul TensorProduct.RightActions.LinearMap.baseChange_id TensorProduct.RightActions.algebraMap_eval TensorProduct.RightActions.Module.TensorProduct.comm_apply_tmul TensorProduct.RightActions.Algebra.TensorProduct.comm_symm_apply_tmul TensorProduct.RightActions.Algebra.TensorProduct.comm_apply_tmul"

set_option autoImplicit false

noncomputable section

section

open NumberField NumberField.StandardAddChar NumberField.AdelicLevel IsDedekindDomain Filter Topology LanglandsTunnell.TateLocal

private theorem hasConductorExponentAt_mul_of_lt
    (K : Type) [Field K] [NumberField K] (v : HeightOneSpectrum (𝓞 K))
    {α β : (v.adicCompletion K)ˣ →* ℂˣ} {a b : ℕ}
    (hα : HasConductorExponentAt K v α a) (hβ : HasConductorExponentAt K v β b) (hab : b < a) :
    HasConductorExponentAt K v (α * β) a := by
  refine ⟨fun u hu => ?_, fun m hm => ?_⟩
  · rw [MonoidHom.mul_apply, hα.1 u hu, hβ.1 u (higherUnitsAt_antitone K v hab.le hu), mul_one]
  · obtain ⟨u, hu, hne⟩ := hα.2 (max m b) (max_lt hm hab)
    refine ⟨u, higherUnitsAt_antitone K v (le_max_left m b) hu, ?_⟩
    rw [MonoidHom.mul_apply, hβ.1 u (higherUnitsAt_antitone K v (le_max_right m b) hu), mul_one]
    exact hne

private theorem hasConductorExponentAt_mul_of_lt'
    (K : Type) [Field K] [NumberField K] (v : HeightOneSpectrum (𝓞 K))
    {α β : (v.adicCompletion K)ˣ →* ℂˣ} {a b : ℕ}
    (hα : HasConductorExponentAt K v α a) (hβ : HasConductorExponentAt K v β b) (hab : b < a) :
    HasConductorExponentAt K v (β * α) a := by
  have h : β * α = α * β := mul_comm β α
  rw [h]
  exact hasConductorExponentAt_mul_of_lt K v hα hβ hab

private theorem hasConductorExponentAt_inv
    (K : Type) [Field K] [NumberField K] (v : HeightOneSpectrum (𝓞 K))
    {α : (v.adicCompletion K)ˣ →* ℂˣ} {a : ℕ} (hα : HasConductorExponentAt K v α a) :
    HasConductorExponentAt K v α⁻¹ a := by
  refine ⟨fun u hu => ?_, fun m hm => ?_⟩
  · simp [hα.1 u hu]
  · obtain ⟨u, hu, hne⟩ := hα.2 m hm
    exact ⟨u, hu, by simpa using hne⟩

private theorem eventually_mem_higherUnitsAt_nhds_one
    (K : Type) [Field K] [NumberField K] (v : HeightOneSpectrum (𝓞 K)) (n : ℕ) :
    ∀ᶠ u in 𝓝 (1 : (v.adicCompletion K)ˣ), u ∈ higherUnitsAt K v n := by
  have hϖ : ((uniformizerUnit K v : (v.adicCompletion K)ˣ) : v.adicCompletion K) ^ n ≠ 0 :=
    pow_ne_zero n (uniformizerUnit K v).ne_zero
  have hval : Valued.v (((uniformizerUnit K v : (v.adicCompletion K)ˣ) : v.adicCompletion K) ^ n)
      = WithZero.exp (-(n : ℤ)) := by
    rw [map_pow, valued_uniformizerUnit, ← WithZero.exp_nsmul, nsmul_eq_mul, mul_neg, mul_one]
  have hv1 : Valued.v (1 : v.adicCompletion K) ≠ (0 : WithZero (Multiplicative ℤ)) :=
    (Valuation.ne_zero_iff _).mpr one_ne_zero
  have h1 : ∀ᶠ z in 𝓝 (1 : v.adicCompletion K), Valued.v z = Valued.v (1 : v.adicCompletion K) :=
    Valued.locally_const hv1
  have h0 : ∀ᶠ y in 𝓝 (0 : v.adicCompletion K),
      Valued.v y < Valued.v (((uniformizerUnit K v : (v.adicCompletion K)ˣ) : v.adicCompletion K) ^ n) := by
    rw [Filter.Eventually, Valued.mem_nhds_zero]
    refine ⟨Units.mk0 (Valued.v.restrict _) ((Valuation.ne_zero_iff _).mpr hϖ), fun y hy => ?_⟩
    exact (Valuation.restrict_lt_iff _).mp hy
  have hsub : Tendsto (fun z : v.adicCompletion K => z - 1) (𝓝 (1 : v.adicCompletion K)) (𝓝 0) := by
    first
      | exact tendsto_sub_nhds_zero_iff.mpr tendsto_id
      | simpa using (continuous_id.sub continuous_const).tendsto (1 : v.adicCompletion K)
  have h2 : ∀ᶠ z in 𝓝 (1 : v.adicCompletion K),
      Valued.v (z - 1) < Valued.v (((uniformizerUnit K v : (v.adicCompletion K)ˣ) : v.adicCompletion K) ^ n) :=
    hsub.eventually h0
  have hcoe : Tendsto (fun u : (v.adicCompletion K)ˣ => (u : v.adicCompletion K)) (𝓝 1)
      (𝓝 (1 : v.adicCompletion K)) := by
    first
      | simpa using Units.continuous_val.tendsto (1 : (v.adicCompletion K)ˣ)
      | (have h := Units.continuous_val.tendsto (1 : (v.adicCompletion K)ˣ); rwa [Units.val_one] at h)
  filter_upwards [hcoe.eventually h1, hcoe.eventually h2] with u hu1 hu2
  refine (mem_higherUnitsAt_iff K v).mpr ⟨by rw [hu1, map_one], Or.inr ?_⟩
  rw [← hval]
  exact hu2.le

private theorem isLocallyConstant_of_hasConductorExponentAt
    (K : Type) [Field K] [NumberField K] (v : HeightOneSpectrum (𝓞 K))
    {χ : (v.adicCompletion K)ˣ →* ℂˣ} {c : ℕ} (hχ : HasConductorExponentAt K v χ c) :
    IsLocallyConstant χ := by
  rw [IsLocallyConstant.iff_eventually_eq]
  intro x
  have hmul : Tendsto (fun y : (v.adicCompletion K)ˣ => x⁻¹ * y) (𝓝 x) (𝓝 1) := by
    have hx : x⁻¹ * x = (1 : (v.adicCompletion K)ˣ) := inv_mul_cancel x
    have h : Tendsto (fun y : (v.adicCompletion K)ˣ => x⁻¹ * y) (𝓝 x) (𝓝 (x⁻¹ * x)) :=
      (continuous_const.mul continuous_id).tendsto x
    first
      | (rw [hx] at h; exact h)
      | exact hx ▸ h
      | simpa [hx] using h
  filter_upwards [hmul.eventually (eventually_mem_higherUnitsAt_nhds_one K v c)] with y hy
  have hxy : x * (x⁻¹ * y) = y := mul_inv_cancel_left x y
  calc χ y = χ (x * (x⁻¹ * y)) := by rw [hxy]
    _ = χ x := by rw [map_mul, hχ.1 _ hy, mul_one]

private theorem exists_double_top
    (K : Type) [Field K] [NumberField K] (v : HeightOneSpectrum (𝓞 K))
    (θ : (v.adicCompletion K)ˣ →* ℂˣ) {t : ℕ} (hθ : HasConductorExponentAt K v θ t)
    (A : ℕ) (hA : 2 * t + 12 ≤ A) :
    ∃ (ξ₁ ξ₂ ξ₃ : (v.adicCompletion K)ˣ →* ℂˣ) (T c : ℕ),
      2 ≤ c ∧ c < T ∧ t < T ∧ 2 * T + c = A ∧
      HasConductorExponentAt K v ξ₁ T ∧ HasConductorExponentAt K v ξ₂ T ∧ HasConductorExponentAt K v ξ₃ c ∧
      ξ₁ (uniformizerUnit K v) = 1 ∧ ξ₃ (uniformizerUnit K v) = 1 ∧ ξ₁ * ξ₂ * ξ₃ = θ := by
  obtain ⟨ξ₁, -, hξ₁ϖ, hξ₁⟩ :=
    exists_continuous_hasConductorExponentAt K v ((A - (2 + A % 2)) / 2) (by omega)
  obtain ⟨ξ₃, -, hξ₃ϖ, hξ₃⟩ := exists_continuous_hasConductorExponentAt K v (2 + A % 2) (by omega)
  refine ⟨ξ₁, θ * ξ₁⁻¹ * ξ₃⁻¹, ξ₃, (A - (2 + A % 2)) / 2, 2 + A % 2, by omega, by omega, by omega, by omega,
    hξ₁, ?_, hξ₃, hξ₁ϖ, hξ₃ϖ, ?_⟩
  · exact hasConductorExponentAt_mul_of_lt K v
      (hasConductorExponentAt_mul_of_lt' K v (hasConductorExponentAt_inv K v hξ₁) hθ (by omega))
      (hasConductorExponentAt_inv K v hξ₃) (by omega)
  · have h3 : θ * ξ₁⁻¹ * ξ₃⁻¹ * ξ₃ = θ * ξ₁⁻¹ := inv_mul_cancel_right (θ * ξ₁⁻¹) ξ₃
    have h4 : ξ₁ * (ξ₁⁻¹ * θ) = θ := mul_inv_cancel_left ξ₁ θ
    calc ξ₁ * (θ * ξ₁⁻¹ * ξ₃⁻¹) * ξ₃
      _ = ξ₁ * (θ * ξ₁⁻¹ * ξ₃⁻¹ * ξ₃) := mul_assoc ξ₁ (θ * ξ₁⁻¹ * ξ₃⁻¹) ξ₃
      _ = ξ₁ * (θ * ξ₁⁻¹) := congrArg (ξ₁ * ·) h3
      _ = ξ₁ * (ξ₁⁻¹ * θ) := congrArg (ξ₁ * ·) (mul_comm θ ξ₁⁻¹)
      _ = θ := h4

private theorem stdRootNumberAt_mul_twist_mul_twist_inv
    (K : Type) [Field K] [NumberField K] (v : HeightOneSpectrum (𝓞 K)) (hψ : psiLocal K v ≠ 1)
    {ξ₁ ξ₃ η : (v.adicCompletion K)ˣ →* ℂˣ} {T c : ℕ}
    (hξ₁ : HasConductorExponentAt K v ξ₁ T) (hξ₃ : HasConductorExponentAt K v ξ₃ c)
    (hη : HasConductorExponentAt K v η 0) (hcT : c ≤ T)
    (n₁ : ‖((ξ₁ (uniformizerUnit K v) : ℂˣ) : ℂ)‖ = 1) (n₃ : ‖((ξ₃ (uniformizerUnit K v) : ℂˣ) : ℂ)‖ = 1)
    (nη : ‖((η (uniformizerUnit K v) : ℂˣ) : ℂ)‖ = 1) :
    stdRootNumberAt K v (ξ₁ * η) * stdRootNumberAt K v (ξ₃ * η⁻¹)
      = ((η (uniformizerUnit K v) : ℂˣ) : ℂ) ^ (T - c) * (stdRootNumberAt K v ξ₁ * stdRootNumberAt K v ξ₃) := by
  have hinv : ((η⁻¹ (uniformizerUnit K v) : ℂˣ) : ℂ) = (((η (uniformizerUnit K v) : ℂˣ) : ℂ))⁻¹ := by
    rw [MonoidHom.inv_apply]
    exact Units.val_inv_eq_inv_val _
  have hη' : HasConductorExponentAt K v η⁻¹ 0 := hasConductorExponentAt_inv K v hη
  have nη' : ‖((η⁻¹ (uniformizerUnit K v) : ℂˣ) : ℂ)‖ = 1 := by
    rw [hinv, norm_inv, nη, inv_one]
  have hu0 : ((η (uniformizerUnit K v) : ℂˣ) : ℂ) ≠ 0 := (η (uniformizerUnit K v)).ne_zero
  have hiz : (((η (uniformizerUnit K v) : ℂˣ) : ℂ))⁻¹ ^ ((c : ℤ) + addCharLevel (psiLocal K v))
      = ((η (uniformizerUnit K v) : ℂˣ) : ℂ) ^ (-((c : ℤ) + addCharLevel (psiLocal K v))) :=
    inv_zpow' _ _
  have hexp : ((η (uniformizerUnit K v) : ℂˣ) : ℂ) ^ ((T : ℤ) + addCharLevel (psiLocal K v))
        * ((η (uniformizerUnit K v) : ℂˣ) : ℂ) ^ (-((c : ℤ) + addCharLevel (psiLocal K v)))
      = ((η (uniformizerUnit K v) : ℂˣ) : ℂ) ^ (T - c) := by
    rw [← zpow_add₀ hu0, ← zpow_natCast, Nat.cast_sub hcT]
    first
      | (congr 1; ring)
      | (congr 1; omega)
  rw [stdRootNumberAt_mul_of_hasConductorExponentAt_zero K v ξ₁ η T hξ₁ hη n₁ nη hψ,
    stdRootNumberAt_mul_of_hasConductorExponentAt_zero K v ξ₃ η⁻¹ c hξ₃ hη' n₃ nη' hψ, hinv, hiz, ← hexp]
  ring

private theorem exists_fin_three_saturated_local_data
    (K : Type) [Field K] [NumberField K] (v : HeightOneSpectrum (𝓞 K)) (hψ : psiLocal K v ≠ 1)
    (hunit : ∀ (ξ : (v.adicCompletion K)ˣ →* ℂˣ) (c : ℕ), 1 ≤ c → HasConductorExponentAt K v ξ c →
      ‖((ξ (uniformizerUnit K v) : ℂˣ) : ℂ)‖ = 1 → ‖stdRootNumberAt K v ξ‖ = 1)
    (hunr : ∀ u : ℂˣ, ‖(u : ℂ)‖ = 1 →
      ∃ η : (v.adicCompletion K)ˣ →* ℂˣ, HasConductorExponentAt K v η 0 ∧ η (uniformizerUnit K v) = u)
    (θ : (v.adicCompletion K)ˣ →* ℂˣ) {t : ℕ} (hθ : HasConductorExponentAt K v θ t)
    (hθϖ : ‖((θ (uniformizerUnit K v) : ℂˣ) : ℂ)‖ = 1)
    (A : ℕ) (hA : 2 * t + 12 ≤ A) (z : ℂ) (hz : ‖z‖ = 1) :
    ∃ (ν : Fin 3 → ((v.adicCompletion K)ˣ →* ℂˣ)) (a : Fin 3 → ℕ),
      (∀ i, IsLocallyConstant (ν i)) ∧
      (∀ i, 1 ≤ a i ∧ HasConductorExponentAt K v (ν i) (a i)) ∧
      (∑ i, a i) = A ∧
      (∀ i, ‖((ν i (uniformizerUnit K v) : ℂˣ) : ℂ)‖ = 1) ∧
      ν 0 * ν 1 * ν 2 = θ ∧
      (∏ i, stdRootNumberAt K v (ν i)) = z := by
  obtain ⟨ξ₁, ξ₂, ξ₃, T, c, hc2, hcT, htT, hsum, hξ₁, hξ₂, hξ₃, hξ₁ϖ, hξ₃ϖ, hprod⟩ :=
    exists_double_top K v θ hθ A hA
  have n₁ : ‖((ξ₁ (uniformizerUnit K v) : ℂˣ) : ℂ)‖ = 1 := by rw [hξ₁ϖ, Units.val_one, norm_one]
  have n₃ : ‖((ξ₃ (uniformizerUnit K v) : ℂˣ) : ℂ)‖ = 1 := by rw [hξ₃ϖ, Units.val_one, norm_one]
  have hξ₂ϖ : ξ₂ (uniformizerUnit K v) = θ (uniformizerUnit K v) := by
    have h := congrArg (fun f : (v.adicCompletion K)ˣ →* ℂˣ => f (uniformizerUnit K v)) hprod
    first
      | (simp only [MonoidHom.mul_apply, hξ₁ϖ, hξ₃ϖ, one_mul, mul_one] at h; exact h)
      | (simpa [hξ₁ϖ, hξ₃ϖ] using h)
  have n₂ : ‖((ξ₂ (uniformizerUnit K v) : ℂˣ) : ℂ)‖ = 1 := by rw [hξ₂ϖ]; exact hθϖ
  have u₁ : ‖stdRootNumberAt K v ξ₁‖ = 1 := hunit ξ₁ T (by omega) hξ₁ n₁
  have u₂ : ‖stdRootNumberAt K v ξ₂‖ = 1 := hunit ξ₂ T (by omega) hξ₂ n₂
  have u₃ : ‖stdRootNumberAt K v ξ₃‖ = 1 := hunit ξ₃ c (by omega) hξ₃ n₃
  obtain ⟨E, hE⟩ : ∃ E : ℂ, E = stdRootNumberAt K v ξ₁ * stdRootNumberAt K v ξ₂ * stdRootNumberAt K v ξ₃ :=
    ⟨_, rfl⟩
  have hEn : ‖E‖ = 1 := by simp only [hE, norm_mul, u₁, u₂, u₃, mul_one]
  have hE0 : E ≠ 0 := by
    intro h
    rw [h, norm_zero] at hEn
    exact zero_ne_one hEn
  have hE' : stdRootNumberAt K v ξ₁ * stdRootNumberAt K v ξ₃ * stdRootNumberAt K v ξ₂ = E := by
    rw [hE]
    ring
  obtain ⟨w, hw⟩ := IsAlgClosed.exists_pow_nat_eq (z / E) (by omega : 0 < T - c)
  have hw1 : ‖w‖ = 1 := by
    have h1 : ‖w‖ ^ (T - c) = 1 := by rw [← norm_pow, hw, norm_div, hz, hEn, div_one]
    exact (pow_eq_one_iff_of_nonneg (norm_nonneg w) (by omega)).mp h1
  have hw0 : w ≠ 0 := by
    intro h
    rw [h, norm_zero] at hw1
    exact zero_ne_one hw1
  obtain ⟨η, hη, hηϖ⟩ := hunr (Units.mk0 w hw0) (by simpa using hw1)
  have hηval : ((η (uniformizerUnit K v) : ℂˣ) : ℂ) = w := by rw [hηϖ, Units.val_mk0]
  have nη : ‖((η (uniformizerUnit K v) : ℂˣ) : ℂ)‖ = 1 := by rw [hηval]; exact hw1
  have e₁ : HasConductorExponentAt K v (ξ₁ * η) T := hasConductorExponentAt_mul_of_lt K v hξ₁ hη (by omega)
  have e₃ : HasConductorExponentAt K v (ξ₃ * η⁻¹) c :=
    hasConductorExponentAt_mul_of_lt K v hξ₃ (hasConductorExponentAt_inv K v hη) (by omega)
  have htw := stdRootNumberAt_mul_twist_mul_twist_inv K v hψ hξ₁ hξ₃ hη hcT.le n₁ n₃ nη
  rw [hηval, hw] at htw
  refine ⟨![ξ₁ * η, ξ₂, ξ₃ * η⁻¹], ![T, T, c], ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro i
    fin_cases i
    · exact isLocallyConstant_of_hasConductorExponentAt K v e₁
    · exact isLocallyConstant_of_hasConductorExponentAt K v hξ₂
    · exact isLocallyConstant_of_hasConductorExponentAt K v e₃
  · intro i
    fin_cases i
    · show 1 ≤ T ∧ HasConductorExponentAt K v (ξ₁ * η) T
      exact ⟨by omega, e₁⟩
    · show 1 ≤ T ∧ HasConductorExponentAt K v ξ₂ T
      exact ⟨by omega, hξ₂⟩
    · show 1 ≤ c ∧ HasConductorExponentAt K v (ξ₃ * η⁻¹) c
      exact ⟨by omega, e₃⟩
  · rw [Fin.sum_univ_three]
    show T + T + c = A
    omega
  · intro i
    fin_cases i
    · show ‖(((ξ₁ * η) (uniformizerUnit K v) : ℂˣ) : ℂ)‖ = 1
      rw [MonoidHom.mul_apply, Units.val_mul, norm_mul, n₁, nη, one_mul]
    · show ‖((ξ₂ (uniformizerUnit K v) : ℂˣ) : ℂ)‖ = 1
      exact n₂
    · show ‖(((ξ₃ * η⁻¹) (uniformizerUnit K v) : ℂˣ) : ℂ)‖ = 1
      have hinv : ((η⁻¹ (uniformizerUnit K v) : ℂˣ) : ℂ) = (((η (uniformizerUnit K v) : ℂˣ) : ℂ))⁻¹ := by
        rw [MonoidHom.inv_apply]
        exact Units.val_inv_eq_inv_val _
      rw [MonoidHom.mul_apply, Units.val_mul, norm_mul, n₃, hinv, norm_inv, nη, inv_one, one_mul]
  · show ξ₁ * η * ξ₂ * (ξ₃ * η⁻¹) = θ
    have hηη : η * η⁻¹ = 1 := mul_inv_cancel η
    calc ξ₁ * η * ξ₂ * (ξ₃ * η⁻¹)
      _ = ξ₁ * ξ₂ * η * (ξ₃ * η⁻¹) := congrArg (· * (ξ₃ * η⁻¹)) (mul_right_comm ξ₁ η ξ₂)
      _ = ξ₁ * ξ₂ * (η * (ξ₃ * η⁻¹)) := mul_assoc (ξ₁ * ξ₂) η (ξ₃ * η⁻¹)
      _ = ξ₁ * ξ₂ * (ξ₃ * (η * η⁻¹)) := congrArg (ξ₁ * ξ₂ * ·) (mul_left_comm η ξ₃ η⁻¹)
      _ = ξ₁ * ξ₂ * (ξ₃ * 1) := congrArg (ξ₁ * ξ₂ * ·) (congrArg (ξ₃ * ·) hηη)
      _ = ξ₁ * ξ₂ * ξ₃ := congrArg (ξ₁ * ξ₂ * ·) (mul_one ξ₃)
      _ = θ := hprod
  · rw [Fin.prod_univ_three]
    show stdRootNumberAt K v (ξ₁ * η) * stdRootNumberAt K v ξ₂ * stdRootNumberAt K v (ξ₃ * η⁻¹) = z
    first
      | (rw [mul_right_comm, htw, mul_assoc, hE', div_mul_eq_mul_div, mul_div_assoc, div_self hE0, mul_one]; done)
      | (rw [mul_right_comm, htw, mul_assoc, hE']; field_simp)

end

section

open NumberField NumberField.AdelicLevel IsDedekindDomain LanglandsTunnell.TateLocal

variable (K : Type) [Field K] [NumberField K] (v : HeightOneSpectrum (𝓞 K))

private def unramifiedCharOf (z : ℂˣ) : (v.adicCompletion K)ˣ →* ℂˣ where
  toFun x := z ^ (-(WithZero.log (Valued.v (x : v.adicCompletion K))))
  map_one' := by simp
  map_mul' x y := by
    have hx : Valued.v (x : v.adicCompletion K) ≠ 0 := (Valuation.ne_zero_iff _).mpr x.ne_zero
    have hy : Valued.v (y : v.adicCompletion K) ≠ 0 := (Valuation.ne_zero_iff _).mpr y.ne_zero
    simp only [Units.val_mul, map_mul, WithZero.log_mul hx hy, neg_add, zpow_add]

private theorem unramifiedCharOf_apply (z : ℂˣ) (x : (v.adicCompletion K)ˣ) :
    unramifiedCharOf K v z x = z ^ (-(WithZero.log (Valued.v (x : v.adicCompletion K)))) :=
  rfl

private theorem unramifiedCharOf_of_valued_eq_one (z : ℂˣ) {u : (v.adicCompletion K)ˣ}
    (hu : Valued.v (u : v.adicCompletion K) = 1) : unramifiedCharOf K v z u = 1 := by
  rw [unramifiedCharOf_apply, hu, WithZero.log_one, neg_zero, zpow_zero]

private theorem hasConductorExponentAt_zero_unramifiedCharOf (z : ℂˣ) :
    HasConductorExponentAt K v (unramifiedCharOf K v z) 0 :=
  (hasConductorExponentAt_zero_iff K v).mpr fun _ hu => unramifiedCharOf_of_valued_eq_one K v z hu

private theorem unramifiedCharOf_uniformizerUnit (z : ℂˣ) :
    unramifiedCharOf K v z (uniformizerUnit K v) = z := by
  rw [unramifiedCharOf_apply, valued_uniformizerUnit, WithZero.log_exp, neg_neg, zpow_one]

private theorem norm_unramifiedCharOf_uniformizerUnit (z : ℂˣ) :
    ‖(unramifiedCharOf K v z (uniformizerUnit K v) : ℂ)‖ = ‖(z : ℂ)‖ := by
  rw [unramifiedCharOf_uniformizerUnit]

private theorem isLocallyConstant_unramifiedCharOf (z : ℂˣ) :
    IsLocallyConstant (unramifiedCharOf K v z) := by
  refine (IsLocallyConstant.iff_eventually_eq _).mpr fun x => ?_
  have hx : Valued.v (x : v.adicCompletion K) ≠ 0 := (Valuation.ne_zero_iff _).mpr x.ne_zero
  have hloc : ∀ᶠ y in nhds (x : v.adicCompletion K), Valued.v y = Valued.v (x : v.adicCompletion K) :=
    Valued.locally_const hx
  have hv : ∀ᶠ y in nhds x,
      Valued.v ((y : (v.adicCompletion K)ˣ) : v.adicCompletion K) = Valued.v (x : v.adicCompletion K) :=
    (Units.continuous_val.tendsto x).eventually hloc
  filter_upwards [hv] with y hy
  rw [unramifiedCharOf_apply, unramifiedCharOf_apply, hy]

private theorem localLFactorAt_unramifiedCharOf (z : ℂˣ) (s : ℂ) :
    localLFactorAt K v (unramifiedCharOf K v z) s
      = (1 - (z : ℂ) * (Ideal.absNorm v.asIdeal : ℂ) ^ (-s))⁻¹ := by
  rw [localLFactorAt_of_hasConductorExponentAt_zero K v (hasConductorExponentAt_zero_unramifiedCharOf K v z),
    unramifiedCharOf_uniformizerUnit]

private theorem exists_hasConductorExponentAt_zero_and_apply_uniformizerUnit_eq (z : ℂˣ) :
    ∃ ω : (v.adicCompletion K)ˣ →* ℂˣ, IsLocallyConstant ω ∧ HasConductorExponentAt K v ω 0 ∧
      ω (uniformizerUnit K v) = z :=
  ⟨unramifiedCharOf K v z, isLocallyConstant_unramifiedCharOf K v z,
    hasConductorExponentAt_zero_unramifiedCharOf K v z, unramifiedCharOf_uniformizerUnit K v z⟩

end

section

open IsDedekindDomain NumberField Polynomial LanglandsTunnell.CubicInduction LanglandsTunnell.RankinSelberg

section SaturatedEuler

variable (F : Type*) [Field F] {K : Type*} [Field K] [Algebra (𝓞 F) (𝓞 K)] [Algebra.IsIntegral (𝓞 F) (𝓞 K)]
  {R : Type*} [CommRing R]

private theorem inducedFactor_of_eq_zero (c : HeightOneSpectrum (𝓞 K) → R) {𝔓 : HeightOneSpectrum (𝓞 K)}
    (h : c 𝔓 = 0) : inducedFactor F c 𝔓 = 1 := by
  simp [inducedFactor, h]

private theorem inducedEulerPoly_eq_one_of_forall_eq_zero (c : HeightOneSpectrum (𝓞 K) → R)
    (p : HeightOneSpectrum (𝓞 F)) (h : ∀ 𝔓 ∈ primeFibre F K p, c 𝔓 = 0) :
    inducedEulerPoly F c p = 1 := by
  unfold inducedEulerPoly
  exact finprod_mem_of_eqOn_one fun 𝔓 h𝔓 => inducedFactor_of_eq_zero F c (h 𝔓 h𝔓)

end SaturatedEuler

section Saturated

variable (K : Type) [Field K] [NumberField K] [Algebra (𝓞 ℚ) (𝓞 K)] [Algebra.IsIntegral (𝓞 ℚ) (𝓞 K)]

private theorem inducedCoeff_of_not_isUnramifiedCharAt (μ : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ) {𝔓 : HeightOneSpectrum (𝓞 K)}
    (h : ¬ TateGlobal.IsUnramifiedCharAt μ 𝔓) : inducedCoeff K μ 𝔓 = 0 := by
  simp [inducedCoeff, h]

private theorem inducedEulerPoly_inducedCoeff_eq_one_of_forall_not_isUnramifiedCharAt (μ : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ)
    (v : HeightOneSpectrum (𝓞 ℚ)) (h : ∀ 𝔓 ∈ primeFibre ℚ K v, ¬ TateGlobal.IsUnramifiedCharAt μ 𝔓) :
    inducedEulerPoly ℚ (inducedCoeff K μ) v = 1 :=
  inducedEulerPoly_eq_one_of_forall_eq_zero ℚ _ v fun 𝔓 h𝔓 =>
    inducedCoeff_of_not_isUnramifiedCharAt K μ (h 𝔓 h𝔓)

private theorem inv_eval_inducedEulerPoly_inducedCoeff_eq_one_of_forall_not_isUnramifiedCharAt
    (μ : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ) (v : HeightOneSpectrum (𝓞 ℚ))
    (h : ∀ 𝔓 ∈ primeFibre ℚ K v, ¬ TateGlobal.IsUnramifiedCharAt μ 𝔓) (x : ℂ) :
    ((inducedEulerPoly ℚ (inducedCoeff K μ) v).eval x)⁻¹ = 1 := by
  rw [inducedEulerPoly_inducedCoeff_eq_one_of_forall_not_isUnramifiedCharAt K μ v h, eval_one, inv_one]

end Saturated

end

section

open IsDedekindDomain NumberField NumberField.TateGlobal AutomorphicForm LanglandsTunnell.Converse LanglandsTunnell.RankinSelberg LanglandsTunnell.CubicLambda LanglandsTunnell LanglandsTunnell.CubicInduction

private theorem exists_saturated_local_data_assembly
    (K : Type) [Field K] [NumberField K] [Algebra (𝓞 ℚ) (𝓞 K)] [Algebra.IsIntegral (𝓞 ℚ) (𝓞 K)]
    (μ : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ)
    (ω : (AdeleRing (𝓞 ℚ) ℚ)ˣ →* ℂˣ)
    (hω : IsAdmissibleTwist ℚ ω)
    (hsat : ∀ v : HeightOneSpectrum (𝓞 ℚ), IsBadPlace K μ v →
      (∀ w ∈ primeFibre ℚ K v, ¬ IsUnramifiedCharAt μ w) ∧
        ∃ t : ℕ, LanglandsTunnell.TateLocal.HasConductorExponentAt ℚ v (localChar ω v) t ∧
          2 * (t : ℤ) + 12 ≤
            ∑ᶠ w ∈ primeFibre ℚ K v, (v.asIdeal.inertiaDeg' w.asIdeal : ℤ) * LanglandsTunnell.Converse.pinnedExp K μ w)
    (hB : ∀ (v : HeightOneSpectrum (𝓞 ℚ)) (χ : (v.adicCompletion ℚ)ˣ →* ℂˣ) (a : ℕ), 1 ≤ a →
      LanglandsTunnell.TateLocal.HasConductorExponentAt ℚ v χ a →
      ‖((χ (NumberField.AdelicLevel.uniformizerUnit ℚ v) : ℂˣ) : ℂ)‖ = 1 →
      ‖LanglandsTunnell.TateLocal.stdRootNumberAt ℚ v χ‖ = 1)
    (hA : ∀ (v : HeightOneSpectrum (𝓞 ℚ)) (z : ℂˣ), ∃ η : (v.adicCompletion ℚ)ˣ →* ℂˣ, IsLocallyConstant η ∧
      LanglandsTunnell.TateLocal.HasConductorExponentAt ℚ v η 0 ∧ η (NumberField.AdelicLevel.uniformizerUnit ℚ v) = z)
    (hE : ∀ v : HeightOneSpectrum (𝓞 ℚ), (∀ w ∈ primeFibre ℚ K v, ¬ IsUnramifiedCharAt μ w) →
      inducedEulerPoly ℚ (inducedCoeff K μ) v = 1)
    :
    ∀ v : HeightOneSpectrum (𝓞 ℚ), IsBadPlace K μ v → ∀ θ : ℂ, ‖θ‖ = 1 →
      ∃ (ν : Fin 3 → ((v.adicCompletion ℚ)ˣ →* ℂˣ)) (a : Fin 3 → ℕ),
        (∀ i, IsLocallyConstant (ν i)) ∧
        (∀ i, 1 ≤ a i ∧ LanglandsTunnell.TateLocal.HasConductorExponentAt ℚ v (ν i) (a i)) ∧
        (∑ i, (a i : ℤ)) =
          ∑ᶠ w ∈ primeFibre ℚ K v, (v.asIdeal.inertiaDeg' w.asIdeal : ℤ) * LanglandsTunnell.Converse.pinnedExp K μ w ∧
        (∀ i, ‖((ν i (NumberField.AdelicLevel.uniformizerUnit ℚ v) : ℂˣ) : ℂ)‖ = 1) ∧
        ν 0 * ν 1 * ν 2 = localChar ω v ∧
        (∀ s : ℂ, (∏ i, LanglandsTunnell.TateLocal.localLFactorAt ℚ v (ν i) s) =
          ((inducedEulerPoly ℚ (inducedCoeff K μ) v).eval ((Ideal.absNorm v.asIdeal : ℂ) ^ (-s)))⁻¹) ∧
        (∏ i, LanglandsTunnell.TateLocal.stdRootNumberAt ℚ v (ν i)) = θ := by
  intro v hv θ hθ
  obtain ⟨h1, t, ht, hle⟩ := hsat v hv
  set S : ℤ :=
    ∑ᶠ w ∈ primeFibre ℚ K v, (v.asIdeal.inertiaDeg' w.asIdeal : ℤ) * LanglandsTunnell.Converse.pinnedExp K μ w
    with hS
  have hS0 : (0 : ℤ) ≤ S := le_trans (by omega) hle
  have hAS : ((S.toNat : ℕ) : ℤ) = S := Int.toNat_of_nonneg hS0
  have hA' : 2 * t + 12 ≤ S.toNat := by omega
  have hωϖ : ‖((localChar ω v (NumberField.AdelicLevel.uniformizerUnit ℚ v) : ℂˣ) : ℂ)‖ = 1 := by
    first
      | exact hω.2.2 _
      | (change ‖((ω _ : ℂˣ) : ℂ)‖ = 1; exact hω.2.2 _)
      | (unfold localChar; simp only [MonoidHom.comp_apply]; exact hω.2.2 _)
  have hunr : ∀ u : ℂˣ, ‖(u : ℂ)‖ = 1 → ∃ η : (v.adicCompletion ℚ)ˣ →* ℂˣ,
      LanglandsTunnell.TateLocal.HasConductorExponentAt ℚ v η 0 ∧
        η (NumberField.AdelicLevel.uniformizerUnit ℚ v) = u := by
    intro u _
    obtain ⟨η, -, h0, hz⟩ := hA v u
    exact ⟨η, h0, hz⟩
  obtain ⟨ν, a, hlc, hexp, hsum, hnorm, hprod, hphase⟩ :=
    exists_fin_three_saturated_local_data ℚ v
      (LanglandsTunnell.TateLocal.psiLocal_ne_one ℚ v) (hB v) hunr (localChar ω v) ht hωϖ S.toNat hA' θ hθ
  refine ⟨ν, a, hlc, hexp, ?_, hnorm, hprod, ?_, hphase⟩
  · first
      | (rw [← Nat.cast_sum, hsum]; exact hAS)
      | (rw [← hsum] at hAS; exact_mod_cast hAS)
  · intro s
    rw [hE v h1, Polynomial.eval_one, inv_one]
    refine Finset.prod_eq_one fun i _ => ?_
    refine LanglandsTunnell.TateLocal.localLFactorAt_of_not_hasConductorExponentAt_zero ℚ v ?_ s
    intro h0
    have h1i := (hexp i).1
    have h0i := LanglandsTunnell.TateLocal.hasConductorExponentAt_unique ℚ v (hexp i).2 h0
    omega

theorem solution
    (K : Type) [Field K] [NumberField K] [Algebra (𝓞 ℚ) (𝓞 K)] [Algebra.IsIntegral (𝓞 ℚ) (𝓞 K)]
    (hdeg : Module.finrank ℚ K = 3)
    (μ : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ) (hμ : IsAdmissibleTwist K μ)
    (ω : (AdeleRing (𝓞 ℚ) ℚ)ˣ →* ℂˣ)
    (hω : IsAdmissibleTwist ℚ ω ∧
      (∀ p : HeightOneSpectrum (𝓞 ℚ), ¬ IsBadPlace K μ p →
        IsUnramifiedCharAt ω p ∧ eulerCoeff ℚ ω p = inducedE3 ℚ (inducedCoeff K μ) p) ∧
      ∀ (uR : ∀ w : InfinitePlace K, w.IsReal → ℂ) (aR : ∀ w : InfinitePlace K, w.IsReal → ZMod 2)
        (uC : ∀ w : InfinitePlace K, w.IsComplex → ℂ) (kC : ∀ w : InfinitePlace K, w.IsComplex → ℤ),
        (∀ w, ∀ hw : w.IsReal, IsArchCompAt K μ w (uR w hw) ((aR w hw).val : ℤ)) →
        (∀ w, ∀ hw : w.IsComplex, IsArchCompAt K μ w (uC w hw) (kC w hw)) →
        ∀ v : InfinitePlace ℚ, v.IsReal →
          IsArchCompAt ℚ ω v
            ((∑ᶠ (w) (hw : w.IsReal), uR w hw) + (∑ᶠ (w) (hw : w.IsComplex), 2 * uC w hw))
            ((∑ᶠ (w) (hw : w.IsReal), ((aR w hw).val : ℤ)) + (∑ᶠ (w) (hw : w.IsComplex), (kC w hw + 1))))
    (hsat : ∀ v : HeightOneSpectrum (𝓞 ℚ), IsBadPlace K μ v →
      (∀ w ∈ primeFibre ℚ K v, ¬ IsUnramifiedCharAt μ w) ∧
        ∃ t : ℕ, LanglandsTunnell.TateLocal.HasConductorExponentAt ℚ v (localChar ω v) t ∧
          2 * (t : ℤ) + 12 ≤
            ∑ᶠ w ∈ primeFibre ℚ K v, (v.asIdeal.inertiaDeg' w.asIdeal : ℤ) * LanglandsTunnell.Converse.pinnedExp K μ w)
    :
    ∀ v : HeightOneSpectrum (𝓞 ℚ), IsBadPlace K μ v → ∀ θ : ℂ, ‖θ‖ = 1 →
      ∃ (ν : Fin 3 → ((v.adicCompletion ℚ)ˣ →* ℂˣ)) (a : Fin 3 → ℕ),
        (∀ i, IsLocallyConstant (ν i)) ∧
        (∀ i, 1 ≤ a i ∧ LanglandsTunnell.TateLocal.HasConductorExponentAt ℚ v (ν i) (a i)) ∧
        (∑ i, (a i : ℤ)) =
          ∑ᶠ w ∈ primeFibre ℚ K v, (v.asIdeal.inertiaDeg' w.asIdeal : ℤ) * LanglandsTunnell.Converse.pinnedExp K μ w ∧
        (∀ i, ‖((ν i (NumberField.AdelicLevel.uniformizerUnit ℚ v) : ℂˣ) : ℂ)‖ = 1) ∧
        ν 0 * ν 1 * ν 2 = localChar ω v ∧
        (∀ s : ℂ, (∏ i, LanglandsTunnell.TateLocal.localLFactorAt ℚ v (ν i) s) =
          ((inducedEulerPoly ℚ (inducedCoeff K μ) v).eval ((Ideal.absNorm v.asIdeal : ℂ) ^ (-s)))⁻¹) ∧
        (∏ i, LanglandsTunnell.TateLocal.stdRootNumberAt ℚ v (ν i)) = θ := by
  have _ := hdeg
  have _ := hμ
  exact exists_saturated_local_data_assembly K μ ω hω.1 hsat
    (LanglandsTunnell.TateLocal.norm_stdRootNumberAt_eq_one ℚ)
    (exists_hasConductorExponentAt_zero_and_apply_uniformizerUnit_eq ℚ)
    (inducedEulerPoly_inducedCoeff_eq_one_of_forall_not_isUnramifiedCharAt K μ)

end

end

end S_LanglandsTunnell_CubicInduction_exists_prod_eq_localChar_and_prod_stdRootNumberAt_eq_of_saturated
end P2MW
export P2MW.S_LanglandsTunnell_CubicInduction_exists_prod_eq_localChar_and_prod_stdRootNumberAt_eq_of_saturated (solution)
