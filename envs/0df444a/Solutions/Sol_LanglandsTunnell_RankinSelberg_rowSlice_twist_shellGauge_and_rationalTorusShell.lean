-- Prove2me | solution 1 for LanglandsTunnell.RankinSelberg.rowSlice_twist_shellGauge_and_rationalTorusShell
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:08.670037+00:00
-- url     : https://prove2.me/submissions/55baba20-100a-5dc2-afc7-71ee3f717796

import Definitions.Def_AutomorphicForm_LocalOrbitalBase
import Definitions.Def_AutomorphicForm_ConstantTerm
import Definitions.Def_AdelicDock_LocalEmbedding
import Definitions.Def_UnramifiedWhittaker_HeckeRecursion
import Definitions.Def_LanglandsTunnell_CubicInduction_IotaTorus
import Definitions.Def_LanglandsTunnell_RSCarrier
import Definitions.Def_LanglandsTunnell_StandardLocalConstantsAt
import Definitions.Def_LanglandsTunnell_TateLocalConstantsAt
import Definitions.Def_LanglandsTunnell_TateLocalZeta

import Theorems.Thm_LanglandsTunnell_RankinSelberg_exists_rowSlice_shell_profile_of_isLocallyConstant_of_hasCompactSupport
import Theorems.Thm_AdelicDock_isCompact_and_isOpen_localLevelOne
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_LanglandsTunnell_RankinSelberg_rowSlice_twist_shellGauge_and_rationalTorusShell
p2m_attr_erase "instance" "IsDedekindDomain.HeightOneSpectrum.Extension.instAlgebraSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersValEqUnder IsDedekindDomain.HeightOneSpectrum.Extension.instAlgebraSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersValEqUnder_1 IsDedekindDomain.HeightOneSpectrum.instMulActionHomClassAlgHomTensorProductAdicCompletionForallValEqUnder_definitions IsDedekindDomain.HeightOneSpectrum.Extension.instAlgebraAdicCompletionValEqUnder IsDedekindDomain.HeightOneSpectrum.adicCompletion.instFiniteForallValEqUnderOfFiniteDimensional_definitions IsDedekindDomain.HeightOneSpectrum.instIsBiscalarSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersTensorProductCoeAlgHomTensorAdicCompletionIntegersTo IsDedekindDomain.HeightOneSpectrum.Extension.instContinuousSMulAdicCompletionValEqUnder IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsModuleTopology IsDedekindDomain.HeightOneSpectrum.Extension.instFiniteSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersValEqUnderOfFiniteDimensional IsDedekindDomain.HeightOneSpectrum.adicCompletion.instFiniteValEqUnderOfFiniteDimensional_definitions instIsBiscalarTensorProductCoeAlgHomBaseChange_of_algebraMap IsDedekindDomain.HeightOneSpectrum.instIsScalarTowerSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersValEqUnder_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsModuleTopologyPi IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions Submodule.instIsTopologicalModuleSubtypeMem Pi.instTopologicalModule IsTopologicalModule.toContinuousSMul IsTopologicalModule.toContinuousAdd instFunLike SemialgHomClass.toSemilinearMapClass instCoeTCSemialgHom SemialgHomClass.toRingHomClass SemialgHomClass.instSemialgHom instFiniteResidueFieldAdicCompletionRingOfIntegersWithZeroMultiplicativeInt_definitions NumberField.instCompactSpaceAdicCompletionIntegers Rat.adicCompletion.locallyCompactSpace NumberField.instFiniteResidueFieldAdicCompletionIntegers instWeaklyLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instCountableOfNumberField_definitions"
p2m_attr_erase "simp" "SemialgHom.baseChange_of_algebraMap_tmul_left SemialgHom.baseChangeRightOfAlgebraMap_apply Pi.semialgHomPi_apply Pi.semialgHom_apply Module.Basis.rightBaseChange_apply LinearEquiv.coe_mulLeft LinearEquiv.coe_mulRight WithVal.semialgebraMap_toFun_ofVal Module.Basis.rightBaseChange_repr IsDedekindDomain.HeightOneSpectrum.adicCompletionIntegers.tensorCoe_tmul IsDedekindDomain.HeightOneSpectrum.tensorAdicCompletionIntegersTo_tmul SemialgHom.baseChangeRightOfAlgebraMap_coe IsDedekindDomain.HeightOneSpectrum.adicCompletion.integerBaseChangeLinearEquiv_tmul_apply SemialgHom.baseChange_of_algebraMap_tmul_right IsLocalization.map_moduleTensorEquiv_symm_tmul IsLocalization.leftModuleTensorEquiv_apply IsLocalization.moduleLid_symm_apply IsLocalization.leftModuleTensorEquiv_symm_apply IsLocalization.map_moduleTensorEquiv_tmul IsModuleTopology.continuousLinearEquiv_apply AlgEquiv.extendScalars_symm_apply IsModuleTopology.Module.Basis.equivFun_homeo_symm_apply IsModuleTopology.Module.Basis.equivFun_homeo_apply IsModuleTopology.continuousAlgEquivOfIsBiscalar_apply AlgEquiv.extendScalars_apply IsModuleTopology.continuousLinearEquiv_symm_apply SemialgHom.restrictScalars_toFun SemialgHom.mk.sizeOf_spec SemialgHom.mk.injEq SemialgHom.coe_coe coe_mk TensorProduct.RightActions.smul_def TensorProduct.RightActions.Module.TensorProduct.comm_symm_apply_tmul TensorProduct.RightActions.LinearMap.baseChange_id TensorProduct.RightActions.algebraMap_eval TensorProduct.RightActions.Module.TensorProduct.comm_apply_tmul TensorProduct.RightActions.Algebra.TensorProduct.comm_symm_apply_tmul TensorProduct.RightActions.Algebra.TensorProduct.comm_apply_tmul"

set_option autoImplicit false

open MeasureTheory IsDedekindDomain NumberField AutomorphicForm UnramifiedWhittaker LanglandsTunnell.TateLocal LanglandsTunnell.CubicInduction

namespace GamKit

variable (p : HeightOneSpectrum (𝓞 ℚ))
local notation "F" => (p.adicCompletion ℚ)
local notation "O" => (p.adicCompletionIntegers ℚ)
local notation "G2" => (GL (Fin 2) (p.adicCompletion ℚ))
local notation "M22" => (Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ))

variable {ϖ : p.adicCompletionIntegers ℚ}

theorem det_scalarPi (hπ : algebraMap O F ϖ ≠ 0) :
    Matrix.GeneralLinearGroup.det (scalarPi (algebraMap O F ϖ) hπ) = Units.mk0 (algebraMap O F ϖ) hπ ^ 2 := by
  apply Units.ext
  simp [Matrix.GeneralLinearGroup.val_det_apply, scalarPi, Matrix.det_fin_two_of, pow_two]

theorem det_diagZ (hπ : algebraMap O F ϖ ≠ 0) (m : ℤ) :
    Matrix.GeneralLinearGroup.det (diagZ (algebraMap O F ϖ) hπ m) = Units.mk0 (algebraMap O F ϖ) hπ ^ m := by
  apply Units.ext
  simp [Matrix.GeneralLinearGroup.val_det_apply, diagZ, Matrix.det_fin_two_of, Units.val_zpow_eq_zpow_val]

theorem det_diagUnitGL2 (x : Fˣ) : Matrix.GeneralLinearGroup.det (diagUnitGL2 x : G2) = x := by
  apply Units.ext
  simp [Matrix.GeneralLinearGroup.val_det_apply, Matrix.det_fin_two_of]

theorem diagZ_eq_diagUnitGL2 (hπ : algebraMap O F ϖ ≠ 0) (m : ℤ) :
    diagZ (algebraMap O F ϖ) hπ m = diagUnitGL2 (Units.mk0 (algebraMap O F ϖ) hπ ^ m * 1) := by
  apply Units.ext
  rw [mul_one, coe_diagUnitGL2, Units.val_zpow_eq_zpow_val]
  simp [diagZ]

theorem continuous_det : Continuous (Matrix.GeneralLinearGroup.det : G2 → Fˣ) := by
  rw [Units.continuous_iff]
  refine ⟨?_, ?_⟩
  · have : (Units.val ∘ (Matrix.GeneralLinearGroup.det : G2 → Fˣ)) = fun g : G2 => (g : M22).det := by
      funext g; simp [Matrix.GeneralLinearGroup.val_det_apply]
    rw [this]; exact Units.continuous_val.matrix_det
  · have : (fun g : G2 => (((Matrix.GeneralLinearGroup.det g)⁻¹ : Fˣ) : F)) = fun g : G2 => (((g⁻¹ : G2)) : M22).det := by
      funext g; rw [← map_inv]; simp [Matrix.GeneralLinearGroup.val_det_apply]
    rw [this]; exact Units.continuous_coe_inv.matrix_det

theorem exists_bound_chi_det (χ : Fˣ →* ℂˣ) (hχ : IsLocallyConstant χ) :
    ∃ Cχ : ℝ, 0 ≤ Cχ ∧ ∀ k ∈ AdelicDock.localLevelOne (𝓞 ℚ) ℚ p ⊤, ‖((χ (Matrix.GeneralLinearGroup.det k) : ℂˣ) : ℂ)‖ ≤ Cχ := by
  have hK := (AdelicDock.isCompact_and_isOpen_localLevelOne ℚ p (⊤ : Ideal (𝓞 ℚ)) (by simp)).1
  have hc : Continuous fun k : G2 => ‖((χ (Matrix.GeneralLinearGroup.det k) : ℂˣ) : ℂ)‖ :=
    (Units.continuous_val.comp (hχ.continuous.comp (continuous_det p))).norm
  obtain ⟨C, hC⟩ := hK.exists_bound_of_continuousOn (f := fun k : G2 => ((χ (Matrix.GeneralLinearGroup.det k) : ℂˣ) : ℂ))
    (Units.continuous_val.comp (hχ.continuous.comp (continuous_det p))).continuousOn
  exact ⟨max C 0, le_max_right _ _, fun k hk => (hC k hk).trans (le_max_left _ _)⟩

theorem zpow_le_max_zpow_abs (r : ℝ) (hr : 0 < r) (e : ℤ) : r ^ e ≤ (max r r⁻¹) ^ |e| := by
  rcases Int.eq_nat_or_neg e with ⟨n, rfl | rfl⟩
  · rw [Nat.abs_cast, zpow_natCast, zpow_natCast]
    exact pow_le_pow_left₀ hr.le (le_max_left _ _) n
  · rw [abs_neg, Nat.abs_cast, zpow_neg, zpow_natCast, zpow_natCast, ← inv_pow]
    exact pow_le_pow_left₀ (inv_pos.2 hr).le (le_max_right _ _) n

theorem zpow_le_zpow_base {R S : ℝ} (hR : 0 ≤ R) (hRS : R ≤ S) {k : ℤ} (hk : 0 ≤ k) : R ^ k ≤ S ^ k := by
  obtain ⟨n, rfl⟩ := Int.eq_ofNat_of_zero_le hk
  rw [zpow_natCast, zpow_natCast]
  exact pow_le_pow_left₀ hR hRS n

theorem exists_growth (r N : ℝ) (hr : 0 < r) (hN : 1 < N) (m₀ c : ℤ) :
    ∃ (t : ℕ) (K : ℝ), 0 ≤ K ∧ ∀ n₁ n₂ : ℤ, m₀ ≤ n₁ → m₀ ≤ n₂ → n₂ ≤ c →
      r ^ (2 * n₂ + n₁) ≤ K * N ^ ((t : ℤ) * (n₁ + n₂)) := by
  set R : ℝ := max r r⁻¹ with hR
  have hR1 : 1 ≤ R := by
    by_cases h : 1 ≤ r
    · exact h.trans (le_max_left _ _)
    · push Not at h
      exact ((one_le_inv₀ hr).2 h.le).trans (le_max_right _ _)
  have hR0 : 0 < R := one_pos.trans_le hR1
  have hN0 : 0 < N := one_pos.trans hN
  obtain ⟨t, ht⟩ := pow_unbounded_of_one_lt R hN
  set A₀ : ℤ := max |m₀| |c| with hA₀
  refine ⟨t, (N ^ (t : ℤ)) ^ (-(2 * m₀)) * R ^ (2 * |m₀|) * R ^ A₀, by positivity, ?_⟩
  intro n₁ n₂ h₁ h₂ h₂c
  have hr0 : r ≠ 0 := hr.ne'
  rw [show (2 * n₂ + n₁ : ℤ) = (n₁ + n₂) + n₂ by ring, zpow_add₀ hr0]
  have e1 : r ^ (n₁ + n₂) ≤ R ^ |n₁ + n₂| := zpow_le_max_zpow_abs r hr _
  have e2 : r ^ n₂ ≤ R ^ |n₂| := zpow_le_max_zpow_abs r hr _
  have habs : |n₁ + n₂| ≤ (n₁ + n₂ - 2 * m₀) + 2 * |m₀| := by
    rcases le_or_gt 0 (n₁ + n₂) with h | h
    · rw [abs_of_nonneg h]; have := abs_nonneg m₀; have := le_abs_self m₀; omega
    · rw [abs_of_neg h]; have := neg_abs_le m₀; have := le_abs_self m₀; omega
  have e3 : R ^ |n₁ + n₂| ≤ R ^ (n₁ + n₂ - 2 * m₀) * R ^ (2 * |m₀|) := by
    rw [← zpow_add₀ hR0.ne']; exact zpow_le_zpow_right₀ hR1 habs
  have e4 : R ^ (n₁ + n₂ - 2 * m₀) ≤ (N ^ (t : ℤ)) ^ (n₁ + n₂ - 2 * m₀) := by
    refine zpow_le_zpow_base hR0.le ?_ (by omega)
    rw [zpow_natCast]; exact ht.le
  have e5 : (N ^ (t : ℤ)) ^ (n₁ + n₂ - 2 * m₀) = N ^ ((t : ℤ) * (n₁ + n₂)) * (N ^ (t : ℤ)) ^ (-(2 * m₀)) := by
    rw [← zpow_mul, ← zpow_mul, ← zpow_add₀ hN0.ne']; congr 1; ring
  have e6 : R ^ |n₂| ≤ R ^ A₀ := by
    refine zpow_le_zpow_right₀ hR1 ?_
    rw [hA₀, abs_le]
    have := le_abs_self m₀; have := neg_abs_le m₀; have := le_abs_self c
    have := le_max_left |m₀| |c|; have := le_max_right |m₀| |c|
    constructor <;> omega
  have hpos1 : 0 ≤ R ^ (2 * |m₀|) := (zpow_pos hR0 _).le
  have hpos2 : 0 ≤ (N ^ (t : ℤ)) ^ (-(2 * m₀)) := (zpow_pos (zpow_pos hN0 _) _).le
  have hpos3 : 0 ≤ N ^ ((t : ℤ) * (n₁ + n₂)) := (zpow_pos hN0 _).le
  calc r ^ (n₁ + n₂) * r ^ n₂ ≤ R ^ |n₁ + n₂| * R ^ |n₂| :=
        mul_le_mul e1 e2 (zpow_pos hr _).le ((zpow_pos hR0 _).le)
    _ ≤ (R ^ (n₁ + n₂ - 2 * m₀) * R ^ (2 * |m₀|)) * R ^ A₀ :=
        mul_le_mul e3 e6 (zpow_pos hR0 _).le (by positivity)
    _ ≤ ((N ^ (t : ℤ)) ^ (n₁ + n₂ - 2 * m₀) * R ^ (2 * |m₀|)) * R ^ A₀ := by
        gcongr
    _ = (N ^ (t : ℤ)) ^ (-(2 * m₀)) * R ^ (2 * |m₀|) * R ^ A₀ * N ^ ((t : ℤ) * (n₁ + n₂)) := by rw [e5]; ring

theorem hAshell_of (hπ : algebraMap O F ϖ ≠ 0)
    (hϖ : Valued.v (algebraMap O F ϖ) = WithZero.exp (-1 : ℤ))
    (Φ : M22 → ℂ) (χ : Fˣ →* ℂˣ) (hχ : IsLocallyConstant χ) (c M : ℤ) (C : ℝ)
    (hprof : letI := localBorel ℚ p
      ∀ k ∈ AdelicDock.localLevelOne (𝓞 ℚ) ℚ p ⊤, ∀ (n₁ n₂ : ℤ) (u : (p.adicCompletion ℚ)ˣ),
      Valued.v (u : (p.adicCompletion ℚ)) = 1 →

        (c < n₂ →
          (∫ x : (p.adicCompletion ℚ), NumberField.StandardAddChar.psiLocal ℚ p x *
            Φ ((unipotent x * (scalarPi (algebraMap (p.adicCompletionIntegers ℚ) (p.adicCompletion ℚ) ϖ) hπ ^ n₂ * diagUnitGL2 (Units.mk0 (algebraMap (p.adicCompletionIntegers ℚ) (p.adicCompletion ℚ) ϖ) hπ ^ n₁ * u) * k) : GL (Fin 2) (p.adicCompletion ℚ)) : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ)) ∂(selfDualHaarAt ℚ p)) = 0) ∧

        (n₂ < -M →
          (∫ x : (p.adicCompletion ℚ), NumberField.StandardAddChar.psiLocal ℚ p x *
            Φ ((unipotent x * (scalarPi (algebraMap (p.adicCompletionIntegers ℚ) (p.adicCompletion ℚ) ϖ) hπ ^ n₂ * diagUnitGL2 (Units.mk0 (algebraMap (p.adicCompletionIntegers ℚ) (p.adicCompletion ℚ) ϖ) hπ ^ n₁ * u) * k) : GL (Fin 2) (p.adicCompletion ℚ)) : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ)) ∂(selfDualHaarAt ℚ p)) = 0) ∧

        (n₁ + n₂ < -M →
          (∫ x : (p.adicCompletion ℚ), NumberField.StandardAddChar.psiLocal ℚ p x *
            Φ ((unipotent x * (scalarPi (algebraMap (p.adicCompletionIntegers ℚ) (p.adicCompletion ℚ) ϖ) hπ ^ n₂ * diagUnitGL2 (Units.mk0 (algebraMap (p.adicCompletionIntegers ℚ) (p.adicCompletion ℚ) ϖ) hπ ^ n₁ * u) * k) : GL (Fin 2) (p.adicCompletion ℚ)) : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ)) ∂(selfDualHaarAt ℚ p)) = 0) ∧

        (c ≤ n₁ + n₂ →
          (∫ x : (p.adicCompletion ℚ), NumberField.StandardAddChar.psiLocal ℚ p x *
            Φ ((unipotent x * (scalarPi (algebraMap (p.adicCompletionIntegers ℚ) (p.adicCompletion ℚ) ϖ) hπ ^ n₂ * diagUnitGL2 (Units.mk0 (algebraMap (p.adicCompletionIntegers ℚ) (p.adicCompletion ℚ) ϖ) hπ ^ n₁ * u) * k) : GL (Fin 2) (p.adicCompletion ℚ)) : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ)) ∂(selfDualHaarAt ℚ p)) =
          (∫ x : (p.adicCompletion ℚ), NumberField.StandardAddChar.psiLocal ℚ p x *
            Φ ((unipotent x * (scalarPi (algebraMap (p.adicCompletionIntegers ℚ) (p.adicCompletion ℚ) ϖ) hπ ^ n₂ * diagZ (algebraMap (p.adicCompletionIntegers ℚ) (p.adicCompletion ℚ) ϖ) hπ (c - n₂) * k) : GL (Fin 2) (p.adicCompletion ℚ)) : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ)) ∂(selfDualHaarAt ℚ p))) ∧

        (‖(∫ x : (p.adicCompletion ℚ), NumberField.StandardAddChar.psiLocal ℚ p x *
            Φ ((unipotent x * (scalarPi (algebraMap (p.adicCompletionIntegers ℚ) (p.adicCompletion ℚ) ϖ) hπ ^ n₂ * diagUnitGL2 (Units.mk0 (algebraMap (p.adicCompletionIntegers ℚ) (p.adicCompletion ℚ) ϖ) hπ ^ n₁ * u) * k) : GL (Fin 2) (p.adicCompletion ℚ)) : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ)) ∂(selfDualHaarAt ℚ p))‖ ≤ C))
    (A : G2 → ℂ) (hAeq : letI := localBorel ℚ p
      ∀ g : G2, A g = (∫ x : p.adicCompletion ℚ, NumberField.StandardAddChar.psiLocal ℚ p x *
            Φ ((unipotent x * (g) : GL (Fin 2) (p.adicCompletion ℚ)) : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ)) ∂(selfDualHaarAt ℚ p)) * ((χ (Matrix.GeneralLinearGroup.det g) : ℂˣ) : ℂ)) :
    ∃ (m₀ : ℤ) (t : ℕ) (CA : ℝ), ∀ (dn : ℤ × ℤ), ∀ k ∈ AdelicDock.localLevelOne (𝓞 ℚ) ℚ p ⊤,
      (¬ (m₀ ≤ dn.1 ∧ m₀ ≤ dn.2) → A (scalarPi (algebraMap (p.adicCompletionIntegers ℚ) (p.adicCompletion ℚ) ϖ) hπ ^ dn.2 * diagZ (algebraMap (p.adicCompletionIntegers ℚ) (p.adicCompletion ℚ) ϖ) hπ dn.1 * k) = 0) ∧
      ‖A (scalarPi (algebraMap (p.adicCompletionIntegers ℚ) (p.adicCompletion ℚ) ϖ) hπ ^ dn.2 * diagZ (algebraMap (p.adicCompletionIntegers ℚ) (p.adicCompletion ℚ) ϖ) hπ dn.1 * k)‖ ≤ CA * (Ideal.absNorm p.asIdeal : ℝ) ^ ((t : ℤ) * (dn.1 + dn.2)) := by
  classical
  letI := localBorel ℚ p
  set ϖu : Fˣ := Units.mk0 (algebraMap (p.adicCompletionIntegers ℚ) (p.adicCompletion ℚ) ϖ) hπ with hϖu
  obtain ⟨Cχ, hCχ0, hCχ⟩ := exists_bound_chi_det p χ hχ
  set r : ℝ := ‖((χ ϖu : ℂˣ) : ℂ)‖ with hr
  have hr0 : 0 < r := by rw [hr]; exact norm_pos_iff.2 (χ ϖu).ne_zero
  have hN1 : (1 : ℝ) < (Ideal.absNorm p.asIdeal : ℝ) := by exact_mod_cast NumberField.HeightOneSpectrum.one_lt_absNorm p
  set m₀ : ℤ := min (-M) (-M - c) with hm₀
  obtain ⟨t, K, hK0, hK⟩ := exists_growth r (Ideal.absNorm p.asIdeal : ℝ) hr0 hN1 m₀ c
  refine ⟨m₀, t, C * Cχ * K, fun dn k hk => ?_⟩
  have hP := hprof k hk dn.1 dn.2 1 (by rw [Units.val_one, map_one])
  have hshell : scalarPi (algebraMap (p.adicCompletionIntegers ℚ) (p.adicCompletion ℚ) ϖ) hπ ^ dn.2 * diagZ (algebraMap (p.adicCompletionIntegers ℚ) (p.adicCompletion ℚ) ϖ) hπ dn.1 * k = scalarPi (algebraMap (p.adicCompletionIntegers ℚ) (p.adicCompletion ℚ) ϖ) hπ ^ dn.2 * diagUnitGL2 (Units.mk0 (algebraMap (p.adicCompletionIntegers ℚ) (p.adicCompletion ℚ) ϖ) hπ ^ dn.1 * 1) * k := by
    rw [diagZ_eq_diagUnitGL2]
  have hdet : Matrix.GeneralLinearGroup.det (scalarPi (algebraMap (p.adicCompletionIntegers ℚ) (p.adicCompletion ℚ) ϖ) hπ ^ dn.2 * diagZ (algebraMap (p.adicCompletionIntegers ℚ) (p.adicCompletion ℚ) ϖ) hπ dn.1 * k) = ϖu ^ (2 * dn.2 + dn.1) * Matrix.GeneralLinearGroup.det k := by
    rw [map_mul, map_mul, map_zpow, det_scalarPi, det_diagZ, hϖu, ← zpow_natCast, ← zpow_mul, ← zpow_add]
    congr 2
  have hnormχ : ‖((χ (Matrix.GeneralLinearGroup.det (scalarPi (algebraMap (p.adicCompletionIntegers ℚ) (p.adicCompletion ℚ) ϖ) hπ ^ dn.2 * diagZ (algebraMap (p.adicCompletionIntegers ℚ) (p.adicCompletion ℚ) ϖ) hπ dn.1 * k)) : ℂˣ) : ℂ)‖ =
      r ^ (2 * dn.2 + dn.1) * ‖((χ (Matrix.GeneralLinearGroup.det k) : ℂˣ) : ℂ)‖ := by
    rw [hdet, map_mul, map_zpow, Units.val_mul, norm_mul, Units.val_zpow_eq_zpow_val, norm_zpow, hr]
  have hC0 : 0 ≤ C := le_trans (norm_nonneg _) (hP.2.2.2.2)
  have hzero : ¬ (m₀ ≤ dn.1 ∧ m₀ ≤ dn.2 ∧ dn.2 ≤ c) → (∫ x : p.adicCompletion ℚ, NumberField.StandardAddChar.psiLocal ℚ p x *
            Φ ((unipotent x * (scalarPi (algebraMap (p.adicCompletionIntegers ℚ) (p.adicCompletion ℚ) ϖ) hπ ^ dn.2 * diagUnitGL2 (Units.mk0 (algebraMap (p.adicCompletionIntegers ℚ) (p.adicCompletion ℚ) ϖ) hπ ^ dn.1 * 1) * k) : GL (Fin 2) (p.adicCompletion ℚ)) : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ)) ∂(selfDualHaarAt ℚ p)) = 0 := by
    intro hcone
    by_cases hc2 : c < dn.2
    · exact hP.1 hc2
    push Not at hc2
    by_cases h2 : dn.2 < -M
    · exact hP.2.1 h2
    push Not at h2
    have h1 : dn.1 < m₀ := by
      by_contra h1; push Not at h1
      exact hcone ⟨h1, le_trans (min_le_left _ _) (by omega), hc2⟩
    have : dn.1 + dn.2 < -M := by have : m₀ ≤ -M - c := min_le_right _ _; omega
    exact hP.2.2.1 this
  rw [hAeq, hshell]
  constructor
  · intro hcone
    rw [hzero (fun h => hcone ⟨h.1, h.2.1⟩), zero_mul]
  · rw [norm_mul, ← hshell, hnormχ, hshell]
    by_cases hcone : m₀ ≤ dn.1 ∧ m₀ ≤ dn.2 ∧ dn.2 ≤ c
    · have hb : ‖(∫ x : p.adicCompletion ℚ, NumberField.StandardAddChar.psiLocal ℚ p x *
            Φ ((unipotent x * (scalarPi (algebraMap (p.adicCompletionIntegers ℚ) (p.adicCompletion ℚ) ϖ) hπ ^ dn.2 * diagUnitGL2 (Units.mk0 (algebraMap (p.adicCompletionIntegers ℚ) (p.adicCompletion ℚ) ϖ) hπ ^ dn.1 * 1) * k) : GL (Fin 2) (p.adicCompletion ℚ)) : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ)) ∂(selfDualHaarAt ℚ p))‖ ≤ C := hP.2.2.2.2
      have hg := hK dn.1 dn.2 hcone.1 hcone.2.1 hcone.2.2
      calc ‖(∫ x : p.adicCompletion ℚ, NumberField.StandardAddChar.psiLocal ℚ p x *
            Φ ((unipotent x * (scalarPi (algebraMap (p.adicCompletionIntegers ℚ) (p.adicCompletion ℚ) ϖ) hπ ^ dn.2 * diagUnitGL2 (Units.mk0 (algebraMap (p.adicCompletionIntegers ℚ) (p.adicCompletion ℚ) ϖ) hπ ^ dn.1 * 1) * k) : GL (Fin 2) (p.adicCompletion ℚ)) : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ)) ∂(selfDualHaarAt ℚ p))‖ * (r ^ (2 * dn.2 + dn.1) * ‖((χ (Matrix.GeneralLinearGroup.det k) : ℂˣ) : ℂ)‖)
          ≤ C * ((K * (Ideal.absNorm p.asIdeal : ℝ) ^ ((t : ℤ) * (dn.1 + dn.2))) * Cχ) := by
            apply mul_le_mul hb (mul_le_mul hg (hCχ k hk) (norm_nonneg _) (by positivity)) (by positivity) hC0
        _ = C * Cχ * K * (Ideal.absNorm p.asIdeal : ℝ) ^ ((t : ℤ) * (dn.1 + dn.2)) := by ring
    · rw [hzero hcone, norm_zero, zero_mul]
      positivity

theorem hA_of (Φ : M22 → ℂ) (χ : Fˣ →* ℂˣ) (hχ : IsLocallyConstant χ)
    (U : Subgroup G2) (hUo : IsOpen (U : Set G2))
    (hUinv : letI := localBorel ℚ p
      ∀ k ∈ U, ∀ g : G2, (∫ x : p.adicCompletion ℚ, NumberField.StandardAddChar.psiLocal ℚ p x *
            Φ ((unipotent x * (g * k) : GL (Fin 2) (p.adicCompletion ℚ)) : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ)) ∂(selfDualHaarAt ℚ p)) = (∫ x : p.adicCompletion ℚ, NumberField.StandardAddChar.psiLocal ℚ p x *
            Φ ((unipotent x * (g) : GL (Fin 2) (p.adicCompletion ℚ)) : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ)) ∂(selfDualHaarAt ℚ p)))
    (A : G2 → ℂ) (hAeq : letI := localBorel ℚ p
      ∀ g : G2, A g = (∫ x : p.adicCompletion ℚ, NumberField.StandardAddChar.psiLocal ℚ p x *
            Φ ((unipotent x * (g) : GL (Fin 2) (p.adicCompletion ℚ)) : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ)) ∂(selfDualHaarAt ℚ p)) * ((χ (Matrix.GeneralLinearGroup.det g) : ℂˣ) : ℂ)) :
    ∃ U' : Subgroup G2, IsOpen (U' : Set G2) ∧ ∀ k ∈ U', ∀ g : G2, A (g * k) = A g := by
  letI := localBorel ℚ p
  set Uχ : Subgroup G2 := (MonoidHom.ker χ).comap Matrix.GeneralLinearGroup.det with hUχ
  have hUχo : IsOpen (Uχ : Set G2) := by
    have h1 : IsOpen ((MonoidHom.ker χ : Subgroup Fˣ) : Set Fˣ) := by
      have : ((MonoidHom.ker χ : Subgroup Fˣ) : Set Fˣ) = χ ⁻¹' {1} := by
        ext z; simp [MonoidHom.mem_ker]
      rw [this]; exact hχ.isOpen_fiber 1
    rw [hUχ, Subgroup.coe_comap]; exact h1.preimage (continuous_det p)
  refine ⟨U ⊓ Uχ, ?_, ?_⟩
  · rw [Subgroup.coe_inf]; exact hUo.inter hUχo
  · intro k hk g
    obtain ⟨hkU, hkχ'⟩ := Subgroup.mem_inf.1 hk
    have hkχ : χ (Matrix.GeneralLinearGroup.det k) = 1 := by
      rw [hUχ] at hkχ'; exact Subgroup.mem_comap.1 hkχ'
    rw [hAeq, hAeq, hUinv k hkU g, map_mul, map_mul, hkχ, mul_one]

theorem separatedRational_of_geometric (Arr : ℤ × ℤ → ℂ) (a : ℂ) (ha : a ≠ 0) (c M : ℤ)
    (hV1 : ∀ n : ℤ × ℤ, c < n.2 → Arr n = 0) (hV2 : ∀ n : ℤ × ℤ, n.2 < -M → Arr n = 0)
    (hV3 : ∀ n : ℤ × ℤ, n.1 + n.2 < -M → Arr n = 0)
    (Γ : ℤ → ℂ) (hG : ∀ n : ℤ × ℤ, c ≤ n.1 + n.2 → n.2 ≤ c → Arr n = a ^ n.1 * Γ n.2) :
    ∃ (N₁ : ℤ) (D₁ D₂ : Polynomial ℂ) (M' : ℕ), D₁.eval 0 ≠ 0 ∧ D₂.eval 0 ≠ 0 ∧
      (∀ n : ℤ × ℤ, (n.1 < N₁ ∨ n.2 < N₁) → Arr n = 0) ∧
      (∀ m₁ m₂ : ℕ, (M' ≤ m₁ ∨ M' ≤ m₂) →
        ∑ i ∈ Finset.range (D₁.natDegree + 1), ∑ l ∈ Finset.range (D₂.natDegree + 1),
          D₁.coeff i * D₂.coeff l * Arr (N₁ + (m₁ : ℤ) - (i : ℤ), N₁ + (m₂ : ℤ) - (l : ℤ)) = 0) := by
  classical
  set N₁ : ℤ := min (-M) (-M - c) with hN₁
  set D₁ : Polynomial ℂ := Polynomial.C (-a) * Polynomial.X + Polynomial.C 1 with hD₁
  have hD₁deg : D₁.natDegree = 1 := by rw [hD₁]; exact Polynomial.natDegree_linear (neg_ne_zero.2 ha)
  have hD₁0 : D₁.coeff 0 = 1 := by rw [hD₁]; simp
  have hD₁1 : D₁.coeff 1 = -a := by rw [hD₁]; simp [Polynomial.coeff_one]
  have hD₁ev : D₁.eval 0 = 1 := by rw [hD₁]; simp
  refine ⟨N₁, D₁, Polynomial.C 1, Int.toNat (c - 2 * N₁ + 2) + Int.toNat (c - N₁ + 1), by rw [hD₁ev]; exact one_ne_zero,
    by rw [Polynomial.eval_C]; exact one_ne_zero, ?_, ?_⟩
  ·
    rintro n (h | h)
    · by_cases hc2 : c < n.2
      · exact hV1 n hc2
      · push Not at hc2
        have : N₁ ≤ -M - c := min_le_right _ _
        exact hV3 n (by omega)
    · have : N₁ ≤ -M := min_le_left _ _
      exact hV2 n (by omega)
  · intro m₁ m₂ hm
    have hMc : c - 2 * N₁ + 2 ≤ ((Int.toNat (c - 2 * N₁ + 2) : ℕ) : ℤ) := Int.self_le_toNat _
    have hMc' : c - N₁ + 1 ≤ ((Int.toNat (c - N₁ + 1) : ℕ) : ℤ) := Int.self_le_toNat _
    rw [hD₁deg, Polynomial.natDegree_C]
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add, Polynomial.coeff_C_zero, hD₁0, hD₁1,
      Nat.cast_zero, Nat.cast_one, sub_zero, one_mul, mul_one]

    by_cases hc2 : c < N₁ + (m₂ : ℤ)
    · rw [hV1 _ hc2, hV1 _ hc2]; ring
    push Not at hc2
    rcases hm with hm | hm
    ·
      have hN₁M : N₁ ≤ -M := min_le_left _ _
      have hreg1 : c ≤ (N₁ + (m₁ : ℤ)) + (N₁ + (m₂ : ℤ)) := by omega
      have hreg2 : c ≤ (N₁ + (m₁ : ℤ) - 1) + (N₁ + (m₂ : ℤ)) := by omega
      rw [hG (N₁ + (m₁ : ℤ), N₁ + (m₂ : ℤ)) hreg1 hc2, hG (N₁ + (m₁ : ℤ) - 1, N₁ + (m₂ : ℤ)) hreg2 hc2]
      simp only
      rw [show (N₁ + (m₁ : ℤ)) = (N₁ + (m₁ : ℤ) - 1) + 1 by ring, zpow_add_one₀ ha]
      ring
    · exfalso; omega

end GamKit

namespace GamArat

abbrev Profile (p : HeightOneSpectrum (𝓞 ℚ)) {ϖ : p.adicCompletionIntegers ℚ}
    (hπ : algebraMap (p.adicCompletionIntegers ℚ) (p.adicCompletion ℚ) ϖ ≠ 0)
    (Φ : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ) → ℂ) (c₀ M₀ : ℤ) (C₀ : ℝ) : Prop :=
  letI := localBorel ℚ p
  ∀ k ∈ AdelicDock.localLevelOne (𝓞 ℚ) ℚ p ⊤, ∀ (n₁ n₂ : ℤ) (u : (p.adicCompletion ℚ)ˣ),
      Valued.v (u : (p.adicCompletion ℚ)) = 1 →

        (c₀ < n₂ →
          (∫ x : (p.adicCompletion ℚ), NumberField.StandardAddChar.psiLocal ℚ p x *
            Φ ((unipotent x * (scalarPi (algebraMap (p.adicCompletionIntegers ℚ) (p.adicCompletion ℚ) ϖ) hπ ^ n₂ * diagUnitGL2 (Units.mk0 (algebraMap (p.adicCompletionIntegers ℚ) (p.adicCompletion ℚ) ϖ) hπ ^ n₁ * u) * k) : GL (Fin 2) (p.adicCompletion ℚ)) : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ)) ∂(selfDualHaarAt ℚ p)) = 0) ∧

        (n₂ < -M₀ →
          (∫ x : (p.adicCompletion ℚ), NumberField.StandardAddChar.psiLocal ℚ p x *
            Φ ((unipotent x * (scalarPi (algebraMap (p.adicCompletionIntegers ℚ) (p.adicCompletion ℚ) ϖ) hπ ^ n₂ * diagUnitGL2 (Units.mk0 (algebraMap (p.adicCompletionIntegers ℚ) (p.adicCompletion ℚ) ϖ) hπ ^ n₁ * u) * k) : GL (Fin 2) (p.adicCompletion ℚ)) : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ)) ∂(selfDualHaarAt ℚ p)) = 0) ∧

        (n₁ + n₂ < -M₀ →
          (∫ x : (p.adicCompletion ℚ), NumberField.StandardAddChar.psiLocal ℚ p x *
            Φ ((unipotent x * (scalarPi (algebraMap (p.adicCompletionIntegers ℚ) (p.adicCompletion ℚ) ϖ) hπ ^ n₂ * diagUnitGL2 (Units.mk0 (algebraMap (p.adicCompletionIntegers ℚ) (p.adicCompletion ℚ) ϖ) hπ ^ n₁ * u) * k) : GL (Fin 2) (p.adicCompletion ℚ)) : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ)) ∂(selfDualHaarAt ℚ p)) = 0) ∧

        (c₀ ≤ n₁ + n₂ →
          (∫ x : (p.adicCompletion ℚ), NumberField.StandardAddChar.psiLocal ℚ p x *
            Φ ((unipotent x * (scalarPi (algebraMap (p.adicCompletionIntegers ℚ) (p.adicCompletion ℚ) ϖ) hπ ^ n₂ * diagUnitGL2 (Units.mk0 (algebraMap (p.adicCompletionIntegers ℚ) (p.adicCompletion ℚ) ϖ) hπ ^ n₁ * u) * k) : GL (Fin 2) (p.adicCompletion ℚ)) : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ)) ∂(selfDualHaarAt ℚ p)) =
          (∫ x : (p.adicCompletion ℚ), NumberField.StandardAddChar.psiLocal ℚ p x *
            Φ ((unipotent x * (scalarPi (algebraMap (p.adicCompletionIntegers ℚ) (p.adicCompletion ℚ) ϖ) hπ ^ n₂ * diagZ (algebraMap (p.adicCompletionIntegers ℚ) (p.adicCompletion ℚ) ϖ) hπ (c₀ - n₂) * k) : GL (Fin 2) (p.adicCompletion ℚ)) : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ)) ∂(selfDualHaarAt ℚ p))) ∧

        (‖(∫ x : (p.adicCompletion ℚ), NumberField.StandardAddChar.psiLocal ℚ p x *
            Φ ((unipotent x * (scalarPi (algebraMap (p.adicCompletionIntegers ℚ) (p.adicCompletion ℚ) ϖ) hπ ^ n₂ * diagUnitGL2 (Units.mk0 (algebraMap (p.adicCompletionIntegers ℚ) (p.adicCompletion ℚ) ϖ) hπ ^ n₁ * u) * k) : GL (Fin 2) (p.adicCompletion ℚ)) : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ)) ∂(selfDualHaarAt ℚ p))‖ ≤ C₀)

variable (p : HeightOneSpectrum (𝓞 ℚ)) {ϖ : p.adicCompletionIntegers ℚ}
  (hπ : algebraMap (p.adicCompletionIntegers ℚ) (p.adicCompletion ℚ) ϖ ≠ 0)

theorem det_scalarPi : Matrix.GeneralLinearGroup.det (scalarPi (algebraMap (p.adicCompletionIntegers ℚ) (p.adicCompletion ℚ) ϖ) hπ) = Units.mk0 (algebraMap (p.adicCompletionIntegers ℚ) (p.adicCompletion ℚ) ϖ) hπ ^ 2 := by
  apply Units.ext
  simp [Matrix.GeneralLinearGroup.val_det_apply, scalarPi, Matrix.det_fin_two_of, pow_two]

theorem det_diagUnitGL2 (x : (p.adicCompletion ℚ)ˣ) : Matrix.GeneralLinearGroup.det (diagUnitGL2 x : (GL (Fin 2) (p.adicCompletion ℚ))) = x := by
  apply Units.ext
  simp [Matrix.GeneralLinearGroup.val_det_apply, Matrix.det_fin_two_of]

theorem det_shell (n : ℤ × ℤ) (u : (p.adicCompletion ℚ)ˣ) (g : (GL (Fin 2) (p.adicCompletion ℚ))) :
    Matrix.GeneralLinearGroup.det (scalarPi (algebraMap (p.adicCompletionIntegers ℚ) (p.adicCompletion ℚ) ϖ) hπ ^ n.2 * diagUnitGL2 (Units.mk0 (algebraMap (p.adicCompletionIntegers ℚ) (p.adicCompletion ℚ) ϖ) hπ ^ n.1 * u) * g) =
      Units.mk0 (algebraMap (p.adicCompletionIntegers ℚ) (p.adicCompletion ℚ) ϖ) hπ ^ n.1 * Matrix.GeneralLinearGroup.det (scalarPi (algebraMap (p.adicCompletionIntegers ℚ) (p.adicCompletion ℚ) ϖ) hπ ^ n.2 * diagUnitGL2 u * g) := by
  simp only [map_mul, map_zpow, det_diagUnitGL2]
  rw [mul_left_comm (Matrix.GeneralLinearGroup.det (scalarPi (algebraMap (p.adicCompletionIntegers ℚ) (p.adicCompletion ℚ) ϖ) hπ) ^ n.2) (Units.mk0 (algebraMap (p.adicCompletionIntegers ℚ) (p.adicCompletion ℚ) ϖ) hπ ^ n.1) u, mul_assoc]

variable (Φ : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ) → ℂ) (χ : (p.adicCompletion ℚ)ˣ →* ℂˣ)
  {c₀ M₀ : ℤ} {C₀ : ℝ}

theorem integrand_geom (hprof : Profile p hπ Φ c₀ M₀ C₀)
    {k₀ k : (GL (Fin 2) (p.adicCompletion ℚ))} (hk₀ : k₀ ∈ AdelicDock.localLevelOne (𝓞 ℚ) ℚ p ⊤) (hk : k ∈ AdelicDock.localLevelOne (𝓞 ℚ) ℚ p ⊤)
    (n : ℤ × ℤ) (u : (p.adicCompletion ℚ)ˣ) (hu : Valued.v (u : (p.adicCompletion ℚ)) = 1) (hle : c₀ ≤ n.1 + n.2) :
    letI := localBorel ℚ p
    (∫ x : (p.adicCompletion ℚ), NumberField.StandardAddChar.psiLocal ℚ p x *
            Φ ((unipotent x * (scalarPi (algebraMap (p.adicCompletionIntegers ℚ) (p.adicCompletion ℚ) ϖ) hπ ^ n.2 * diagUnitGL2 (Units.mk0 (algebraMap (p.adicCompletionIntegers ℚ) (p.adicCompletion ℚ) ϖ) hπ ^ n.1 * u) * (k₀ * k)) : (GL (Fin 2) (p.adicCompletion ℚ))) : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ)) ∂(selfDualHaarAt ℚ p)) *
          ((χ (Matrix.GeneralLinearGroup.det (scalarPi (algebraMap (p.adicCompletionIntegers ℚ) (p.adicCompletion ℚ) ϖ) hπ ^ n.2 * diagUnitGL2 (Units.mk0 (algebraMap (p.adicCompletionIntegers ℚ) (p.adicCompletion ℚ) ϖ) hπ ^ n.1 * u) * (k₀ * k))) : ℂˣ) : ℂ) =
      ((χ (Units.mk0 (algebraMap (p.adicCompletionIntegers ℚ) (p.adicCompletion ℚ) ϖ) hπ) : ℂˣ) : ℂ) ^ n.1 *
        ((∫ x : (p.adicCompletion ℚ), NumberField.StandardAddChar.psiLocal ℚ p x *
            Φ ((unipotent x * (scalarPi (algebraMap (p.adicCompletionIntegers ℚ) (p.adicCompletion ℚ) ϖ) hπ ^ n.2 * diagZ (algebraMap (p.adicCompletionIntegers ℚ) (p.adicCompletion ℚ) ϖ) hπ (c₀ - n.2) * (k₀ * k)) : (GL (Fin 2) (p.adicCompletion ℚ))) : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ)) ∂(selfDualHaarAt ℚ p)) *
          ((χ (Matrix.GeneralLinearGroup.det (scalarPi (algebraMap (p.adicCompletionIntegers ℚ) (p.adicCompletion ℚ) ϖ) hπ ^ n.2 * diagUnitGL2 u * (k₀ * k))) : ℂˣ) : ℂ)) := by
  have hkk : k₀ * k ∈ AdelicDock.localLevelOne (𝓞 ℚ) ℚ p ⊤ := Subgroup.mul_mem _ hk₀ hk
  have h4 := (hprof (k₀ * k) hkk n.1 n.2 u hu).2.2.2.1 hle
  rw [h4, det_shell, map_mul, map_zpow, Units.val_mul, Units.val_zpow_eq_zpow_val]
  ring

theorem integrand_zero (hprof : Profile p hπ Φ c₀ M₀ C₀)
    {k₀ k : (GL (Fin 2) (p.adicCompletion ℚ))} (hk₀ : k₀ ∈ AdelicDock.localLevelOne (𝓞 ℚ) ℚ p ⊤) (hk : k ∈ AdelicDock.localLevelOne (𝓞 ℚ) ℚ p ⊤)
    (n : ℤ × ℤ) (u : (p.adicCompletion ℚ)ˣ) (hu : Valued.v (u : (p.adicCompletion ℚ)) = 1) (hcase : c₀ < n.2 ∨ n.2 < -M₀ ∨ n.1 + n.2 < -M₀) :
    letI := localBorel ℚ p
    (∫ x : (p.adicCompletion ℚ), NumberField.StandardAddChar.psiLocal ℚ p x *
            Φ ((unipotent x * (scalarPi (algebraMap (p.adicCompletionIntegers ℚ) (p.adicCompletion ℚ) ϖ) hπ ^ n.2 * diagUnitGL2 (Units.mk0 (algebraMap (p.adicCompletionIntegers ℚ) (p.adicCompletion ℚ) ϖ) hπ ^ n.1 * u) * (k₀ * k)) : (GL (Fin 2) (p.adicCompletion ℚ))) : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ)) ∂(selfDualHaarAt ℚ p)) *
          ((χ (Matrix.GeneralLinearGroup.det (scalarPi (algebraMap (p.adicCompletionIntegers ℚ) (p.adicCompletion ℚ) ϖ) hπ ^ n.2 * diagUnitGL2 (Units.mk0 (algebraMap (p.adicCompletionIntegers ℚ) (p.adicCompletion ℚ) ϖ) hπ ^ n.1 * u) * (k₀ * k))) : ℂˣ) : ℂ) = (0 : ℂ) := by
  have hkk : k₀ * k ∈ AdelicDock.localLevelOne (𝓞 ℚ) ℚ p ⊤ := Subgroup.mul_mem _ hk₀ hk
  have hP := hprof (k₀ * k) hkk n.1 n.2 u hu
  apply mul_eq_zero_of_left
  rcases hcase with h | h | h
  · exact hP.1 h
  · exact hP.2.1 h
  · exact hP.2.2.1 h

theorem ae_mem_levelOne (Kb : Subgroup (GL (Fin 2) (p.adicCompletion ℚ))) (hKb : Kb ≤ AdelicDock.localLevelOne (𝓞 ℚ) ℚ p ⊤) :
    letI := localGLBorel ℚ p
    ∀ (μ₂ : Measure (GL (Fin 2) (p.adicCompletion ℚ))), ∀ᵐ k ∂(μ₂.restrict ((Kb : Subgroup (GL (Fin 2) (p.adicCompletion ℚ))) : Set (GL (Fin 2) (p.adicCompletion ℚ)))),
      k ∈ ((AdelicDock.localLevelOne (𝓞 ℚ) ℚ p ⊤ : Subgroup (GL (Fin 2) (p.adicCompletion ℚ))) : Set (GL (Fin 2) (p.adicCompletion ℚ))) := by
  letI := localGLBorel ℚ p
  haveI := borelSpace_localGLBorel ℚ p
  intro μ₂
  have hK₀o : IsOpen ((AdelicDock.localLevelOne (𝓞 ℚ) ℚ p ⊤ : Subgroup (GL (Fin 2) (p.adicCompletion ℚ))) : Set (GL (Fin 2) (p.adicCompletion ℚ))) :=
    (AdelicDock.isCompact_and_isOpen_localLevelOne ℚ p ⊤ top_ne_bot).2
  rw [MeasureTheory.ae_iff]
  show (μ₂.restrict ((Kb : Subgroup (GL (Fin 2) (p.adicCompletion ℚ))) : Set (GL (Fin 2) (p.adicCompletion ℚ)))) (((AdelicDock.localLevelOne (𝓞 ℚ) ℚ p ⊤ : Subgroup (GL (Fin 2) (p.adicCompletion ℚ))) : Set (GL (Fin 2) (p.adicCompletion ℚ)))ᶜ) = 0
  rw [Measure.restrict_apply hK₀o.measurableSet.compl]
  have : ((AdelicDock.localLevelOne (𝓞 ℚ) ℚ p ⊤ : Subgroup (GL (Fin 2) (p.adicCompletion ℚ))) : Set (GL (Fin 2) (p.adicCompletion ℚ)))ᶜ ∩ ((Kb : Subgroup (GL (Fin 2) (p.adicCompletion ℚ))) : Set (GL (Fin 2) (p.adicCompletion ℚ))) = ∅ := by
    exact Set.eq_empty_iff_forall_notMem.mpr fun k hk => hk.1 (hKb hk.2)
  rw [this, measure_empty]

theorem measurableSet_unitSphere :
    letI := localBorel ℚ p
    MeasurableSet {u : (p.adicCompletion ℚ)ˣ | Valued.v (u : (p.adicCompletion ℚ)) = 1} := by
  letI := localBorel ℚ p
  haveI : BorelSpace (p.adicCompletion ℚ) := ⟨rfl⟩
  have hsph : IsClosed {x : (p.adicCompletion ℚ) | Valued.v x = 1} := by
    have hset : {x : (p.adicCompletion ℚ) | Valued.v x = 1} =
        {x : (p.adicCompletion ℚ) | (Valued.v (R := (p.adicCompletion ℚ))).restrict x = 1} :=
      Set.ext fun x => (Valuation.restrict_eq_one_iff Valued.v).symm
    rw [hset]
    exact Valued.isClosed_sphere _ 1
  exact ⟨{x : (p.adicCompletion ℚ) | Valued.v x = 1}, hsph.measurableSet, rfl⟩

end GamArat

namespace GamArat

theorem arat_of_profile
    (p : HeightOneSpectrum (𝓞 ℚ))
    {ϖ : p.adicCompletionIntegers ℚ}
    (hπ : algebraMap (p.adicCompletionIntegers ℚ) (p.adicCompletion ℚ) ϖ ≠ 0)
    (Φ : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ) → ℂ)
    (χ : (p.adicCompletion ℚ)ˣ →* ℂˣ) (c₀ M₀ : ℤ) (C₀ : ℝ)
    (hprof : letI := localBorel ℚ p
      ∀ k ∈ AdelicDock.localLevelOne (𝓞 ℚ) ℚ p ⊤, ∀ (n₁ n₂ : ℤ) (u : (p.adicCompletion ℚ)ˣ),
      Valued.v (u : (p.adicCompletion ℚ)) = 1 →

        (c₀ < n₂ →
          (∫ x : (p.adicCompletion ℚ), NumberField.StandardAddChar.psiLocal ℚ p x *
            Φ ((unipotent x * (scalarPi (algebraMap (p.adicCompletionIntegers ℚ) (p.adicCompletion ℚ) ϖ) hπ ^ n₂ * diagUnitGL2 (Units.mk0 (algebraMap (p.adicCompletionIntegers ℚ) (p.adicCompletion ℚ) ϖ) hπ ^ n₁ * u) * k) : GL (Fin 2) (p.adicCompletion ℚ)) : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ)) ∂(selfDualHaarAt ℚ p)) = 0) ∧

        (n₂ < -M₀ →
          (∫ x : (p.adicCompletion ℚ), NumberField.StandardAddChar.psiLocal ℚ p x *
            Φ ((unipotent x * (scalarPi (algebraMap (p.adicCompletionIntegers ℚ) (p.adicCompletion ℚ) ϖ) hπ ^ n₂ * diagUnitGL2 (Units.mk0 (algebraMap (p.adicCompletionIntegers ℚ) (p.adicCompletion ℚ) ϖ) hπ ^ n₁ * u) * k) : GL (Fin 2) (p.adicCompletion ℚ)) : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ)) ∂(selfDualHaarAt ℚ p)) = 0) ∧

        (n₁ + n₂ < -M₀ →
          (∫ x : (p.adicCompletion ℚ), NumberField.StandardAddChar.psiLocal ℚ p x *
            Φ ((unipotent x * (scalarPi (algebraMap (p.adicCompletionIntegers ℚ) (p.adicCompletion ℚ) ϖ) hπ ^ n₂ * diagUnitGL2 (Units.mk0 (algebraMap (p.adicCompletionIntegers ℚ) (p.adicCompletion ℚ) ϖ) hπ ^ n₁ * u) * k) : GL (Fin 2) (p.adicCompletion ℚ)) : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ)) ∂(selfDualHaarAt ℚ p)) = 0) ∧

        (c₀ ≤ n₁ + n₂ →
          (∫ x : (p.adicCompletion ℚ), NumberField.StandardAddChar.psiLocal ℚ p x *
            Φ ((unipotent x * (scalarPi (algebraMap (p.adicCompletionIntegers ℚ) (p.adicCompletion ℚ) ϖ) hπ ^ n₂ * diagUnitGL2 (Units.mk0 (algebraMap (p.adicCompletionIntegers ℚ) (p.adicCompletion ℚ) ϖ) hπ ^ n₁ * u) * k) : GL (Fin 2) (p.adicCompletion ℚ)) : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ)) ∂(selfDualHaarAt ℚ p)) =
          (∫ x : (p.adicCompletion ℚ), NumberField.StandardAddChar.psiLocal ℚ p x *
            Φ ((unipotent x * (scalarPi (algebraMap (p.adicCompletionIntegers ℚ) (p.adicCompletion ℚ) ϖ) hπ ^ n₂ * diagZ (algebraMap (p.adicCompletionIntegers ℚ) (p.adicCompletion ℚ) ϖ) hπ (c₀ - n₂) * k) : GL (Fin 2) (p.adicCompletion ℚ)) : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ)) ∂(selfDualHaarAt ℚ p))) ∧

        (‖(∫ x : (p.adicCompletion ℚ), NumberField.StandardAddChar.psiLocal ℚ p x *
            Φ ((unipotent x * (scalarPi (algebraMap (p.adicCompletionIntegers ℚ) (p.adicCompletion ℚ) ϖ) hπ ^ n₂ * diagUnitGL2 (Units.mk0 (algebraMap (p.adicCompletionIntegers ℚ) (p.adicCompletion ℚ) ϖ) hπ ^ n₁ * u) * k) : GL (Fin 2) (p.adicCompletion ℚ)) : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ)) ∂(selfDualHaarAt ℚ p))‖ ≤ C₀)) :
    ∀ (b : ℕ) (Kb : Subgroup (GL (Fin 2) (p.adicCompletion ℚ))), Kb ≤ AdelicDock.localLevelOne (𝓞 ℚ) ℚ p ⊤ → ∀ k₀ ∈ AdelicDock.localLevelOne (𝓞 ℚ) ℚ p ⊤, ∀ (η : (p.adicCompletion ℚ)ˣ →* ℂˣ) (c : ℕ),
      HasConductorExponentAt ℚ p η c → c ≤ b →
      letI := localBorel ℚ p
      letI := localGLBorel ℚ p
      haveI := borelSpace_localGLBorel ℚ p
      ∀ (μ₂ : Measure (GL (Fin 2) (p.adicCompletion ℚ))) [μ₂.IsHaarMeasure],
        let Arr : ℤ × ℤ → ℂ := fun n =>
          ∫ u in {u : (p.adicCompletion ℚ)ˣ | Valued.v (u : p.adicCompletion ℚ) = 1},
            (∫ k in ((Kb : Subgroup (GL (Fin 2) (p.adicCompletion ℚ))) : Set (GL (Fin 2) (p.adicCompletion ℚ))),
                (fun g : GL (Fin 2) (p.adicCompletion ℚ) =>
        (∫ x : p.adicCompletion ℚ, NumberField.StandardAddChar.psiLocal ℚ p x *
            Φ ((unipotent x * g : GL (Fin 2) (p.adicCompletion ℚ)) : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ)) ∂(selfDualHaarAt ℚ p)) *
          ((χ (Matrix.GeneralLinearGroup.det g) : ℂˣ) : ℂ)) (scalarPi (algebraMap (p.adicCompletionIntegers ℚ) (p.adicCompletion ℚ) ϖ) hπ ^ n.2 *
                  diagUnitGL2 (Units.mk0 (algebraMap (p.adicCompletionIntegers ℚ) (p.adicCompletion ℚ) ϖ) hπ ^ n.1 * u) * (k₀ * k)) ∂μ₂) * ((η u : ℂˣ) : ℂ)
          ∂(Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ p)))
        ∃ (N₁ : ℤ) (D₁ D₂ : Polynomial ℂ) (M : ℕ), D₁.eval 0 ≠ 0 ∧ D₂.eval 0 ≠ 0 ∧
          (∀ n : ℤ × ℤ, (n.1 < N₁ ∨ n.2 < N₁) → Arr n = 0) ∧
          (∀ m₁ m₂ : ℕ, (M ≤ m₁ ∨ M ≤ m₂) →
            ∑ i ∈ Finset.range (D₁.natDegree + 1), ∑ l ∈ Finset.range (D₂.natDegree + 1),
              D₁.coeff i * D₂.coeff l * Arr (N₁ + (m₁ : ℤ) - (i : ℤ), N₁ + (m₂ : ℤ) - (l : ℤ)) = 0) := by
  intro b Kb hKb k₀ hk₀ η cη hη hcb μ₂ _hμ₂
  letI := localBorel ℚ p
  letI := localGLBorel ℚ p
  haveI := borelSpace_localGLBorel ℚ p
  have hprof' : Profile p hπ Φ c₀ M₀ C₀ := hprof
  have hae := ae_mem_levelOne p Kb hKb μ₂
  have hS := measurableSet_unitSphere p
  intro Arr
  let Γ : ℤ → ℂ := fun n₂ : ℤ =>
    ∫ u in {u : (p.adicCompletion ℚ)ˣ | Valued.v (u : (p.adicCompletion ℚ)) = 1},
      (∫ k in ((Kb : Subgroup (GL (Fin 2) (p.adicCompletion ℚ))) : Set (GL (Fin 2) (p.adicCompletion ℚ))),
        (∫ x : (p.adicCompletion ℚ), NumberField.StandardAddChar.psiLocal ℚ p x *
            Φ ((unipotent x * (scalarPi (algebraMap (p.adicCompletionIntegers ℚ) (p.adicCompletion ℚ) ϖ) hπ ^ n₂ * diagZ (algebraMap (p.adicCompletionIntegers ℚ) (p.adicCompletion ℚ) ϖ) hπ (c₀ - n₂) * (k₀ * k)) : (GL (Fin 2) (p.adicCompletion ℚ))) : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ)) ∂(selfDualHaarAt ℚ p)) *
          ((χ (Matrix.GeneralLinearGroup.det (scalarPi (algebraMap (p.adicCompletionIntegers ℚ) (p.adicCompletion ℚ) ϖ) hπ ^ n₂ * diagUnitGL2 u * (k₀ * k))) : ℂˣ) : ℂ) ∂μ₂) * ((η u : ℂˣ) : ℂ)
      ∂(Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ p)))
  have hZ : ∀ n : ℤ × ℤ, (c₀ < n.2 ∨ n.2 < -M₀ ∨ n.1 + n.2 < -M₀) → Arr n = 0 := by
    intro n hn
    refine MeasureTheory.setIntegral_eq_zero_of_forall_eq_zero fun u hu => ?_
    rw [MeasureTheory.integral_eq_zero_of_ae
      ((hae.mono fun k hk => integrand_zero p hπ Φ χ hprof' hk₀ hk n u hu hn)), zero_mul]
  have hR : ∀ n : ℤ × ℤ, c₀ ≤ n.1 + n.2 → Arr n = ((χ (Units.mk0 (algebraMap (p.adicCompletionIntegers ℚ) (p.adicCompletion ℚ) ϖ) hπ) : ℂˣ) : ℂ) ^ n.1 * Γ n.2 := by
    intro n hn
    show ∫ u in {u : (p.adicCompletion ℚ)ˣ | Valued.v (u : p.adicCompletion ℚ) = 1},
            (∫ k in ((Kb : Subgroup (GL (Fin 2) (p.adicCompletion ℚ))) : Set (GL (Fin 2) (p.adicCompletion ℚ))),
                (fun g : GL (Fin 2) (p.adicCompletion ℚ) =>
        (∫ x : p.adicCompletion ℚ, NumberField.StandardAddChar.psiLocal ℚ p x *
            Φ ((unipotent x * g : GL (Fin 2) (p.adicCompletion ℚ)) : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ)) ∂(selfDualHaarAt ℚ p)) *
          ((χ (Matrix.GeneralLinearGroup.det g) : ℂˣ) : ℂ)) (scalarPi (algebraMap (p.adicCompletionIntegers ℚ) (p.adicCompletion ℚ) ϖ) hπ ^ n.2 *
                  diagUnitGL2 (Units.mk0 (algebraMap (p.adicCompletionIntegers ℚ) (p.adicCompletion ℚ) ϖ) hπ ^ n.1 * u) * (k₀ * k)) ∂μ₂) * ((η u : ℂˣ) : ℂ)
          ∂(Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ p))) = ((χ (Units.mk0 (algebraMap (p.adicCompletionIntegers ℚ) (p.adicCompletion ℚ) ϖ) hπ) : ℂˣ) : ℂ) ^ n.1 * (fun n₂ : ℤ =>
    ∫ u in {u : (p.adicCompletion ℚ)ˣ | Valued.v (u : (p.adicCompletion ℚ)) = 1},
      (∫ k in ((Kb : Subgroup (GL (Fin 2) (p.adicCompletion ℚ))) : Set (GL (Fin 2) (p.adicCompletion ℚ))),
        (∫ x : (p.adicCompletion ℚ), NumberField.StandardAddChar.psiLocal ℚ p x *
            Φ ((unipotent x * (scalarPi (algebraMap (p.adicCompletionIntegers ℚ) (p.adicCompletion ℚ) ϖ) hπ ^ n₂ * diagZ (algebraMap (p.adicCompletionIntegers ℚ) (p.adicCompletion ℚ) ϖ) hπ (c₀ - n₂) * (k₀ * k)) : (GL (Fin 2) (p.adicCompletion ℚ))) : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ)) ∂(selfDualHaarAt ℚ p)) *
          ((χ (Matrix.GeneralLinearGroup.det (scalarPi (algebraMap (p.adicCompletionIntegers ℚ) (p.adicCompletion ℚ) ϖ) hπ ^ n₂ * diagUnitGL2 u * (k₀ * k))) : ℂˣ) : ℂ) ∂μ₂) * ((η u : ℂˣ) : ℂ)
      ∂(Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ p)))) n.2
    rw [← MeasureTheory.integral_const_mul]
    refine MeasureTheory.setIntegral_congr_fun hS (fun u hu => ?_)
    rw [MeasureTheory.integral_congr_ae (hae.mono fun k hk => integrand_geom p hπ Φ χ hprof' hk₀ hk n u hu hn),
      MeasureTheory.integral_const_mul, mul_assoc]
  exact GamKit.separatedRational_of_geometric Arr ((χ (Units.mk0 (algebraMap (p.adicCompletionIntegers ℚ) (p.adicCompletion ℚ) ϖ) hπ) : ℂˣ) : ℂ) (Units.ne_zero _) c₀ M₀
    (fun n h => hZ n (Or.inl h)) (fun n h => hZ n (Or.inr (Or.inl h))) (fun n h => hZ n (Or.inr (Or.inr h)))
    Γ (fun n h _ => hR n h)

end GamArat

theorem solution
    (p : HeightOneSpectrum (𝓞 ℚ))
    {ϖ : p.adicCompletionIntegers ℚ}
    (hπ : algebraMap (p.adicCompletionIntegers ℚ) (p.adicCompletion ℚ) ϖ ≠ 0)
    (hϖ : Valued.v (algebraMap (p.adicCompletionIntegers ℚ) (p.adicCompletion ℚ) ϖ) = WithZero.exp (-1 : ℤ))
    (Φ : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ) → ℂ) (hΦ : IsLocallyConstant Φ) (hΦc : HasCompactSupport Φ)
    (χ : (p.adicCompletion ℚ)ˣ →* ℂˣ) (hχ : IsLocallyConstant χ) :
    letI := localBorel ℚ p
    let A : GL (Fin 2) (p.adicCompletion ℚ) → ℂ := (fun g : GL (Fin 2) (p.adicCompletion ℚ) =>
        (∫ x : p.adicCompletion ℚ, NumberField.StandardAddChar.psiLocal ℚ p x *
            Φ ((unipotent x * g : GL (Fin 2) (p.adicCompletion ℚ)) : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ)) ∂(selfDualHaarAt ℚ p)) *
          ((χ (Matrix.GeneralLinearGroup.det g) : ℂˣ) : ℂ))
    (∃ U : Subgroup (GL (Fin 2) (p.adicCompletion ℚ)), IsOpen (U : Set (GL (Fin 2) (p.adicCompletion ℚ))) ∧
        ∀ k ∈ U, ∀ g : GL (Fin 2) (p.adicCompletion ℚ), A (g * k) = A g) ∧
      (∃ (m₀ : ℤ) (t : ℕ) (CA : ℝ), ∀ (dn : ℤ × ℤ), ∀ k ∈ AdelicDock.localLevelOne (𝓞 ℚ) ℚ p ⊤,
      (¬ (m₀ ≤ dn.1 ∧ m₀ ≤ dn.2) → A (scalarPi (algebraMap (p.adicCompletionIntegers ℚ) (p.adicCompletion ℚ) ϖ) hπ ^ dn.2 * diagZ (algebraMap (p.adicCompletionIntegers ℚ) (p.adicCompletion ℚ) ϖ) hπ dn.1 * k) = 0) ∧
      ‖A (scalarPi (algebraMap (p.adicCompletionIntegers ℚ) (p.adicCompletion ℚ) ϖ) hπ ^ dn.2 * diagZ (algebraMap (p.adicCompletionIntegers ℚ) (p.adicCompletion ℚ) ϖ) hπ dn.1 * k)‖ ≤
        CA * (Ideal.absNorm p.asIdeal : ℝ) ^ ((t : ℤ) * (dn.1 + dn.2))) ∧
      (∀ (b : ℕ) (Kb : Subgroup (GL (Fin 2) (p.adicCompletion ℚ))), Kb ≤ AdelicDock.localLevelOne (𝓞 ℚ) ℚ p ⊤ → ∀ k₀ ∈ AdelicDock.localLevelOne (𝓞 ℚ) ℚ p ⊤, ∀ (η : (p.adicCompletion ℚ)ˣ →* ℂˣ) (c : ℕ),
      HasConductorExponentAt ℚ p η c → c ≤ b →
      letI := localBorel ℚ p
      letI := localGLBorel ℚ p
      haveI := borelSpace_localGLBorel ℚ p
      ∀ (μ₂ : Measure (GL (Fin 2) (p.adicCompletion ℚ))) [μ₂.IsHaarMeasure],
        let Arr : ℤ × ℤ → ℂ := fun n =>
          ∫ u in {u : (p.adicCompletion ℚ)ˣ | Valued.v (u : p.adicCompletion ℚ) = 1},
            (∫ k in ((Kb : Subgroup (GL (Fin 2) (p.adicCompletion ℚ))) : Set (GL (Fin 2) (p.adicCompletion ℚ))),
                A (scalarPi (algebraMap (p.adicCompletionIntegers ℚ) (p.adicCompletion ℚ) ϖ) hπ ^ n.2 *
                  diagUnitGL2 (Units.mk0 (algebraMap (p.adicCompletionIntegers ℚ) (p.adicCompletion ℚ) ϖ) hπ ^ n.1 * u) * (k₀ * k)) ∂μ₂) * ((η u : ℂˣ) : ℂ)
          ∂(Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ p)))
        ∃ (N₁ : ℤ) (D₁ D₂ : Polynomial ℂ) (M : ℕ), D₁.eval 0 ≠ 0 ∧ D₂.eval 0 ≠ 0 ∧
          (∀ n : ℤ × ℤ, (n.1 < N₁ ∨ n.2 < N₁) → Arr n = 0) ∧
          (∀ m₁ m₂ : ℕ, (M ≤ m₁ ∨ M ≤ m₂) →
            ∑ i ∈ Finset.range (D₁.natDegree + 1), ∑ l ∈ Finset.range (D₂.natDegree + 1),
              D₁.coeff i * D₂.coeff l * Arr (N₁ + (m₁ : ℤ) - (i : ℤ), N₁ + (m₂ : ℤ) - (l : ℤ)) = 0)) := by
  intro A
  obtain ⟨hint, ⟨U, hUo, hUinv⟩, ⟨c, M, C, hprof⟩⟩ :=
    LanglandsTunnell.RankinSelberg.exists_rowSlice_shell_profile_of_isLocallyConstant_of_hasCompactSupport p hπ hϖ Φ hΦ hΦc
  have hAeq : ∀ g : GL (Fin 2) (p.adicCompletion ℚ), A g = (∫ x : p.adicCompletion ℚ, NumberField.StandardAddChar.psiLocal ℚ p x *
            Φ ((unipotent x * (g) : GL (Fin 2) (p.adicCompletion ℚ)) : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ)) ∂(selfDualHaarAt ℚ p)) * ((χ (Matrix.GeneralLinearGroup.det g) : ℂˣ) : ℂ) := fun g => rfl
  exact ⟨GamKit.hA_of p Φ χ hχ U hUo hUinv A hAeq, GamKit.hAshell_of p hπ hϖ Φ χ hχ c M C hprof A hAeq,
    GamArat.arat_of_profile p hπ Φ χ c M C hprof⟩

end S_LanglandsTunnell_RankinSelberg_rowSlice_twist_shellGauge_and_rationalTorusShell
end P2MW
export P2MW.S_LanglandsTunnell_RankinSelberg_rowSlice_twist_shellGauge_and_rationalTorusShell (solution)
