-- Prove2me | solution 1 for LanglandsTunnell.CubicInduction.globalZeta30_eq_sPart_mul_inducedL_of_isCubicInductionDataOn
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:08.353894+00:00
-- url     : https://prove2.me/submissions/fcfc62f9-0ac0-5001-9b56-5b71e7663d86

import Definitions.Def_LanglandsTunnell_CubicInduction_GlobalZeta31
import Definitions.Def_LanglandsTunnell_CubicLambda
import Theorems.Thm_AutomorphicForm_exists_localComponents_of_isGlobalAddChar
import Theorems.Thm_LanglandsTunnell_CubicInduction_exists_hasProd_sphericalShellSums_and_globalZeta30_eq_mul_integral_sPart
import Theorems.Thm_LanglandsTunnell_RankinSelberg_eval_inducedEulerPoly_eq_of_finrank_le_three
import Theorems.Thm_LanglandsTunnell_TateLocal_forall_eq_one_and_exists_ne_one_of_addCharLevel
import Theorems.Thm_NumberField_TateGlobal_apply_eq_one_of_forall_isUnramifiedCharAt_of_continuous
import Definitions.Def_LanglandsTunnell_CubicInduction_DataOn
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_LanglandsTunnell_CubicInduction_globalZeta30_eq_sPart_mul_inducedL_of_isCubicInductionDataOn
p2m_attr_erase "instance" "IsDedekindDomain.HeightOneSpectrum.Extension.instAlgebraSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersValEqUnder IsDedekindDomain.HeightOneSpectrum.Extension.instAlgebraSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersValEqUnder_1 IsDedekindDomain.HeightOneSpectrum.instMulActionHomClassAlgHomTensorProductAdicCompletionForallValEqUnder_definitions IsDedekindDomain.HeightOneSpectrum.Extension.instAlgebraAdicCompletionValEqUnder IsDedekindDomain.HeightOneSpectrum.adicCompletion.instFiniteForallValEqUnderOfFiniteDimensional_definitions IsDedekindDomain.HeightOneSpectrum.instIsBiscalarSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersTensorProductCoeAlgHomTensorAdicCompletionIntegersTo IsDedekindDomain.HeightOneSpectrum.Extension.instContinuousSMulAdicCompletionValEqUnder IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsModuleTopology IsDedekindDomain.HeightOneSpectrum.Extension.instFiniteSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersValEqUnderOfFiniteDimensional IsDedekindDomain.HeightOneSpectrum.adicCompletion.instFiniteValEqUnderOfFiniteDimensional_definitions instIsBiscalarTensorProductCoeAlgHomBaseChange_of_algebraMap IsDedekindDomain.HeightOneSpectrum.instIsScalarTowerSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersValEqUnder_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsModuleTopologyPi IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions Submodule.instIsTopologicalModuleSubtypeMem Pi.instTopologicalModule IsTopologicalModule.toContinuousSMul IsTopologicalModule.toContinuousAdd instFunLike SemialgHomClass.toSemilinearMapClass instCoeTCSemialgHom SemialgHomClass.toRingHomClass SemialgHomClass.instSemialgHom instCountableOfNumberField_definitions"
p2m_attr_erase "simp" "SemialgHom.baseChange_of_algebraMap_tmul_left SemialgHom.baseChangeRightOfAlgebraMap_apply Pi.semialgHomPi_apply Pi.semialgHom_apply Module.Basis.rightBaseChange_apply LinearEquiv.coe_mulLeft LinearEquiv.coe_mulRight WithVal.semialgebraMap_toFun_ofVal Module.Basis.rightBaseChange_repr IsDedekindDomain.HeightOneSpectrum.adicCompletionIntegers.tensorCoe_tmul IsDedekindDomain.HeightOneSpectrum.tensorAdicCompletionIntegersTo_tmul SemialgHom.baseChangeRightOfAlgebraMap_coe IsDedekindDomain.HeightOneSpectrum.adicCompletion.integerBaseChangeLinearEquiv_tmul_apply SemialgHom.baseChange_of_algebraMap_tmul_right IsLocalization.map_moduleTensorEquiv_symm_tmul IsLocalization.leftModuleTensorEquiv_apply IsLocalization.moduleLid_symm_apply IsLocalization.leftModuleTensorEquiv_symm_apply IsLocalization.map_moduleTensorEquiv_tmul IsModuleTopology.continuousLinearEquiv_apply AlgEquiv.extendScalars_symm_apply IsModuleTopology.Module.Basis.equivFun_homeo_symm_apply IsModuleTopology.Module.Basis.equivFun_homeo_apply IsModuleTopology.continuousAlgEquivOfIsBiscalar_apply AlgEquiv.extendScalars_apply IsModuleTopology.continuousLinearEquiv_symm_apply SemialgHom.restrictScalars_toFun SemialgHom.mk.sizeOf_spec SemialgHom.mk.injEq SemialgHom.coe_coe coe_mk TensorProduct.RightActions.smul_def TensorProduct.RightActions.Module.TensorProduct.comm_symm_apply_tmul TensorProduct.RightActions.LinearMap.baseChange_id TensorProduct.RightActions.algebraMap_eval TensorProduct.RightActions.Module.TensorProduct.comm_apply_tmul TensorProduct.RightActions.Algebra.TensorProduct.comm_symm_apply_tmul TensorProduct.RightActions.Algebra.TensorProduct.comm_apply_tmul AutomorphicForm.SiegelCoordinates.upperUnit_apply_zero_zero AutomorphicForm.SiegelCoordinates.upperUnit_apply_one_zero"
p2m_attr_erase "simp" "AutomorphicForm.SiegelCoordinates.upperUnit_apply_one_one AutomorphicForm.SiegelCoordinates.upperUnit_apply_zero_one"

set_option autoImplicit false

open IsDedekindDomain NumberField NumberField.TateGlobal AutomorphicForm LanglandsTunnell.Converse LanglandsTunnell.CubicInduction LanglandsTunnell.TateLocal MeasureTheory LanglandsTunnell.RankinSelberg

private theorem psiLoc_eq_one_of_valued_le_one_and_exists_ne_one
    (K : Type) [Field K] [NumberField K]
    [Algebra (𝓞 ℚ) (𝓞 K)] [Algebra.IsIntegral (𝓞 ℚ) (𝓞 K)]
    (ψ : AddChar (AdeleRing (𝓞 ℚ) ℚ) ℂ) (_hψ : IsGlobalAddChar ℚ ψ) (μ : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ)
    (_hlev : ∀ v : HeightOneSpectrum (𝓞 ℚ), ¬ IsBadPlace K μ v →
      LanglandsTunnell.TateLocal.addCharLevel (psiLoc ψ v) = 0)
    (S : Finset (HeightOneSpectrum (𝓞 ℚ))) (hSbad : ∀ w : HeightOneSpectrum (𝓞 ℚ), IsBadPlace K μ w ↔ w ∈ S) :
    (∀ v, v ∉ S → ∀ x : v.adicCompletion ℚ, Valued.v x ≤ 1 → psiLoc ψ v x = 1) ∧
    (∀ v, v ∉ S → ∃ x : v.adicCompletion ℚ, Valued.v x ≤ 1 ∧ psiLoc ψ v ((varpi v)⁻¹ * x) ≠ 1) := by
  obtain ⟨ψv, nψ, -, -, h1, h2, -, h4, -⟩ :=
    AutomorphicForm.exists_localComponents_of_isGlobalAddChar ℚ ψ _hψ

  have hloc : ∀ (v : HeightOneSpectrum (𝓞 ℚ)) (x : v.adicCompletion ℚ), psiLoc ψ v x = ψv v x := by
    intro v x
    have hfp : (∏ᶠ w, ψv w (NumberField.StandardAddChar.finAdeleSingleAt ℚ v x w)) = ψv v x := by
      refine (finprod_eq_single _ v fun w hw => ?_).trans ?_
      · simp only [NumberField.StandardAddChar.finAdeleSingleAt_apply_of_ne ℚ v x hw, AddChar.map_zero_eq_one]
      · simp only [NumberField.StandardAddChar.finAdeleSingleAt_apply_self]
    show ψ (AddMonoidHom.inr (InfiniteAdeleRing ℚ) (FiniteAdeleRing (𝓞 ℚ) ℚ)
      (NumberField.StandardAddChar.finAdeleSingleAt ℚ v x)) = ψv v x
    exact (h4 _).trans hfp
  have hv : ∀ v : HeightOneSpectrum (𝓞 ℚ), v ∉ S →
      (∀ x : v.adicCompletion ℚ, Valued.v x ≤ 1 → psiLoc ψ v x = 1) ∧
        ∃ x : v.adicCompletion ℚ, Valued.v x ≤ 1 ∧ psiLoc ψ v ((varpi v)⁻¹ * x) ≠ 1 := by
    intro v hvS
    have hl : LanglandsTunnell.TateLocal.addCharLevel (psiLoc ψ v) = 0 :=
      _hlev v fun hb => hvS ((hSbad v).mp hb)
    have hne : psiLoc ψ v ≠ 1 := by
      obtain ⟨x, -, hx⟩ := h2 v
      intro h
      exact hx (by rw [← hloc v x, h, AddChar.one_apply])
    have hk := LanglandsTunnell.TateLocal.forall_eq_one_and_exists_ne_one_of_addCharLevel ℚ v (psiLoc ψ v)
      ⟨nψ v, fun x hx => by rw [hloc v x]; exact h1 v x hx⟩ hne
    rw [hl, WithZero.exp_zero] at hk
    obtain ⟨hk1, x₀, hx₀, hne₀⟩ := hk
    refine ⟨hk1, varpi v * x₀, ?_, ?_⟩
    · rw [Valuation.map_mul, NumberField.AdelicLevel.valued_uniformizerUnit ℚ v]
      calc WithZero.exp (-1 : ℤ) * Valued.v x₀
          ≤ WithZero.exp (-1 : ℤ) * WithZero.exp (0 + 1) := by gcongr
        _ = 1 := by rw [← WithZero.exp_add]; norm_num
    · rwa [inv_mul_cancel_left₀ (varpi_ne_zero v)]
  exact ⟨fun v hvS => (hv v hvS).1, fun v hvS => (hv v hvS).2⟩

private theorem tsum_sphericalTorusValue_mul_pow_eq_inv_of_mul_norm_lt_one
    (e₁ e₂ e₃ z : ℂ) (hz : (1 + ‖e₁‖ + ‖e₂‖ + ‖e₃‖) * ‖z‖ < 1) :
    Summable (fun n : ℕ => sphericalTorusValue e₁ e₂ e₃ n * z ^ n) ∧
      1 - e₁ * z + e₂ * z ^ 2 - e₃ * z ^ 3 ≠ 0 ∧
      ∑' n : ℕ, sphericalTorusValue e₁ e₂ e₃ n * z ^ n = (1 - e₁ * z + e₂ * z ^ 2 - e₃ * z ^ 3)⁻¹ := by
  obtain ⟨M, hMdef⟩ : ∃ M : ℝ, M = 1 + ‖e₁‖ + ‖e₂‖ + ‖e₃‖ := ⟨_, rfl⟩
  rw [← hMdef] at hz
  have hM1 : (1 : ℝ) ≤ M := by
    have := norm_nonneg e₁; have := norm_nonneg e₂; have := norm_nonneg e₃; linarith
  have hrec : ∀ n : ℕ, sphericalTorusValue e₁ e₂ e₃ (n + 3) =
      e₁ * sphericalTorusValue e₁ e₂ e₃ (n + 2) - e₂ * sphericalTorusValue e₁ e₂ e₃ (n + 1) +
        e₃ * sphericalTorusValue e₁ e₂ e₃ n := fun n => by rw [sphericalTorusValue]
  have hb : ∀ n : ℕ, ‖sphericalTorusValue e₁ e₂ e₃ n‖ ≤ M ^ n ∧
      ‖sphericalTorusValue e₁ e₂ e₃ (n + 1)‖ ≤ M ^ (n + 1) ∧
        ‖sphericalTorusValue e₁ e₂ e₃ (n + 2)‖ ≤ M ^ (n + 2) := by
    intro n
    induction n with
    | zero =>
      have h1 : ‖e₁‖ ≤ M := by have := norm_nonneg e₂; have := norm_nonneg e₃; linarith
      refine ⟨by simp [sphericalTorusValue], by simpa [sphericalTorusValue] using h1, ?_⟩
      calc ‖sphericalTorusValue e₁ e₂ e₃ (0 + 2)‖ = ‖e₁ ^ 2 - e₂‖ := by rw [sphericalTorusValue]
        _ ≤ ‖e₁ ^ 2‖ + ‖e₂‖ := norm_sub_le _ _
        _ = ‖e₁‖ ^ 2 + ‖e₂‖ := by rw [norm_pow]
        _ ≤ M ^ (0 + 2) := by
              have hA : ‖e₁‖ + ‖e₂‖ + 1 ≤ M := by have := norm_nonneg e₃; linarith
              simp only [zero_add]
              nlinarith [mul_le_mul hA hA (by positivity) (by positivity), norm_nonneg e₁, norm_nonneg e₂]
    | succ n ih =>
      obtain ⟨h0, h1, h2⟩ := ih
      refine ⟨h1, h2, ?_⟩
      have hp1 : M ^ (n + 1) ≤ M ^ (n + 2) := pow_le_pow_right₀ hM1 (by omega)
      have hp0 : M ^ n ≤ M ^ (n + 2) := pow_le_pow_right₀ hM1 (by omega)
      have hE : ‖e₁‖ + ‖e₂‖ + ‖e₃‖ ≤ M := by linarith
      have hMn : (0 : ℝ) ≤ M ^ (n + 2) := by positivity
      calc ‖sphericalTorusValue e₁ e₂ e₃ (n + 1 + 2)‖
          = ‖e₁ * sphericalTorusValue e₁ e₂ e₃ (n + 2) - e₂ * sphericalTorusValue e₁ e₂ e₃ (n + 1) +
              e₃ * sphericalTorusValue e₁ e₂ e₃ n‖ := by rw [show n + 1 + 2 = n + 3 by omega, hrec]
        _ ≤ ‖e₁ * sphericalTorusValue e₁ e₂ e₃ (n + 2) - e₂ * sphericalTorusValue e₁ e₂ e₃ (n + 1)‖ +
              ‖e₃ * sphericalTorusValue e₁ e₂ e₃ n‖ := norm_add_le _ _
        _ ≤ ‖e₁ * sphericalTorusValue e₁ e₂ e₃ (n + 2)‖ + ‖e₂ * sphericalTorusValue e₁ e₂ e₃ (n + 1)‖ +
              ‖e₃ * sphericalTorusValue e₁ e₂ e₃ n‖ := by gcongr; exact norm_sub_le _ _
        _ = ‖e₁‖ * ‖sphericalTorusValue e₁ e₂ e₃ (n + 2)‖ + ‖e₂‖ * ‖sphericalTorusValue e₁ e₂ e₃ (n + 1)‖ +
              ‖e₃‖ * ‖sphericalTorusValue e₁ e₂ e₃ n‖ := by simp only [norm_mul]
        _ ≤ ‖e₁‖ * M ^ (n + 2) + ‖e₂‖ * M ^ (n + 2) + ‖e₃‖ * M ^ (n + 2) :=
              add_le_add (add_le_add (mul_le_mul_of_nonneg_left h2 (norm_nonneg _))
                (mul_le_mul_of_nonneg_left (h1.trans hp1) (norm_nonneg _)))
                (mul_le_mul_of_nonneg_left (h0.trans hp0) (norm_nonneg _))
        _ = (‖e₁‖ + ‖e₂‖ + ‖e₃‖) * M ^ (n + 2) := by ring
        _ ≤ M * M ^ (n + 2) := mul_le_mul_of_nonneg_right hE hMn
        _ = M ^ (n + 1 + 2) := by ring
  have hsum : Summable (fun n : ℕ => sphericalTorusValue e₁ e₂ e₃ n * z ^ n) := by
    refine Summable.of_norm_bounded (summable_geometric_of_lt_one (by positivity) hz) fun n => ?_
    rw [norm_mul, norm_pow, mul_pow]
    exact mul_le_mul_of_nonneg_right (hb n).1 (by positivity)
  have hS := hsum.hasSum
  have h3 := (hasSum_nat_add_iff' 3).mpr hS
  have h2 := ((hasSum_nat_add_iff' 2).mpr hS).mul_left (e₁ * z)
  have h1 := ((hasSum_nat_add_iff' 1).mpr hS).mul_left (e₂ * z ^ 2)
  have h0 := hS.mul_left (e₃ * z ^ 3)
  have hcomb : HasSum (fun _ : ℕ => (0 : ℂ)) _ :=
    (((h3.sub h2).add h1).sub h0).congr_fun fun n => by simp only [hrec]; ring
  have hkey := hasSum_zero.unique hcomb
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, sphericalTorusValue, pow_zero, pow_one, zero_add,
    mul_one] at hkey
  have hSD : (∑' n : ℕ, sphericalTorusValue e₁ e₂ e₃ n * z ^ n) * (1 - e₁ * z + e₂ * z ^ 2 - e₃ * z ^ 3) = 1 := by
    linear_combination -hkey
  refine ⟨hsum, fun hD => ?_, eq_inv_of_mul_eq_one_left hSD⟩
  rw [hD, mul_zero] at hSD
  exact zero_ne_one hSD

private theorem prod_neg_C_mul_X_pow {ι : Type} (t : Finset ι) (c : ι → ℂ) (f : ι → ℕ) :
    ∏ i ∈ t, (-(Polynomial.C (c i) * Polynomial.X ^ f i) : Polynomial ℂ) =
      Polynomial.C (∏ i ∈ t, -c i) * Polynomial.X ^ (∑ i ∈ t, f i) := by
  classical
  induction t using Finset.induction_on with
  | empty => simp
  | insert a t hat ih =>
    rw [Finset.prod_insert hat, Finset.prod_insert hat, Finset.sum_insert hat, ih, Polynomial.C_mul,
      Polynomial.C_neg, pow_add]
    ring

private theorem card_filter_sum_eq_le_three {ι : Type} [DecidableEq ι] (T : Finset ι) (hT : T.card ≤ 3)
    (f : ι → ℕ) (hf : ∀ i, 1 ≤ f i) (k : ℕ) :
    (T.powerset.filter fun t => ∑ i ∈ t, f i = k).card ≤ 3 := by
  rw [Finset.card_filter]
  have h4 : T.card = 0 ∨ T.card = 1 ∨ T.card = 2 ∨ T.card = 3 := by omega
  rcases h4 with h | h | h | h
  · rw [Finset.card_eq_zero.mp h]
    simp only [Finset.powerset_empty, Finset.sum_singleton, Finset.sum_empty]
    split_ifs <;> omega
  · obtain ⟨x, rfl⟩ := Finset.card_eq_one.mp h
    have hx := hf x
    rw [← Finset.insert_empty]
    simp only [Finset.sum_powerset_insert, Finset.notMem_empty, not_false_eq_true, Finset.powerset_empty,
      Finset.sum_singleton, Finset.sum_empty, Finset.sum_insert]
    split_ifs <;> omega
  · obtain ⟨x, y, hxy, rfl⟩ := Finset.card_eq_two.mp h
    have hx := hf x
    have hy := hf y
    rw [← Finset.insert_empty]
    simp only [Finset.sum_powerset_insert, Finset.mem_insert, Finset.notMem_empty, hxy, or_self, not_false_eq_true,
      Finset.powerset_empty, Finset.sum_singleton, Finset.sum_empty, Finset.sum_insert]
    split_ifs <;> omega
  · obtain ⟨x, y, z, hxy, hxz, hyz, rfl⟩ := Finset.card_eq_three.mp h
    have hx := hf x
    have hy := hf y
    have hz := hf z
    rw [← Finset.insert_empty]
    simp only [Finset.sum_powerset_insert, Finset.mem_insert, Finset.notMem_empty, hxy, hxz, hyz, or_self,
      not_false_eq_true, Finset.powerset_empty, Finset.sum_singleton, Finset.sum_empty, Finset.sum_insert]
    split_ifs <;> omega

private theorem norm_coeff_prod_one_sub_le_three {ι : Type} [DecidableEq ι] (T : Finset ι) (hT : T.card ≤ 3)
    (c : ι → ℂ) (hc : ∀ i, ‖c i‖ ≤ 1) (f : ι → ℕ) (hf : ∀ i, 1 ≤ f i) (k : ℕ) :
    ‖(∏ i ∈ T, (Polynomial.C 1 - Polynomial.C (c i) * Polynomial.X ^ f i : Polynomial ℂ)).coeff k‖ ≤ 3 := by
  have hexp : (∏ i ∈ T, (Polynomial.C 1 - Polynomial.C (c i) * Polynomial.X ^ f i : Polynomial ℂ)) =
      ∑ t ∈ T.powerset, Polynomial.C (∏ i ∈ t, -c i) * Polynomial.X ^ (∑ i ∈ t, f i) := by
    have h1 : ∀ i ∈ T, (Polynomial.C 1 - Polynomial.C (c i) * Polynomial.X ^ f i : Polynomial ℂ) =
        -(Polynomial.C (c i) * Polynomial.X ^ f i) + 1 := by
      intro i _
      rw [Polynomial.C_1]
      ring
    rw [Finset.prod_congr rfl h1, Finset.prod_add]
    refine Finset.sum_congr rfl fun t _ => ?_
    rw [Finset.prod_const_one, mul_one, prod_neg_C_mul_X_pow]
  have hterm : ∀ t ∈ T.powerset,
      ‖(Polynomial.C (∏ i ∈ t, -c i) * Polynomial.X ^ (∑ i ∈ t, f i) : Polynomial ℂ).coeff k‖ ≤
        if ∑ i ∈ t, f i = k then (1 : ℝ) else 0 := by
    intro t _
    rw [Polynomial.coeff_C_mul_X_pow]
    by_cases hk : k = ∑ i ∈ t, f i
    · rw [if_pos hk, if_pos hk.symm, norm_prod]
      exact Finset.prod_le_one (fun i _ => norm_nonneg _) fun i _ => by rw [norm_neg]; exact hc i
    · rw [if_neg hk, if_neg (Ne.symm hk), norm_zero]
  calc ‖(∏ i ∈ T, (Polynomial.C 1 - Polynomial.C (c i) * Polynomial.X ^ f i : Polynomial ℂ)).coeff k‖
      = ‖∑ t ∈ T.powerset,
          (Polynomial.C (∏ i ∈ t, -c i) * Polynomial.X ^ (∑ i ∈ t, f i) : Polynomial ℂ).coeff k‖ := by
        rw [hexp, Polynomial.finsetSum_coeff]
    _ ≤ ∑ t ∈ T.powerset,
          ‖(Polynomial.C (∏ i ∈ t, -c i) * Polynomial.X ^ (∑ i ∈ t, f i) : Polynomial ℂ).coeff k‖ :=
        norm_sum_le _ _
    _ ≤ ∑ t ∈ T.powerset, (if ∑ i ∈ t, f i = k then (1 : ℝ) else 0) := Finset.sum_le_sum hterm
    _ = ((T.powerset.filter fun t => ∑ i ∈ t, f i = k).card : ℝ) := by rw [Finset.sum_boole]
    _ ≤ 3 := by exact_mod_cast card_filter_sum_eq_le_three T hT f hf k

private theorem algebra_ringOfIntegers_rat_subsingleton (A : Type) [Ring A] :
    Subsingleton (Algebra (𝓞 ℚ) A) := by
  refine ⟨fun P Q => Algebra.algebra_ext P Q fun r => ?_⟩
  have key : ∀ f g : 𝓞 ℚ →+* A, f = g := by
    intro f g
    refine RingHom.ext fun x => ?_
    have hx : x = ((Rat.ringOfIntegersEquiv x : ℤ) : 𝓞 ℚ) :=
      Rat.ringOfIntegersEquiv.injective (by rw [map_intCast, Int.cast_id])
    rw [hx, map_intCast, map_intCast]
  exact RingHom.congr_fun (key (@algebraMap (𝓞 ℚ) A _ _ P) (@algebraMap (𝓞 ℚ) A _ _ Q)) r

private theorem norm_inducedE_le_three_of_isAdmissibleTwist
    (K : Type) [Field K] [NumberField K]
    [Algebra (𝓞 ℚ) (𝓞 K)] [Algebra.IsIntegral (𝓞 ℚ) (𝓞 K)]
    (hdeg : Module.finrank ℚ K = 3) (μ : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ) (hμ : IsAdmissibleTwist K μ)
    (p : HeightOneSpectrum (𝓞 ℚ)) :
    ‖LanglandsTunnell.RankinSelberg.inducedE1 ℚ (inducedCoeff K μ) p‖ ≤ 3 ∧
      ‖LanglandsTunnell.RankinSelberg.inducedE2 ℚ (inducedCoeff K μ) p‖ ≤ 3 ∧
      ‖LanglandsTunnell.RankinSelberg.inducedE3 ℚ (inducedCoeff K μ) p‖ ≤ 3 := by
  haveI := algebra_ringOfIntegers_rat_subsingleton (𝓞 K)
  obtain rfl : ‹Algebra (𝓞 ℚ) (𝓞 K)› = NumberField.inst_ringOfIntegersAlgebra ℚ K := Subsingleton.elim _ _
  classical
  have hc : ∀ 𝔓 : HeightOneSpectrum (𝓞 K), ‖LanglandsTunnell.CubicInduction.inducedCoeff K μ 𝔓‖ ≤ 1 := by
    intro 𝔓
    unfold LanglandsTunnell.CubicInduction.inducedCoeff
    split_ifs
    · exact (hμ.2.2 _).le
    · simp
  haveI : Module.Finite (𝓞 ℚ) (𝓞 K) := Module.Finite.of_restrictScalars_finite ℤ (𝓞 ℚ) (𝓞 K)
  have hf : ∀ 𝔓 : HeightOneSpectrum (𝓞 K), 1 ≤ (𝔓.under (𝓞 ℚ)).asIdeal.inertiaDeg' 𝔓.asIdeal := by
    intro 𝔓
    haveI : 𝔓.asIdeal.LiesOver (𝔓.under (𝓞 ℚ)).asIdeal := ⟨rfl⟩
    exact Ideal.inertiaDeg'_pos (𝔓.under (𝓞 ℚ)).asIdeal 𝔓.asIdeal
  haveI : NoZeroSMulDivisors (𝓞 ℚ) (𝓞 K) := by
    have hinj : Function.Injective (algebraMap (𝓞 ℚ) (𝓞 K)) := by
      have h : Function.Injective (algebraMap (𝓞 ℚ) K) := by
        rw [IsScalarTower.algebraMap_eq (𝓞 ℚ) ℚ K]
        exact (algebraMap ℚ K).injective.comp (IsFractionRing.injective (𝓞 ℚ) ℚ)
      rw [IsScalarTower.algebraMap_eq (𝓞 ℚ) (𝓞 K) K, RingHom.coe_comp] at h
      exact h.of_comp
    refine ⟨fun {a x} hax => ?_⟩
    rw [Algebra.smul_def, mul_eq_zero] at hax
    exact hax.imp (fun h0 => hinj (by rw [h0, map_zero])) id
  have hcard : (IsDedekindDomain.primesOverFinset p.asIdeal (𝓞 K)).card ≤ 3 := by
    have h := Ideal.card_primesOverFinset_le_finrank (𝓞 K) ℚ K p.ne_bot
    rwa [hdeg] at h
  have hmaps : Set.MapsTo (fun 𝔓 : HeightOneSpectrum (𝓞 K) => 𝔓.asIdeal)
      (LanglandsTunnell.RankinSelberg.primeFibre ℚ K p) ↑(IsDedekindDomain.primesOverFinset p.asIdeal (𝓞 K)) := by
    intro 𝔓 h𝔓
    have h𝔓' : 𝔓.under (𝓞 ℚ) = p := (LanglandsTunnell.RankinSelberg.mem_primeFibre ℚ p 𝔓).mp h𝔓
    rw [Finset.mem_coe, IsDedekindDomain.mem_primesOverFinset_iff p.ne_bot]
    refine ⟨𝔓.isPrime, ⟨?_⟩⟩
    rw [← h𝔓']
    rfl
  have hinj : Set.InjOn (fun 𝔓 : HeightOneSpectrum (𝓞 K) => 𝔓.asIdeal)
      (LanglandsTunnell.RankinSelberg.primeFibre ℚ K p) :=
    fun _ _ _ _ h => HeightOneSpectrum.ext h
  have hfin : (LanglandsTunnell.RankinSelberg.primeFibre ℚ K p).Finite :=
    Set.Finite.of_finite_image ((IsDedekindDomain.primesOverFinset p.asIdeal (𝓞 K)).finite_toSet.subset
      hmaps.image_subset) hinj
  have hT : hfin.toFinset.card ≤ 3 :=
    le_trans (Finset.card_le_card_of_injOn (fun 𝔓 : HeightOneSpectrum (𝓞 K) => 𝔓.asIdeal)
      (by rwa [Set.Finite.coe_toFinset]) (by rwa [Set.Finite.coe_toFinset])) hcard
  have key : ∀ k : ℕ, ‖(LanglandsTunnell.RankinSelberg.inducedEulerPoly ℚ (inducedCoeff K μ) p).coeff k‖ ≤ 3 := by
    intro k
    unfold LanglandsTunnell.RankinSelberg.inducedEulerPoly LanglandsTunnell.RankinSelberg.inducedFactor
    rw [finprod_mem_eq_finite_toFinset_prod _ hfin]
    exact norm_coeff_prod_one_sub_le_three hfin.toFinset hT (inducedCoeff K μ) hc
      (fun 𝔓 => (𝔓.under (𝓞 ℚ)).asIdeal.inertiaDeg' 𝔓.asIdeal) hf k
  refine ⟨?_, key 2, ?_⟩
  · unfold LanglandsTunnell.RankinSelberg.inducedE1
    rw [norm_neg]
    exact key 1
  · unfold LanglandsTunnell.RankinSelberg.inducedE3
    rw [norm_neg]
    exact key 3

private theorem mul_rpow_neg_lt_one_of_le_ten_of_two_le_of_six_lt
    (m : ℝ) (hm : m ≤ 10) (N : ℕ) (hN : 2 ≤ N) (σ : ℝ) (hσ : 6 < σ) :
    m * (N : ℝ) ^ (-σ) < 1 := by
  have hN2 : (2 : ℝ) ≤ N := by exact_mod_cast hN
  have h1 : (N : ℝ) ^ (-σ) ≤ (2 : ℝ) ^ (-σ) :=
    Real.rpow_le_rpow_of_nonpos two_pos hN2 (by linarith)
  have h2 : (2 : ℝ) ^ (-σ) < (2 : ℝ) ^ (-(6 : ℝ)) :=
    Real.rpow_lt_rpow_of_exponent_lt one_lt_two (by linarith)
  have h3 : (2 : ℝ) ^ (-(6 : ℝ)) = 1 / 64 := by
    rw [Real.rpow_neg two_pos.le, show (6 : ℝ) = ((6 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
    norm_num
  have h4 : 0 ≤ (N : ℝ) ^ (-σ) := Real.rpow_nonneg N.cast_nonneg _
  have h5 : (N : ℝ) ^ (-σ) < 1 / 64 := (h1.trans_lt h2).trans_eq h3
  calc m * (N : ℝ) ^ (-σ) ≤ 10 * (N : ℝ) ^ (-σ) := mul_le_mul_of_nonneg_right hm h4
    _ < 10 * (1 / 64) := mul_lt_mul_of_pos_left h5 (by norm_num)
    _ < 1 := by norm_num

attribute [local instance] NumberField.Idele.ideleBorel NumberField.AdelicHaar.adeleBorel in

theorem solution
    (K : Type) [Field K] [NumberField K]
    [Algebra (𝓞 ℚ) (𝓞 K)] [Algebra.IsIntegral (𝓞 ℚ) (𝓞 K)]
    (_hdeg : Module.finrank ℚ K = 3)
    (ψ : AddChar (AdeleRing (𝓞 ℚ) ℚ) ℂ) (_hψ : IsGlobalAddChar ℚ ψ)
    (μ : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ) (_hμ : IsAdmissibleTwist K μ)
    (_hlev : ∀ v : HeightOneSpectrum (𝓞 ℚ), ¬ IsBadPlace K μ v →
      LanglandsTunnell.TateLocal.addCharLevel (psiLoc ψ v) = 0)
    (D : Set (AdelicGL2 (𝓞 ℚ) ℚ)) (U : Ideal (𝓞 ℚ) → Subgroup (AdelicGL2 (𝓞 ℚ) ℚ))
    (gen : HeightOneSpectrum (𝓞 ℚ) → AdelicGL2 (𝓞 ℚ) ℚ)
    (X : CubicInductionData)
    (hX : IsCubicInductionDataOn K (productionPinsOf ℚ D U gen (AdelicBox.adelicBox ℚ)) ψ μ {v | IsBadPlace K μ v} X)
    (hexp : X.form ≠ 0 ∧ ∀ v, ¬ IsBadPlace K μ v →
      LanglandsTunnell.TateLocal.addCharLevel (psiLoc ψ v) = 0 →
        X.whittakerLoc v 1 = 1 ∧ HasSphericalTorusValuesAt (inducedCoeff K μ) v (X.whittakerLoc v))
    (S : Finset (HeightOneSpectrum (𝓞 ℚ))) (hSbad : ∀ w : HeightOneSpectrum (𝓞 ℚ), IsBadPlace K μ w ↔ w ∈ S)
    (hS : ∀ τ : (AdeleRing (𝓞 ℚ) ℚ)ˣ →* ℂˣ, IsAdmissibleTwist ℚ τ → ∀ g : AdelicGL 3 (𝓞 ℚ) ℚ, ∃ σ₀ : ℝ,
      ∀ s : ℂ, σ₀ < s.re →
        Integrable (fun a : (AdeleRing (𝓞 ℚ) ℚ)ˣ =>
          X.whittaker (iotaGL (diagUnitGL2 a) * g) * ((τ a : ℂˣ) : ℂ) * ((TateGlobal.ideleNorm ℚ a : ℝ) : ℂ) ^ (s - 1))
          (NumberField.Idele.productMeasureData ℚ S).νS) :
    ∀ τ : (AdeleRing (𝓞 ℚ) ℚ)ˣ →* ℂˣ, IsAdmissibleTwist ℚ τ →
      (∀ p : HeightOneSpectrum (𝓞 ℚ), p ∉ S → IsUnramifiedCharAt τ p) → ∀ g : AdelicGL 3 (𝓞 ℚ) ℚ,
      (∀ w : HeightOneSpectrum (𝓞 ℚ), w ∉ S →
        componentAt3 (𝓞 ℚ) ℚ w g ∈ localMaximalCompact3 (𝓞 ℚ) ℚ w) →
      ∃ (L : ℂ → ℂ) (σ₀ : ℝ), ∀ s : ℂ, σ₀ < s.re →
        HasProd (fun p : {p : HeightOneSpectrum (𝓞 ℚ) // p ∉ S} =>
            ((inducedEulerPoly ℚ (inducedCoeff K μ) p.1).eval
              (LanglandsTunnell.CubicLambda.eulerCoeff ℚ τ p.1 * (Ideal.absNorm p.1.asIdeal : ℂ) ^ (-s)))⁻¹)
          (L s) ∧
        globalZeta30 X.whittaker τ s g =
          ((NumberField.Idele.productMeasureData ℚ S).c : ℂ) *
            (∫ a : (AdeleRing (𝓞 ℚ) ℚ)ˣ,
              X.whittaker (iotaGL (diagUnitGL2 a) * g) * ((τ a : ℂˣ) : ℂ) *
                ((TateGlobal.ideleNorm ℚ a : ℝ) : ℂ) ^ (s - 1)
              ∂(NumberField.Idele.productMeasureData ℚ S).νS) *
            L s := by
  intro τ hτadm hunr g hg
  have hbad : ∀ v : HeightOneSpectrum (𝓞 ℚ), v ∉ S → ¬ IsBadPlace K μ v := fun v hv hb => hv ((hSbad v).1 hb)
  have hpair := psiLoc_eq_one_of_valued_le_one_and_exists_ne_one K ψ _hψ μ _hlev S hSbad
  have hfac : ∀ (x : AdelicGL 3 (𝓞 ℚ) ℚ) (T : Finset (HeightOneSpectrum (𝓞 ℚ))), S ⊆ T →
      (∀ v, v ∉ T → componentAt3 (𝓞 ℚ) ℚ v x ∈ localMaximalCompact3 (𝓞 ℚ) ℚ v) →
      X.whittaker x = X.whittakerArch (archComponent3 (𝓞 ℚ) ℚ x) *
        ∏ v ∈ T, X.whittakerLoc v (componentAt3 (𝓞 ℚ) ℚ v x) :=
    fun x T hST hx => hX.factorizable x T (fun v hv => hST ((hSbad v).1 hv)) hx
  have hK : ∀ v, v ∉ S → ∀ k ∈ localMaximalCompact3 (𝓞 ℚ) ℚ v, ∀ y : LocalGL3 v,
      X.whittakerLoc v (y * k) = X.whittakerLoc v y :=
    fun v hv k hk y => (hX.spherical v (hbad v hv)).1 y k hk
  have hlaw : ∀ v, v ∉ S → IsGL3PsiWhittakerFn (psiLoc ψ v) (X.whittakerLoc v) := fun v _ => hX.whittakerLoc_law v
  have hsph : ∀ v, v ∉ S → HasSphericalTorusValuesAt (inducedCoeff K μ) v (X.whittakerLoc v) :=
    fun v hv => (hexp.2 v (hbad v hv) (_hlev v (hbad v hv))).2
  have hχU := NumberField.TateGlobal.apply_eq_one_of_forall_isUnramifiedCharAt_of_continuous ℚ τ hτadm.2.1 S hunr
  have hunit : ∀ x : (AdeleRing (𝓞 ℚ) ℚ)ˣ, ‖((τ x : ℂˣ) : ℂ)‖ = 1 := hτadm.2.2
  have hτ0 : ∀ v, v ∉ S →
      ‖((τ (uniformizerIdele ℚ v) : ℂˣ) : ℂ)‖ ≤ ((Ideal.absNorm v.asIdeal : ℕ) : ℝ) ^ (0 : ℝ) := by
    intro v _
    simp only [Real.rpow_zero, hunit, le_refl]
  have hE : ∀ v : HeightOneSpectrum (𝓞 ℚ),
      ‖LanglandsTunnell.RankinSelberg.inducedE1 ℚ (inducedCoeff K μ) v‖ ≤ 3 ∧
        ‖LanglandsTunnell.RankinSelberg.inducedE2 ℚ (inducedCoeff K μ) v‖ ≤ 3 ∧
        ‖LanglandsTunnell.RankinSelberg.inducedE3 ℚ (inducedCoeff K μ) v‖ ≤ 3 :=
    fun v => norm_inducedE_le_three_of_isAdmissibleTwist K _hdeg μ _hμ v
  have hN2 : ∀ v : HeightOneSpectrum (𝓞 ℚ), (2 : ℝ) ≤ ((Ideal.absNorm v.asIdeal : ℕ) : ℝ) := by
    intro v
    exact_mod_cast NumberField.HeightOneSpectrum.one_lt_absNorm (v := v)
  have hN3 : ∀ v : HeightOneSpectrum (𝓞 ℚ), (3 : ℝ) ≤ ((Ideal.absNorm v.asIdeal : ℕ) : ℝ) ^ (2 : ℝ) := by
    intro v
    rw [Real.rpow_two]
    nlinarith [hN2 v]
  have hκ : ∀ v, v ∉ S →
      ‖LanglandsTunnell.RankinSelberg.inducedE1 ℚ (inducedCoeff K μ) v‖ ≤
          ((Ideal.absNorm v.asIdeal : ℕ) : ℝ) ^ (2 : ℝ) ∧
        ‖LanglandsTunnell.RankinSelberg.inducedE2 ℚ (inducedCoeff K μ) v‖ ≤
          ((Ideal.absNorm v.asIdeal : ℕ) : ℝ) ^ (2 : ℝ) ∧
        ‖LanglandsTunnell.RankinSelberg.inducedE3 ℚ (inducedCoeff K μ) v‖ ≤
          ((Ideal.absNorm v.asIdeal : ℕ) : ℝ) ^ (2 : ℝ) :=
    fun v _ => ⟨(hE v).1.trans (hN3 v), (hE v).2.1.trans (hN3 v), (hE v).2.2.trans (hN3 v)⟩
  have hint := hS τ hτadm g
  obtain ⟨σ₁, hσ₁⟩ := hint
  have hS' : ∀ s : ℂ, max 6 σ₁ < s.re →
      Integrable (fun a : (AdeleRing (𝓞 ℚ) ℚ)ˣ =>
        X.whittaker (iotaGL (diagUnitGL2 a) * g) * ((τ a : ℂˣ) : ℂ) * ((TateGlobal.ideleNorm ℚ a : ℝ) : ℂ) ^ (s - 1))
        (NumberField.Idele.productMeasureData ℚ S).νS :=
    fun s hs => hσ₁ s (lt_of_le_of_lt (le_max_right 6 σ₁) hs)
  have hσ : (2 : ℝ) + 0 + 4 ≤ max 6 σ₁ := by
    have h6 : (6 : ℝ) ≤ max 6 σ₁ := le_max_left 6 σ₁
    linarith
  have hshell := exists_hasProd_sphericalShellSums_and_globalZeta30_eq_mul_integral_sPart (inducedCoeff K μ) ψ S
    X.whittaker X.whittakerArch X.whittakerLoc hfac hK hlaw hpair.1 hpair.2 hsph τ hχU g hg 0 hτ0 2 (by norm_num) hκ
    (max 6 σ₁) hσ (NumberField.Idele.productMeasureData ℚ S) hS'
  obtain ⟨L, hL⟩ := hshell
  refine ⟨L, max 6 σ₁, fun s hs => ?_⟩
  have hLs := hL s hs
  obtain ⟨hprod, -, hid⟩ := hLs
  refine ⟨?_, hid⟩
  have hsre : (6 : ℝ) < s.re := lt_of_le_of_lt (le_max_left 6 σ₁) hs
  convert hprod using 1
  funext p
  have hz : (1 + ‖LanglandsTunnell.RankinSelberg.inducedE1 ℚ (inducedCoeff K μ) p.1‖ +
        ‖LanglandsTunnell.RankinSelberg.inducedE2 ℚ (inducedCoeff K μ) p.1‖ +
        ‖LanglandsTunnell.RankinSelberg.inducedE3 ℚ (inducedCoeff K μ) p.1‖) *
      ‖((τ (uniformizerIdele ℚ p.1) : ℂˣ) : ℂ) * (Ideal.absNorm p.1.asIdeal : ℂ) ^ (-s)‖ < 1 := by
    have hnorm : ‖((τ (uniformizerIdele ℚ p.1) : ℂˣ) : ℂ) * (Ideal.absNorm p.1.asIdeal : ℂ) ^ (-s)‖ =
        ((Ideal.absNorm p.1.asIdeal : ℕ) : ℝ) ^ (-s.re) := by
      have hpos : (0 : ℝ) < ((Ideal.absNorm p.1.asIdeal : ℕ) : ℝ) := by linarith [hN2 p.1]
      rw [norm_mul, hunit, one_mul, ← Complex.ofReal_natCast, Complex.norm_cpow_eq_rpow_re_of_pos hpos,
        Complex.neg_re]
    rw [hnorm]
    refine mul_rpow_neg_lt_one_of_le_ten_of_two_le_of_six_lt _ ?_ _
      (NumberField.HeightOneSpectrum.one_lt_absNorm (v := p.1)) s.re hsre
    have h := hE p.1
    linarith [h.1, h.2.1, h.2.2]
  have hser := tsum_sphericalTorusValue_mul_pow_eq_inv_of_mul_norm_lt_one
    (LanglandsTunnell.RankinSelberg.inducedE1 ℚ (inducedCoeff K μ) p.1)
    (LanglandsTunnell.RankinSelberg.inducedE2 ℚ (inducedCoeff K μ) p.1)
    (LanglandsTunnell.RankinSelberg.inducedE3 ℚ (inducedCoeff K μ) p.1)
    (((τ (uniformizerIdele ℚ p.1) : ℂˣ) : ℂ) * (Ideal.absNorm p.1.asIdeal : ℂ) ^ (-s)) hz
  rw [LanglandsTunnell.CubicLambda.eulerCoeff, if_pos (hunr p.1 p.2),
    LanglandsTunnell.RankinSelberg.eval_inducedEulerPoly_eq_of_finrank_le_three K _hdeg.le (inducedCoeff K μ) p.1]
  exact hser.2.2.symm

end S_LanglandsTunnell_CubicInduction_globalZeta30_eq_sPart_mul_inducedL_of_isCubicInductionDataOn
end P2MW
export P2MW.S_LanglandsTunnell_CubicInduction_globalZeta30_eq_sPart_mul_inducedL_of_isCubicInductionDataOn (solution)
