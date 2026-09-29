-- Prove2me | solution 1 for LanglandsTunnell.CubicInduction.jacquetWhittaker3_eq_integral_of_integrable
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:08.670037+00:00
-- url     : https://prove2.me/submissions/e57e808d-284f-5cdc-9213-6abf186e7a67

import Definitions.Def_LanglandsTunnell_CubicInduction_JacquetWhittaker
import Theorems.Thm_LanglandsTunnell_CubicInduction_exists_forall_le_integrableOn_and_jacquetTruncated3_eq_of_cellSectionOf
import Theorems.Thm_NumberField_StandardAddChar_psiLocal_rat_eq_psiV
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_LanglandsTunnell_CubicInduction_jacquetWhittaker3_eq_integral_of_integrable
p2m_attr_erase "instance" "IsDedekindDomain.HeightOneSpectrum.Extension.instAlgebraSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersValEqUnder IsDedekindDomain.HeightOneSpectrum.Extension.instAlgebraSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersValEqUnder_1 IsDedekindDomain.HeightOneSpectrum.instMulActionHomClassAlgHomTensorProductAdicCompletionForallValEqUnder_definitions IsDedekindDomain.HeightOneSpectrum.Extension.instAlgebraAdicCompletionValEqUnder IsDedekindDomain.HeightOneSpectrum.adicCompletion.instFiniteForallValEqUnderOfFiniteDimensional_definitions IsDedekindDomain.HeightOneSpectrum.instIsBiscalarSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersTensorProductCoeAlgHomTensorAdicCompletionIntegersTo IsDedekindDomain.HeightOneSpectrum.Extension.instContinuousSMulAdicCompletionValEqUnder IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsModuleTopology IsDedekindDomain.HeightOneSpectrum.Extension.instFiniteSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersValEqUnderOfFiniteDimensional IsDedekindDomain.HeightOneSpectrum.adicCompletion.instFiniteValEqUnderOfFiniteDimensional_definitions instIsBiscalarTensorProductCoeAlgHomBaseChange_of_algebraMap IsDedekindDomain.HeightOneSpectrum.instIsScalarTowerSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersValEqUnder_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsModuleTopologyPi IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions Submodule.instIsTopologicalModuleSubtypeMem Pi.instTopologicalModule IsTopologicalModule.toContinuousSMul IsTopologicalModule.toContinuousAdd instFunLike SemialgHomClass.toSemilinearMapClass instCoeTCSemialgHom SemialgHomClass.toRingHomClass SemialgHomClass.instSemialgHom"
p2m_attr_erase "simp" "LanglandsTunnell.CubicInduction.translateRepStep_apply_coe LanglandsTunnell.CubicInduction.translateFn_apply SemialgHom.baseChange_of_algebraMap_tmul_left SemialgHom.baseChangeRightOfAlgebraMap_apply Pi.semialgHomPi_apply Pi.semialgHom_apply Module.Basis.rightBaseChange_apply LinearEquiv.coe_mulLeft LinearEquiv.coe_mulRight WithVal.semialgebraMap_toFun_ofVal Module.Basis.rightBaseChange_repr IsDedekindDomain.HeightOneSpectrum.adicCompletionIntegers.tensorCoe_tmul IsDedekindDomain.HeightOneSpectrum.tensorAdicCompletionIntegersTo_tmul SemialgHom.baseChangeRightOfAlgebraMap_coe IsDedekindDomain.HeightOneSpectrum.adicCompletion.integerBaseChangeLinearEquiv_tmul_apply SemialgHom.baseChange_of_algebraMap_tmul_right IsLocalization.map_moduleTensorEquiv_symm_tmul IsLocalization.leftModuleTensorEquiv_apply IsLocalization.moduleLid_symm_apply IsLocalization.leftModuleTensorEquiv_symm_apply IsLocalization.map_moduleTensorEquiv_tmul IsModuleTopology.continuousLinearEquiv_apply AlgEquiv.extendScalars_symm_apply IsModuleTopology.Module.Basis.equivFun_homeo_symm_apply IsModuleTopology.Module.Basis.equivFun_homeo_apply IsModuleTopology.continuousAlgEquivOfIsBiscalar_apply AlgEquiv.extendScalars_apply IsModuleTopology.continuousLinearEquiv_symm_apply SemialgHom.restrictScalars_toFun SemialgHom.mk.sizeOf_spec SemialgHom.mk.injEq SemialgHom.coe_coe coe_mk TensorProduct.RightActions.smul_def TensorProduct.RightActions.Module.TensorProduct.comm_symm_apply_tmul TensorProduct.RightActions.LinearMap.baseChange_id TensorProduct.RightActions.algebraMap_eval TensorProduct.RightActions.Module.TensorProduct.comm_apply_tmul TensorProduct.RightActions.Algebra.TensorProduct.comm_symm_apply_tmul TensorProduct.RightActions.Algebra.TensorProduct.comm_apply_tmul"

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

noncomputable section

namespace LTJacquetUntruncated

open MeasureTheory IsDedekindDomain NumberField NumberField.AdelicLevel NumberField.StandardAddChar LanglandsTunnell.TateLocal LanglandsTunnell.CubicInduction Filter Topology

open scoped WithZero

variable (v : HeightOneSpectrum (𝓞 ℚ))

local notation "F" => HeightOneSpectrum.adicCompletion ℚ v
local notation "ϖ" => (uniformizerUnit ℚ v : (HeightOneSpectrum.adicCompletion ℚ v)ˣ)

section Sets

theorem valued_uniformizerUnit_zpow (m : ℤ) :
    Valued.v ((ϖ ^ m : Fˣ) : F) = WithZero.exp (-m) := by
  rw [Units.val_zpow_eq_zpow_val, map_zpow₀, valued_uniformizerUnit, ← WithZero.exp_zsmul]
  congr 1
  simp

def ball (m : ℤ) : Set F := {x | Valued.v x ≤ WithZero.exp m}

theorem mem_ball {m : ℤ} {x : F} : x ∈ ball v m ↔ Valued.v x ≤ WithZero.exp m := Iff.rfl

theorem isClosed_ball (k : ℤ) : IsClosed (ball v k) := by
  have ht : ((ϖ ^ (-k) : Fˣ) : F) ≠ 0 := Units.ne_zero _
  have h := isClosed_setOf_valued_le v _ ht
  rw [valued_uniformizerUnit_zpow, neg_neg] at h
  exact h

def box (c : ℤ) : Set (F × F × F) := ball v c ×ˢ (ball v c ×ˢ ball v (2 * c))

theorem unipotentBall3_eq (c : ℤ) : unipotentBall3 v c = box v c := by
  ext p
  simp only [mem_unipotentBall3_iff, box, Set.mem_prod, mem_ball]

theorem exists_nat_valued_le (x : F) : ∃ n : ℕ, Valued.v x ≤ WithZero.exp (n : ℤ) := by
  by_cases hx : Valued.v x = 0
  · exact ⟨0, by rw [hx]; exact zero_le'⟩
  · obtain ⟨m, hm⟩ : ∃ m : ℤ, Valued.v x = WithZero.exp m := ⟨_, (WithZero.exp_log hx).symm⟩
    refine ⟨m.toNat, ?_⟩
    rw [hm]
    exact WithZero.exp_le_exp.mpr (Int.self_le_toNat m)

theorem iUnion_unipotentBall3_nat : (⋃ n : ℕ, unipotentBall3 v (n : ℤ)) = Set.univ := by
  refine Set.eq_univ_of_forall fun p => ?_
  obtain ⟨n₁, h₁⟩ := exists_nat_valued_le v p.1
  obtain ⟨n₂, h₂⟩ := exists_nat_valued_le v p.2.1
  obtain ⟨n₃, h₃⟩ := exists_nat_valued_le v p.2.2
  refine Set.mem_iUnion.mpr ⟨n₁ + n₂ + n₃, ?_⟩
  simp only [mem_unipotentBall3_iff]
  refine ⟨h₁.trans (WithZero.exp_le_exp.mpr (by push_cast; omega)),
    h₂.trans (WithZero.exp_le_exp.mpr (by push_cast; omega)),
    h₃.trans (WithZero.exp_le_exp.mpr (by push_cast; omega))⟩

theorem monotone_unipotentBall3_nat : Monotone fun n : ℕ => unipotentBall3 v (n : ℤ) :=
  fun _ _ h => unipotentBall3_mono v (by exact_mod_cast h)

variable [MeasurableSpace (HeightOneSpectrum.adicCompletion ℚ v)] [BorelSpace (HeightOneSpectrum.adicCompletion ℚ v)]

theorem measurableSet_ball (m : ℤ) : MeasurableSet (ball v m) := (isClosed_ball v m).measurableSet

theorem measurableSet_unipotentBall3 (c : ℤ) : MeasurableSet (unipotentBall3 v c) := by
  rw [unipotentBall3_eq]
  exact (measurableSet_ball v c).prod ((measurableSet_ball v c).prod (measurableSet_ball v _))

end Sets

section Psi

theorem norm_psiPadicFun {p : ℕ} [Fact p.Prime] (y : ℚ_[p]) : ‖psiPadicFun y‖ = 1 := by
  obtain ⟨a, k, hk⟩ := exists_pPow_approx y
  rw [psiPadicFun_eq hk]
  have hcast : -(2 * (Real.pi : ℂ) * Complex.I) * ((a : ℂ) / (p : ℂ) ^ k)
      = ((-(2 * Real.pi * ((a : ℝ) / (p : ℝ) ^ k)) : ℝ) : ℂ) * Complex.I := by
    push_cast
    ring
  rw [hcast, Complex.norm_exp_ofReal_mul_I]

theorem norm_psiV (x : F) : ‖psiV v x‖ = 1 := by
  haveI : Fact (Nat.Prime (Rat.HeightOneSpectrum.primesEquiv v : ℕ)) := ⟨(Rat.HeightOneSpectrum.primesEquiv v).2⟩
  rw [psiV_apply, psiPadic_apply]
  exact norm_psiPadicFun _

theorem norm_psiLocal (x : F) : ‖psiLocal ℚ v x‖ = 1 := by
  rw [psiLocal_rat_eq_psiV, norm_psiV]

end Psi

section Main

theorem main
    (ν : Fin 3 → (Fˣ →* ℂˣ)) (hν : ∀ i, IsLocallyConstant (ν i))
    (Φ : (Fin 3 → F) → ℂ) (hΦ : IsLocallyConstant Φ ∧ HasCompactSupport Φ)
    (g : LocalGL3 v)
    (hint : letI := localBorel ℚ v
      Integrable (fun p : F × F × F =>
        cellSectionOf v ν Φ (antidiagonal3 v * upperUnipotent3 p.1 p.2.1 p.2.2 * g)) (jacquetHaar3 v)) :
    letI := localBorel ℚ v
    jacquetWhittaker3 v ν Φ g =
      ∫ p : F × F × F, psiLocal ℚ v (-(p.1 + p.2.1)) *
        cellSectionOf v ν Φ (antidiagonal3 v * upperUnipotent3 p.1 p.2.1 p.2.2 * g) ∂(jacquetHaar3 v) := by
  letI : MeasurableSpace F := localBorel ℚ v
  haveI : BorelSpace F := ⟨rfl⟩

  set u : LocalGL3 v → ℂ := gl3AmbientRightTranslate (R := ℂ) g (cellSectionOf v ν Φ) with hu
  set G : F × F × F → ℂ := fun p => psiLocal ℚ v (-(p.1 + p.2.1)) *
    cellSectionOf v ν Φ (antidiagonal3 v * upperUnipotent3 p.1 p.2.1 p.2.2 * g) with hG

  have hD : ∀ c : ℤ, jacquetTruncated3 v c u = ∫ p in unipotentBall3 v c, G p ∂(jacquetHaar3 v) := by
    intro c
    rfl

  obtain ⟨c₀, hc₀⟩ :=
    exists_forall_le_integrableOn_and_jacquetTruncated3_eq_of_cellSectionOf v ν hν Φ hΦ g
  have hstab : ∃ c₀ : ℕ, ∀ c : ℤ, (c₀ : ℤ) ≤ c → jacquetTruncated3 v c u = jacquetTruncated3 v c₀ u :=
    ⟨c₀, fun c hc => (hc₀ c hc).2⟩
  have hval : ∀ c : ℤ, (jacquetLevel v u : ℤ) ≤ c → jacquetTruncated3 v c u = jacquetValue v u :=
    fun c hc => jacquetTruncated3_eq_jacquetValue v u hstab hc

  have hGint : Integrable G (jacquetHaar3 v) := by
    have hmeas : AEStronglyMeasurable (fun p : F × F × F => psiLocal ℚ v (-(p.1 + p.2.1))) (jacquetHaar3 v) := by
      refine (Continuous.aestronglyMeasurable ?_)
      exact (continuous_psiLocal ℚ v).comp ((continuous_fst.add (continuous_fst.comp continuous_snd)).neg)
    have hbd : ∀ᵐ p : F × F × F ∂(jacquetHaar3 v), ‖psiLocal ℚ v (-(p.1 + p.2.1))‖ ≤ 1 :=
      Eventually.of_forall fun p => (norm_psiLocal v _).le
    exact hint.bdd_mul hmeas hbd

  have htend : Tendsto (fun n : ℕ => ∫ p in unipotentBall3 v (n : ℤ), G p ∂(jacquetHaar3 v)) atTop
      (𝓝 (∫ p, G p ∂(jacquetHaar3 v))) := by
    have h := tendsto_setIntegral_of_monotone (μ := jacquetHaar3 v) (f := G)
      (s := fun n : ℕ => unipotentBall3 v (n : ℤ)) (fun n => measurableSet_unipotentBall3 v (n : ℤ))
      (monotone_unipotentBall3_nat v) (by rw [iUnion_unipotentBall3_nat]; exact hGint.integrableOn)
    rwa [iUnion_unipotentBall3_nat, Measure.restrict_univ] at h

  have hev : ∀ᶠ n : ℕ in atTop, jacquetValue v u = ∫ p in unipotentBall3 v (n : ℤ), G p ∂(jacquetHaar3 v) := by
    filter_upwards [eventually_ge_atTop (jacquetLevel v u)] with n hn
    rw [← hD, hval (n : ℤ) (by exact_mod_cast hn)]
  have hconst : Tendsto (fun n : ℕ => ∫ p in unipotentBall3 v (n : ℤ), G p ∂(jacquetHaar3 v)) atTop
      (𝓝 (jacquetValue v u)) :=
    (tendsto_const_nhds (x := jacquetValue v u)).congr' hev
  have hlim : jacquetValue v u = ∫ p, G p ∂(jacquetHaar3 v) := tendsto_nhds_unique hconst htend
  rw [jacquetWhittaker3_apply]
  exact hlim

end Main

end LTJacquetUntruncated

end

open MeasureTheory IsDedekindDomain NumberField NumberField.StandardAddChar LanglandsTunnell.TateLocal LanglandsTunnell.CubicInduction in

theorem solution
    (v : HeightOneSpectrum (𝓞 ℚ))
    (ν : Fin 3 → ((v.adicCompletion ℚ)ˣ →* ℂˣ)) (hν : ∀ i, IsLocallyConstant (ν i))
    (Φ : (Fin 3 → v.adicCompletion ℚ) → ℂ) (hΦ : IsLocallyConstant Φ ∧ HasCompactSupport Φ)
    (g : LocalGL3 v)
    (hint : letI := localBorel ℚ v
      Integrable (fun p : v.adicCompletion ℚ × v.adicCompletion ℚ × v.adicCompletion ℚ =>
        cellSectionOf v ν Φ (antidiagonal3 v * upperUnipotent3 p.1 p.2.1 p.2.2 * g)) (jacquetHaar3 v)) :
    letI := localBorel ℚ v
    jacquetWhittaker3 v ν Φ g =
      ∫ p : v.adicCompletion ℚ × v.adicCompletion ℚ × v.adicCompletion ℚ,
        psiLocal ℚ v (-(p.1 + p.2.1)) *
          cellSectionOf v ν Φ (antidiagonal3 v * upperUnipotent3 p.1 p.2.1 p.2.2 * g) ∂(jacquetHaar3 v) :=
  LTJacquetUntruncated.main v ν hν Φ hΦ g hint

end S_LanglandsTunnell_CubicInduction_jacquetWhittaker3_eq_integral_of_integrable
end P2MW
export P2MW.S_LanglandsTunnell_CubicInduction_jacquetWhittaker3_eq_integral_of_integrable (solution)
