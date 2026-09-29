-- Prove2me | solution 1 for LanglandsTunnell.CubicInduction.tendsto_setIntegral_annulus_setIntegral_ball_jacquetWindow_sub_jacquetValue
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:08.670037+00:00
-- url     : https://prove2.me/submissions/ad495a80-3fbb-57e5-ac73-5f0fd4f25a72

import Definitions.Def_LanglandsTunnell_CubicInduction_JacquetWhittaker
import Definitions.Def_LanglandsTunnell_CubicInduction_GlobalZeta31
import Definitions.Def_LanglandsTunnell_StandardLocalConstantsAt
import Definitions.Def_LanglandsTunnell_TateLocalZeta
import Definitions.Def_LanglandsTunnell_CubicInduction_PrincipalSeries3
import Definitions.Def_LanglandsTunnell_CubicInduction_IotaTorus
import Theorems.Thm_LanglandsTunnell_TateLocal_modulus_adicCompletion_eq_nnnorm
import Theorems.Thm_LanglandsTunnell_TateLocal_addCharLevel_psiLocal_rat
import Theorems.Thm_LanglandsTunnell_TateLocal_psiLocal_ne_one
import Theorems.Thm_LanglandsTunnell_TateLocal_exists_hasConductorExponentAt_of_continuous
import Theorems.Thm_LanglandsTunnell_CubicInduction_exists_forall_le_integrableOn_and_jacquetTruncated3_eq_of_cellSectionOf
import Theorems.Thm_LanglandsTunnell_CubicInduction_exists_forall_gl3AmbientRightTranslate_eq_of_mem_principalSeries3
import Mathlib.Analysis.SpecialFunctions.Pow.Complex
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Algebra.Polynomial.Eval.Defs
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

p2m_attr_erase "ext" "IsDedekindDomain.HeightOneSpectrum.adicCompletion.ext"
namespace P2MW.S_LanglandsTunnell_CubicInduction_tendsto_setIntegral_annulus_setIntegral_ball_jacquetWindow_sub_jacquetValue
p2m_attr_erase "instance" "instFiniteResidueFieldAdicCompletionRingOfIntegersWithZeroMultiplicativeInt_definitions NumberField.instCompactSpaceAdicCompletionIntegers Rat.adicCompletion.locallyCompactSpace NumberField.instFiniteResidueFieldAdicCompletionIntegers instWeaklyLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions instCountableOfNumberField_definitions IsDedekindDomain.HeightOneSpectrum.Extension.instAlgebraSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersValEqUnder IsDedekindDomain.HeightOneSpectrum.Extension.instAlgebraSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersValEqUnder_1 IsDedekindDomain.HeightOneSpectrum.instMulActionHomClassAlgHomTensorProductAdicCompletionForallValEqUnder_definitions IsDedekindDomain.HeightOneSpectrum.Extension.instAlgebraAdicCompletionValEqUnder IsDedekindDomain.HeightOneSpectrum.adicCompletion.instFiniteForallValEqUnderOfFiniteDimensional_definitions IsDedekindDomain.HeightOneSpectrum.instIsBiscalarSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersTensorProductCoeAlgHomTensorAdicCompletionIntegersTo IsDedekindDomain.HeightOneSpectrum.Extension.instContinuousSMulAdicCompletionValEqUnder IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsModuleTopology IsDedekindDomain.HeightOneSpectrum.Extension.instFiniteSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersValEqUnderOfFiniteDimensional IsDedekindDomain.HeightOneSpectrum.adicCompletion.instFiniteValEqUnderOfFiniteDimensional_definitions instIsBiscalarTensorProductCoeAlgHomBaseChange_of_algebraMap IsDedekindDomain.HeightOneSpectrum.instIsScalarTowerSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersValEqUnder_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsModuleTopologyPi Submodule.instIsTopologicalModuleSubtypeMem Pi.instTopologicalModule IsTopologicalModule.toContinuousSMul IsTopologicalModule.toContinuousAdd instFunLike SemialgHomClass.toSemilinearMapClass instCoeTCSemialgHom SemialgHomClass.toRingHomClass SemialgHomClass.instSemialgHom"
p2m_attr_erase "simp" "SemialgHom.baseChange_of_algebraMap_tmul_left SemialgHom.baseChangeRightOfAlgebraMap_apply Pi.semialgHomPi_apply Pi.semialgHom_apply Module.Basis.rightBaseChange_apply LinearEquiv.coe_mulLeft LinearEquiv.coe_mulRight WithVal.semialgebraMap_toFun_ofVal Module.Basis.rightBaseChange_repr IsDedekindDomain.HeightOneSpectrum.adicCompletionIntegers.tensorCoe_tmul IsDedekindDomain.HeightOneSpectrum.tensorAdicCompletionIntegersTo_tmul SemialgHom.baseChangeRightOfAlgebraMap_coe IsDedekindDomain.HeightOneSpectrum.adicCompletion.integerBaseChangeLinearEquiv_tmul_apply SemialgHom.baseChange_of_algebraMap_tmul_right IsLocalization.map_moduleTensorEquiv_symm_tmul IsLocalization.leftModuleTensorEquiv_apply IsLocalization.moduleLid_symm_apply IsLocalization.leftModuleTensorEquiv_symm_apply IsLocalization.map_moduleTensorEquiv_tmul IsModuleTopology.continuousLinearEquiv_apply AlgEquiv.extendScalars_symm_apply IsModuleTopology.Module.Basis.equivFun_homeo_symm_apply IsModuleTopology.Module.Basis.equivFun_homeo_apply IsModuleTopology.continuousAlgEquivOfIsBiscalar_apply AlgEquiv.extendScalars_apply IsModuleTopology.continuousLinearEquiv_symm_apply SemialgHom.restrictScalars_toFun SemialgHom.mk.sizeOf_spec SemialgHom.mk.injEq SemialgHom.coe_coe coe_mk TensorProduct.RightActions.smul_def TensorProduct.RightActions.Module.TensorProduct.comm_symm_apply_tmul TensorProduct.RightActions.LinearMap.baseChange_id TensorProduct.RightActions.algebraMap_eval TensorProduct.RightActions.Module.TensorProduct.comm_apply_tmul TensorProduct.RightActions.Algebra.TensorProduct.comm_symm_apply_tmul TensorProduct.RightActions.Algebra.TensorProduct.comm_apply_tmul LanglandsTunnell.CubicInduction.translateRepStep_apply_coe LanglandsTunnell.CubicInduction.translateFn_apply"

set_option autoImplicit false

section Part2

set_option autoImplicit false

open IsDedekindDomain NumberField MeasureTheory
open scoped NNReal ENNReal Pointwise

namespace LanglandsTunnell
p2m_export "LanglandsTunnell" "TateLocal.localBorel TateLocal.borelSpace_localBorel TateLocal.integersPositiveCompacts TateLocal.coe_integersPositiveCompacts"
namespace TateLocal
p2m_export "LanglandsTunnell.TateLocal" "addCharLevel addCharLevel_def localBorel borelSpace_localBorel integersPositiveCompacts coe_integersPositiveCompacts selfDualHaarAt higherUnitsAt mem_higherUnitsAt_iff HasConductorExponentAt modulus modulus_of_ne_zero modulus_pos modulus_ne_zero modulus_mul charExt charExt_of_ne_zero charExt_coe_units mulMeasure modulus_adicCompletion_eq_nnnorm addCharLevel_psiLocal_rat psiLocal_ne_one exists_hasConductorExponentAt_of_continuous"
p2m_open "LanglandsTunnell.TateLocal LanglandsTunnell"

variable (K : Type) [Field K] [NumberField K] (v : HeightOneSpectrum (𝓞 K))

section Scaling

private theorem modulus_coe_units_eq (u : (v.adicCompletion K)ˣ) :
    modulus (u : v.adicCompletion K) = distribHaarChar (v.adicCompletion K) u := by
  rw [modulus_of_ne_zero u.ne_zero, Units.mk0_val]

private theorem charExt_mul (χ : (v.adicCompletion K)ˣ →* ℂˣ) (a b : v.adicCompletion K) :
    charExt χ (a * b) = charExt χ a * charExt χ b := by
  by_cases ha : a = 0
  · simp [ha]
  by_cases hb : b = 0
  · simp [hb]
  rw [charExt_of_ne_zero χ (mul_ne_zero ha hb), charExt_of_ne_zero χ ha, charExt_of_ne_zero χ hb,
    ← Units.val_mul, ← map_mul]
  congr 2
  exact Units.ext (by simp)

private theorem selfDualHaarAt_smul_set (u : (v.adicCompletion K)ˣ) (S : Set (v.adicCompletion K)) :
    letI := localBorel K v
    selfDualHaarAt K v (u • S) = (modulus (u : v.adicCompletion K) : ℝ≥0∞) * selfDualHaarAt K v S := by
  letI := localBorel K v
  haveI : BorelSpace (v.adicCompletion K) := borelSpace_localBorel K v
  rw [modulus_coe_units_eq]
  unfold selfDualHaarAt
  simp only [Measure.smul_apply]
  rw [← distribHaarChar_mul (Measure.addHaarMeasure (integersPositiveCompacts K v)) u S]
  exact (mul_smul_comm _ _ _).symm

private theorem map_mul_left_selfDualHaarAt (u : (v.adicCompletion K)ˣ) :
    letI := localBorel K v
    Measure.map (fun x : v.adicCompletion K => (u : v.adicCompletion K) * x) (selfDualHaarAt K v) =
      (modulus (u : v.adicCompletion K) : ℝ≥0∞)⁻¹ • selfDualHaarAt K v := by
  letI := localBorel K v
  haveI : BorelSpace (v.adicCompletion K) := borelSpace_localBorel K v
  have hmul : Measurable fun x : v.adicCompletion K => (u : v.adicCompletion K) * x := measurable_id.const_mul _
  ext S hS
  rw [Measure.map_apply hmul hS, Measure.smul_apply, smul_eq_mul]
  have hpre : (fun x : v.adicCompletion K => (u : v.adicCompletion K) * x) ⁻¹' S = u⁻¹ • S :=
    Set.preimage_smul u S
  rw [hpre, selfDualHaarAt_smul_set, modulus_coe_units_eq, modulus_coe_units_eq, map_inv,
    ENNReal.coe_inv (distribHaarChar_pos (A := v.adicCompletion K) (g := u)).ne']

private theorem lintegral_mul_left_selfDualHaarAt (u : (v.adicCompletion K)ˣ) (g : v.adicCompletion K → ℝ≥0∞) :
    letI := localBorel K v
    ∫⁻ x, g ((u : v.adicCompletion K) * x) ∂(selfDualHaarAt K v) =
      (modulus (u : v.adicCompletion K) : ℝ≥0∞)⁻¹ * ∫⁻ x, g x ∂(selfDualHaarAt K v) := by
  letI := localBorel K v
  haveI : BorelSpace (v.adicCompletion K) := borelSpace_localBorel K v
  rw [← (measurableEmbedding_mulLeft₀ u.ne_zero).lintegral_map g, map_mul_left_selfDualHaarAt]
  simp only [lintegral_smul_measure, smul_eq_mul]

private theorem map_mul_left_mulMeasure (u : (v.adicCompletion K)ˣ) :
    letI := localBorel K v
    Measure.map (fun x : v.adicCompletion K => (u : v.adicCompletion K) * x) (mulMeasure (selfDualHaarAt K v)) =
      mulMeasure (selfDualHaarAt K v) := by
  letI := localBorel K v
  haveI : BorelSpace (v.adicCompletion K) := borelSpace_localBorel K v
  have hc : MeasurableSet ({0}ᶜ : Set (v.adicCompletion K)) := isClosed_singleton.measurableSet.compl
  have hmul : Measurable fun x : v.adicCompletion K => (u : v.adicCompletion K) * x := measurable_id.const_mul _
  ext S hS
  rw [Measure.map_apply hmul hS]
  unfold mulMeasure
  rw [withDensity_apply _ (hmul hS), withDensity_apply _ hS, Measure.restrict_restrict (hmul hS),
    Measure.restrict_restrict hS, ← lintegral_indicator (hmul hS |>.inter hc), ← lintegral_indicator (hS.inter hc)]
  have hpt : ∀ x : v.adicCompletion K,
      ((fun y => (u : v.adicCompletion K) * y) ⁻¹' S ∩ {0}ᶜ).indicator (fun y => ((modulus y : ℝ≥0∞))⁻¹) x =
        (modulus (u : v.adicCompletion K) : ℝ≥0∞) *
          (S ∩ {0}ᶜ).indicator (fun y => ((modulus y : ℝ≥0∞))⁻¹) ((u : v.adicCompletion K) * x) := by
    intro x
    by_cases hx : (u : v.adicCompletion K) * x ∈ S ∩ {0}ᶜ
    · have hx' : x ∈ (fun y => (u : v.adicCompletion K) * y) ⁻¹' S ∩ {0}ᶜ := by
        refine ⟨hx.1, ?_⟩
        intro h0
        exact hx.2 (by simp [Set.mem_singleton_iff.mp h0])
      rw [Set.indicator_of_mem hx', Set.indicator_of_mem hx, modulus_mul, ENNReal.coe_mul,
        ENNReal.mul_inv (Or.inl (ENNReal.coe_ne_zero.mpr (modulus_ne_zero u.ne_zero))) (Or.inl ENNReal.coe_ne_top),
        ← mul_assoc, ENNReal.mul_inv_cancel (ENNReal.coe_ne_zero.mpr (modulus_ne_zero u.ne_zero)) ENNReal.coe_ne_top,
        one_mul]
    · have hx' : x ∉ (fun y => (u : v.adicCompletion K) * y) ⁻¹' S ∩ {0}ᶜ := by
        intro h
        refine hx ⟨h.1, ?_⟩
        intro h0
        exact h.2 (by simp [mul_eq_zero, u.ne_zero] at h0; simp [h0])
      rw [Set.indicator_of_notMem hx', Set.indicator_of_notMem hx, mul_zero]
  simp only [hpt]
  rw [lintegral_const_mul' _ _ ENNReal.coe_ne_top, lintegral_mul_left_selfDualHaarAt,
    ← mul_assoc, ENNReal.mul_inv_cancel (ENNReal.coe_ne_zero.mpr (modulus_ne_zero u.ne_zero)) ENNReal.coe_ne_top,
    one_mul]

end Scaling

section MeasureClasses

private theorem selfDualConst_ne_zero :
    ((Ideal.absNorm v.asIdeal : ℝ≥0) ^ (-(addCharLevel (StandardAddChar.psiLocal K v) : ℝ) / 2)) ≠ 0 := by
  have hq : (0 : ℝ≥0) < (Ideal.absNorm v.asIdeal : ℝ≥0) := by
    have h : Ideal.absNorm v.asIdeal ≠ 0 := by
      rw [Ne, Ideal.absNorm_eq_zero_iff]
      exact v.ne_bot
    exact_mod_cast Nat.pos_of_ne_zero h
  exact (NNReal.rpow_pos hq).ne'

private theorem isAddHaarMeasure_selfDualHaarAt :
    letI := localBorel K v
    (selfDualHaarAt K v).IsAddHaarMeasure := by
  letI := localBorel K v
  haveI : BorelSpace (v.adicCompletion K) := borelSpace_localBorel K v
  unfold selfDualHaarAt
  exact Measure.IsAddHaarMeasure.nnreal_smul (Measure.addHaarMeasure (integersPositiveCompacts K v))
    (selfDualConst_ne_zero K v)

private theorem sFinite_selfDualHaarAt :
    letI := localBorel K v
    SFinite (selfDualHaarAt K v) := by
  letI := localBorel K v
  haveI : BorelSpace (v.adicCompletion K) := borelSpace_localBorel K v
  unfold selfDualHaarAt
  infer_instance

private theorem sFinite_mulMeasure_selfDualHaarAt :
    letI := localBorel K v
    SFinite (mulMeasure (selfDualHaarAt K v)) := by
  letI := localBorel K v
  haveI := sFinite_selfDualHaarAt K v
  unfold mulMeasure
  infer_instance

end MeasureClasses

end LanglandsTunnell.TateLocal
end Part2

section Part1

set_option autoImplicit false

open NumberField NumberField.AdelicLevel IsDedekindDomain MeasureTheory
p2m_open "LanglandsTunnell.TateLocal P2MW.S_LanglandsTunnell_CubicInduction_tendsto_setIntegral_annulus_setIntegral_ball_jacquetWindow_sub_jacquetValue.LanglandsTunnell.TateLocal"
open scoped NNReal ENNReal

open Polynomial in
private def IsLaurentInQPow (q : ℂ) (P : ℂ → ℂ) : Prop :=
  ∃ (Q : Polynomial ℂ) (m : ℕ), ∀ s : ℂ, P s = Q.eval (q ^ (-s)) * q ^ ((m : ℂ) * s)

namespace IsLaurentInQPow

variable {q : ℂ}

private theorem const (q c : ℂ) : IsLaurentInQPow q fun _ => c :=
  ⟨Polynomial.C c, 0, fun s => by simp⟩

private theorem mul (hq : q ≠ 0) {P₁ P₂ : ℂ → ℂ} (h₁ : IsLaurentInQPow q P₁) (h₂ : IsLaurentInQPow q P₂) :
    IsLaurentInQPow q fun s => P₁ s * P₂ s := by
  obtain ⟨Q₁, m₁, e₁⟩ := h₁
  obtain ⟨Q₂, m₂, e₂⟩ := h₂
  refine ⟨Q₁ * Q₂, m₁ + m₂, fun s => ?_⟩
  show P₁ s * P₂ s = _
  rw [e₁ s, e₂ s, Polynomial.eval_mul, Nat.cast_add, add_mul, Complex.cpow_add _ _ hq]
  ring

private theorem qpow_add_nat_mul_mul_pow (hq : q ≠ 0) (m k : ℕ) (s : ℂ) :
    q ^ (((m + k : ℕ) : ℂ) * s) * (q ^ (-s)) ^ k = q ^ ((m : ℂ) * s) := by
  rw [← Complex.cpow_nat_mul, ← Complex.cpow_add _ _ hq]
  congr 1
  push_cast
  ring

private theorem add (hq : q ≠ 0) {P₁ P₂ : ℂ → ℂ} (h₁ : IsLaurentInQPow q P₁) (h₂ : IsLaurentInQPow q P₂) :
    IsLaurentInQPow q fun s => P₁ s + P₂ s := by
  obtain ⟨Q₁, m₁, e₁⟩ := h₁
  obtain ⟨Q₂, m₂, e₂⟩ := h₂
  refine ⟨Q₁ * Polynomial.X ^ m₂ + Q₂ * Polynomial.X ^ m₁, m₁ + m₂, fun s => ?_⟩
  show P₁ s + P₂ s = _
  rw [e₁ s, e₂ s, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_mul, Polynomial.eval_pow,
    Polynomial.eval_pow, Polynomial.eval_X, add_mul]
  have h₁' := qpow_add_nat_mul_mul_pow hq m₁ m₂ s
  have h₂' := qpow_add_nat_mul_mul_pow hq m₂ m₁ s
  rw [add_comm m₂ m₁] at h₂'
  rw [← h₁', ← h₂']
  ring

end IsLaurentInQPow

namespace LaurentZetaSlot

variable (v : HeightOneSpectrum (𝓞 ℚ))

attribute [local instance] LanglandsTunnell.TateLocal.localBorel
attribute [local instance] LanglandsTunnell.TateLocal.borelSpace_localBorel

private theorem one_lt_absNorm_real : (1 : ℝ) < (Ideal.absNorm v.asIdeal : ℝ) := by
  exact_mod_cast NumberField.HeightOneSpectrum.one_lt_absNorm (v := v)

private theorem _root_.LaurentZetaSlot.absNorm_ne_zero : (Ideal.absNorm v.asIdeal : ℕ) ≠ 0 := by
  intro h0
  have h := one_lt_absNorm_real v
  rw [h0] at h
  norm_num at h

p2m_export "LaurentZetaSlot" "absNorm_ne_zero"
private def shell (j : ℤ) : Set (v.adicCompletion ℚ) := {x | Valued.v x = WithZero.exp (-j)}

private theorem modulus_eq_of_mem_shell {j : ℤ} {x : v.adicCompletion ℚ} (hx : x ∈ shell v j) :
    modulus x = (Ideal.absNorm v.asIdeal : ℝ≥0) ^ (-j) := by
  have hnorm : ‖x‖ = ((WithZeroMulInt.toNNReal (HeightOneSpectrum.absNorm_ne_zero v) (Valued.v x) : ℝ≥0) : ℝ) :=
    FinitePlace.norm_def v x
  have hx' : Valued.v x = WithZero.exp (-j) := hx
  rw [modulus_adicCompletion_eq_nnnorm ℚ v x]
  apply NNReal.coe_injective
  rw [coe_nnnorm, hnorm, hx', WithZeroMulInt.toNNReal_neg_apply _ WithZero.exp_ne_zero]
  have htoAdd : ∀ h : WithZero.exp (-j) ≠ (0 : WithZero (Multiplicative ℤ)),
      Multiplicative.toAdd (WithZero.unzero h) = -j := fun _ => rfl
  rw [htoAdd]

private def unitShell : Set (v.adicCompletion ℚ) := {x | Valued.v x = 1}

private theorem isAddHaarMeasure_selfDualHaarAt' : (selfDualHaarAt ℚ v).IsAddHaarMeasure := by
  exact LanglandsTunnell.TateLocal.isAddHaarMeasure_selfDualHaarAt ℚ v

private theorem sFinite_mulMeasure_selfDualHaarAt' : SFinite (mulMeasure (selfDualHaarAt ℚ v)) := by
  exact LanglandsTunnell.TateLocal.sFinite_mulMeasure_selfDualHaarAt ℚ v

attribute [local instance] sFinite_mulMeasure_selfDualHaarAt'

private theorem continuousOn_charExt_compl (χ : (v.adicCompletion ℚ)ˣ →* ℂˣ) (hχ : IsLocallyConstant χ) :
    ContinuousOn (charExt χ) ({0}ᶜ : Set (v.adicCompletion ℚ)) := by
  rw [continuousOn_iff_continuous_restrict]
  have hmk : Continuous fun x : ({0}ᶜ : Set (v.adicCompletion ℚ)) => Units.mk0 (x : v.adicCompletion ℚ) x.2 :=
    Units.isEmbedding_val₀.continuous_iff.mpr continuous_subtype_val
  have hlc : IsLocallyConstant fun x : ({0}ᶜ : Set (v.adicCompletion ℚ)) =>
      ((χ (Units.mk0 (x : v.adicCompletion ℚ) x.2) : ℂˣ) : ℂ) :=
    IsLocallyConstant.comp (IsLocallyConstant.comp_continuous hχ hmk) fun u : ℂˣ => (u : ℂ)
  refine (IsLocallyConstant.continuous hlc).congr fun x => ?_
  simp only [Set.restrict_apply, charExt_of_ne_zero χ x.2]

private theorem map_mul_left_mulMeasure' (u : (v.adicCompletion ℚ)ˣ) :
    Measure.map (fun x : v.adicCompletion ℚ => (u : v.adicCompletion ℚ) * x) (mulMeasure (selfDualHaarAt ℚ v)) =
      mulMeasure (selfDualHaarAt ℚ v) := by
  exact LanglandsTunnell.TateLocal.map_mul_left_mulMeasure ℚ v u

private theorem measurable_modulus : Measurable fun x : v.adicCompletion ℚ => (modulus x : ℝ) := by
  have h : (fun x : v.adicCompletion ℚ => (modulus x : ℝ)) = fun x => ‖x‖ := by
    funext x
    rw [modulus_adicCompletion_eq_nnnorm ℚ v x, coe_nnnorm]
  rw [h]
  exact measurable_norm

private theorem measurable_modulus_cpow (s : ℂ) :
    Measurable fun x : v.adicCompletion ℚ => ((modulus x : ℝ) : ℂ) ^ s :=
  (Complex.measurable_ofReal.comp (measurable_modulus v)).pow_const s

private theorem measurable_charExt (χ : (v.adicCompletion ℚ)ˣ →* ℂˣ) (hχ : IsLocallyConstant χ) :
    Measurable (charExt χ) :=
  measurable_of_continuousOn_compl_singleton (0 : v.adicCompletion ℚ) (continuousOn_charExt_compl v χ hχ)

private theorem isClopen_shell (j : ℤ) : IsClopen (shell v j) := by
  obtain ⟨x₀, hx₀⟩ := HeightOneSpectrum.valuedAdicCompletion_surjective ℚ v (WithZero.exp (-j))
  have hset : shell v j = {x | Valued.v.restrict x = Valued.v.restrict x₀} := by
    ext x
    simp only [shell, Set.mem_setOf_eq, Valuation.restrict_inj, hx₀]
  have hne : Valued.v.restrict x₀ ≠ 0 := by
    intro h0
    have h1 : Valued.v x₀ = Valued.v (0 : v.adicCompletion ℚ) :=
      (Valuation.restrict_inj Valued.v).mp (by rw [h0, map_zero])
    rw [map_zero, hx₀] at h1
    exact WithZero.exp_ne_zero h1
  rw [hset]
  exact Valued.isClopen_sphere _ hne

private theorem unitShell_eq_shell_zero : unitShell v = shell v 0 := by
  simp only [unitShell, shell, neg_zero, WithZero.exp_zero]

private theorem modulus_eq_one_of_mem_unitShell {x : v.adicCompletion ℚ} (hx : x ∈ unitShell v) : modulus x = 1 := by
  rw [unitShell_eq_shell_zero] at hx
  rw [modulus_eq_of_mem_shell v hx, neg_zero, zpow_zero]

private theorem isClopen_unitShell : IsClopen (unitShell v) := by
  rw [unitShell_eq_shell_zero]
  exact isClopen_shell v 0

private theorem measurableSet_shell (j : ℤ) : MeasurableSet (shell v j) :=
  (isClopen_shell v j).isOpen.measurableSet

private theorem measurableSet_unitShell : MeasurableSet (unitShell v) :=
  (isClopen_unitShell v).isOpen.measurableSet

private theorem unitShell_subset_integers : unitShell v ⊆ (v.adicCompletionIntegers ℚ : Set (v.adicCompletion ℚ)) :=
  fun x hx => by
    rw [SetLike.mem_coe, HeightOneSpectrum.mem_adicCompletionIntegers]
    exact le_of_eq hx

private theorem isCompact_unitShell : IsCompact (unitShell v) := by
  have hO : IsCompact (v.adicCompletionIntegers ℚ : Set (v.adicCompletion ℚ)) := by
    rw [← coe_integersPositiveCompacts ℚ v]
    exact (integersPositiveCompacts ℚ v).isCompact
  exact hO.of_isClosed_subset (isClopen_unitShell v).isClosed (unitShell_subset_integers v)

private theorem shell_subset_compl_zero (j : ℤ) : shell v j ⊆ ({0}ᶜ : Set (v.adicCompletion ℚ)) := by
  intro x hx
  have hx' : Valued.v x = WithZero.exp (-j) := hx
  intro h0
  rw [Set.mem_singleton_iff.mp h0, map_zero] at hx'
  exact WithZero.exp_ne_zero hx'.symm

private theorem valued_uniformizerUnit_zpow (j : ℤ) :
    Valued.v ((uniformizerUnit ℚ v ^ j : (v.adicCompletion ℚ)ˣ) : v.adicCompletion ℚ) = WithZero.exp (-j) := by
  rw [Units.val_zpow_eq_zpow_val, map_zpow₀, valued_uniformizerUnit, ← WithZero.exp_zsmul]
  congr 1
  simp

private theorem image_unitShell_eq_shell (j : ℤ) :
    (fun x : v.adicCompletion ℚ => ((uniformizerUnit ℚ v ^ j : (v.adicCompletion ℚ)ˣ) : v.adicCompletion ℚ) * x) ''
      unitShell v = shell v j := by
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩
    have hx' : Valued.v x = 1 := hx
    show Valued.v _ = WithZero.exp (-j)
    rw [map_mul, valued_uniformizerUnit_zpow, hx', mul_one]
  · intro hy
    have hy' : Valued.v y = WithZero.exp (-j) := hy
    refine ⟨((uniformizerUnit ℚ v ^ j : (v.adicCompletion ℚ)ˣ)⁻¹ : (v.adicCompletion ℚ)ˣ) * y, ?_, ?_⟩
    · show Valued.v _ = 1
      rw [map_mul, Units.val_inv_eq_inv_val, map_inv₀, valued_uniformizerUnit_zpow, hy']
      exact inv_mul_cancel₀ WithZero.exp_ne_zero
    · exact Units.mul_inv_cancel_left _ _

private theorem isCompact_shell (j : ℤ) : IsCompact (shell v j) := by
  rw [← image_unitShell_eq_shell]
  exact (isCompact_unitShell v).image (continuous_const.mul continuous_id)

private theorem
    mulMeasure_unitShell : mulMeasure (selfDualHaarAt ℚ v) (unitShell v) = selfDualHaarAt ℚ v (unitShell v) := by
  rw [mulMeasure, withDensity_apply _ (measurableSet_unitShell v),
    Measure.restrict_restrict (measurableSet_unitShell v)]
  have hsub : unitShell v ∩ {(0 : v.adicCompletion ℚ)}ᶜ = unitShell v := by
    refine Set.inter_eq_left.mpr fun x hx => ?_
    rintro rfl
    simp [unitShell] at hx
  rw [hsub]
  calc ∫⁻ x in unitShell v, ((modulus x : ℝ≥0∞))⁻¹ ∂(selfDualHaarAt ℚ v)
      = ∫⁻ _ in unitShell v, (1 : ℝ≥0∞) ∂(selfDualHaarAt ℚ v) := by
        refine setLIntegral_congr_fun (measurableSet_unitShell v) fun x hx => ?_
        rw [modulus_eq_one_of_mem_unitShell v hx]
        simp
    _ = selfDualHaarAt ℚ v (unitShell v) := by simp

private theorem mulMeasure_unitShell_lt_top : mulMeasure (selfDualHaarAt ℚ v) (unitShell v) < ⊤ := by
  haveI := isAddHaarMeasure_selfDualHaarAt' v
  rw [mulMeasure_unitShell]
  exact (isCompact_unitShell v).measure_lt_top

private theorem mulMeasure_shell (j : ℤ) :
    mulMeasure (selfDualHaarAt ℚ v) (shell v j) = mulMeasure (selfDualHaarAt ℚ v) (unitShell v) := by
  set u : (v.adicCompletion ℚ)ˣ := uniformizerUnit ℚ v ^ j with hu
  have hvu : Valued.v (u : v.adicCompletion ℚ) = WithZero.exp (-j) := valued_uniformizerUnit_zpow v j
  have hpre : (fun x : v.adicCompletion ℚ => (u : v.adicCompletion ℚ) * x) ⁻¹' shell v j = unitShell v := by
    ext x
    simp only [Set.mem_preimage, shell, unitShell, Set.mem_setOf_eq, map_mul, hvu]
    exact mul_eq_left₀ WithZero.exp_ne_zero
  conv_lhs => rw [← map_mul_left_mulMeasure' v u]
  rw [Measure.map_apply (measurable_const_mul _) (measurableSet_shell v j), hpre]

private theorem mulMeasure_shell_lt_top (j : ℤ) : mulMeasure (selfDualHaarAt ℚ v) (shell v j) < ⊤ := by
  rw [mulMeasure_shell]
  exact mulMeasure_unitShell_lt_top v

private scoped instance isFiniteMeasure_restrict_unitShell :
    IsFiniteMeasure ((mulMeasure (selfDualHaarAt ℚ v)).restrict (unitShell v)) :=
  ⟨by rw [Measure.restrict_apply_univ]; exact mulMeasure_unitShell_lt_top v⟩

private theorem charExt_mul' (χ : (v.adicCompletion ℚ)ˣ →* ℂˣ) (a b : v.adicCompletion ℚ) :
    charExt χ (a * b) = charExt χ a * charExt χ b := by
  exact LanglandsTunnell.TateLocal.charExt_mul ℚ v χ a b

private theorem measurable_of_eventually_eq {f : v.adicCompletion ℚ → ℂ}
    (hf : ∀ t : v.adicCompletion ℚ, t ≠ 0 → ∀ᶠ t' in nhds t, f t' = f t) : Measurable f :=
  measurable_of_continuousOn_compl_singleton (0 : v.adicCompletion ℚ) fun t ht =>
    (Filter.EventuallyEq.continuousAt (hf t ht)).continuousWithinAt

private theorem eventually_charExt_eq (χ : (v.adicCompletion ℚ)ˣ →* ℂˣ) (hχ : IsLocallyConstant χ)
    {x : v.adicCompletion ℚ} (hx : x ≠ 0) : ∀ᶠ y in nhds x, charExt χ y = charExt χ x := by
  have hmk : Continuous fun z : ({0}ᶜ : Set (v.adicCompletion ℚ)) => Units.mk0 (z : v.adicCompletion ℚ) z.2 :=
    Units.isEmbedding_val₀.continuous_iff.mpr continuous_subtype_val
  have hlc : IsLocallyConstant fun z : ({0}ᶜ : Set (v.adicCompletion ℚ)) => charExt χ (z : v.adicCompletion ℚ) := by
    have heq : (fun z : ({0}ᶜ : Set (v.adicCompletion ℚ)) => charExt χ (z : v.adicCompletion ℚ)) =
        (fun u : ℂˣ => (u : ℂ)) ∘
          fun z : ({0}ᶜ : Set (v.adicCompletion ℚ)) => χ (Units.mk0 (z : v.adicCompletion ℚ) z.2) := by
      funext z
      simp only [Function.comp, charExt_of_ne_zero χ z.2]
    rw [heq]
    exact IsLocallyConstant.comp (IsLocallyConstant.comp_continuous hχ hmk) fun u : ℂˣ => (u : ℂ)
  have hx' : x ∈ ({0}ᶜ : Set (v.adicCompletion ℚ)) := hx
  have hfib : IsOpen {z : ({0}ᶜ : Set (v.adicCompletion ℚ)) | charExt χ (z : v.adicCompletion ℚ) = charExt χ x} :=
    hlc.isOpen_fiber (charExt χ x)
  have himg : IsOpen (Subtype.val '' {z : ({0}ᶜ : Set (v.adicCompletion ℚ)) |
      charExt χ (z : v.adicCompletion ℚ) = charExt χ x}) :=
    isOpen_compl_singleton.isOpenMap_subtype_val _ hfib
  have hmem : x ∈ Subtype.val '' {z : ({0}ᶜ : Set (v.adicCompletion ℚ)) |
      charExt χ (z : v.adicCompletion ℚ) = charExt χ x} := ⟨⟨x, hx'⟩, rfl, rfl⟩
  filter_upwards [himg.mem_nhds hmem] with y hy
  obtain ⟨z, hz, rfl⟩ := hy
  exact hz

private theorem exists_mem_shell {x : v.adicCompletion ℚ} (hx : x ≠ 0) : ∃ j : ℤ, x ∈ shell v j := by
  have hv : Valued.v x ≠ 0 := (Valuation.ne_zero_iff _).mpr hx
  refine ⟨-WithZero.log (Valued.v x), ?_⟩
  show Valued.v x = WithZero.exp (- -WithZero.log (Valued.v x))
  rw [neg_neg, WithZero.exp_log hv]

private theorem coe_modulus_eq_of_mem_shell {j : ℤ} {x : v.adicCompletion ℚ} (hx : x ∈ shell v j) :
    (modulus x : ℝ) = (Ideal.absNorm v.asIdeal : ℝ) ^ (-j) := by
  rw [modulus_eq_of_mem_shell v hx, NNReal.coe_zpow, NNReal.coe_natCast]

private def ShellBounded (h : v.adicCompletion ℚ → ℂ) : Prop := ∀ j : ℤ, ∃ M : ℝ, ∀ x ∈ shell v j, ‖h x‖ ≤ M

private theorem shellBounded_of_eventually {h : v.adicCompletion ℚ → ℂ}
    (hh : ∀ t : v.adicCompletion ℚ, t ≠ 0 → ∀ᶠ t' in nhds t, h t' = h t) : ShellBounded v h := by
  intro j
  have hcont : ContinuousOn h (shell v j) := fun x hx =>
    (Filter.EventuallyEq.continuousAt (hh x (shell_subset_compl_zero v j hx))).continuousWithinAt
  exact (isCompact_shell v j).exists_bound_of_continuousOn hcont

private def GeomBoundFrom (h : v.adicCompletion ℚ → ℂ) (j₀ : ℤ) (C R : ℝ) : Prop :=
  ∀ j : ℤ, j₀ ≤ j → ∀ x ∈ shell v j, ‖h x‖ ≤ C * R ^ j

private theorem exists_bound_charExt_unitShell (χ : (v.adicCompletion ℚ)ˣ →* ℂˣ) (hχ : IsLocallyConstant χ) :
    ∃ Mχ : ℝ, ∀ u ∈ unitShell v, ‖charExt χ u‖ ≤ Mχ :=
  (isCompact_unitShell v).exists_bound_of_continuousOn ((continuousOn_charExt_compl v χ hχ).mono
    (by rw [unitShell_eq_shell_zero]; exact shell_subset_compl_zero v 0))

private theorem norm_charExt_le_of_mem_shell (χ : (v.adicCompletion ℚ)ˣ →* ℂˣ) {Mχ : ℝ}
    (hMχ : ∀ u ∈ unitShell v, ‖charExt χ u‖ ≤ Mχ) {j : ℤ} {x : v.adicCompletion ℚ} (hx : x ∈ shell v j) :
    ‖charExt χ x‖ ≤ ‖(χ (uniformizerUnit ℚ v) : ℂ)‖ ^ j * Mχ := by
  rw [← image_unitShell_eq_shell] at hx
  obtain ⟨u, hu, rfl⟩ := hx
  rw [charExt_mul', charExt_coe_units, map_zpow, Units.val_zpow_eq_zpow_val, norm_mul, norm_zpow]
  exact mul_le_mul_of_nonneg_left (hMχ u hu) (by positivity)

private theorem norm_modulus_cpow_of_mem_shell {j : ℤ} {x : v.adicCompletion ℚ} (hx : x ∈ shell v j) (s : ℂ) :
    ‖((modulus x : ℝ) : ℂ) ^ s‖ = ((Ideal.absNorm v.asIdeal : ℝ) ^ (-s.re)) ^ j := by
  have hq0 : (0 : ℝ) < (Ideal.absNorm v.asIdeal : ℝ) := zero_lt_one.trans (one_lt_absNorm_real v)
  have hpos : (0 : ℝ) < (modulus x : ℝ) := by
    rw [coe_modulus_eq_of_mem_shell v hx]
    exact zpow_pos hq0 _
  rw [Complex.norm_cpow_eq_rpow_re_of_pos hpos, coe_modulus_eq_of_mem_shell v hx, ← Real.rpow_intCast,
    ← Real.rpow_mul hq0.le, ← Real.rpow_mul_intCast hq0.le]
  congr 1
  push_cast
  ring

private theorem integrableOn_shell_and_integral_norm_le (χ : (v.adicCompletion ℚ)ˣ →* ℂˣ) (hχ : IsLocallyConstant χ)
    {φ : v.adicCompletion ℚ → ℂ} (hφ : ∀ t : v.adicCompletion ℚ, t ≠ 0 → ∀ᶠ t' in nhds t, φ t' = φ t) {Mχ : ℝ}
    (hMχ : ∀ u ∈ unitShell v, ‖charExt χ u‖ ≤ Mχ) (s : ℂ) {j : ℤ} {Mφ : ℝ} (hMφ : ∀ x ∈ shell v j, ‖φ x‖ ≤ Mφ) :
    IntegrableOn (fun x => φ x * charExt χ x * ((modulus x : ℝ) : ℂ) ^ s) (shell v j)
        (mulMeasure (selfDualHaarAt ℚ v)) ∧
      ∫ x in shell v j, ‖φ x * charExt χ x * ((modulus x : ℝ) : ℂ) ^ s‖ ∂(mulMeasure (selfDualHaarAt ℚ v)) ≤
        (mulMeasure (selfDualHaarAt ℚ v)).real (unitShell v) *
          (Mφ * (‖(χ (uniformizerUnit ℚ v) : ℂ)‖ ^ j * Mχ) * ((Ideal.absNorm v.asIdeal : ℝ) ^ (-s.re)) ^ j) := by
  set K : ℝ := Mφ * (‖(χ (uniformizerUnit ℚ v) : ℂ)‖ ^ j * Mχ) * ((Ideal.absNorm v.asIdeal : ℝ) ^ (-s.re)) ^ j
    with hK
  have hpt : ∀ x ∈ shell v j, ‖φ x * charExt χ x * ((modulus x : ℝ) : ℂ) ^ s‖ ≤ K := by
    intro x hx
    rw [norm_mul, norm_mul, norm_modulus_cpow_of_mem_shell v hx s, hK]
    have hqs : (0 : ℝ) ≤ ((Ideal.absNorm v.asIdeal : ℝ) ^ (-s.re)) ^ j := by positivity
    have hMφ0 : 0 ≤ Mφ := (norm_nonneg _).trans (hMφ x hx)
    gcongr
    · exact hMφ x hx
    · exact norm_charExt_le_of_mem_shell v χ hMχ hx
  have hmeas : AEStronglyMeasurable (fun x => φ x * charExt χ x * ((modulus x : ℝ) : ℂ) ^ s)
      (mulMeasure (selfDualHaarAt ℚ v)) :=
    (((measurable_of_eventually_eq v hφ).mul (measurable_charExt v χ hχ)).mul
      (measurable_modulus_cpow v s)).aestronglyMeasurable
  have hint : IntegrableOn (fun x => φ x * charExt χ x * ((modulus x : ℝ) : ℂ) ^ s) (shell v j)
      (mulMeasure (selfDualHaarAt ℚ v)) := by
    refine Measure.integrableOn_of_bounded (mulMeasure_shell_lt_top v j).ne hmeas (M := K) ?_
    exact (ae_restrict_mem (measurableSet_shell v j)).mono hpt
  refine ⟨hint, ?_⟩
  calc ∫ x in shell v j, ‖φ x * charExt χ x * ((modulus x : ℝ) : ℂ) ^ s‖ ∂(mulMeasure (selfDualHaarAt ℚ v))
      ≤ ∫ _ in shell v j, K ∂(mulMeasure (selfDualHaarAt ℚ v)) :=
        setIntegral_mono_on hint.norm (integrableOn_const (mulMeasure_shell_lt_top v j).ne)
          (measurableSet_shell v j) hpt
    _ = (mulMeasure (selfDualHaarAt ℚ v)).real (shell v j) * K := by rw [setIntegral_const, smul_eq_mul]
    _ = (mulMeasure (selfDualHaarAt ℚ v)).real (unitShell v) * K := by
        rw [measureReal_def, measureReal_def, mulMeasure_shell]

private theorem integrable_of_geomBoundFrom (χ : (v.adicCompletion ℚ)ˣ →* ℂˣ) (hχ : IsLocallyConstant χ)
    {φ : v.adicCompletion ℚ → ℂ} (hφ : ∀ t : v.adicCompletion ℚ, t ≠ 0 → ∀ᶠ t' in nhds t, φ t' = φ t)
    (hφB : ∃ B : ℝ, ∀ t : v.adicCompletion ℚ, B < (modulus t : ℝ) → φ t = 0) {j₀ : ℤ} {C R : ℝ} (hR : 0 < R)
    (hgeom : GeomBoundFrom v φ j₀ C R) (s : ℂ)
    (hs : R * ‖(χ (uniformizerUnit ℚ v) : ℂ)‖ * (Ideal.absNorm v.asIdeal : ℝ) ^ (-s.re) < 1) :
    Integrable (fun x => φ x * charExt χ x * ((modulus x : ℝ) : ℂ) ^ s) (mulMeasure (selfDualHaarAt ℚ v)) := by
  classical
  have hq1 : (1 : ℝ) < (Ideal.absNorm v.asIdeal : ℝ) := one_lt_absNorm_real v
  obtain ⟨Mχ, hMχ⟩ := exists_bound_charExt_unitShell v χ hχ
  obtain ⟨B, hB⟩ := hφB
  obtain ⟨k, hk⟩ := pow_unbounded_of_one_lt B hq1
  have hsb : ShellBounded v φ := shellBounded_of_eventually v hφ
  set F : v.adicCompletion ℚ → ℂ := fun x => φ x * charExt χ x * ((modulus x : ℝ) : ℂ) ^ s with hF
  set r : ℝ := R * ‖(χ (uniformizerUnit ℚ v) : ℂ)‖ * (Ideal.absNorm v.asIdeal : ℝ) ^ (-s.re) with hr
  have hr0 : 0 ≤ r := by positivity
  set j₁ : ℤ := max j₀ 0 with hj₁

  have hinner : IntegrableOn F (⋃ n : ℕ, shell v (j₁ + n)) (mulMeasure (selfDualHaarAt ℚ v)) := by
    have hsh : ∀ n : ℕ, IntegrableOn F (shell v (j₁ + n)) (mulMeasure (selfDualHaarAt ℚ v)) ∧
        ∫ x in shell v (j₁ + n), ‖F x‖ ∂(mulMeasure (selfDualHaarAt ℚ v)) ≤
          ((mulMeasure (selfDualHaarAt ℚ v)).real (unitShell v) * (C * Mχ) * r ^ j₁) * r ^ n := by
      intro n
      obtain ⟨h1, h2⟩ := integrableOn_shell_and_integral_norm_le v χ hχ hφ hMχ s
        (hgeom (j₁ + n) (by omega))
      refine ⟨h1, h2.trans (le_of_eq ?_)⟩
      have hχ0 : ‖(χ (uniformizerUnit ℚ v) : ℂ)‖ ≠ 0 := norm_ne_zero_iff.mpr (Units.ne_zero _)
      have hqs0 : (Ideal.absNorm v.asIdeal : ℝ) ^ (-s.re) ≠ 0 := by positivity
      rw [hr, mul_zpow, mul_zpow, zpow_add₀ hR.ne', zpow_add₀ hχ0, zpow_add₀ hqs0, zpow_natCast, zpow_natCast,
        zpow_natCast, mul_pow, mul_pow]
      ring
    refine integrableOn_iUnion_of_summable_integral_norm (fun n => (hsh n).1) ?_
    exact Summable.of_nonneg_of_le (fun n => integral_nonneg fun x => norm_nonneg _) (fun n => (hsh n).2)
      ((summable_geometric_of_lt_one hr0 hs).mul_left _)

  have hmid : IntegrableOn F (⋃ j ∈ Finset.Ico (-(k : ℤ)) j₁, shell v j) (mulMeasure (selfDualHaarAt ℚ v)) := by
    refine integrableOn_finset_iUnion.mpr fun j _ => ?_
    obtain ⟨M, hM⟩ := hsb j
    exact (integrableOn_shell_and_integral_norm_le v χ hχ hφ hMχ s hM).1

  have hsupp : Function.support F ⊆
      (⋃ n : ℕ, shell v (j₁ + n)) ∪ ⋃ j ∈ Finset.Ico (-(k : ℤ)) j₁, shell v j := by
    intro x hx
    have hx0 : x ≠ 0 := by
      rintro rfl
      apply hx
      simp [hF]
    obtain ⟨j, hj⟩ := exists_mem_shell v hx0
    by_cases hjbig : j₁ ≤ j
    · obtain ⟨n, hn⟩ : ∃ n : ℕ, j - j₁ = n := Int.eq_ofNat_of_zero_le (by omega)
      refine Or.inl (Set.mem_iUnion.mpr ⟨n, ?_⟩)
      have : j₁ + n = j := by omega
      rwa [this]
    · by_cases hjk : -(k : ℤ) ≤ j
      · exact Or.inr (Set.mem_iUnion₂.mpr ⟨j, Finset.mem_Ico.mpr ⟨hjk, by omega⟩, hj⟩)
      · exfalso
        apply hx
        have hφ0 : φ x = 0 := by
          apply hB
          rw [coe_modulus_eq_of_mem_shell v hj]
          calc B < (Ideal.absNorm v.asIdeal : ℝ) ^ k := hk
            _ = (Ideal.absNorm v.asIdeal : ℝ) ^ (k : ℤ) := (zpow_natCast _ _).symm
            _ ≤ (Ideal.absNorm v.asIdeal : ℝ) ^ (-j) := zpow_le_zpow_right₀ hq1.le (by omega)
        simp [hF, hφ0]
  exact (integrableOn_iff_integrable_of_support_subset hsupp).mp (hinner.union hmid)

end LaurentZetaSlot
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_tendsto_setIntegral_annulus_setIntegral_ball_jacquetWindow_sub_jacquetValue.LaurentZetaSlot"
end Part1
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_tendsto_setIntegral_annulus_setIntegral_ball_jacquetWindow_sub_jacquetValue.LaurentZetaSlot"

section Part3

set_option autoImplicit false

open Matrix IsDedekindDomain NumberField

namespace LanglandsTunnell
p2m_export "LanglandsTunnell" "TateLocal.localBorel TateLocal.borelSpace_localBorel TateLocal.integersPositiveCompacts TateLocal.coe_integersPositiveCompacts"
namespace CubicInduction
p2m_export "LanglandsTunnell.CubicInduction" "unipotentBall3 mem_unipotentBall3_iff jacquetHaar3 jacquetTruncated3 jacquetLevel jacquetValue jacquetTruncated3_eq_jacquetValue bigCell3 mem_bigCell3_iff cellSectionOf cellSectionOf_apply_of_mem cellSectionOf_apply_of_notMem cellSectionOf_upperUnipotent3_mul cellSectionOf_diagonal3_mul principalSeries3 gl3Entry cornerEntry lowerMinor outerMinor gl3Det gl3Det_ne_zero cellRatio cellValue antidiagonal3 antidiagonal3_coe eventually_valued_eq eventually_valued_lt eventually_norm_eq eventually_charExt_eq continuous_gl3Entry continuous_cornerEntry continuous_lowerMinor continuous_outerMinor continuous_gl3Det exists_bottom_entry_ne_zero_of_cornerEntry_eq_zero outerMinor_ne_zero_of_lowerMinor_eq_zero gl3AmbientRightTranslate gl3AmbientRightTranslate_apply transposeInv3 upperUnipotent3 upperUnipotent3_coe embedMat2 iotaGL coe_iotaGL LocalGL3 diagUnitGL2 coe_diagUnitGL2 lowerUnipotent21 longWeyl3 longWeyl3_coe weylPrime3 weylPrime3_coe transposeInv3_weylPrime3 transposeInv3_lowerUnipotent21 exists_forall_le_integrableOn_and_jacquetTruncated3_eq_of_cellSectionOf exists_forall_gl3AmbientRightTranslate_eq_of_mem_principalSeries3"
p2m_open "LanglandsTunnell.CubicInduction LanglandsTunnell"

section TransposeInverse

variable {A : Type*} [CommRing A]

private theorem transposeInv3_mul (g h : GL (Fin 3) A) :
    transposeInv3 (g * h) = transposeInv3 g * transposeInv3 h := by
  refine Units.ext ?_
  change ((((g * h)⁻¹ : GL (Fin 3) A)) : Matrix (Fin 3) (Fin 3) A)ᵀ =
    (((g⁻¹ : GL (Fin 3) A) : Matrix (Fin 3) (Fin 3) A))ᵀ * (((h⁻¹ : GL (Fin 3) A) : Matrix (Fin 3) (Fin 3) A))ᵀ
  rw [_root_.mul_inv_rev, Units.val_mul, Matrix.transpose_mul]

private theorem transposeInv3_one : transposeInv3 (1 : GL (Fin 3) A) = 1 := by
  refine Units.ext ?_
  change ((((1 : GL (Fin 3) A)⁻¹ : GL (Fin 3) A)) : Matrix (Fin 3) (Fin 3) A)ᵀ = ((1 : GL (Fin 3) A) : Matrix _ _ _)
  rw [inv_one, Units.val_one, Matrix.transpose_one]

private theorem coe_inv_diagUnitGL2 (a : Aˣ) :
    (((diagUnitGL2 a)⁻¹ : GL (Fin 2) A) : Matrix (Fin 2) (Fin 2) A) = !![((a⁻¹ : Aˣ) : A), 0; 0, 1] :=
  rfl

private theorem transposeInv3_iotaGL_diagUnitGL2 (a : Aˣ) :
    transposeInv3 (iotaGL (diagUnitGL2 a)) = iotaGL (diagUnitGL2 a⁻¹) := by
  refine Units.ext ?_
  change ((((iotaGL (diagUnitGL2 a))⁻¹ : GL (Fin 3) A)) : Matrix (Fin 3) (Fin 3) A)ᵀ = _
  rw [← map_inv, coe_iotaGL, coe_iotaGL, coe_inv_diagUnitGL2, coe_diagUnitGL2]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [embedMat2, Matrix.transpose_apply]

private theorem coe_longWeyl3_mul_transposeInv3_mul_longWeyl3 (a : Aˣ) (x : A) :
    ((longWeyl3 * transposeInv3 (iotaGL (diagUnitGL2 a) * lowerUnipotent21 x * (weylPrime3 * transposeInv3 1)) *
          longWeyl3 : GL (Fin 3) A) : Matrix (Fin 3) (Fin 3) A) =
      !![0, 1, 0; 1, 0, 0; -(((a⁻¹ : Aˣ) : A) * x), 0, ((a⁻¹ : Aˣ) : A)] := by
  rw [transposeInv3_one, mul_one, transposeInv3_mul, transposeInv3_mul, transposeInv3_iotaGL_diagUnitGL2,
    transposeInv3_lowerUnipotent21, transposeInv3_weylPrime3]
  simp only [Units.val_mul, coe_iotaGL, coe_diagUnitGL2, longWeyl3_coe, weylPrime3_coe, upperUnipotent3_coe]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [embedMat2, Matrix.mul_apply, Fin.sum_univ_three]

end TransposeInverse
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_tendsto_setIntegral_annulus_setIntegral_ball_jacquetWindow_sub_jacquetValue.LaurentZetaSlot"

section Local

variable (v : HeightOneSpectrum (𝓞 ℚ))

private theorem longWeyl3_eq_antidiagonal3 : (longWeyl3 : LocalGL3 v) = antidiagonal3 v :=
  Units.ext (longWeyl3_coe.trans (antidiagonal3_coe v).symm)

private theorem coe_dualPoint_mul_antidiagonal3 (a : (v.adicCompletion ℚ)ˣ) (x : v.adicCompletion ℚ) :
    ((longWeyl3 * transposeInv3 (iotaGL (diagUnitGL2 a) * lowerUnipotent21 x * (weylPrime3 * transposeInv3 1)) *
          antidiagonal3 v : LocalGL3 v) : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)) =
      !![0, 1, 0; 1, 0, 0; -(((a⁻¹ : (v.adicCompletion ℚ)ˣ) : v.adicCompletion ℚ) * x), 0,
        ((a⁻¹ : (v.adicCompletion ℚ)ˣ) : v.adicCompletion ℚ)] := by
  rw [← longWeyl3_eq_antidiagonal3]
  exact coe_longWeyl3_mul_transposeInv3_mul_longWeyl3 a x

end Local
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_tendsto_setIntegral_annulus_setIntegral_ball_jacquetWindow_sub_jacquetValue.LaurentZetaSlot"

end LanglandsTunnell.CubicInduction
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_tendsto_setIntegral_annulus_setIntegral_ball_jacquetWindow_sub_jacquetValue.LaurentZetaSlot"
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_tendsto_setIntegral_annulus_setIntegral_ball_jacquetWindow_sub_jacquetValue.LaurentZetaSlot"
end Part3
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_tendsto_setIntegral_annulus_setIntegral_ball_jacquetWindow_sub_jacquetValue.LaurentZetaSlot"

section Part4

set_option autoImplicit false

p2m_open "Matrix IsDedekindDomain NumberField LanglandsTunnell.TateLocal P2MW.S_LanglandsTunnell_CubicInduction_tendsto_setIntegral_annulus_setIntegral_ball_jacquetWindow_sub_jacquetValue.LanglandsTunnell.TateLocal"

namespace LanglandsTunnell
p2m_export "LanglandsTunnell" "TateLocal.localBorel TateLocal.borelSpace_localBorel TateLocal.integersPositiveCompacts TateLocal.coe_integersPositiveCompacts"
namespace CubicInduction
p2m_export "LanglandsTunnell.CubicInduction" "unipotentBall3 mem_unipotentBall3_iff jacquetHaar3 jacquetTruncated3 jacquetLevel jacquetValue jacquetTruncated3_eq_jacquetValue bigCell3 mem_bigCell3_iff cellSectionOf cellSectionOf_apply_of_mem cellSectionOf_apply_of_notMem cellSectionOf_upperUnipotent3_mul cellSectionOf_diagonal3_mul principalSeries3 gl3Entry cornerEntry lowerMinor outerMinor gl3Det gl3Det_ne_zero cellRatio cellValue antidiagonal3 antidiagonal3_coe eventually_valued_eq eventually_valued_lt eventually_norm_eq eventually_charExt_eq continuous_gl3Entry continuous_cornerEntry continuous_lowerMinor continuous_outerMinor continuous_gl3Det exists_bottom_entry_ne_zero_of_cornerEntry_eq_zero outerMinor_ne_zero_of_lowerMinor_eq_zero gl3AmbientRightTranslate gl3AmbientRightTranslate_apply transposeInv3 upperUnipotent3 upperUnipotent3_coe embedMat2 iotaGL coe_iotaGL LocalGL3 diagUnitGL2 coe_diagUnitGL2 lowerUnipotent21 longWeyl3 longWeyl3_coe weylPrime3 weylPrime3_coe transposeInv3_weylPrime3 transposeInv3_lowerUnipotent21 exists_forall_le_integrableOn_and_jacquetTruncated3_eq_of_cellSectionOf exists_forall_gl3AmbientRightTranslate_eq_of_mem_principalSeries3"
p2m_open "LanglandsTunnell.CubicInduction LanglandsTunnell"

variable (v : HeightOneSpectrum (𝓞 ℚ))

section DualPoint

private noncomputable def
    dualCellPoint (α β γ : v.adicCompletion ℚ) (a : (v.adicCompletion ℚ)ˣ) (x : v.adicCompletion ℚ) :
    LocalGL3 v :=
  antidiagonal3 v * upperUnipotent3 α β γ *
    (longWeyl3 * transposeInv3 (iotaGL (diagUnitGL2 a) * lowerUnipotent21 x * (weylPrime3 * transposeInv3 1)) *
      antidiagonal3 v)

private theorem dualCellPoint_coe (α β γ : v.adicCompletion ℚ) (a : (v.adicCompletion ℚ)ˣ) (x : v.adicCompletion ℚ) :
    (dualCellPoint v α β γ a x : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)) =
      !![-(x * (a : v.adicCompletion ℚ)⁻¹), 0, (a : v.adicCompletion ℚ)⁻¹;
        1 - β * (x * (a : v.adicCompletion ℚ)⁻¹), 0, β * (a : v.adicCompletion ℚ)⁻¹;
        α - γ * (x * (a : v.adicCompletion ℚ)⁻¹), 1, γ * (a : v.adicCompletion ℚ)⁻¹] := by
  rw [dualCellPoint, Units.val_mul, coe_dualPoint_mul_antidiagonal3, Units.val_mul, antidiagonal3_coe,
    upperUnipotent3_coe]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_three] <;> ring

private theorem
    gl3Entry_dualCellPoint (α β γ : v.adicCompletion ℚ) (a : (v.adicCompletion ℚ)ˣ) (x : v.adicCompletion ℚ)
    (i j : Fin 3) :
    gl3Entry v (dualCellPoint v α β γ a x) i j =
      !![-(x * (a : v.adicCompletion ℚ)⁻¹), 0, (a : v.adicCompletion ℚ)⁻¹;
        1 - β * (x * (a : v.adicCompletion ℚ)⁻¹), 0, β * (a : v.adicCompletion ℚ)⁻¹;
        α - γ * (x * (a : v.adicCompletion ℚ)⁻¹), 1, γ * (a : v.adicCompletion ℚ)⁻¹] i j := by
  rw [gl3Entry, dualCellPoint_coe]

private theorem cornerEntry_dualCellPoint (α β γ : v.adicCompletion ℚ) (a : (v.adicCompletion ℚ)ˣ)
    (x : v.adicCompletion ℚ) :
    cornerEntry v (dualCellPoint v α β γ a x) = α - γ * x / a := by
  simp only [cornerEntry, gl3Entry_dualCellPoint]
  simp
  ring

private theorem lowerMinor_dualCellPoint (α β γ : v.adicCompletion ℚ) (a : (v.adicCompletion ℚ)ˣ)
    (x : v.adicCompletion ℚ) :
    lowerMinor v (dualCellPoint v α β γ a x) = 1 - β * x / a := by
  simp only [lowerMinor, gl3Entry_dualCellPoint]
  simp
  ring

private theorem outerMinor_dualCellPoint (α β γ : v.adicCompletion ℚ) (a : (v.adicCompletion ℚ)ˣ)
    (x : v.adicCompletion ℚ) :
    outerMinor v (dualCellPoint v α β γ a x) = (γ - α * β) / a := by
  simp only [outerMinor, gl3Entry_dualCellPoint]
  simp
  ring

private theorem
    gl3Det_dualCellPoint (α β γ : v.adicCompletion ℚ) (a : (v.adicCompletion ℚ)ˣ) (x : v.adicCompletion ℚ) :
    gl3Det v (dualCellPoint v α β γ a x) = (a : v.adicCompletion ℚ)⁻¹ := by
  rw [gl3Det, dualCellPoint_coe, Matrix.det_fin_three]
  simp
  ring

private theorem
    cellRatio_dualCellPoint (α β γ : v.adicCompletion ℚ) (a : (v.adicCompletion ℚ)ˣ) (x : v.adicCompletion ℚ) :
    cellRatio v (dualCellPoint v α β γ a x) =
      ![1 / (α - γ * x / a), γ * (a : v.adicCompletion ℚ)⁻¹ / (α - γ * x / a),
        (γ - α * β) / a / (1 - β * x / a)] := by
  rw [cellRatio, cornerEntry_dualCellPoint, outerMinor_dualCellPoint, lowerMinor_dualCellPoint]
  simp [gl3Entry_dualCellPoint]

private theorem cellValue_dualCellPoint (χ : Fin 3 → ((v.adicCompletion ℚ)ˣ →* ℂˣ)) (α β γ : v.adicCompletion ℚ)
    (a : (v.adicCompletion ℚ)ˣ) (x : v.adicCompletion ℚ) :
    cellValue v χ (dualCellPoint v α β γ a x) =
      charExt (χ 0) ((a : v.adicCompletion ℚ)⁻¹ / (1 - β * x / a)) *
          charExt (χ 1) ((1 - β * x / a) / (α - γ * x / a)) * charExt (χ 2) (α - γ * x / a) *
        ((‖(a : v.adicCompletion ℚ)⁻¹ / (1 - β * x / a)‖ / ‖α - γ * x / a‖ : ℝ) : ℂ) := by
  rw [cellValue, gl3Det_dualCellPoint, lowerMinor_dualCellPoint, cornerEntry_dualCellPoint]

end DualPoint
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_tendsto_setIntegral_annulus_setIntegral_ball_jacquetWindow_sub_jacquetValue.LaurentZetaSlot"

end LanglandsTunnell.CubicInduction
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_tendsto_setIntegral_annulus_setIntegral_ball_jacquetWindow_sub_jacquetValue.LaurentZetaSlot"
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_tendsto_setIntegral_annulus_setIntegral_ball_jacquetWindow_sub_jacquetValue.LaurentZetaSlot"
end Part4
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_tendsto_setIntegral_annulus_setIntegral_ball_jacquetWindow_sub_jacquetValue.LaurentZetaSlot"

section Part5

set_option autoImplicit false

open MeasureTheory
open IsDedekindDomain
open NumberField
p2m_open "LanglandsTunnell.TateLocal P2MW.S_LanglandsTunnell_CubicInduction_tendsto_setIntegral_annulus_setIntegral_ball_jacquetWindow_sub_jacquetValue.LanglandsTunnell.TateLocal"
open NumberField.StandardAddChar
open scoped Topology

namespace LanglandsTunnell
p2m_export "LanglandsTunnell" "TateLocal.localBorel TateLocal.borelSpace_localBorel TateLocal.integersPositiveCompacts TateLocal.coe_integersPositiveCompacts"
namespace CubicInduction
p2m_export "LanglandsTunnell.CubicInduction" "unipotentBall3 mem_unipotentBall3_iff jacquetHaar3 jacquetTruncated3 jacquetLevel jacquetValue jacquetTruncated3_eq_jacquetValue bigCell3 mem_bigCell3_iff cellSectionOf cellSectionOf_apply_of_mem cellSectionOf_apply_of_notMem cellSectionOf_upperUnipotent3_mul cellSectionOf_diagonal3_mul principalSeries3 gl3Entry cornerEntry lowerMinor outerMinor gl3Det gl3Det_ne_zero cellRatio cellValue antidiagonal3 antidiagonal3_coe eventually_valued_eq eventually_valued_lt eventually_norm_eq eventually_charExt_eq continuous_gl3Entry continuous_cornerEntry continuous_lowerMinor continuous_outerMinor continuous_gl3Det exists_bottom_entry_ne_zero_of_cornerEntry_eq_zero outerMinor_ne_zero_of_lowerMinor_eq_zero gl3AmbientRightTranslate gl3AmbientRightTranslate_apply transposeInv3 upperUnipotent3 upperUnipotent3_coe embedMat2 iotaGL coe_iotaGL LocalGL3 diagUnitGL2 coe_diagUnitGL2 lowerUnipotent21 longWeyl3 longWeyl3_coe weylPrime3 weylPrime3_coe transposeInv3_weylPrime3 transposeInv3_lowerUnipotent21 exists_forall_le_integrableOn_and_jacquetTruncated3_eq_of_cellSectionOf exists_forall_gl3AmbientRightTranslate_eq_of_mem_principalSeries3"
p2m_open "LanglandsTunnell.CubicInduction LanglandsTunnell"

section TorusValues

variable (v : HeightOneSpectrum (𝓞 ℚ))
variable (ν : Fin 3 → ((v.adicCompletion ℚ)ˣ →* ℂˣ)) (Φ : (Fin 3 → v.adicCompletion ℚ) → ℂ)

private theorem exists_invariance_radius (hΦl : IsLocallyConstant Φ) (hΦc : HasCompactSupport Φ) :
    ∃ r : ℝ, 0 < r ∧ ∀ p q : Fin 3 → v.adicCompletion ℚ, (∀ i, ‖q i - p i‖ ≤ r) → Φ q = Φ p := by
  classical

  have hultra : ∀ a b c : v.adicCompletion ℚ, dist a c ≤ max (dist a b) (dist b c) :=
    fun a b c => IsUltrametricDist.dist_triangle_max a b c
  have hK : IsCompact (tsupport Φ) := hΦc

  have hball : ∀ x : tsupport Φ, ∃ ε : ℝ, 0 < ε ∧ ∀ q, dist q (x : Fin 3 → v.adicCompletion ℚ) < ε → Φ q = Φ x := by
    intro x
    have hopen : IsOpen {q : Fin 3 → v.adicCompletion ℚ | Φ q = Φ x} := hΦl.isOpen_fiber (Φ x)
    obtain ⟨ε, hε, hsub⟩ := Metric.isOpen_iff.mp hopen (x : Fin 3 → v.adicCompletion ℚ) rfl
    exact ⟨ε, hε, fun q hq => hsub hq⟩
  choose ε hεpos hε using hball
  obtain ⟨J, hJ⟩ := hK.elim_finite_subcover (fun x : tsupport Φ => Metric.ball (x : Fin 3 → v.adicCompletion ℚ) (ε x))
    (fun x => Metric.isOpen_ball) fun y hy => Set.mem_iUnion.mpr ⟨⟨y, hy⟩, Metric.mem_ball_self (hεpos ⟨y, hy⟩)⟩

  obtain ⟨r, hr, hrJ⟩ : ∃ r : ℝ, 0 < r ∧ ∀ x ∈ J, r < ε x := by
    by_cases hJne : J.Nonempty
    · have hinf : 0 < J.inf' hJne ε := (Finset.lt_inf'_iff hJne).mpr fun y _ => hεpos y
      exact ⟨J.inf' hJne ε / 2, half_pos hinf, fun x hx => (half_lt_self hinf).trans_le (Finset.inf'_le ε hx)⟩
    · exact ⟨1, one_pos, fun x hx => absurd ⟨x, hx⟩ hJne⟩
  refine ⟨r, hr, ?_⟩

  have key : ∀ p q : Fin 3 → v.adicCompletion ℚ, (∀ i, ‖q i - p i‖ ≤ r) → p ∈ tsupport Φ → Φ q = Φ p := by
    intro p q hpq hp
    obtain ⟨x, hxJ, hpx⟩ := Set.mem_iUnion₂.mp (hJ hp)
    have hpx' : dist p (x : Fin 3 → v.adicCompletion ℚ) < ε x := hpx
    have hqx : dist q (x : Fin 3 → v.adicCompletion ℚ) < ε x := by
      rw [dist_pi_lt_iff (hεpos x)] at hpx' ⊢
      intro i
      refine (hultra (q i) (p i) ((x : Fin 3 → v.adicCompletion ℚ) i)).trans_lt (max_lt ?_ (hpx' i))
      rw [dist_eq_norm]
      exact (hpq i).trans_lt (hrJ x hxJ)
    rw [hε x q hqx, hε x p hpx']
  intro p q hpq
  by_cases hp : p ∈ tsupport Φ
  · exact key p q hpq hp
  by_cases hq : q ∈ tsupport Φ
  · refine (key q p (fun i => ?_) hq).symm
    rw [norm_sub_rev]
    exact hpq i
  rw [image_eq_zero_of_notMem_tsupport hp, image_eq_zero_of_notMem_tsupport hq]

private theorem exists_support_radius (hΦc : HasCompactSupport Φ) :
    ∃ R : ℝ, ∀ p : Fin 3 → v.adicCompletion ℚ, Φ p ≠ 0 → ∀ i, ‖p i‖ ≤ R := by
  have hK : IsCompact (tsupport Φ) := hΦc
  choose C hC using fun i : Fin 3 =>
    hK.exists_bound_of_continuousOn
      ((continuous_apply i).continuousOn : ContinuousOn (fun p : Fin 3 → v.adicCompletion ℚ => p i) (tsupport Φ))
  refine ⟨∑ i, max (C i) 0, fun p hp i => ?_⟩
  have hpK : p ∈ tsupport Φ := subset_tsupport Φ hp
  calc ‖p i‖ ≤ C i := hC i p hpK
    _ ≤ max (C i) 0 := le_max_left _ _
    _ ≤ ∑ j, max (C j) 0 :=
        Finset.single_le_sum (f := fun j => max (C j) 0) (fun j _ => le_max_right _ _) (Finset.mem_univ i)

private theorem norm_le_zpow_of_valued_le {x : v.adicCompletion ℚ} {n : ℤ} (hx : Valued.v x ≤ WithZero.exp n) :
    ‖x‖ ≤ (Ideal.absNorm v.asIdeal : ℝ) ^ n := by
  have hexp : WithZeroMulInt.toNNReal (NumberField.HeightOneSpectrum.absNorm_ne_zero v) (WithZero.exp n) =
      (Ideal.absNorm v.asIdeal : NNReal) ^ n := by
    rw [WithZeroMulInt.toNNReal_neg_apply _ WithZero.exp_ne_zero]
    rfl
  have hkey : WithZeroMulInt.toNNReal (NumberField.HeightOneSpectrum.absNorm_ne_zero v) (Valued.v x) ≤
      WithZeroMulInt.toNNReal (NumberField.HeightOneSpectrum.absNorm_ne_zero v) (WithZero.exp n) :=
    (WithZeroMulInt.toNNReal_strictMono (NumberField.HeightOneSpectrum.one_lt_absNorm_nnreal (v := v))).monotone hx
  have h2 : (WithZeroMulInt.toNNReal (NumberField.HeightOneSpectrum.absNorm_ne_zero v) (Valued.v x) : ℝ) ≤
      (((Ideal.absNorm v.asIdeal : NNReal) ^ n : NNReal) : ℝ) :=
    NNReal.coe_le_coe.mpr (hkey.trans_eq hexp)
  rw [NumberField.FinitePlace.norm_def v x]
  exact_mod_cast h2

private theorem
    valued_le_of_norm_le_zpow {x : v.adicCompletion ℚ} {n : ℤ} (hx : ‖x‖ ≤ (Ideal.absNorm v.asIdeal : ℝ) ^ n) :
    Valued.v x ≤ WithZero.exp n := by
  have hexp : WithZeroMulInt.toNNReal (NumberField.HeightOneSpectrum.absNorm_ne_zero v) (WithZero.exp n) =
      (Ideal.absNorm v.asIdeal : NNReal) ^ n := by
    rw [WithZeroMulInt.toNNReal_neg_apply _ WithZero.exp_ne_zero]
    rfl
  have hx' : (WithZeroMulInt.toNNReal (NumberField.HeightOneSpectrum.absNorm_ne_zero v) (Valued.v x) : ℝ) ≤
      (((Ideal.absNorm v.asIdeal : NNReal) ^ n : NNReal) : ℝ) := by
    rw [NumberField.FinitePlace.norm_def v x] at hx
    exact_mod_cast hx
  have hkey : WithZeroMulInt.toNNReal (NumberField.HeightOneSpectrum.absNorm_ne_zero v) (Valued.v x) ≤
      WithZeroMulInt.toNNReal (NumberField.HeightOneSpectrum.absNorm_ne_zero v) (WithZero.exp n) := by
    rw [hexp]
    exact NNReal.coe_le_coe.mp hx'
  have hmono := WithZeroMulInt.toNNReal_strictMono (NumberField.HeightOneSpectrum.one_lt_absNorm_nnreal (v := v))
  exact hmono.le_iff_le.mp hkey

private theorem modulus_real_eq_norm (x : v.adicCompletion ℚ) : (modulus x : ℝ) = ‖x‖ := by
  rw [modulus_adicCompletion_eq_nnnorm ℚ v x, coe_nnnorm]

private theorem one_lt_absNorm_real : (1 : ℝ) < (Ideal.absNorm v.asIdeal : ℝ) := by
  exact_mod_cast NumberField.HeightOneSpectrum.one_lt_absNorm (v := v)

private theorem valued_eq_one_of_valued_sub_one_le {u : v.adicCompletion ℚ} {k : ℕ} (hk : 1 ≤ k)
    (hu : Valued.v (u - 1) ≤ WithZero.exp (-(k : ℤ))) : Valued.v u = 1 := by
  have hlt : Valued.v (u - 1) < Valued.v (1 : v.adicCompletion ℚ) := by
    rw [Valuation.map_one]
    refine lt_of_le_of_lt hu ?_
    rw [← WithZero.exp_zero]
    exact WithZero.exp_lt_exp.mpr (by omega)
  have h := Valued.v.map_add_eq_of_lt_right hlt
  rwa [sub_add_cancel, Valuation.map_one] at h

private theorem isClosed_valued_le (n : ℤ) : IsClosed {x : v.adicCompletion ℚ | Valued.v x ≤ WithZero.exp n} := by
  obtain ⟨y₀, hy₀⟩ := HeightOneSpectrum.valuedAdicCompletion_surjective ℚ v (WithZero.exp n)
  have hset : {x : v.adicCompletion ℚ | Valued.v x ≤ WithZero.exp n}
      = {x | Valued.v.restrict x ≤ Valued.v.restrict y₀} := by
    ext x
    simp only [Set.mem_setOf_eq]
    rw [Valuation.restrict_le_iff, hy₀]
  rw [hset]
  exact Valued.isClosed_closedBall _ _

private theorem measurableSet_unipotentBall3 (c : ℤ) :
    letI := localBorel ℚ v
    MeasurableSet (unipotentBall3 v c) := by
  letI := localBorel ℚ v
  haveI : BorelSpace (v.adicCompletion ℚ) := borelSpace_localBorel ℚ v
  have hset : unipotentBall3 v c =
      (Prod.fst ⁻¹' {x : v.adicCompletion ℚ | Valued.v x ≤ WithZero.exp c}) ∩
        ((fun p : v.adicCompletion ℚ × v.adicCompletion ℚ × v.adicCompletion ℚ => p.2.1) ⁻¹'
          {x : v.adicCompletion ℚ | Valued.v x ≤ WithZero.exp c}) ∩
        ((fun p : v.adicCompletion ℚ × v.adicCompletion ℚ × v.adicCompletion ℚ => p.2.2) ⁻¹'
          {x : v.adicCompletion ℚ | Valued.v x ≤ WithZero.exp (2 * c)}) := by
    ext p
    simp only [unipotentBall3, Set.mem_setOf_eq, Set.mem_inter_iff, Set.mem_preimage, and_assoc]
  rw [hset]
  exact (((isClosed_valued_le v c).measurableSet.preimage measurable_fst).inter
    ((isClosed_valued_le v c).measurableSet.preimage (measurable_fst.comp measurable_snd))).inter
    ((isClosed_valued_le v (2 * c)).measurableSet.preimage (measurable_snd.comp measurable_snd))

private theorem bddAbove_levels_psiLocal :
    BddAbove {n : ℤ | ∀ x : v.adicCompletion ℚ, Valued.v x ≤ WithZero.exp n → psiLocal ℚ v x = 1} := by
  obtain ⟨x₀, hx₀⟩ : ∃ x₀ : v.adicCompletion ℚ, psiLocal ℚ v x₀ ≠ 1 := by
    by_contra h
    push Not at h
    exact psiLocal_ne_one ℚ v (AddChar.ext _ _ h)
  have hx₀0 : x₀ ≠ 0 := by
    rintro rfl
    exact hx₀ (AddChar.map_zero_eq_one _)
  have hv : Valued.v x₀ ≠ 0 := (Valuation.ne_zero_iff _).mpr hx₀0
  refine ⟨WithZero.log (Valued.v x₀), fun n hn => ?_⟩
  by_contra hlt
  push Not at hlt
  apply hx₀
  apply hn x₀
  rw [← WithZero.exp_log hv]
  exact WithZero.exp_le_exp.mpr hlt.le

private theorem exists_psiLocal_neg_ne_one :
    ∃ ε : v.adicCompletion ℚ, Valued.v ε ≤ WithZero.exp (1 : ℤ) ∧ psiLocal ℚ v (-ε) ≠ 1 := by
  have hlevel := addCharLevel_psiLocal_rat v
  rw [addCharLevel_def] at hlevel
  have h1 : (1 : ℤ) ∉ {n : ℤ | ∀ x : v.adicCompletion ℚ, Valued.v x ≤ WithZero.exp n → psiLocal ℚ v x = 1} := by
    intro h1
    have := le_csSup (bddAbove_levels_psiLocal v) h1
    rw [hlevel] at this
    exact absurd this (by decide)
  simp only [Set.mem_setOf_eq, not_forall] at h1
  obtain ⟨x, hx, hψ⟩ := h1
  refine ⟨-x, ?_, ?_⟩
  · rwa [Valuation.map_neg]
  · rwa [neg_neg]

end TorusValues
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_tendsto_setIntegral_annulus_setIntegral_ball_jacquetWindow_sub_jacquetValue.LaurentZetaSlot"

end LanglandsTunnell.CubicInduction
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_tendsto_setIntegral_annulus_setIntegral_ball_jacquetWindow_sub_jacquetValue.LaurentZetaSlot"
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_tendsto_setIntegral_annulus_setIntegral_ball_jacquetWindow_sub_jacquetValue.LaurentZetaSlot"
end Part5
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_tendsto_setIntegral_annulus_setIntegral_ball_jacquetWindow_sub_jacquetValue.LaurentZetaSlot"

section Part6

set_option autoImplicit false

open MeasureTheory
open IsDedekindDomain
open NumberField
p2m_open "LanglandsTunnell.TateLocal P2MW.S_LanglandsTunnell_CubicInduction_tendsto_setIntegral_annulus_setIntegral_ball_jacquetWindow_sub_jacquetValue.LanglandsTunnell.TateLocal"
open NumberField.StandardAddChar
open scoped Topology

namespace LanglandsTunnell
p2m_export "LanglandsTunnell" "TateLocal.localBorel TateLocal.borelSpace_localBorel TateLocal.integersPositiveCompacts TateLocal.coe_integersPositiveCompacts"
namespace CubicInduction
p2m_export "LanglandsTunnell.CubicInduction" "unipotentBall3 mem_unipotentBall3_iff jacquetHaar3 jacquetTruncated3 jacquetLevel jacquetValue jacquetTruncated3_eq_jacquetValue bigCell3 mem_bigCell3_iff cellSectionOf cellSectionOf_apply_of_mem cellSectionOf_apply_of_notMem cellSectionOf_upperUnipotent3_mul cellSectionOf_diagonal3_mul principalSeries3 gl3Entry cornerEntry lowerMinor outerMinor gl3Det gl3Det_ne_zero cellRatio cellValue antidiagonal3 antidiagonal3_coe eventually_valued_eq eventually_valued_lt eventually_norm_eq eventually_charExt_eq continuous_gl3Entry continuous_cornerEntry continuous_lowerMinor continuous_outerMinor continuous_gl3Det exists_bottom_entry_ne_zero_of_cornerEntry_eq_zero outerMinor_ne_zero_of_lowerMinor_eq_zero gl3AmbientRightTranslate gl3AmbientRightTranslate_apply transposeInv3 upperUnipotent3 upperUnipotent3_coe embedMat2 iotaGL coe_iotaGL LocalGL3 diagUnitGL2 coe_diagUnitGL2 lowerUnipotent21 longWeyl3 longWeyl3_coe weylPrime3 weylPrime3_coe transposeInv3_weylPrime3 transposeInv3_lowerUnipotent21 exists_forall_le_integrableOn_and_jacquetTruncated3_eq_of_cellSectionOf exists_forall_gl3AmbientRightTranslate_eq_of_mem_principalSeries3"
p2m_open "LanglandsTunnell.CubicInduction LanglandsTunnell"

section DualTorusValues

variable (v : HeightOneSpectrum (𝓞 ℚ))
variable (ν : Fin 3 → ((v.adicCompletion ℚ)ˣ →* ℂˣ)) (Φ : (Fin 3 → v.adicCompletion ℚ) → ℂ)

private noncomputable def dualPoint (a : (v.adicCompletion ℚ)ˣ) (x : v.adicCompletion ℚ) : LocalGL3 v :=
  longWeyl3 * transposeInv3 (iotaGL (diagUnitGL2 a) * lowerUnipotent21 x * (weylPrime3 * transposeInv3 1)) *
    antidiagonal3 v

private noncomputable def dualTranslate (a : (v.adicCompletion ℚ)ˣ) (x : v.adicCompletion ℚ) : LocalGL3 v → ℂ :=
  gl3AmbientRightTranslate (R := ℂ) (dualPoint v a x) (cellSectionOf v ν Φ)

private theorem exists_level_dualTranslate (hν : ∀ i, IsLocallyConstant (ν i)) (hΦl : IsLocallyConstant Φ)
    (hΦc : HasCompactSupport Φ) (a : (v.adicCompletion ℚ)ˣ) (x : v.adicCompletion ℚ) :
    ∃ c₀ : ℕ, ∀ c : ℤ, (c₀ : ℤ) ≤ c →
      jacquetTruncated3 v c (dualTranslate v ν Φ a x) = jacquetTruncated3 v c₀ (dualTranslate v ν Φ a x) := by
  obtain ⟨c₀, h⟩ := exists_forall_le_integrableOn_and_jacquetTruncated3_eq_of_cellSectionOf v ν hν Φ ⟨hΦl, hΦc⟩
    (dualPoint v a x)
  exact ⟨c₀, fun c hc => (h c hc).2⟩

end DualTorusValues
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_tendsto_setIntegral_annulus_setIntegral_ball_jacquetWindow_sub_jacquetValue.LaurentZetaSlot"

end LanglandsTunnell.CubicInduction
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_tendsto_setIntegral_annulus_setIntegral_ball_jacquetWindow_sub_jacquetValue.LaurentZetaSlot"
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_tendsto_setIntegral_annulus_setIntegral_ball_jacquetWindow_sub_jacquetValue.LaurentZetaSlot"
end Part6
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_tendsto_setIntegral_annulus_setIntegral_ball_jacquetWindow_sub_jacquetValue.LaurentZetaSlot"

section Part13

set_option autoImplicit false

open IsDedekindDomain
open NumberField

namespace LanglandsTunnell
p2m_export "LanglandsTunnell" "TateLocal.localBorel TateLocal.borelSpace_localBorel TateLocal.integersPositiveCompacts TateLocal.coe_integersPositiveCompacts"
namespace TateLocal
p2m_export "LanglandsTunnell.TateLocal" "addCharLevel addCharLevel_def localBorel borelSpace_localBorel integersPositiveCompacts coe_integersPositiveCompacts selfDualHaarAt higherUnitsAt mem_higherUnitsAt_iff HasConductorExponentAt modulus modulus_of_ne_zero modulus_pos modulus_ne_zero modulus_mul charExt charExt_of_ne_zero charExt_coe_units mulMeasure modulus_adicCompletion_eq_nnnorm addCharLevel_psiLocal_rat psiLocal_ne_one exists_hasConductorExponentAt_of_continuous"
p2m_open "LanglandsTunnell.TateLocal LanglandsTunnell"

section ConductorWitness

variable (K : Type) [Field K] [NumberField K] (w : HeightOneSpectrum (𝓞 K))

private theorem exists_hasConductorExponentAt_of_isLocallyConstant (η : (w.adicCompletion K)ˣ →* ℂˣ)
    (hη : IsLocallyConstant η) : ∃ c : ℕ, HasConductorExponentAt K w η c :=
  exists_hasConductorExponentAt_of_continuous K w η hη.continuous

end ConductorWitness
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_tendsto_setIntegral_annulus_setIntegral_ball_jacquetWindow_sub_jacquetValue.LaurentZetaSlot"

section NormPowerAssembly

end NormPowerAssembly
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_tendsto_setIntegral_annulus_setIntegral_ball_jacquetWindow_sub_jacquetValue.LaurentZetaSlot"

end LanglandsTunnell.TateLocal
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_tendsto_setIntegral_annulus_setIntegral_ball_jacquetWindow_sub_jacquetValue.LaurentZetaSlot"
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_tendsto_setIntegral_annulus_setIntegral_ball_jacquetWindow_sub_jacquetValue.LaurentZetaSlot"
end Part13
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_tendsto_setIntegral_annulus_setIntegral_ball_jacquetWindow_sub_jacquetValue.LaurentZetaSlot"

section Part16

set_option autoImplicit false

open MeasureTheory
open IsDedekindDomain
open NumberField
p2m_open "LanglandsTunnell.TateLocal P2MW.S_LanglandsTunnell_CubicInduction_tendsto_setIntegral_annulus_setIntegral_ball_jacquetWindow_sub_jacquetValue.LanglandsTunnell.TateLocal"
open scoped Topology

namespace LanglandsTunnell
p2m_export "LanglandsTunnell" "TateLocal.localBorel TateLocal.borelSpace_localBorel TateLocal.integersPositiveCompacts TateLocal.coe_integersPositiveCompacts"
namespace CubicInduction
p2m_export "LanglandsTunnell.CubicInduction" "unipotentBall3 mem_unipotentBall3_iff jacquetHaar3 jacquetTruncated3 jacquetLevel jacquetValue jacquetTruncated3_eq_jacquetValue bigCell3 mem_bigCell3_iff cellSectionOf cellSectionOf_apply_of_mem cellSectionOf_apply_of_notMem cellSectionOf_upperUnipotent3_mul cellSectionOf_diagonal3_mul principalSeries3 gl3Entry cornerEntry lowerMinor outerMinor gl3Det gl3Det_ne_zero cellRatio cellValue antidiagonal3 antidiagonal3_coe eventually_valued_eq eventually_valued_lt eventually_norm_eq eventually_charExt_eq continuous_gl3Entry continuous_cornerEntry continuous_lowerMinor continuous_outerMinor continuous_gl3Det exists_bottom_entry_ne_zero_of_cornerEntry_eq_zero outerMinor_ne_zero_of_lowerMinor_eq_zero gl3AmbientRightTranslate gl3AmbientRightTranslate_apply transposeInv3 upperUnipotent3 upperUnipotent3_coe embedMat2 iotaGL coe_iotaGL LocalGL3 diagUnitGL2 coe_diagUnitGL2 lowerUnipotent21 longWeyl3 longWeyl3_coe weylPrime3 weylPrime3_coe transposeInv3_weylPrime3 transposeInv3_lowerUnipotent21 exists_forall_le_integrableOn_and_jacquetTruncated3_eq_of_cellSectionOf exists_forall_gl3AmbientRightTranslate_eq_of_mem_principalSeries3"
p2m_open "LanglandsTunnell.CubicInduction LanglandsTunnell"

section CellSectionMembership

variable (v : HeightOneSpectrum (𝓞 ℚ))
variable (ν : Fin 3 → ((v.adicCompletion ℚ)ˣ →* ℂˣ)) (Φ : (Fin 3 → v.adicCompletion ℚ) → ℂ)

private theorem eventually_lt_norm_div {n d : LocalGL3 v → v.adicCompletion ℚ} {g : LocalGL3 v} (hn : Continuous n)
    (hd : Continuous d) (hng : n g ≠ 0) (hdg : d g = 0) (R : ℝ) :
    ∀ᶠ h in 𝓝 g, d h ≠ 0 → R < ‖n h / d h‖ := by
  have hr : 0 < ‖n g‖ := norm_pos_iff.mpr hng
  have hm : max R 0 + 1 ≠ 0 := by positivity
  obtain ⟨δ, hδ, hδR⟩ : ∃ δ : ℝ, 0 < δ ∧ (max R 0 + 1) * δ = ‖n g‖ :=
    ⟨‖n g‖ / (max R 0 + 1), by positivity, by field_simp⟩
  have h₁ : ∀ᶠ h in 𝓝 g, ‖n h‖ = ‖n g‖ := (hn.tendsto g).eventually (eventually_norm_eq v hng)
  have h₂ : ∀ᶠ h in 𝓝 g, ‖d h‖ < δ := by
    have ht : Filter.Tendsto d (𝓝 g) (𝓝 0) := by simpa [hdg] using hd.tendsto g
    exact NormedAddGroup.tendsto_nhds_zero.mp ht δ hδ
  filter_upwards [h₁, h₂] with h hn' hd' hd0
  have hpos : 0 < ‖d h‖ := norm_pos_iff.mpr hd0
  rw [norm_div, hn', lt_div_iff₀ hpos]
  have hR : R ≤ max R 0 := le_max_left R 0
  have hR0 : 0 ≤ max R 0 := le_max_right R 0
  nlinarith [norm_nonneg (d h)]

private theorem eventually_cellSectionOf_eq_of_den (hΦc : HasCompactSupport Φ) {g : LocalGL3 v}
    {n d : LocalGL3 v → v.adicCompletion ℚ} (i : Fin 3) (hn : Continuous n) (hd : Continuous d) (hng : n g ≠ 0)
    (hdg : d g = 0) (hratio : ∀ h, cellRatio v h i = n h / d h) (hden : ∀ h, h ∈ bigCell3 v → d h ≠ 0) :
    ∀ᶠ h in 𝓝 g, cellSectionOf v ν Φ h = cellSectionOf v ν Φ g := by
  obtain ⟨R, hR⟩ := exists_support_radius v Φ hΦc
  have hg : g ∉ bigCell3 v := fun hmem => hden g hmem hdg
  filter_upwards [eventually_lt_norm_div v hn hd hng hdg R] with h hh
  rw [cellSectionOf_apply_of_notMem v ν Φ hg]
  by_cases hmem : h ∈ bigCell3 v
  · have hΦ : Φ (cellRatio v h) = 0 := by
      by_contra hne
      have hle := hR (cellRatio v h) hne i
      rw [hratio] at hle
      exact absurd (hh (hden h hmem)) (not_lt.mpr hle)
    rw [cellSectionOf_apply_of_mem v ν Φ hmem, hΦ, mul_zero]
  · exact cellSectionOf_apply_of_notMem v ν Φ hmem

private theorem isLocallyConstant_cellSectionOf (hν : ∀ i, IsLocallyConstant (ν i)) (hΦl : IsLocallyConstant Φ)
    (hΦc : HasCompactSupport Φ) : IsLocallyConstant (cellSectionOf v ν Φ) := by
  rw [IsLocallyConstant.iff_eventually_eq]
  intro g
  by_cases hc : cornerEntry v g = 0
  · rcases exists_bottom_entry_ne_zero_of_cornerEntry_eq_zero v hc with h21 | h22
    · exact eventually_cellSectionOf_eq_of_den v ν Φ hΦc 0 (continuous_gl3Entry v 2 1) (continuous_cornerEntry v)
        h21 hc (fun h => rfl) (fun h hh => ((mem_bigCell3_iff v h).mp hh).1)
    · exact eventually_cellSectionOf_eq_of_den v ν Φ hΦc 1 (continuous_gl3Entry v 2 2) (continuous_cornerEntry v)
        h22 hc (fun h => rfl) (fun h hh => ((mem_bigCell3_iff v h).mp hh).1)
  by_cases hl : lowerMinor v g = 0
  · exact eventually_cellSectionOf_eq_of_den v ν Φ hΦc 2 (continuous_outerMinor v) (continuous_lowerMinor v)
      (outerMinor_ne_zero_of_lowerMinor_eq_zero v hc hl) hl (fun h => rfl)
      (fun h hh => ((mem_bigCell3_iff v h).mp hh).2)
  have hgmem : g ∈ bigCell3 v := (mem_bigCell3_iff v g).mpr ⟨hc, hl⟩
  have hcA : ContinuousAt (cornerEntry v) g := (continuous_cornerEntry v).continuousAt
  have hlA : ContinuousAt (lowerMinor v) g := (continuous_lowerMinor v).continuousAt
  have hdA : ContinuousAt (gl3Det v) g := (continuous_gl3Det v).continuousAt
  have hr : ContinuousAt (cellRatio v) g := by
    refine continuousAt_pi.mpr fun i => ?_
    fin_cases i
    · exact ((continuous_gl3Entry v 2 1).continuousAt).div hcA hc
    · exact ((continuous_gl3Entry v 2 2).continuousAt).div hcA hc
    · exact ((continuous_outerMinor v).continuousAt).div hlA hl
  have hmem : ∀ᶠ h in 𝓝 g, h ∈ bigCell3 v := by
    filter_upwards [hcA.eventually_ne hc, hlA.eventually_ne hl] with h h₁ h₂
    exact (mem_bigCell3_iff v h).mpr ⟨h₁, h₂⟩
  have hval : ∀ᶠ h in 𝓝 g, cellValue v ν h = cellValue v ν g := by
    have hq0 : gl3Det v g / lowerMinor v g ≠ 0 := div_ne_zero (gl3Det_ne_zero v g) hl
    have hq1 : lowerMinor v g / cornerEntry v g ≠ 0 := div_ne_zero hl hc
    have e0 : ∀ᶠ h in 𝓝 g,
        charExt (ν 0) (gl3Det v h / lowerMinor v h) = charExt (ν 0) (gl3Det v g / lowerMinor v g) :=
      (hdA.div hlA hl).eventually (eventually_charExt_eq v (ν 0) (hν 0) hq0)
    have e1 : ∀ᶠ h in 𝓝 g,
        charExt (ν 1) (lowerMinor v h / cornerEntry v h) = charExt (ν 1) (lowerMinor v g / cornerEntry v g) :=
      (hlA.div hcA hc).eventually (eventually_charExt_eq v (ν 1) (hν 1) hq1)
    have e2 : ∀ᶠ h in 𝓝 g, charExt (ν 2) (cornerEntry v h) = charExt (ν 2) (cornerEntry v g) :=
      hcA.eventually (eventually_charExt_eq v (ν 2) (hν 2) hc)
    have e3 : ∀ᶠ h in 𝓝 g, ‖gl3Det v h / lowerMinor v h‖ = ‖gl3Det v g / lowerMinor v g‖ :=
      (hdA.div hlA hl).eventually (eventually_norm_eq v hq0)
    have e4 : ∀ᶠ h in 𝓝 g, ‖cornerEntry v h‖ = ‖cornerEntry v g‖ := hcA.eventually (eventually_norm_eq v hc)
    filter_upwards [e0, e1, e2, e3, e4] with h h0 h1 h2 h3 h4
    simp only [cellValue, h0, h1, h2, h3, h4]
  have hΦ : ∀ᶠ h in 𝓝 g, Φ (cellRatio v h) = Φ (cellRatio v g) := hr.eventually (hΦl.eventually_eq (cellRatio v g))
  filter_upwards [hmem, hval, hΦ] with h h₁ h₂ h₃
  rw [cellSectionOf_apply_of_mem v ν Φ h₁, cellSectionOf_apply_of_mem v ν Φ hgmem, h₂, h₃]

private theorem cellSectionOf_mem_principalSeries3 (hν : ∀ i, IsLocallyConstant (ν i)) (hΦl : IsLocallyConstant Φ)
    (hΦc : HasCompactSupport Φ) : cellSectionOf v ν Φ ∈ principalSeries3 v ν :=
  ⟨isLocallyConstant_cellSectionOf v ν Φ hν hΦl hΦc, cellSectionOf_upperUnipotent3_mul v ν Φ,
    cellSectionOf_diagonal3_mul v ν Φ⟩

end CellSectionMembership
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_tendsto_setIntegral_annulus_setIntegral_ball_jacquetWindow_sub_jacquetValue.LaurentZetaSlot"

end LanglandsTunnell.CubicInduction
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_tendsto_setIntegral_annulus_setIntegral_ball_jacquetWindow_sub_jacquetValue.LaurentZetaSlot"
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_tendsto_setIntegral_annulus_setIntegral_ball_jacquetWindow_sub_jacquetValue.LaurentZetaSlot"
end Part16
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_tendsto_setIntegral_annulus_setIntegral_ball_jacquetWindow_sub_jacquetValue.LaurentZetaSlot"

section Part17

set_option autoImplicit false

open MeasureTheory
open IsDedekindDomain
open NumberField

namespace LanglandsTunnell
p2m_export "LanglandsTunnell" "TateLocal.localBorel TateLocal.borelSpace_localBorel TateLocal.integersPositiveCompacts TateLocal.coe_integersPositiveCompacts"
namespace CubicInduction
p2m_export "LanglandsTunnell.CubicInduction" "unipotentBall3 mem_unipotentBall3_iff jacquetHaar3 jacquetTruncated3 jacquetLevel jacquetValue jacquetTruncated3_eq_jacquetValue bigCell3 mem_bigCell3_iff cellSectionOf cellSectionOf_apply_of_mem cellSectionOf_apply_of_notMem cellSectionOf_upperUnipotent3_mul cellSectionOf_diagonal3_mul principalSeries3 gl3Entry cornerEntry lowerMinor outerMinor gl3Det gl3Det_ne_zero cellRatio cellValue antidiagonal3 antidiagonal3_coe eventually_valued_eq eventually_valued_lt eventually_norm_eq eventually_charExt_eq continuous_gl3Entry continuous_cornerEntry continuous_lowerMinor continuous_outerMinor continuous_gl3Det exists_bottom_entry_ne_zero_of_cornerEntry_eq_zero outerMinor_ne_zero_of_lowerMinor_eq_zero gl3AmbientRightTranslate gl3AmbientRightTranslate_apply transposeInv3 upperUnipotent3 upperUnipotent3_coe embedMat2 iotaGL coe_iotaGL LocalGL3 diagUnitGL2 coe_diagUnitGL2 lowerUnipotent21 longWeyl3 longWeyl3_coe weylPrime3 weylPrime3_coe transposeInv3_weylPrime3 transposeInv3_lowerUnipotent21 exists_forall_le_integrableOn_and_jacquetTruncated3_eq_of_cellSectionOf exists_forall_gl3AmbientRightTranslate_eq_of_mem_principalSeries3"
p2m_open "LanglandsTunnell.CubicInduction LanglandsTunnell"

section UniformLevel

variable (v : HeightOneSpectrum (𝓞 ℚ))

private theorem gl3AmbientRightTranslate_mul_apply (g k : LocalGL3 v) (f : LocalGL3 v → ℂ) :
    gl3AmbientRightTranslate (R := ℂ) (g * k) f =
      gl3AmbientRightTranslate (R := ℂ) g (gl3AmbientRightTranslate (R := ℂ) k f) := by
  funext h
  simp only [gl3AmbientRightTranslate_apply, mul_assoc]

private theorem congruent_one_mem_nhds_one (n : ℕ) :
    {k : LocalGL3 v | ∀ i j : Fin 3,
        Valued.v (gl3Entry v k i j - (1 : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)) i j) ≤
          WithZero.exp (-(n : ℤ))} ∈ nhds (1 : LocalGL3 v) := by

  have hpow : Valued.v ((NumberField.AdelicLevel.uniformizerUnit ℚ v : v.adicCompletion ℚ) ^ n) =
      WithZero.exp (-(n : ℤ)) := by
    rw [map_pow, NumberField.AdelicLevel.valued_uniformizerUnit, WithZero.exp_eq_coe_ofAdd,
      WithZero.exp_eq_coe_ofAdd, ← WithZero.coe_pow, ← ofAdd_nsmul]
    congr 2
    simp
  have hpow0 : (NumberField.AdelicLevel.uniformizerUnit ℚ v : v.adicCompletion ℚ) ^ n ≠ 0 :=
    pow_ne_zero _ (Units.ne_zero _)
  have hball : {y : v.adicCompletion ℚ | Valued.v y ≤ WithZero.exp (-(n : ℤ))} ∈
      nhds (0 : v.adicCompletion ℚ) := by
    refine (eventually_valued_lt v hpow0).mono fun y hy => ?_
    rw [hpow] at hy
    exact hy.le
  have hmem : ∀ i j : Fin 3,
      {k : LocalGL3 v |
        Valued.v (gl3Entry v k i j - (1 : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)) i j) ≤
          WithZero.exp (-(n : ℤ))} ∈ nhds (1 : LocalGL3 v) := by
    intro i j
    have hc : Continuous fun k : LocalGL3 v =>
        gl3Entry v k i j - (1 : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)) i j :=
      (continuous_gl3Entry v i j).sub continuous_const
    have h1 : gl3Entry v (1 : LocalGL3 v) i j - (1 : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)) i j = 0 := by
      simp [gl3Entry]
    have h0 : {y : v.adicCompletion ℚ | Valued.v y ≤ WithZero.exp (-(n : ℤ))} ∈
        nhds (gl3Entry v (1 : LocalGL3 v) i j - (1 : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)) i j) := by
      rw [h1]
      exact hball
    exact hc.continuousAt.preimage_mem_nhds h0
  have hall : (⋂ i : Fin 3, ⋂ j : Fin 3,
      {k : LocalGL3 v |
        Valued.v (gl3Entry v k i j - (1 : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)) i j) ≤
          WithZero.exp (-(n : ℤ))}) ∈ nhds (1 : LocalGL3 v) :=
    Filter.iInter_mem.mpr fun i => Filter.iInter_mem.mpr fun j => hmem i j
  refine Filter.mem_of_superset hall ?_
  intro k hk i j
  simp only [Set.mem_iInter, Set.mem_setOf_eq] at hk
  exact hk i j

private theorem exists_level_forall_jacquetTruncated3_eq_jacquetValue_of_isLocallyConstant {X : Type*}
    [TopologicalSpace X] [CompactSpace X] (F : X → LocalGL3 v → ℂ)
    (hlc : IsLocallyConstant fun t : X => fun c : ℤ => jacquetTruncated3 v c (F t))
    (hstab : ∀ t : X, ∃ c₀ : ℕ, ∀ c : ℤ, (c₀ : ℤ) ≤ c →
      jacquetTruncated3 v c (F t) = jacquetTruncated3 v c₀ (F t)) :
    ∃ c₁ : ℕ, ∀ t : X, ∀ c : ℤ, (c₁ : ℤ) ≤ c → jacquetTruncated3 v c (F t) = jacquetValue v (F t) := by

  have hlevel : IsLocallyConstant fun t : X => jacquetLevel v (F t) :=
    hlc.comp fun T : ℤ → ℂ => sInf {c₀ : ℕ | ∀ c : ℤ, (c₀ : ℤ) ≤ c → T c = T c₀}

  obtain ⟨c₁, hc₁⟩ := hlevel.range_finite.bddAbove
  refine ⟨c₁, fun t c hc => ?_⟩
  have hle : jacquetLevel v (F t) ≤ c₁ := hc₁ (Set.mem_range_self t)
  have hle' : (jacquetLevel v (F t) : ℤ) ≤ c := le_trans (by exact_mod_cast hle) hc
  exact jacquetTruncated3_eq_jacquetValue v _ (hstab t) hle'

private theorem exists_level_forall_jacquetTruncated3_eq_jacquetValue {X : Type*} [TopologicalSpace X]
    [CompactSpace X] (g : X → LocalGL3 v) (hg : Continuous g) (f : LocalGL3 v → ℂ)
    (hf : ∃ n : ℕ, ∀ k : LocalGL3 v,
      (∀ i j : Fin 3,
        Valued.v (gl3Entry v k i j - (1 : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)) i j)
          ≤ WithZero.exp (-(n : ℤ))) →
      gl3AmbientRightTranslate (R := ℂ) k f = f)
    (hstab : ∀ t : X, ∃ c₀ : ℕ, ∀ c : ℤ, (c₀ : ℤ) ≤ c →
      jacquetTruncated3 v c (gl3AmbientRightTranslate (R := ℂ) (g t) f) =
        jacquetTruncated3 v c₀ (gl3AmbientRightTranslate (R := ℂ) (g t) f)) :
    ∃ c₁ : ℕ, ∀ t : X, ∀ c : ℤ, (c₁ : ℤ) ≤ c →
      jacquetTruncated3 v c (gl3AmbientRightTranslate (R := ℂ) (g t) f) =
        jacquetValue v (gl3AmbientRightTranslate (R := ℂ) (g t) f) := by
  obtain ⟨n, hn⟩ := hf

  have hlc : IsLocallyConstant fun t : X => gl3AmbientRightTranslate (R := ℂ) (g t) f := by
    rw [IsLocallyConstant.iff_eventually_eq]
    intro t₀
    have hcont : Continuous fun t : X => (g t₀)⁻¹ * g t := continuous_const.mul hg
    have hnear : (fun t : X => (g t₀)⁻¹ * g t) ⁻¹'
        {k : LocalGL3 v | ∀ i j : Fin 3,
          Valued.v (gl3Entry v k i j - (1 : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)) i j) ≤
            WithZero.exp (-(n : ℤ))} ∈ nhds t₀ := by
      apply hcont.continuousAt.preimage_mem_nhds
      rw [inv_mul_cancel]
      exact congruent_one_mem_nhds_one v n
    filter_upwards [hnear] with t ht
    have hk : gl3AmbientRightTranslate (R := ℂ) ((g t₀)⁻¹ * g t) f = f := hn _ ht
    calc gl3AmbientRightTranslate (R := ℂ) (g t) f
        = gl3AmbientRightTranslate (R := ℂ) (g t₀ * ((g t₀)⁻¹ * g t)) f := by
          rw [mul_inv_cancel_left]
      _ = gl3AmbientRightTranslate (R := ℂ) (g t₀) (gl3AmbientRightTranslate (R := ℂ) ((g t₀)⁻¹ * g t) f) :=
          gl3AmbientRightTranslate_mul_apply v _ _ _
      _ = gl3AmbientRightTranslate (R := ℂ) (g t₀) f := by rw [hk]
  exact exists_level_forall_jacquetTruncated3_eq_jacquetValue_of_isLocallyConstant v
    (fun t => gl3AmbientRightTranslate (R := ℂ) (g t) f)
    (hlc.comp fun u : LocalGL3 v → ℂ => fun c : ℤ => jacquetTruncated3 v c u) hstab

end UniformLevel
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_tendsto_setIntegral_annulus_setIntegral_ball_jacquetWindow_sub_jacquetValue.LaurentZetaSlot"

end LanglandsTunnell.CubicInduction
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_tendsto_setIntegral_annulus_setIntegral_ball_jacquetWindow_sub_jacquetValue.LaurentZetaSlot"
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_tendsto_setIntegral_annulus_setIntegral_ball_jacquetWindow_sub_jacquetValue.LaurentZetaSlot"
end Part17
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_tendsto_setIntegral_annulus_setIntegral_ball_jacquetWindow_sub_jacquetValue.LaurentZetaSlot"

section Part18
set_option autoImplicit false

open MeasureTheory
open IsDedekindDomain
open NumberField
p2m_open "LanglandsTunnell.TateLocal P2MW.S_LanglandsTunnell_CubicInduction_tendsto_setIntegral_annulus_setIntegral_ball_jacquetWindow_sub_jacquetValue.LanglandsTunnell.TateLocal"

attribute [local instance] LanglandsTunnell.TateLocal.localBorel

namespace LanglandsTunnell
p2m_export "LanglandsTunnell" "TateLocal.localBorel TateLocal.borelSpace_localBorel TateLocal.integersPositiveCompacts TateLocal.coe_integersPositiveCompacts"
namespace CubicInduction
p2m_export "LanglandsTunnell.CubicInduction" "unipotentBall3 mem_unipotentBall3_iff jacquetHaar3 jacquetTruncated3 jacquetLevel jacquetValue jacquetTruncated3_eq_jacquetValue bigCell3 mem_bigCell3_iff cellSectionOf cellSectionOf_apply_of_mem cellSectionOf_apply_of_notMem cellSectionOf_upperUnipotent3_mul cellSectionOf_diagonal3_mul principalSeries3 gl3Entry cornerEntry lowerMinor outerMinor gl3Det gl3Det_ne_zero cellRatio cellValue antidiagonal3 antidiagonal3_coe eventually_valued_eq eventually_valued_lt eventually_norm_eq eventually_charExt_eq continuous_gl3Entry continuous_cornerEntry continuous_lowerMinor continuous_outerMinor continuous_gl3Det exists_bottom_entry_ne_zero_of_cornerEntry_eq_zero outerMinor_ne_zero_of_lowerMinor_eq_zero gl3AmbientRightTranslate gl3AmbientRightTranslate_apply transposeInv3 upperUnipotent3 upperUnipotent3_coe embedMat2 iotaGL coe_iotaGL LocalGL3 diagUnitGL2 coe_diagUnitGL2 lowerUnipotent21 longWeyl3 longWeyl3_coe weylPrime3 weylPrime3_coe transposeInv3_weylPrime3 transposeInv3_lowerUnipotent21 exists_forall_le_integrableOn_and_jacquetTruncated3_eq_of_cellSectionOf exists_forall_gl3AmbientRightTranslate_eq_of_mem_principalSeries3"
p2m_open "LanglandsTunnell.CubicInduction LanglandsTunnell"

section DualLevelFacts

variable (v : HeightOneSpectrum (𝓞 ℚ))

private theorem continuous_transposeInv3 : Continuous fun g : LocalGL3 v => transposeInv3 g := by
  refine Units.continuous_iff.mpr ⟨?_, ?_⟩
  · show Continuous fun g : LocalGL3 v =>
      Matrix.transpose ((g⁻¹ : LocalGL3 v) : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ))
    exact Units.continuous_coe_inv.matrix_transpose
  · show Continuous fun g : LocalGL3 v => Matrix.transpose (g : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ))
    exact Units.continuous_val.matrix_transpose

private theorem continuous_iotaGL_diagUnitGL2 :
    Continuous fun a : (v.adicCompletion ℚ)ˣ => (iotaGL (diagUnitGL2 a) : LocalGL3 v) := by
  refine Units.continuous_iff.mpr ⟨?_, ?_⟩
  · show Continuous fun a : (v.adicCompletion ℚ)ˣ => embedMat2 !![(a : v.adicCompletion ℚ), 0; 0, 1]
    refine continuous_matrix fun i j => ?_
    fin_cases i <;> fin_cases j <;> simp only [embedMat2, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.cons_val_two, Fin.zero_eta, Fin.mk_one,
      Fin.reduceFinMk, Matrix.empty_val', Matrix.cons_val_fin_one] <;>
      first | exact continuous_const | exact Units.continuous_val
  · show Continuous fun a : (v.adicCompletion ℚ)ˣ =>
      embedMat2 !![((a⁻¹ : (v.adicCompletion ℚ)ˣ) : v.adicCompletion ℚ), 0; 0, 1]
    refine continuous_matrix fun i j => ?_
    fin_cases i <;> fin_cases j <;> simp only [embedMat2, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.cons_val_two, Fin.zero_eta, Fin.mk_one,
      Fin.reduceFinMk, Matrix.empty_val', Matrix.cons_val_fin_one] <;>
      first | exact continuous_const | exact Units.continuous_coe_inv

private theorem continuous_lowerUnipotent21 :
    Continuous fun x : v.adicCompletion ℚ => (lowerUnipotent21 x : LocalGL3 v) := by
  refine Units.continuous_iff.mpr ⟨?_, ?_⟩
  · show Continuous fun x : v.adicCompletion ℚ => !![(1 : v.adicCompletion ℚ), 0, 0; x, 1, 0; 0, 0, 1]
    refine continuous_matrix fun i j => ?_
    fin_cases i <;> fin_cases j <;> simp only [Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.cons_val_two, Fin.zero_eta, Fin.mk_one,
      Fin.reduceFinMk, Matrix.empty_val', Matrix.cons_val_fin_one] <;>
      first | exact continuous_const | exact continuous_id
  · show Continuous fun x : v.adicCompletion ℚ => !![(1 : v.adicCompletion ℚ), 0, 0; -x, 1, 0; 0, 0, 1]
    refine continuous_matrix fun i j => ?_
    fin_cases i <;> fin_cases j <;> simp only [Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.cons_val_two, Fin.zero_eta, Fin.mk_one,
      Fin.reduceFinMk, Matrix.empty_val', Matrix.cons_val_fin_one] <;>
      first | exact continuous_const | exact continuous_neg

private theorem continuous_dualPoint :
    Continuous fun t : (v.adicCompletion ℚ)ˣ × v.adicCompletion ℚ => dualPoint v t.1 t.2 := by
  unfold dualPoint
  refine (continuous_const.mul ((continuous_transposeInv3 v).comp ?_)).mul continuous_const
  exact (((continuous_iotaGL_diagUnitGL2 v).comp continuous_fst).mul
    ((continuous_lowerUnipotent21 v).comp continuous_snd)).mul continuous_const

private theorem exists_level_forall_dualTranslate_of_isCompact (ν : Fin 3 → ((v.adicCompletion ℚ)ˣ →* ℂˣ))
    (Φ : (Fin 3 → v.adicCompletion ℚ) → ℂ) (hν : ∀ i, IsLocallyConstant (ν i)) (hΦl : IsLocallyConstant Φ)
    (hΦc : HasCompactSupport Φ) {K : Set ((v.adicCompletion ℚ)ˣ × v.adicCompletion ℚ)} (hK : IsCompact K) :
    ∃ c₁ : ℕ, ∀ (a : (v.adicCompletion ℚ)ˣ) (x : v.adicCompletion ℚ), (a, x) ∈ K → ∀ c : ℤ, (c₁ : ℤ) ≤ c →
      jacquetTruncated3 v c (dualTranslate v ν Φ a x) = jacquetValue v (dualTranslate v ν Φ a x) := by
  haveI : CompactSpace K := isCompact_iff_compactSpace.mp hK
  obtain ⟨c₁, hc₁⟩ := exists_level_forall_jacquetTruncated3_eq_jacquetValue v
    (fun t : K => dualPoint v t.1.1 t.1.2) ((continuous_dualPoint v).comp continuous_subtype_val)
    (cellSectionOf v ν Φ)
    (exists_forall_gl3AmbientRightTranslate_eq_of_mem_principalSeries3 v ν (cellSectionOf v ν Φ)
      (cellSectionOf_mem_principalSeries3 v ν Φ hν hΦl hΦc))
    (fun t : K => exists_level_dualTranslate v ν Φ hν hΦl hΦc t.1.1 t.1.2)
  exact ⟨c₁, fun a x hax c hc => hc₁ ⟨(a, x), hax⟩ c hc⟩

private def annulus (N : ℕ) : Set (v.adicCompletion ℚ) :=
  {t | WithZero.exp (-(N : ℤ)) ≤ Valued.v t ∧ Valued.v t ≤ WithZero.exp (N : ℤ)}

private theorem ne_zero_of_mem_annulus {N : ℕ} {t : v.adicCompletion ℚ} (ht : t ∈ annulus v N) : t ≠ 0 := by
  rintro rfl
  have h := ht.1
  rw [map_zero] at h
  exact (not_le.mpr WithZero.exp_pos) h

private theorem isCompact_valued_le (n : ℤ) :
    IsCompact {x : v.adicCompletion ℚ | Valued.v x ≤ WithZero.exp n} := by
  obtain ⟨y₀, hy₀⟩ := HeightOneSpectrum.valuedAdicCompletion_surjective ℚ v (WithZero.exp n)
  have hy₀0 : y₀ ≠ 0 := by
    rintro rfl
    rw [map_zero] at hy₀
    exact WithZero.exp_ne_zero hy₀.symm
  have hring : IsCompact ((integersPositiveCompacts ℚ v : Set (v.adicCompletion ℚ))) :=
    (integersPositiveCompacts ℚ v).isCompact
  have hmul : Continuous fun z : v.adicCompletion ℚ => y₀ * z := continuous_const.mul continuous_id
  refine (hring.image hmul).of_isClosed_subset (isClosed_valued_le v n) ?_
  intro x hx
  refine ⟨y₀⁻¹ * x, ?_, ?_⟩
  · show Valued.v (y₀⁻¹ * x) ≤ 1
    rw [map_mul, map_inv₀, hy₀]
    calc (WithZero.exp n)⁻¹ * Valued.v x ≤ (WithZero.exp n)⁻¹ * WithZero.exp n := mul_le_mul_right hx _
      _ = 1 := inv_mul_cancel₀ WithZero.exp_ne_zero
  · show y₀ * (y₀⁻¹ * x) = x
    rw [← mul_assoc, mul_inv_cancel₀ hy₀0, one_mul]

private theorem isClosed_annulus (N : ℕ) : IsClosed (annulus v N) := by
  rw [← isOpen_compl_iff, isOpen_iff_eventually]
  intro t ht
  by_cases ht0 : t = 0
  ·
    subst ht0
    obtain ⟨y₀, hy₀⟩ := HeightOneSpectrum.valuedAdicCompletion_surjective ℚ v (WithZero.exp (-(N : ℤ)))
    have hy₀0 : y₀ ≠ 0 := by
      rintro rfl
      rw [map_zero] at hy₀
      exact WithZero.exp_ne_zero hy₀.symm
    filter_upwards [eventually_valued_lt v hy₀0] with y hy
    rw [hy₀] at hy
    intro hmem
    exact absurd hmem.1 (not_le.mpr hy)
  · filter_upwards [eventually_valued_eq v ht0] with y hy
    intro hmem
    apply ht
    simp only [annulus, Set.mem_setOf_eq] at hmem ⊢
    rw [← hy]
    exact hmem

private theorem isCompact_annulus (N : ℕ) : IsCompact (annulus v N) :=
  (isCompact_valued_le v (N : ℤ)).of_isClosed_subset (isClosed_annulus v N) fun _ ht => ht.2

private def paramSet (N : ℕ) (R : ℝ) : Set ((v.adicCompletion ℚ)ˣ × v.adicCompletion ℚ) :=
  (Units.val ⁻¹' annulus v N) ×ˢ Metric.closedBall (0 : v.adicCompletion ℚ) R

private theorem mem_paramSet {N : ℕ} {R : ℝ} {a : (v.adicCompletion ℚ)ˣ} {x : v.adicCompletion ℚ} :
    (a, x) ∈ paramSet v N R ↔ (a : v.adicCompletion ℚ) ∈ annulus v N ∧ ‖x‖ ≤ R := by
  simp only [paramSet, Set.mem_prod, Set.mem_preimage, mem_closedBall_zero_iff]

private theorem isCompact_paramSet (N : ℕ) (R : ℝ) : IsCompact (paramSet v N R) := by
  refine IsCompact.prod ?_ ?_
  · rw [Units.isEmbedding_val₀.isCompact_iff,
      Set.image_preimage_eq_of_subset fun t ht => ⟨Units.mk0 t (ne_zero_of_mem_annulus v ht), rfl⟩]
    exact isCompact_annulus v N
  · obtain ⟨n, hn⟩ := pow_unbounded_of_one_lt R (one_lt_absNorm_real v)
    refine (isCompact_valued_le v (n : ℤ)).of_isClosed_subset Metric.isClosed_closedBall fun x hx => ?_
    rw [mem_closedBall_zero_iff] at hx
    exact valued_le_of_norm_le_zpow v (by rw [zpow_natCast]; exact hx.trans hn.le)

end DualLevelFacts
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_tendsto_setIntegral_annulus_setIntegral_ball_jacquetWindow_sub_jacquetValue.LaurentZetaSlot"

end LanglandsTunnell.CubicInduction
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_tendsto_setIntegral_annulus_setIntegral_ball_jacquetWindow_sub_jacquetValue.LaurentZetaSlot"
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_tendsto_setIntegral_annulus_setIntegral_ball_jacquetWindow_sub_jacquetValue.LaurentZetaSlot"

end Part18
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_tendsto_setIntegral_annulus_setIntegral_ball_jacquetWindow_sub_jacquetValue.LaurentZetaSlot"

section Part20

set_option autoImplicit false

open IsDedekindDomain
open NumberField
open NumberField.StandardAddChar

namespace LanglandsTunnell
p2m_export "LanglandsTunnell" "TateLocal.localBorel TateLocal.borelSpace_localBorel TateLocal.integersPositiveCompacts TateLocal.coe_integersPositiveCompacts"
namespace CubicInduction
p2m_export "LanglandsTunnell.CubicInduction" "unipotentBall3 mem_unipotentBall3_iff jacquetHaar3 jacquetTruncated3 jacquetLevel jacquetValue jacquetTruncated3_eq_jacquetValue bigCell3 mem_bigCell3_iff cellSectionOf cellSectionOf_apply_of_mem cellSectionOf_apply_of_notMem cellSectionOf_upperUnipotent3_mul cellSectionOf_diagonal3_mul principalSeries3 gl3Entry cornerEntry lowerMinor outerMinor gl3Det gl3Det_ne_zero cellRatio cellValue antidiagonal3 antidiagonal3_coe eventually_valued_eq eventually_valued_lt eventually_norm_eq eventually_charExt_eq continuous_gl3Entry continuous_cornerEntry continuous_lowerMinor continuous_outerMinor continuous_gl3Det exists_bottom_entry_ne_zero_of_cornerEntry_eq_zero outerMinor_ne_zero_of_lowerMinor_eq_zero gl3AmbientRightTranslate gl3AmbientRightTranslate_apply transposeInv3 upperUnipotent3 upperUnipotent3_coe embedMat2 iotaGL coe_iotaGL LocalGL3 diagUnitGL2 coe_diagUnitGL2 lowerUnipotent21 longWeyl3 longWeyl3_coe weylPrime3 weylPrime3_coe transposeInv3_weylPrime3 transposeInv3_lowerUnipotent21 exists_forall_le_integrableOn_and_jacquetTruncated3_eq_of_cellSectionOf exists_forall_gl3AmbientRightTranslate_eq_of_mem_principalSeries3"
p2m_open "LanglandsTunnell.CubicInduction LanglandsTunnell"

variable (v : HeightOneSpectrum (𝓞 ℚ))

private theorem isCompact_setOf_valued_le_exp (n : ℤ) :
    IsCompact {y : v.adicCompletion ℚ | Valued.v y ≤ WithZero.exp n} := by
  have hK : IsCompact (v.adicCompletionIntegers ℚ : Set (v.adicCompletion ℚ)) := by
    rw [← LanglandsTunnell.TateLocal.coe_integersPositiveCompacts]
    exact (LanglandsTunnell.TateLocal.integersPositiveCompacts ℚ v).isCompact
  have himage : (fun z : v.adicCompletion ℚ =>
      ((NumberField.AdelicLevel.uniformizerUnit ℚ v ^ (-n) : (v.adicCompletion ℚ)ˣ) : v.adicCompletion ℚ) * z) ''
        (v.adicCompletionIntegers ℚ : Set (v.adicCompletion ℚ)) =
      {y : v.adicCompletion ℚ | Valued.v y ≤ WithZero.exp n} := by
    ext y
    constructor
    · rintro ⟨z, hz, rfl⟩
      have hz' : Valued.v z ≤ 1 := hz
      show Valued.v (_ * z) ≤ WithZero.exp n
      rw [Valuation.map_mul, LaurentZetaSlot.valued_uniformizerUnit_zpow v, neg_neg]
      calc WithZero.exp n * Valued.v z ≤ WithZero.exp n * 1 := mul_le_mul_right hz' _
        _ = WithZero.exp n := mul_one _
    · intro hy
      refine ⟨((NumberField.AdelicLevel.uniformizerUnit ℚ v ^ n : (v.adicCompletion ℚ)ˣ) : v.adicCompletion ℚ) * y,
        ?_, ?_⟩
      · show Valued.v (((NumberField.AdelicLevel.uniformizerUnit ℚ v ^ n : (v.adicCompletion ℚ)ˣ) :
            v.adicCompletion ℚ) * y) ≤ 1
        rw [Valuation.map_mul, LaurentZetaSlot.valued_uniformizerUnit_zpow v]
        calc WithZero.exp (-n) * Valued.v y ≤ WithZero.exp (-n) * WithZero.exp n := mul_le_mul_right hy _
          _ = 1 := by rw [← WithZero.exp_add, neg_add_cancel, WithZero.exp_zero]
      · show ((NumberField.AdelicLevel.uniformizerUnit ℚ v ^ (-n) : (v.adicCompletion ℚ)ˣ) : v.adicCompletion ℚ) *
            (((NumberField.AdelicLevel.uniformizerUnit ℚ v ^ n : (v.adicCompletion ℚ)ˣ) : v.adicCompletion ℚ) * y) = y
        rw [← mul_assoc, ← Units.val_mul, ← zpow_add, neg_add_cancel, zpow_zero, Units.val_one, one_mul]
  rw [← himage]
  exact hK.image (continuous_const.mul continuous_id)

private theorem valued_nsmul_le (x : v.adicCompletion ℚ) (k : ℕ) :
    Valued.v (k • x) ≤ max (Valued.v x) 1 := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [succ_nsmul]
    exact (Valuation.map_add _ _ _).trans (max_le ih (le_max_left _ _))

private theorem norm_psiLocal_le_one (x : v.adicCompletion ℚ) : ‖psiLocal ℚ v x‖ ≤ 1 := by

  have hpos : (0 : WithZero (Multiplicative ℤ)) < max (Valued.v x) 1 := lt_of_lt_of_le zero_lt_one (le_max_right _ _)
  obtain ⟨n, hn⟩ : ∃ n : ℤ, max (Valued.v x) 1 = WithZero.exp n := ⟨_, (WithZero.exp_log hpos.ne').symm⟩
  obtain ⟨C, hC⟩ := (isCompact_setOf_valued_le_exp v n).exists_bound_of_continuousOn
    (continuous_psiLocal ℚ v).continuousOn
  by_contra hlt
  push Not at hlt
  obtain ⟨k, hk⟩ := pow_unbounded_of_one_lt C hlt
  have hmem : k • x ∈ {y : v.adicCompletion ℚ | Valued.v y ≤ WithZero.exp n} := by
    show Valued.v (k • x) ≤ WithZero.exp n
    rw [← hn]
    exact valued_nsmul_le v x k
  have h := hC _ hmem
  rw [AddChar.map_nsmul_eq_pow, norm_pow] at h
  exact absurd (h.trans_lt hk) (lt_irrefl _)

end LanglandsTunnell.CubicInduction
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_tendsto_setIntegral_annulus_setIntegral_ball_jacquetWindow_sub_jacquetValue.LaurentZetaSlot"
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_tendsto_setIntegral_annulus_setIntegral_ball_jacquetWindow_sub_jacquetValue.LaurentZetaSlot"
end Part20
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_tendsto_setIntegral_annulus_setIntegral_ball_jacquetWindow_sub_jacquetValue.LaurentZetaSlot"

section Part21

set_option autoImplicit false

open MeasureTheory
open IsDedekindDomain
open NumberField
p2m_open "LanglandsTunnell.TateLocal P2MW.S_LanglandsTunnell_CubicInduction_tendsto_setIntegral_annulus_setIntegral_ball_jacquetWindow_sub_jacquetValue.LanglandsTunnell.TateLocal"
open NumberField.StandardAddChar
open scoped NNReal ENNReal

attribute [local instance] LanglandsTunnell.TateLocal.localBorel
attribute [local instance] LanglandsTunnell.TateLocal.borelSpace_localBorel

namespace LanglandsTunnell
p2m_export "LanglandsTunnell" "TateLocal.localBorel TateLocal.borelSpace_localBorel TateLocal.integersPositiveCompacts TateLocal.coe_integersPositiveCompacts"
namespace CubicInduction
p2m_export "LanglandsTunnell.CubicInduction" "unipotentBall3 mem_unipotentBall3_iff jacquetHaar3 jacquetTruncated3 jacquetLevel jacquetValue jacquetTruncated3_eq_jacquetValue bigCell3 mem_bigCell3_iff cellSectionOf cellSectionOf_apply_of_mem cellSectionOf_apply_of_notMem cellSectionOf_upperUnipotent3_mul cellSectionOf_diagonal3_mul principalSeries3 gl3Entry cornerEntry lowerMinor outerMinor gl3Det gl3Det_ne_zero cellRatio cellValue antidiagonal3 antidiagonal3_coe eventually_valued_eq eventually_valued_lt eventually_norm_eq eventually_charExt_eq continuous_gl3Entry continuous_cornerEntry continuous_lowerMinor continuous_outerMinor continuous_gl3Det exists_bottom_entry_ne_zero_of_cornerEntry_eq_zero outerMinor_ne_zero_of_lowerMinor_eq_zero gl3AmbientRightTranslate gl3AmbientRightTranslate_apply transposeInv3 upperUnipotent3 upperUnipotent3_coe embedMat2 iotaGL coe_iotaGL LocalGL3 diagUnitGL2 coe_diagUnitGL2 lowerUnipotent21 longWeyl3 longWeyl3_coe weylPrime3 weylPrime3_coe transposeInv3_weylPrime3 transposeInv3_lowerUnipotent21 exists_forall_le_integrableOn_and_jacquetTruncated3_eq_of_cellSectionOf exists_forall_gl3AmbientRightTranslate_eq_of_mem_principalSeries3"
p2m_open "LanglandsTunnell.CubicInduction LanglandsTunnell"

variable (v : HeightOneSpectrum (𝓞 ℚ))

section FineShells

variable (ν : Fin 3 → ((v.adicCompletion ℚ)ˣ →* ℂˣ)) (Φ : (Fin 3 → v.adicCompletion ℚ) → ℂ)

private theorem charExt_eq_of_hasConductorExponentAt {η : (v.adicCompletion ℚ)ˣ →* ℂˣ} {n : ℕ}
    (hη : HasConductorExponentAt ℚ v η n) {z z' : v.adicCompletion ℚ} (hz : z ≠ 0) (hz' : z' ≠ 0)
    (h : Valued.v (z' / z - 1) ≤ WithZero.exp (-((n : ℤ) + 1))) : charExt η z' = charExt η z := by
  have hy : z' / z ≠ 0 := div_ne_zero hz' hz
  have h' : Valued.v (z' / z - 1) ≤ WithZero.exp (-((n + 1 : ℕ) : ℤ)) := by push_cast; exact h
  have hone : Valued.v (z' / z) = 1 := valued_eq_one_of_valued_sub_one_le v (k := n + 1) (by omega) h'
  have hmem : Units.mk0 (z' / z) hy ∈ higherUnitsAt ℚ v n :=
    (mem_higherUnitsAt_iff ℚ v).mpr ⟨hone, Or.inr (h.trans (WithZero.exp_le_exp.mpr (by omega)))⟩
  have hval : η (Units.mk0 (z' / z) hy) = 1 := hη.1 _ hmem
  have hzz : z * (z' / z) = z' := by field_simp
  rw [← hzz, charExt_mul ℚ v η z (z' / z), charExt_of_ne_zero η hy, hval, Units.val_one, mul_one]

private theorem modulus_eq_of_valued_eq {x y : v.adicCompletion ℚ} (hx : x ≠ 0) (h : Valued.v x = Valued.v y) :
    modulus x = modulus y := by
  obtain ⟨j, hj⟩ := LaurentZetaSlot.exists_mem_shell v hx
  have hy : y ∈ LaurentZetaSlot.shell v j := by
    show Valued.v y = _
    rw [← h]
    exact hj
  rw [LaurentZetaSlot.modulus_eq_of_mem_shell v hj, LaurentZetaSlot.modulus_eq_of_mem_shell v hy]

private theorem exists_translate :
    ∃ e : v.adicCompletion ℚ, psiLocal ℚ v e ≠ 1 ∧ ∃ me : ℤ, Valued.v e = WithZero.exp (-me) ∧ -me ≤ 1 := by
  obtain ⟨ε, hε, hψε⟩ := exists_psiLocal_neg_ne_one v
  have he0 : -ε ≠ 0 := fun h => hψε (by rw [h, AddChar.map_zero_eq_one])
  obtain ⟨me, hme⟩ := LaurentZetaSlot.exists_mem_shell v he0
  have hve : Valued.v (-ε) = WithZero.exp (-me) := hme
  refine ⟨-ε, hψε, me, hve, ?_⟩
  rw [← WithZero.exp_le_exp, ← hve, Valuation.map_neg]
  exact hε

end FineShells
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_tendsto_setIntegral_annulus_setIntegral_ball_jacquetWindow_sub_jacquetValue.LaurentZetaSlot"

end LanglandsTunnell.CubicInduction
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_tendsto_setIntegral_annulus_setIntegral_ball_jacquetWindow_sub_jacquetValue.LaurentZetaSlot"
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_tendsto_setIntegral_annulus_setIntegral_ball_jacquetWindow_sub_jacquetValue.LaurentZetaSlot"
end Part21
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_tendsto_setIntegral_annulus_setIntegral_ball_jacquetWindow_sub_jacquetValue.LaurentZetaSlot"

section Part23

set_option autoImplicit false

open MeasureTheory
open IsDedekindDomain
open NumberField
p2m_open "LanglandsTunnell.TateLocal P2MW.S_LanglandsTunnell_CubicInduction_tendsto_setIntegral_annulus_setIntegral_ball_jacquetWindow_sub_jacquetValue.LanglandsTunnell.TateLocal"
open NumberField.StandardAddChar
open scoped NNReal ENNReal Pointwise

attribute [local instance] LanglandsTunnell.TateLocal.localBorel
attribute [local instance] LanglandsTunnell.TateLocal.borelSpace_localBorel

namespace LanglandsTunnell
p2m_export "LanglandsTunnell" "TateLocal.localBorel TateLocal.borelSpace_localBorel TateLocal.integersPositiveCompacts TateLocal.coe_integersPositiveCompacts"
namespace CubicInduction
p2m_export "LanglandsTunnell.CubicInduction" "unipotentBall3 mem_unipotentBall3_iff jacquetHaar3 jacquetTruncated3 jacquetLevel jacquetValue jacquetTruncated3_eq_jacquetValue bigCell3 mem_bigCell3_iff cellSectionOf cellSectionOf_apply_of_mem cellSectionOf_apply_of_notMem cellSectionOf_upperUnipotent3_mul cellSectionOf_diagonal3_mul principalSeries3 gl3Entry cornerEntry lowerMinor outerMinor gl3Det gl3Det_ne_zero cellRatio cellValue antidiagonal3 antidiagonal3_coe eventually_valued_eq eventually_valued_lt eventually_norm_eq eventually_charExt_eq continuous_gl3Entry continuous_cornerEntry continuous_lowerMinor continuous_outerMinor continuous_gl3Det exists_bottom_entry_ne_zero_of_cornerEntry_eq_zero outerMinor_ne_zero_of_lowerMinor_eq_zero gl3AmbientRightTranslate gl3AmbientRightTranslate_apply transposeInv3 upperUnipotent3 upperUnipotent3_coe embedMat2 iotaGL coe_iotaGL LocalGL3 diagUnitGL2 coe_diagUnitGL2 lowerUnipotent21 longWeyl3 longWeyl3_coe weylPrime3 weylPrime3_coe transposeInv3_weylPrime3 transposeInv3_lowerUnipotent21 exists_forall_le_integrableOn_and_jacquetTruncated3_eq_of_cellSectionOf exists_forall_gl3AmbientRightTranslate_eq_of_mem_principalSeries3"
p2m_open "LanglandsTunnell.CubicInduction LanglandsTunnell"

variable (v : HeightOneSpectrum (𝓞 ℚ))

section InnerDominantLemmas

variable (ν : Fin 3 → ((v.adicCompletion ℚ)ˣ →* ℂˣ)) (Φ : (Fin 3 → v.adicCompletion ℚ) → ℂ)
variable (χ : (v.adicCompletion ℚ)ˣ →* ℂˣ) (s : ℂ)

private theorem exists_forall_norm_apply_le (hΦl : IsLocallyConstant Φ) (hΦc : HasCompactSupport Φ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ p : Fin 3 → v.adicCompletion ℚ, ‖Φ p‖ ≤ C := by
  obtain ⟨C, hC⟩ := (hΦc : IsCompact (tsupport Φ)).exists_bound_of_continuousOn hΦl.continuous.continuousOn
  refine ⟨max C 0, le_max_right _ _, fun p => ?_⟩
  by_cases hp : p ∈ tsupport Φ
  · exact (hC p hp).trans (le_max_left _ _)
  · rw [image_eq_zero_of_notMem_tsupport hp, norm_zero]
    exact le_max_right _ _

end InnerDominantLemmas
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_tendsto_setIntegral_annulus_setIntegral_ball_jacquetWindow_sub_jacquetValue.LaurentZetaSlot"

end LanglandsTunnell.CubicInduction
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_tendsto_setIntegral_annulus_setIntegral_ball_jacquetWindow_sub_jacquetValue.LaurentZetaSlot"
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_tendsto_setIntegral_annulus_setIntegral_ball_jacquetWindow_sub_jacquetValue.LaurentZetaSlot"
end Part23
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_tendsto_setIntegral_annulus_setIntegral_ball_jacquetWindow_sub_jacquetValue.LaurentZetaSlot"

section Part24

set_option autoImplicit false

open MeasureTheory
open IsDedekindDomain
open NumberField
p2m_open "LanglandsTunnell.TateLocal P2MW.S_LanglandsTunnell_CubicInduction_tendsto_setIntegral_annulus_setIntegral_ball_jacquetWindow_sub_jacquetValue.LanglandsTunnell.TateLocal"
open NumberField.StandardAddChar
open scoped NNReal ENNReal

attribute [local instance] LanglandsTunnell.TateLocal.localBorel
attribute [local instance] LanglandsTunnell.TateLocal.borelSpace_localBorel

namespace LanglandsTunnell
p2m_export "LanglandsTunnell" "TateLocal.localBorel TateLocal.borelSpace_localBorel TateLocal.integersPositiveCompacts TateLocal.coe_integersPositiveCompacts"
namespace CubicInduction
p2m_export "LanglandsTunnell.CubicInduction" "unipotentBall3 mem_unipotentBall3_iff jacquetHaar3 jacquetTruncated3 jacquetLevel jacquetValue jacquetTruncated3_eq_jacquetValue bigCell3 mem_bigCell3_iff cellSectionOf cellSectionOf_apply_of_mem cellSectionOf_apply_of_notMem cellSectionOf_upperUnipotent3_mul cellSectionOf_diagonal3_mul principalSeries3 gl3Entry cornerEntry lowerMinor outerMinor gl3Det gl3Det_ne_zero cellRatio cellValue antidiagonal3 antidiagonal3_coe eventually_valued_eq eventually_valued_lt eventually_norm_eq eventually_charExt_eq continuous_gl3Entry continuous_cornerEntry continuous_lowerMinor continuous_outerMinor continuous_gl3Det exists_bottom_entry_ne_zero_of_cornerEntry_eq_zero outerMinor_ne_zero_of_lowerMinor_eq_zero gl3AmbientRightTranslate gl3AmbientRightTranslate_apply transposeInv3 upperUnipotent3 upperUnipotent3_coe embedMat2 iotaGL coe_iotaGL LocalGL3 diagUnitGL2 coe_diagUnitGL2 lowerUnipotent21 longWeyl3 longWeyl3_coe weylPrime3 weylPrime3_coe transposeInv3_weylPrime3 transposeInv3_lowerUnipotent21 exists_forall_le_integrableOn_and_jacquetTruncated3_eq_of_cellSectionOf exists_forall_gl3AmbientRightTranslate_eq_of_mem_principalSeries3"
p2m_open "LanglandsTunnell.CubicInduction LanglandsTunnell"

variable (v : HeightOneSpectrum (𝓞 ℚ))

section InnerDominantBounds

variable (ν : Fin 3 → ((v.adicCompletion ℚ)ˣ →* ℂˣ)) (Φ : (Fin 3 → v.adicCompletion ℚ) → ℂ)
variable (χ : (v.adicCompletion ℚ)ˣ →* ℂˣ) (s : ℂ)

private theorem exists_forall_norm_charExt_le (ξ : (v.adicCompletion ℚ)ˣ →* ℂˣ) (hξ : IsLocallyConstant ξ)
    (h1 : ‖((ξ (NumberField.AdelicLevel.uniformizerUnit ℚ v) : ℂˣ) : ℂ)‖ = 1) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ x : v.adicCompletion ℚ, x ≠ 0 → ‖charExt ξ x‖ ≤ M := by
  obtain ⟨Mξ, hMξ⟩ := LaurentZetaSlot.exists_bound_charExt_unitShell v ξ hξ
  refine ⟨max Mξ 0, le_max_right _ _, fun x hx => ?_⟩
  obtain ⟨j, hj⟩ := LaurentZetaSlot.exists_mem_shell v hx
  refine (LaurentZetaSlot.norm_charExt_le_of_mem_shell v ξ hMξ hj).trans ?_
  rw [h1, one_zpow, one_mul]
  exact le_max_left _ _

private noncomputable def ballInd (B : ℝ) (t : v.adicCompletion ℚ) : ℂ :=
  if (modulus t : ℝ) ≤ B then 1 else 0

private theorem ballInd_eq_one {B : ℝ} {t : v.adicCompletion ℚ} (h : (modulus t : ℝ) ≤ B) : ballInd v B t = 1 := by
  simp only [ballInd, if_pos h]

private theorem ballInd_eq_zero {B : ℝ} {t : v.adicCompletion ℚ} (h : ¬ (modulus t : ℝ) ≤ B) :
    ballInd v B t = 0 := by
  simp only [ballInd, if_neg h]

private theorem norm_ballInd_le_one (B : ℝ) (t : v.adicCompletion ℚ) : ‖ballInd v B t‖ ≤ 1 := by
  by_cases h : (modulus t : ℝ) ≤ B
  · rw [ballInd_eq_one v h]
    exact norm_one.le
  · rw [ballInd_eq_zero v h, norm_zero]
    exact zero_le_one

private theorem exists_integrable_modulus_rpow_le (α : ℝ) (hα : 0 < α) (B : ℝ) :
    ∃ g : v.adicCompletion ℚ → ℝ, Integrable g (mulMeasure (selfDualHaarAt ℚ v)) ∧ (∀ x, 0 ≤ g x) ∧
      ∀ x : v.adicCompletion ℚ, x ≠ 0 → (modulus x : ℝ) ≤ B → (modulus x : ℝ) ^ α ≤ g x := by
  have h1 : IsLocallyConstant ⇑(1 : (v.adicCompletion ℚ)ˣ →* ℂˣ) := by
    have hfun : ⇑(1 : (v.adicCompletion ℚ)ˣ →* ℂˣ) = fun _ => (1 : ℂˣ) := rfl
    rw [hfun]
    exact IsLocallyConstant.const 1
  have hφ : ∀ t : v.adicCompletion ℚ, t ≠ 0 → ∀ᶠ t' in nhds t, ballInd v B t' = ballInd v B t := by
    intro t ht
    refine (eventually_valued_eq v ht).mono fun t' ht' => ?_
    have hm : modulus t' = modulus t := (modulus_eq_of_valued_eq v ht ht'.symm).symm
    simp only [ballInd, hm]
  have hφB : ∃ B' : ℝ, ∀ t : v.adicCompletion ℚ, B' < (modulus t : ℝ) → ballInd v B t = 0 :=
    ⟨B, fun t ht => ballInd_eq_zero v (not_le.mpr ht)⟩
  have hgeom : LaurentZetaSlot.GeomBoundFrom v (ballInd v B) 0 1 1 := fun j _ x _ => by
    rw [one_zpow, mul_one]
    exact norm_ballInd_le_one v B x
  have hs : (1 : ℝ) * ‖((1 : (v.adicCompletion ℚ)ˣ →* ℂˣ) (NumberField.AdelicLevel.uniformizerUnit ℚ v) : ℂ)‖ *
      (Ideal.absNorm v.asIdeal : ℝ) ^ (-(α : ℂ).re) < 1 := by
    simp only [MonoidHom.one_apply, Units.val_one, norm_one, mul_one, one_mul, Complex.ofReal_re]
    exact Real.rpow_lt_one_of_one_lt_of_neg (one_lt_absNorm_real v) (neg_lt_zero.mpr hα)
  have hF := LaurentZetaSlot.integrable_of_geomBoundFrom v 1 h1 hφ hφB one_pos hgeom (α : ℂ) hs
  refine ⟨_, hF.norm, fun x => norm_nonneg _, fun x hx hxB => ?_⟩
  have hmx : (0 : ℝ) < (modulus x : ℝ) := NNReal.coe_pos.mpr (modulus_pos hx)
  have hgx : ‖ballInd v B x * charExt (1 : (v.adicCompletion ℚ)ˣ →* ℂˣ) x * ((modulus x : ℝ) : ℂ) ^ (α : ℂ)‖ =
      (modulus x : ℝ) ^ α := by
    rw [ballInd_eq_one v hxB, charExt_of_ne_zero _ hx, MonoidHom.one_apply, Units.val_one, mul_one, one_mul,
      Complex.norm_cpow_eq_rpow_re_of_pos hmx, Complex.ofReal_re]
  exact hgx.ge

end InnerDominantBounds
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_tendsto_setIntegral_annulus_setIntegral_ball_jacquetWindow_sub_jacquetValue.LaurentZetaSlot"

end LanglandsTunnell.CubicInduction
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_tendsto_setIntegral_annulus_setIntegral_ball_jacquetWindow_sub_jacquetValue.LaurentZetaSlot"
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_tendsto_setIntegral_annulus_setIntegral_ball_jacquetWindow_sub_jacquetValue.LaurentZetaSlot"
end Part24
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_tendsto_setIntegral_annulus_setIntegral_ball_jacquetWindow_sub_jacquetValue.LaurentZetaSlot"

section Part25

set_option autoImplicit false

open MeasureTheory
open IsDedekindDomain
open NumberField
p2m_open "LanglandsTunnell.TateLocal P2MW.S_LanglandsTunnell_CubicInduction_tendsto_setIntegral_annulus_setIntegral_ball_jacquetWindow_sub_jacquetValue.LanglandsTunnell.TateLocal"
open NumberField.StandardAddChar
open scoped NNReal ENNReal Pointwise

attribute [local instance] LanglandsTunnell.TateLocal.localBorel
attribute [local instance] LanglandsTunnell.TateLocal.borelSpace_localBorel

namespace LanglandsTunnell
p2m_export "LanglandsTunnell" "TateLocal.localBorel TateLocal.borelSpace_localBorel TateLocal.integersPositiveCompacts TateLocal.coe_integersPositiveCompacts"
namespace CubicInduction
p2m_export "LanglandsTunnell.CubicInduction" "unipotentBall3 mem_unipotentBall3_iff jacquetHaar3 jacquetTruncated3 jacquetLevel jacquetValue jacquetTruncated3_eq_jacquetValue bigCell3 mem_bigCell3_iff cellSectionOf cellSectionOf_apply_of_mem cellSectionOf_apply_of_notMem cellSectionOf_upperUnipotent3_mul cellSectionOf_diagonal3_mul principalSeries3 gl3Entry cornerEntry lowerMinor outerMinor gl3Det gl3Det_ne_zero cellRatio cellValue antidiagonal3 antidiagonal3_coe eventually_valued_eq eventually_valued_lt eventually_norm_eq eventually_charExt_eq continuous_gl3Entry continuous_cornerEntry continuous_lowerMinor continuous_outerMinor continuous_gl3Det exists_bottom_entry_ne_zero_of_cornerEntry_eq_zero outerMinor_ne_zero_of_lowerMinor_eq_zero gl3AmbientRightTranslate gl3AmbientRightTranslate_apply transposeInv3 upperUnipotent3 upperUnipotent3_coe embedMat2 iotaGL coe_iotaGL LocalGL3 diagUnitGL2 coe_diagUnitGL2 lowerUnipotent21 longWeyl3 longWeyl3_coe weylPrime3 weylPrime3_coe transposeInv3_weylPrime3 transposeInv3_lowerUnipotent21 exists_forall_le_integrableOn_and_jacquetTruncated3_eq_of_cellSectionOf exists_forall_gl3AmbientRightTranslate_eq_of_mem_principalSeries3"
p2m_open "LanglandsTunnell.CubicInduction LanglandsTunnell"

variable (v : HeightOneSpectrum (𝓞 ℚ))

section GaussBalls

private theorem measure_setOf_valued_le (r : ℤ) :
    selfDualHaarAt ℚ v {y : v.adicCompletion ℚ | Valued.v y ≤ WithZero.exp r} =
      (((Ideal.absNorm v.asIdeal : ℝ≥0) ^ r : ℝ≥0) : ℝ≥0∞) *
        selfDualHaarAt ℚ v (v.adicCompletionIntegers ℚ : Set (v.adicCompletion ℚ)) := by
  set ϖ : (v.adicCompletion ℚ)ˣ := NumberField.AdelicLevel.uniformizerUnit ℚ v ^ (-r) with hϖ
  have hvϖ : Valued.v (ϖ : v.adicCompletion ℚ) = WithZero.exp r := by
    rw [hϖ, LaurentZetaSlot.valued_uniformizerUnit_zpow, neg_neg]
  have hmem : (ϖ : v.adicCompletion ℚ) ∈ LaurentZetaSlot.shell v (-r) := by
    show Valued.v (ϖ : v.adicCompletion ℚ) = WithZero.exp (-(-r))
    rw [hvϖ, neg_neg]
  have hset : {y : v.adicCompletion ℚ | Valued.v y ≤ WithZero.exp r} =
      ϖ • (v.adicCompletionIntegers ℚ : Set (v.adicCompletion ℚ)) := by
    ext y
    rw [Set.mem_setOf_eq, Set.mem_smul_set_iff_inv_smul_mem, Units.smul_def, smul_eq_mul, SetLike.mem_coe,
      HeightOneSpectrum.mem_adicCompletionIntegers, map_mul, Units.val_inv_eq_inv_val, map_inv₀, hvϖ,
      inv_mul_le_iff₀ WithZero.exp_pos, mul_one]
  have hs := selfDualHaarAt_smul_set ℚ v ϖ (v.adicCompletionIntegers ℚ : Set (v.adicCompletion ℚ))
  rw [hset, hs, LaurentZetaSlot.modulus_eq_of_mem_shell v hmem, neg_neg]

variable (η : (v.adicCompletion ℚ)ˣ →* ℂˣ)

private theorem integral_eq_zero_of_forall_apply_eq_const_mul {X : Type*} [MeasurableSpace X] {μ : Measure X}
    (e : X ≃ᵐ X) (he : Measure.map e μ = μ) {g : X → ℂ} {κ : ℂ} (hκ : κ ≠ 1) (h : ∀ s, g (e s) = κ * g s) :
    ∫ s, g s ∂μ = 0 := by
  have h₁ : ∫ s, g (e s) ∂μ = ∫ s, g s ∂μ := by
    rw [← integral_map_equiv e g, he]
  have h₂ : ∫ s, g (e s) ∂μ = κ * ∫ s, g s ∂μ := by
    simp_rw [h]
    exact integral_const_mul _ _
  have h₃ : (κ - 1) * ∫ s, g s ∂μ = 0 := by
    rw [sub_mul, one_mul, ← h₂, h₁, sub_self]
  exact (mul_eq_zero.mp h₃).resolve_left (sub_ne_zero.mpr hκ)

end GaussBalls
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_tendsto_setIntegral_annulus_setIntegral_ball_jacquetWindow_sub_jacquetValue.LaurentZetaSlot"

end LanglandsTunnell.CubicInduction
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_tendsto_setIntegral_annulus_setIntegral_ball_jacquetWindow_sub_jacquetValue.LaurentZetaSlot"
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_tendsto_setIntegral_annulus_setIntegral_ball_jacquetWindow_sub_jacquetValue.LaurentZetaSlot"
end Part25
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_tendsto_setIntegral_annulus_setIntegral_ball_jacquetWindow_sub_jacquetValue.LaurentZetaSlot"

section Part26

set_option autoImplicit false

open MeasureTheory
open IsDedekindDomain
open NumberField
p2m_open "LanglandsTunnell.TateLocal P2MW.S_LanglandsTunnell_CubicInduction_tendsto_setIntegral_annulus_setIntegral_ball_jacquetWindow_sub_jacquetValue.LanglandsTunnell.TateLocal"
open NumberField.StandardAddChar
open scoped NNReal ENNReal

attribute [local instance] LanglandsTunnell.TateLocal.localBorel
attribute [local instance] LanglandsTunnell.TateLocal.borelSpace_localBorel

namespace LanglandsTunnell
p2m_export "LanglandsTunnell" "TateLocal.localBorel TateLocal.borelSpace_localBorel TateLocal.integersPositiveCompacts TateLocal.coe_integersPositiveCompacts"
namespace CubicInduction
p2m_export "LanglandsTunnell.CubicInduction" "unipotentBall3 mem_unipotentBall3_iff jacquetHaar3 jacquetTruncated3 jacquetLevel jacquetValue jacquetTruncated3_eq_jacquetValue bigCell3 mem_bigCell3_iff cellSectionOf cellSectionOf_apply_of_mem cellSectionOf_apply_of_notMem cellSectionOf_upperUnipotent3_mul cellSectionOf_diagonal3_mul principalSeries3 gl3Entry cornerEntry lowerMinor outerMinor gl3Det gl3Det_ne_zero cellRatio cellValue antidiagonal3 antidiagonal3_coe eventually_valued_eq eventually_valued_lt eventually_norm_eq eventually_charExt_eq continuous_gl3Entry continuous_cornerEntry continuous_lowerMinor continuous_outerMinor continuous_gl3Det exists_bottom_entry_ne_zero_of_cornerEntry_eq_zero outerMinor_ne_zero_of_lowerMinor_eq_zero gl3AmbientRightTranslate gl3AmbientRightTranslate_apply transposeInv3 upperUnipotent3 upperUnipotent3_coe embedMat2 iotaGL coe_iotaGL LocalGL3 diagUnitGL2 coe_diagUnitGL2 lowerUnipotent21 longWeyl3 longWeyl3_coe weylPrime3 weylPrime3_coe transposeInv3_weylPrime3 transposeInv3_lowerUnipotent21 exists_forall_le_integrableOn_and_jacquetTruncated3_eq_of_cellSectionOf exists_forall_gl3AmbientRightTranslate_eq_of_mem_principalSeries3"
p2m_open "LanglandsTunnell.CubicInduction LanglandsTunnell"

variable (v : HeightOneSpectrum (𝓞 ℚ))

private noncomputable def rv (ρ : WithZero (Multiplicative ℤ)) : ℝ :=
  if ρ = 0 then 0 else (Ideal.absNorm v.asIdeal : ℝ) ^ (WithZero.log ρ)

private theorem absNorm_pos : (0 : ℝ) < (Ideal.absNorm v.asIdeal : ℝ) := zero_lt_one.trans (one_lt_absNorm_real v)

private theorem rv_exp (n : ℤ) : rv v (WithZero.exp n) = (Ideal.absNorm v.asIdeal : ℝ) ^ n := by
  rw [rv, if_neg WithZero.exp_ne_zero, WithZero.log_exp]

private theorem rv_zero : rv v 0 = 0 := by
  rw [rv, if_pos rfl]

private theorem rv_mul (ρ₁ ρ₂ : WithZero (Multiplicative ℤ)) : rv v (ρ₁ * ρ₂) = rv v ρ₁ * rv v ρ₂ := by
  rcases eq_or_ne ρ₁ 0 with rfl | h₁
  · rw [zero_mul, rv_zero, zero_mul]
  rcases eq_or_ne ρ₂ 0 with rfl | h₂
  · rw [mul_zero, rv_zero, mul_zero]
  rw [rv, rv, rv, if_neg (mul_ne_zero h₁ h₂), if_neg h₁, if_neg h₂, WithZero.log_mul h₁ h₂,
    zpow_add₀ (absNorm_pos v).ne']

private theorem rv_le_rv_iff {ρ₁ ρ₂ : WithZero (Multiplicative ℤ)} (h₁ : ρ₁ ≠ 0) (h₂ : ρ₂ ≠ 0) :
    rv v ρ₁ ≤ rv v ρ₂ ↔ ρ₁ ≤ ρ₂ := by
  rw [rv, rv, if_neg h₁, if_neg h₂, zpow_le_zpow_iff_right₀ (one_lt_absNorm_real v), WithZero.log_le_log h₁ h₂]

private theorem rv_lt_rv_iff {ρ₁ ρ₂ : WithZero (Multiplicative ℤ)} (h₁ : ρ₁ ≠ 0) (h₂ : ρ₂ ≠ 0) :
    rv v ρ₁ < rv v ρ₂ ↔ ρ₁ < ρ₂ := by
  rw [rv, rv, if_neg h₁, if_neg h₂, zpow_lt_zpow_iff_right₀ (one_lt_absNorm_real v), WithZero.log_lt_log h₁ h₂]

private theorem rv_valued {x : v.adicCompletion ℚ} (hx : x ≠ 0) : rv v (Valued.v x) = (modulus x : ℝ) := by
  obtain ⟨j, hj⟩ := LaurentZetaSlot.exists_mem_shell v hx
  have hvx : Valued.v x = WithZero.exp (-j) := hj
  rw [hvx, rv_exp, LaurentZetaSlot.coe_modulus_eq_of_mem_shell v hj]

private theorem valued_ne_zero {x : v.adicCompletion ℚ} (hx : x ≠ 0) : Valued.v x ≠ 0 :=
  (Valuation.ne_zero_iff _).mpr hx

section Assembly

variable (ν : Fin 3 → ((v.adicCompletion ℚ)ˣ →* ℂˣ)) (Φ : (Fin 3 → v.adicCompletion ℚ) → ℂ)
variable (χ : (v.adicCompletion ℚ)ˣ →* ℂˣ) (s : ℂ)

end Assembly
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_tendsto_setIntegral_annulus_setIntegral_ball_jacquetWindow_sub_jacquetValue.LaurentZetaSlot"

end LanglandsTunnell.CubicInduction
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_tendsto_setIntegral_annulus_setIntegral_ball_jacquetWindow_sub_jacquetValue.LaurentZetaSlot"
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_tendsto_setIntegral_annulus_setIntegral_ball_jacquetWindow_sub_jacquetValue.LaurentZetaSlot"
end Part26
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_tendsto_setIntegral_annulus_setIntegral_ball_jacquetWindow_sub_jacquetValue.LaurentZetaSlot"

section Part28

set_option autoImplicit false

open MeasureTheory
open IsDedekindDomain
open NumberField
p2m_open "LanglandsTunnell.TateLocal P2MW.S_LanglandsTunnell_CubicInduction_tendsto_setIntegral_annulus_setIntegral_ball_jacquetWindow_sub_jacquetValue.LanglandsTunnell.TateLocal"
open NumberField.StandardAddChar

namespace LanglandsTunnell
p2m_export "LanglandsTunnell" "TateLocal.localBorel TateLocal.borelSpace_localBorel TateLocal.integersPositiveCompacts TateLocal.coe_integersPositiveCompacts"
namespace CubicInduction
p2m_export "LanglandsTunnell.CubicInduction" "unipotentBall3 mem_unipotentBall3_iff jacquetHaar3 jacquetTruncated3 jacquetLevel jacquetValue jacquetTruncated3_eq_jacquetValue bigCell3 mem_bigCell3_iff cellSectionOf cellSectionOf_apply_of_mem cellSectionOf_apply_of_notMem cellSectionOf_upperUnipotent3_mul cellSectionOf_diagonal3_mul principalSeries3 gl3Entry cornerEntry lowerMinor outerMinor gl3Det gl3Det_ne_zero cellRatio cellValue antidiagonal3 antidiagonal3_coe eventually_valued_eq eventually_valued_lt eventually_norm_eq eventually_charExt_eq continuous_gl3Entry continuous_cornerEntry continuous_lowerMinor continuous_outerMinor continuous_gl3Det exists_bottom_entry_ne_zero_of_cornerEntry_eq_zero outerMinor_ne_zero_of_lowerMinor_eq_zero gl3AmbientRightTranslate gl3AmbientRightTranslate_apply transposeInv3 upperUnipotent3 upperUnipotent3_coe embedMat2 iotaGL coe_iotaGL LocalGL3 diagUnitGL2 coe_diagUnitGL2 lowerUnipotent21 longWeyl3 longWeyl3_coe weylPrime3 weylPrime3_coe transposeInv3_weylPrime3 transposeInv3_lowerUnipotent21 exists_forall_le_integrableOn_and_jacquetTruncated3_eq_of_cellSectionOf exists_forall_gl3AmbientRightTranslate_eq_of_mem_principalSeries3"
p2m_open "LanglandsTunnell.CubicInduction LanglandsTunnell"

section DualPointwise

variable (v : HeightOneSpectrum (𝓞 ℚ))
variable (ν : Fin 3 → ((v.adicCompletion ℚ)ˣ →* ℂˣ)) (Φ : (Fin 3 → v.adicCompletion ℚ) → ℂ)

private theorem charExt_mul_char (η₁ η₂ : (v.adicCompletion ℚ)ˣ →* ℂˣ) (y : v.adicCompletion ℚ) :
    charExt (η₁ * η₂) y = charExt η₁ y * charExt η₂ y := by
  by_cases hy : y = 0
  · subst hy
    simp
  · rw [charExt_of_ne_zero _ hy, charExt_of_ne_zero _ hy, charExt_of_ne_zero _ hy, MonoidHom.mul_apply,
      Units.val_mul]

private theorem charExt_inv_char (η : (v.adicCompletion ℚ)ˣ →* ℂˣ) (y : v.adicCompletion ℚ) :
    charExt η⁻¹ y = (charExt η y)⁻¹ := by
  by_cases hy : y = 0
  · subst hy
    simp
  · rw [charExt_of_ne_zero _ hy, charExt_of_ne_zero _ hy, MonoidHom.inv_apply, Units.val_inv_eq_inv_val]

private theorem charExt_inv_arg (η : (v.adicCompletion ℚ)ˣ →* ℂˣ) (y : v.adicCompletion ℚ) :
    charExt η y⁻¹ = (charExt η y)⁻¹ := by
  by_cases hy : y = 0
  · subst hy
    simp
  · have hu : y⁻¹ = (((Units.mk0 y hy)⁻¹ : (v.adicCompletion ℚ)ˣ) : v.adicCompletion ℚ) := by simp
    rw [hu, charExt_coe_units, map_inv, Units.val_inv_eq_inv_val, charExt_of_ne_zero _ hy]

private theorem charExt_div_arg (η : (v.adicCompletion ℚ)ˣ →* ℂˣ) (y z : v.adicCompletion ℚ) :
    charExt η (y / z) = charExt η y * (charExt η z)⁻¹ := by
  rw [div_eq_mul_inv, charExt_mul ℚ v, charExt_inv_arg]

private theorem charExt_units_inv (η : (v.adicCompletion ℚ)ˣ →* ℂˣ) (a : (v.adicCompletion ℚ)ˣ) :
    charExt η ((a : v.adicCompletion ℚ)⁻¹) = ((η a : ℂˣ) : ℂ)⁻¹ := by
  rw [charExt_inv_arg, charExt_coe_units]

private theorem cellSectionOf_dualCellPoint (α β γ : v.adicCompletion ℚ) (a : (v.adicCompletion ℚ)ˣ)
    (x : v.adicCompletion ℚ) :
    cellSectionOf v ν Φ (dualCellPoint v α β γ a x) =
      (((ν 0) a : ℂˣ) : ℂ)⁻¹ * ((‖(a : v.adicCompletion ℚ)‖⁻¹ : ℝ) : ℂ) *
        (charExt (ν 1 * (ν 0)⁻¹) (1 - β / (a : v.adicCompletion ℚ) * x) *
            charExt (ν 2 * (ν 1)⁻¹) (α - γ / (a : v.adicCompletion ℚ) * x) *
            ((‖1 - β / (a : v.adicCompletion ℚ) * x‖⁻¹ * ‖α - γ / (a : v.adicCompletion ℚ) * x‖⁻¹ : ℝ) : ℂ) *
            Φ ![(α - γ / (a : v.adicCompletion ℚ) * x)⁻¹,
              γ / (a : v.adicCompletion ℚ) / (α - γ / (a : v.adicCompletion ℚ) * x),
              (γ / (a : v.adicCompletion ℚ) - α * (β / (a : v.adicCompletion ℚ))) /
                (1 - β / (a : v.adicCompletion ℚ) * x)]) := by
  have h₁ : γ * x / (a : v.adicCompletion ℚ) = γ / (a : v.adicCompletion ℚ) * x := by ring
  have h₂ : β * x / (a : v.adicCompletion ℚ) = β / (a : v.adicCompletion ℚ) * x := by ring
  by_cases hc : α - γ / (a : v.adicCompletion ℚ) * x = 0
  · have hnot : dualCellPoint v α β γ a x ∉ bigCell3 v := by
      rw [mem_bigCell3_iff, cornerEntry_dualCellPoint, h₁, hc]
      exact fun h => h.1 rfl
    rw [cellSectionOf_apply_of_notMem v ν Φ hnot, hc]
    simp
  by_cases hl : 1 - β / (a : v.adicCompletion ℚ) * x = 0
  · have hnot : dualCellPoint v α β γ a x ∉ bigCell3 v := by
      rw [mem_bigCell3_iff, lowerMinor_dualCellPoint, h₂, hl]
      exact fun h => h.2 rfl
    rw [cellSectionOf_apply_of_notMem v ν Φ hnot, hl]
    simp
  have hmem : dualCellPoint v α β γ a x ∈ bigCell3 v := by
    rw [mem_bigCell3_iff, cornerEntry_dualCellPoint, lowerMinor_dualCellPoint, h₁, h₂]
    exact ⟨hc, hl⟩
  have h₃ : 1 / (α - γ / (a : v.adicCompletion ℚ) * x) = (α - γ / (a : v.adicCompletion ℚ) * x)⁻¹ := by ring
  have h₄ : γ * (a : v.adicCompletion ℚ)⁻¹ = γ / (a : v.adicCompletion ℚ) := by ring
  have h₅ : (γ - α * β) / (a : v.adicCompletion ℚ) =
      γ / (a : v.adicCompletion ℚ) - α * (β / (a : v.adicCompletion ℚ)) := by ring
  rw [cellSectionOf_apply_of_mem v ν Φ hmem, cellValue_dualCellPoint, cellRatio_dualCellPoint, h₁, h₂, h₃, h₄,
    h₅]
  simp only [charExt_div_arg, charExt_units_inv, charExt_mul_char, charExt_inv_char, norm_div, norm_inv]
  push_cast
  ring

end DualPointwise
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_tendsto_setIntegral_annulus_setIntegral_ball_jacquetWindow_sub_jacquetValue.LaurentZetaSlot"

end LanglandsTunnell.CubicInduction
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_tendsto_setIntegral_annulus_setIntegral_ball_jacquetWindow_sub_jacquetValue.LaurentZetaSlot"
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_tendsto_setIntegral_annulus_setIntegral_ball_jacquetWindow_sub_jacquetValue.LaurentZetaSlot"
end Part28
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_tendsto_setIntegral_annulus_setIntegral_ball_jacquetWindow_sub_jacquetValue.LaurentZetaSlot"

section Part29
set_option autoImplicit false

open MeasureTheory
open IsDedekindDomain
open NumberField
p2m_open "LanglandsTunnell.TateLocal P2MW.S_LanglandsTunnell_CubicInduction_tendsto_setIntegral_annulus_setIntegral_ball_jacquetWindow_sub_jacquetValue.LanglandsTunnell.TateLocal"
open NumberField.StandardAddChar
open scoped NNReal ENNReal

attribute [local instance] LanglandsTunnell.TateLocal.localBorel
attribute [local instance] LanglandsTunnell.TateLocal.borelSpace_localBorel

namespace LanglandsTunnell
p2m_export "LanglandsTunnell" "TateLocal.localBorel TateLocal.borelSpace_localBorel TateLocal.integersPositiveCompacts TateLocal.coe_integersPositiveCompacts"
namespace CubicInduction
p2m_export "LanglandsTunnell.CubicInduction" "unipotentBall3 mem_unipotentBall3_iff jacquetHaar3 jacquetTruncated3 jacquetLevel jacquetValue jacquetTruncated3_eq_jacquetValue bigCell3 mem_bigCell3_iff cellSectionOf cellSectionOf_apply_of_mem cellSectionOf_apply_of_notMem cellSectionOf_upperUnipotent3_mul cellSectionOf_diagonal3_mul principalSeries3 gl3Entry cornerEntry lowerMinor outerMinor gl3Det gl3Det_ne_zero cellRatio cellValue antidiagonal3 antidiagonal3_coe eventually_valued_eq eventually_valued_lt eventually_norm_eq eventually_charExt_eq continuous_gl3Entry continuous_cornerEntry continuous_lowerMinor continuous_outerMinor continuous_gl3Det exists_bottom_entry_ne_zero_of_cornerEntry_eq_zero outerMinor_ne_zero_of_lowerMinor_eq_zero gl3AmbientRightTranslate gl3AmbientRightTranslate_apply transposeInv3 upperUnipotent3 upperUnipotent3_coe embedMat2 iotaGL coe_iotaGL LocalGL3 diagUnitGL2 coe_diagUnitGL2 lowerUnipotent21 longWeyl3 longWeyl3_coe weylPrime3 weylPrime3_coe transposeInv3_weylPrime3 transposeInv3_lowerUnipotent21 exists_forall_le_integrableOn_and_jacquetTruncated3_eq_of_cellSectionOf exists_forall_gl3AmbientRightTranslate_eq_of_mem_principalSeries3"
p2m_open "LanglandsTunnell.CubicInduction LanglandsTunnell"

variable (v : HeightOneSpectrum (𝓞 ℚ))

section WedgeNear

variable (ν : Fin 3 → ((v.adicCompletion ℚ)ˣ →* ℂˣ)) (Φ : (Fin 3 → v.adicCompletion ℚ) → ℂ)

private theorem norm_eq_rv {x : v.adicCompletion ℚ} (hx : x ≠ 0) : ‖x‖ = rv v (Valued.v x) := by
  rw [rv_valued v hx, modulus_real_eq_norm]

private theorem valued_lt_of_norm_lt {x : v.adicCompletion ℚ} {m : ℤ} (h : ‖x‖ < (Ideal.absNorm v.asIdeal : ℝ) ^ m) :
    Valued.v x < WithZero.exp m := by
  rcases eq_or_ne x 0 with rfl | hx
  · rw [map_zero]
    exact WithZero.exp_pos
  · refine (rv_lt_rv_iff v (valued_ne_zero v hx) WithZero.exp_ne_zero).mp ?_
    rwa [rv_exp, ← norm_eq_rv v hx]

private theorem valued_le_exp_of_lt_exp_succ {y : v.adicCompletion ℚ} {m : ℤ}
    (h : Valued.v y < WithZero.exp (m + 1)) : Valued.v y ≤ WithZero.exp m := by
  rcases eq_or_ne y 0 with rfl | hy
  · rw [map_zero]
    exact zero_le'
  · obtain ⟨j, hj⟩ := LaurentZetaSlot.exists_mem_shell v hy
    have hvy : Valued.v y = WithZero.exp (-j) := hj
    rw [hvy] at h ⊢
    have hlt := WithZero.exp_lt_exp.mp h
    exact WithZero.exp_le_exp.mpr (by omega)

private theorem wedge_norm {c : ℤ} {β γ : v.adicCompletion ℚ} (hw : WithZero.exp c * Valued.v β < Valued.v γ) :
    γ ≠ 0 ∧ (Ideal.absNorm v.asIdeal : ℝ) ^ c * ‖β‖ < ‖γ‖ := by
  have hγ : γ ≠ 0 := by
    rintro rfl
    rw [map_zero] at hw
    exact (not_lt_of_ge zero_le') hw
  refine ⟨hγ, ?_⟩
  rcases eq_or_ne β 0 with rfl | hβ
  · rw [norm_zero, mul_zero]
    exact norm_pos_iff.mpr hγ
  · have h := (rv_lt_rv_iff v (mul_ne_zero WithZero.exp_ne_zero (valued_ne_zero v hβ)) (valued_ne_zero v hγ)).mpr hw
    rwa [rv_mul, rv_exp, ← norm_eq_rv v hβ, ← norm_eq_rv v hγ] at h

private theorem norm_slot_num {c : ℤ} {α β γ : v.adicCompletion ℚ} (a : (v.adicCompletion ℚ)ˣ)
    (hball : Valued.v α ≤ WithZero.exp c) (hw : WithZero.exp c * Valued.v β < Valued.v γ) :
    ‖γ / (a : v.adicCompletion ℚ) - α * (β / (a : v.adicCompletion ℚ))‖ = ‖γ‖ / ‖(a : v.adicCompletion ℚ)‖ := by
  obtain ⟨hγ, hwn⟩ := wedge_norm v hw
  have hapos : 0 < ‖(a : v.adicCompletion ℚ)‖ := norm_pos_iff.mpr a.ne_zero
  have hγa : γ / (a : v.adicCompletion ℚ) ≠ 0 := div_ne_zero hγ a.ne_zero

  have hlt : Valued.v (α * (β / (a : v.adicCompletion ℚ))) < Valued.v (γ / (a : v.adicCompletion ℚ)) := by
    rcases eq_or_ne (α * (β / (a : v.adicCompletion ℚ))) 0 with h0 | hne
    · rw [h0, map_zero]
      exact zero_lt_iff.mpr (valued_ne_zero v hγa)
    · refine (rv_lt_rv_iff v (valued_ne_zero v hne) (valued_ne_zero v hγa)).mp ?_
      rw [← norm_eq_rv v hne, ← norm_eq_rv v hγa, norm_mul, norm_div, norm_div, ← mul_div_assoc]
      refine div_lt_div_of_pos_right ?_ hapos
      calc ‖α‖ * ‖β‖ ≤ (Ideal.absNorm v.asIdeal : ℝ) ^ c * ‖β‖ :=
            mul_le_mul_of_nonneg_right (norm_le_zpow_of_valued_le v hball) (norm_nonneg _)
        _ < ‖γ‖ := hwn
  have hval := Valuation.map_sub_eq_of_lt_left _ hlt
  have hsub : γ / (a : v.adicCompletion ℚ) - α * (β / (a : v.adicCompletion ℚ)) ≠ 0 := by
    intro h0
    rw [h0, map_zero] at hval
    exact valued_ne_zero v hγa hval.symm
  rw [norm_eq_rv v hsub, hval, ← norm_eq_rv v hγa, norm_div]

private theorem norm_wedge_integrand {M₁ M₂ MΦ R : ℝ}
    (hM₁ : ∀ y : v.adicCompletion ℚ, y ≠ 0 → ‖charExt (ν 1 * (ν 0)⁻¹) y‖ ≤ M₁)
    (hM₂ : ∀ y : v.adicCompletion ℚ, y ≠ 0 → ‖charExt (ν 2 * (ν 1)⁻¹) y‖ ≤ M₂)
    (hM₁0 : 0 ≤ M₁) (hM₂0 : 0 ≤ M₂) (hMΦ : ∀ q : Fin 3 → v.adicCompletion ℚ, ‖Φ q‖ ≤ MΦ) (hMΦ0 : 0 ≤ MΦ)
    (hR : 0 < R)
    (hsupp : ∀ q : Fin 3 → v.adicCompletion ℚ, Φ q ≠ 0 → ∀ i, ‖q i‖ ≤ R) {c T₀ : ℤ}
    (a : (v.adicCompletion ℚ)ˣ) (x : v.adicCompletion ℚ) {α β γ : v.adicCompletion ℚ}
    (hball : Valued.v α ≤ WithZero.exp c) (hw : WithZero.exp c * Valued.v β < Valued.v γ)
    (hnear : Valued.v (α - γ / (a : v.adicCompletion ℚ) * x) < WithZero.exp T₀) :
    psiLocal ℚ v (-(α + β)) * cellSectionOf v ν Φ (dualCellPoint v α β γ a x) = 0 ∨
      (‖psiLocal ℚ v (-(α + β)) * cellSectionOf v ν Φ (dualCellPoint v α β γ a x)‖ ≤
          ‖((((ν 0) a)⁻¹ : ℂˣ) : ℂ)‖ * (M₁ * M₂ * R * R * MΦ) * ‖γ‖⁻¹ ∧
        ‖γ‖ ≤ R * ‖(a : v.adicCompletion ℚ)‖ * (Ideal.absNorm v.asIdeal : ℝ) ^ T₀) := by
  have _ := hMΦ0
  obtain ⟨hγ, -⟩ := wedge_norm v hw
  have hγpos : 0 < ‖γ‖ := norm_pos_iff.mpr hγ
  have hapos : 0 < ‖(a : v.adicCompletion ℚ)‖ := norm_pos_iff.mpr a.ne_zero
  rw [cellSectionOf_dualCellPoint v ν Φ]
  by_cases hU : α - γ / (a : v.adicCompletion ℚ) * x = 0
  · left
    rw [hU]
    simp
  by_cases hL : (1 : v.adicCompletion ℚ) - β / (a : v.adicCompletion ℚ) * x = 0
  · left
    rw [hL]
    simp
  by_cases hΦ : Φ ![(α - γ / (a : v.adicCompletion ℚ) * x)⁻¹,
      γ / (a : v.adicCompletion ℚ) / (α - γ / (a : v.adicCompletion ℚ) * x),
      (γ / (a : v.adicCompletion ℚ) - α * (β / (a : v.adicCompletion ℚ))) /
        (1 - β / (a : v.adicCompletion ℚ) * x)] = 0
  · left
    rw [hΦ]
    simp
  right
  rw [Units.val_inv_eq_inv_val]
  have hUpos : 0 < ‖α - γ / (a : v.adicCompletion ℚ) * x‖ := norm_pos_iff.mpr hU
  have hLpos : 0 < ‖(1 : v.adicCompletion ℚ) - β / (a : v.adicCompletion ℚ) * x‖ := norm_pos_iff.mpr hL

  have hs0 : ‖α - γ / (a : v.adicCompletion ℚ) * x‖⁻¹ ≤ R := by
    have h := hsupp _ hΦ 0
    simpa using h
  have hs1 : ‖γ‖ / ‖(a : v.adicCompletion ℚ)‖ / ‖α - γ / (a : v.adicCompletion ℚ) * x‖ ≤ R := by
    have h := hsupp _ hΦ 1
    simpa using h
  have hs2 : ‖γ / (a : v.adicCompletion ℚ) - α * (β / (a : v.adicCompletion ℚ))‖ /
      ‖(1 : v.adicCompletion ℚ) - β / (a : v.adicCompletion ℚ) * x‖ ≤ R := by
    have h := hsupp _ hΦ 2
    simpa using h
  rw [norm_slot_num v a hball hw] at hs2

  have hU_le : ‖α - γ / (a : v.adicCompletion ℚ) * x‖ ≤ (Ideal.absNorm v.asIdeal : ℝ) ^ T₀ :=
    norm_le_zpow_of_valued_le v hnear.le
  have hγ_le : ‖γ‖ ≤ R * ‖(a : v.adicCompletion ℚ)‖ * (Ideal.absNorm v.asIdeal : ℝ) ^ T₀ := by
    rw [div_le_iff₀ hUpos, div_le_iff₀ hapos] at hs1
    calc ‖γ‖ ≤ R * ‖α - γ / (a : v.adicCompletion ℚ) * x‖ * ‖(a : v.adicCompletion ℚ)‖ := hs1
      _ ≤ R * (Ideal.absNorm v.asIdeal : ℝ) ^ T₀ * ‖(a : v.adicCompletion ℚ)‖ :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hU_le hR.le) hapos.le
      _ = R * ‖(a : v.adicCompletion ℚ)‖ * (Ideal.absNorm v.asIdeal : ℝ) ^ T₀ := by ring
  refine ⟨?_, hγ_le⟩

  have hL_inv : ‖(1 : v.adicCompletion ℚ) - β / (a : v.adicCompletion ℚ) * x‖⁻¹ ≤
      R * ‖(a : v.adicCompletion ℚ)‖ * ‖γ‖⁻¹ := by
    rw [div_le_iff₀ hLpos, div_le_iff₀ hapos] at hs2

    have hdiv : ‖γ‖ * ‖(1 : v.adicCompletion ℚ) - β / (a : v.adicCompletion ℚ) * x‖⁻¹ ≤
        R * ‖(a : v.adicCompletion ℚ)‖ := by
      rw [← div_eq_mul_inv, div_le_iff₀ hLpos]
      linarith [hs2]
    have hsplit : ‖(1 : v.adicCompletion ℚ) - β / (a : v.adicCompletion ℚ) * x‖⁻¹ =
        ‖γ‖⁻¹ * (‖γ‖ * ‖(1 : v.adicCompletion ℚ) - β / (a : v.adicCompletion ℚ) * x‖⁻¹) := by
      rw [← mul_assoc, inv_mul_cancel₀ hγpos.ne', one_mul]
    calc ‖(1 : v.adicCompletion ℚ) - β / (a : v.adicCompletion ℚ) * x‖⁻¹
        = ‖γ‖⁻¹ * (‖γ‖ * ‖(1 : v.adicCompletion ℚ) - β / (a : v.adicCompletion ℚ) * x‖⁻¹) := hsplit
      _ ≤ ‖γ‖⁻¹ * (R * ‖(a : v.adicCompletion ℚ)‖) := mul_le_mul_of_nonneg_left hdiv (inv_nonneg.mpr hγpos.le)
      _ = R * ‖(a : v.adicCompletion ℚ)‖ * ‖γ‖⁻¹ := by ring

  have hcast_a : ‖((‖(a : v.adicCompletion ℚ)‖⁻¹ : ℝ) : ℂ)‖ = ‖(a : v.adicCompletion ℚ)‖⁻¹ := by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (inv_nonneg.mpr hapos.le)]
  have hcast_LU : ‖((‖(1 : v.adicCompletion ℚ) - β / (a : v.adicCompletion ℚ) * x‖⁻¹ *
      ‖α - γ / (a : v.adicCompletion ℚ) * x‖⁻¹ : ℝ) : ℂ)‖ =
        ‖(1 : v.adicCompletion ℚ) - β / (a : v.adicCompletion ℚ) * x‖⁻¹ *
          ‖α - γ / (a : v.adicCompletion ℚ) * x‖⁻¹ := by
    rw [Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (mul_nonneg (inv_nonneg.mpr (norm_nonneg _)) (inv_nonneg.mpr (norm_nonneg _)))]
  have hcancel : ‖(a : v.adicCompletion ℚ)‖⁻¹ * ‖(a : v.adicCompletion ℚ)‖ = 1 := inv_mul_cancel₀ hapos.ne'

  calc ‖psiLocal ℚ v (-(α + β)) * ((((ν 0) a : ℂˣ) : ℂ)⁻¹ * ((‖(a : v.adicCompletion ℚ)‖⁻¹ : ℝ) : ℂ) *
          (charExt (ν 1 * (ν 0)⁻¹) (1 - β / (a : v.adicCompletion ℚ) * x) *
            charExt (ν 2 * (ν 1)⁻¹) (α - γ / (a : v.adicCompletion ℚ) * x) *
            ((‖1 - β / (a : v.adicCompletion ℚ) * x‖⁻¹ * ‖α - γ / (a : v.adicCompletion ℚ) * x‖⁻¹ : ℝ) : ℂ) *
            Φ ![(α - γ / (a : v.adicCompletion ℚ) * x)⁻¹,
              γ / (a : v.adicCompletion ℚ) / (α - γ / (a : v.adicCompletion ℚ) * x),
              (γ / (a : v.adicCompletion ℚ) - α * (β / (a : v.adicCompletion ℚ))) /
                (1 - β / (a : v.adicCompletion ℚ) * x)]))‖
        = ‖psiLocal ℚ v (-(α + β))‖ * (‖(((ν 0) a : ℂˣ) : ℂ)⁻¹‖ * ‖(a : v.adicCompletion ℚ)‖⁻¹ *
          (‖charExt (ν 1 * (ν 0)⁻¹) (1 - β / (a : v.adicCompletion ℚ) * x)‖ *
            ‖charExt (ν 2 * (ν 1)⁻¹) (α - γ / (a : v.adicCompletion ℚ) * x)‖ *
            (‖(1 : v.adicCompletion ℚ) - β / (a : v.adicCompletion ℚ) * x‖⁻¹ *
              ‖α - γ / (a : v.adicCompletion ℚ) * x‖⁻¹) *
            ‖Φ ![(α - γ / (a : v.adicCompletion ℚ) * x)⁻¹,
              γ / (a : v.adicCompletion ℚ) / (α - γ / (a : v.adicCompletion ℚ) * x),
              (γ / (a : v.adicCompletion ℚ) - α * (β / (a : v.adicCompletion ℚ))) /
                (1 - β / (a : v.adicCompletion ℚ) * x)]‖)) := by
          simp only [norm_mul, hcast_a, hcast_LU]
    _ ≤ 1 * (‖(((ν 0) a : ℂˣ) : ℂ)⁻¹‖ * ‖(a : v.adicCompletion ℚ)‖⁻¹ *
          (M₁ * M₂ * (R * ‖(a : v.adicCompletion ℚ)‖ * ‖γ‖⁻¹ * R) * MΦ)) := by
          refine mul_le_mul (norm_psiLocal_le_one v _) (mul_le_mul_of_nonneg_left ?_ (by positivity))
            (by positivity) zero_le_one
          refine mul_le_mul (mul_le_mul (mul_le_mul (hM₁ _ hL) (hM₂ _ hU) (norm_nonneg _) hM₁0)
            (mul_le_mul hL_inv hs0 (by positivity) (by positivity)) (by positivity) (by positivity))
            (hMΦ _) (norm_nonneg _) (by positivity)
    _ = (‖(a : v.adicCompletion ℚ)‖⁻¹ * ‖(a : v.adicCompletion ℚ)‖) *
          (‖(((ν 0) a : ℂˣ) : ℂ)⁻¹‖ * (M₁ * M₂ * R * R * MΦ) * ‖γ‖⁻¹) := by ring
    _ = ‖(((ν 0) a : ℂˣ) : ℂ)⁻¹‖ * (M₁ * M₂ * R * R * MΦ) * ‖γ‖⁻¹ := by rw [hcancel, one_mul]

private noncomputable def wedgeMajorant (K₀ : ℝ) (n c T₀ : ℤ) (a : (v.adicCompletion ℚ)ˣ) (x : v.adicCompletion ℚ)
    (p : v.adicCompletion ℚ × v.adicCompletion ℚ × v.adicCompletion ℚ) : ℝ≥0∞ :=
  ENNReal.ofReal (K₀ * ‖p.2.2‖⁻¹) * {y : v.adicCompletion ℚ | Valued.v y ≤ WithZero.exp n}.indicator 1 p.2.2 *
    ({y : v.adicCompletion ℚ | Valued.v y ≤ WithZero.exp (-c - 1)}.indicator 1 (p.2.1 / p.2.2) *
      {y : v.adicCompletion ℚ | Valued.v y ≤ WithZero.exp (T₀ - 1)}.indicator 1
        (p.1 + -(p.2.2 / (a : v.adicCompletion ℚ) * x)))

private theorem measurable_wedgeMajorant (K₀ : ℝ) (n c T₀ : ℤ) (a : (v.adicCompletion ℚ)ˣ) (x : v.adicCompletion ℚ) :
    Measurable (wedgeMajorant v K₀ n c T₀ a x) := by
  unfold wedgeMajorant
  have hγ : Measurable fun p : v.adicCompletion ℚ × v.adicCompletion ℚ × v.adicCompletion ℚ => p.2.2 :=
    measurable_snd.snd
  have hβγ : Measurable fun p : v.adicCompletion ℚ × v.adicCompletion ℚ × v.adicCompletion ℚ => p.2.1 / p.2.2 :=
    measurable_snd.fst.div measurable_snd.snd
  have hα : Measurable fun p : v.adicCompletion ℚ × v.adicCompletion ℚ × v.adicCompletion ℚ =>
      p.1 + -(p.2.2 / (a : v.adicCompletion ℚ) * x) :=
    measurable_fst.add ((measurable_snd.snd.div measurable_const).mul measurable_const).neg
  have h₁ : Measurable fun p : v.adicCompletion ℚ × v.adicCompletion ℚ × v.adicCompletion ℚ =>
      ENNReal.ofReal (K₀ * ‖p.2.2‖⁻¹) :=
    ENNReal.measurable_ofReal.comp (hγ.norm.inv.const_mul K₀)
  have h1 : Measurable (1 : v.adicCompletion ℚ → ℝ≥0∞) := measurable_one
  have h₂ := ((h1.indicator (isClosed_valued_le v n).measurableSet).comp hγ)
  have h₃ := ((h1.indicator (isClosed_valued_le v (-c - 1)).measurableSet).comp hβγ)
  have h₄ := ((h1.indicator (isClosed_valued_le v (T₀ - 1)).measurableSet).comp hα)
  exact (h₁.mul h₂).mul (h₃.mul h₄)

private theorem lintegral_indicator_one_comp {s : Set (v.adicCompletion ℚ)} (hs : MeasurableSet s)
    {f : v.adicCompletion ℚ → v.adicCompletion ℚ} (hf : Measurable f) :
    ∫⁻ y, s.indicator (1 : v.adicCompletion ℚ → ℝ≥0∞) (f y) ∂(selfDualHaarAt ℚ v) = selfDualHaarAt ℚ v (f ⁻¹' s) := by
  have h : (fun y => s.indicator (1 : v.adicCompletion ℚ → ℝ≥0∞) (f y)) = (f ⁻¹' s).indicator 1 := by
    funext y
    by_cases hy : f y ∈ s
    · rw [Set.indicator_of_mem hy, Set.indicator_of_mem (show y ∈ f ⁻¹' s from hy), Pi.one_apply, Pi.one_apply]
    · rw [Set.indicator_of_notMem hy, Set.indicator_of_notMem (show y ∉ f ⁻¹' s from hy)]
  rw [h, lintegral_indicator_one (hs.preimage hf)]

private theorem measure_valued_le_eq_ofReal (r : ℤ) :
    selfDualHaarAt ℚ v {y : v.adicCompletion ℚ | Valued.v y ≤ WithZero.exp r} =
      ENNReal.ofReal ((Ideal.absNorm v.asIdeal : ℝ) ^ r) *
        selfDualHaarAt ℚ v (v.adicCompletionIntegers ℚ : Set (v.adicCompletion ℚ)) := by
  rw [measure_setOf_valued_le v, ← ENNReal.ofReal_coe_nnreal, NNReal.coe_zpow, NNReal.coe_natCast]

private theorem measure_preimage_div_valued_le {γ : v.adicCompletion ℚ} (hγ : γ ≠ 0) (c : ℤ) :
    selfDualHaarAt ℚ v ((fun β => β / γ) ⁻¹' {y : v.adicCompletion ℚ | Valued.v y ≤ WithZero.exp (-c - 1)}) =
      ENNReal.ofReal (‖γ‖ * (Ideal.absNorm v.asIdeal : ℝ) ^ (-c - 1)) *
        selfDualHaarAt ℚ v (v.adicCompletionIntegers ℚ : Set (v.adicCompletion ℚ)) := by
  obtain ⟨j, hj⟩ := LaurentZetaSlot.exists_mem_shell v hγ
  have hγn : ‖γ‖ = (Ideal.absNorm v.asIdeal : ℝ) ^ (-j) := by
    rw [← modulus_real_eq_norm, LaurentZetaSlot.coe_modulus_eq_of_mem_shell v hj]
  have hγpos : 0 < ‖γ‖ := norm_pos_iff.mpr hγ
  have hq0 : (0 : ℝ) < (Ideal.absNorm v.asIdeal : ℝ) := absNorm_pos v

  have hset : (fun β => β / γ) ⁻¹' {y : v.adicCompletion ℚ | Valued.v y ≤ WithZero.exp (-c - 1)} =
      {y : v.adicCompletion ℚ | Valued.v y ≤ WithZero.exp (-j + (-c - 1))} := by
    ext β
    simp only [Set.mem_preimage, Set.mem_setOf_eq]
    rcases eq_or_ne β 0 with rfl | hβ
    · simp only [zero_div, map_zero, zero_le']
    · have hβγ : β / γ ≠ 0 := div_ne_zero hβ hγ
      rw [← rv_le_rv_iff v (valued_ne_zero v hβγ) WithZero.exp_ne_zero,
        ← rv_le_rv_iff v (valued_ne_zero v hβ) WithZero.exp_ne_zero, rv_exp, rv_exp, ← norm_eq_rv v hβγ,
        ← norm_eq_rv v hβ, norm_div, hγn, div_le_iff₀ (zpow_pos hq0 _), add_comm (-j) (-c - 1), zpow_add₀ hq0.ne']
  rw [hset, measure_valued_le_eq_ofReal v, hγn, ← zpow_add₀ hq0.ne']

private theorem lintegral_wedgeMajorant_le {K₀ : ℝ} (hK₀ : 0 ≤ K₀) (n c T₀ : ℤ) (a : (v.adicCompletion ℚ)ˣ)
    (x : v.adicCompletion ℚ) :
    ∫⁻ p, wedgeMajorant v K₀ n c T₀ a x p ∂(jacquetHaar3 v) ≤
      ENNReal.ofReal (K₀ * (Ideal.absNorm v.asIdeal : ℝ) ^ (-c - 1)) *
          selfDualHaarAt ℚ v (v.adicCompletionIntegers ℚ : Set (v.adicCompletion ℚ)) *
          selfDualHaarAt ℚ v {y : v.adicCompletion ℚ | Valued.v y ≤ WithZero.exp (T₀ - 1)} *
        (ENNReal.ofReal ((Ideal.absNorm v.asIdeal : ℝ) ^ n) *
          selfDualHaarAt ℚ v (v.adicCompletionIntegers ℚ : Set (v.adicCompletion ℚ))) := by
  haveI := isAddHaarMeasure_selfDualHaarAt ℚ v
  haveI : SFinite (selfDualHaarAt ℚ v) := sFinite_selfDualHaarAt ℚ v
  have hBn : MeasurableSet {y : v.adicCompletion ℚ | Valued.v y ≤ WithZero.exp n} :=
    (isClosed_valued_le v n).measurableSet
  have hBc : MeasurableSet {y : v.adicCompletion ℚ | Valued.v y ≤ WithZero.exp (-c - 1)} :=
    (isClosed_valued_le v (-c - 1)).measurableSet
  have hBT : MeasurableSet {y : v.adicCompletion ℚ | Valued.v y ≤ WithZero.exp (T₀ - 1)} :=
    (isClosed_valued_le v (T₀ - 1)).measurableSet

  have hinner : ∀ y : v.adicCompletion ℚ × v.adicCompletion ℚ,
      ∫⁻ α, wedgeMajorant v K₀ n c T₀ a x (α, y) ∂(selfDualHaarAt ℚ v) =
        ENNReal.ofReal (K₀ * ‖y.2‖⁻¹) * {z : v.adicCompletion ℚ | Valued.v z ≤ WithZero.exp n}.indicator 1 y.2 *
            {z : v.adicCompletion ℚ | Valued.v z ≤ WithZero.exp (-c - 1)}.indicator 1 (y.1 / y.2) *
          selfDualHaarAt ℚ v {z : v.adicCompletion ℚ | Valued.v z ≤ WithZero.exp (T₀ - 1)} := by
    intro y
    have hg : Measurable fun α : v.adicCompletion ℚ =>
        {z : v.adicCompletion ℚ | Valued.v z ≤ WithZero.exp (T₀ - 1)}.indicator (1 : v.adicCompletion ℚ → ℝ≥0∞)
          (α + -(y.2 / (a : v.adicCompletion ℚ) * x)) :=
      (measurable_one.indicator hBT).comp (measurable_add_const _)
    have hre : ∀ α : v.adicCompletion ℚ, wedgeMajorant v K₀ n c T₀ a x (α, y) =
        (ENNReal.ofReal (K₀ * ‖y.2‖⁻¹) * {z : v.adicCompletion ℚ | Valued.v z ≤ WithZero.exp n}.indicator 1 y.2 *
            {z : v.adicCompletion ℚ | Valued.v z ≤ WithZero.exp (-c - 1)}.indicator 1 (y.1 / y.2)) *
          {z : v.adicCompletion ℚ | Valued.v z ≤ WithZero.exp (T₀ - 1)}.indicator (1 : v.adicCompletion ℚ → ℝ≥0∞)
            (α + -(y.2 / (a : v.adicCompletion ℚ) * x)) := by
      intro α
      simp only [wedgeMajorant]
      ring
    simp only [hre]
    rw [lintegral_const_mul _ hg, lintegral_indicator_one_comp v hBT (measurable_add_const _),
      measure_preimage_add_right]

  have hmeas₂ : Measurable fun y : v.adicCompletion ℚ × v.adicCompletion ℚ =>
      ENNReal.ofReal (K₀ * ‖y.2‖⁻¹) * {z : v.adicCompletion ℚ | Valued.v z ≤ WithZero.exp n}.indicator 1 y.2 *
          {z : v.adicCompletion ℚ | Valued.v z ≤ WithZero.exp (-c - 1)}.indicator 1 (y.1 / y.2) *
        selfDualHaarAt ℚ v {z : v.adicCompletion ℚ | Valued.v z ≤ WithZero.exp (T₀ - 1)} := by
    have hγ : Measurable fun y : v.adicCompletion ℚ × v.adicCompletion ℚ => y.2 := measurable_snd
    have hβγ : Measurable fun y : v.adicCompletion ℚ × v.adicCompletion ℚ => y.1 / y.2 :=
      measurable_fst.div measurable_snd
    have h₁ : Measurable fun y : v.adicCompletion ℚ × v.adicCompletion ℚ => ENNReal.ofReal (K₀ * ‖y.2‖⁻¹) :=
      ENNReal.measurable_ofReal.comp (hγ.norm.inv.const_mul K₀)
    exact ((h₁.mul ((measurable_one.indicator hBn).comp hγ)).mul ((measurable_one.indicator hBc).comp hβγ)).mul
      measurable_const

  have hkey : ∀ γ : v.adicCompletion ℚ,
      ∫⁻ β, ENNReal.ofReal (K₀ * ‖γ‖⁻¹) * {z : v.adicCompletion ℚ | Valued.v z ≤ WithZero.exp n}.indicator 1 γ *
            {z : v.adicCompletion ℚ | Valued.v z ≤ WithZero.exp (-c - 1)}.indicator 1 (β / γ) *
          selfDualHaarAt ℚ v {z : v.adicCompletion ℚ | Valued.v z ≤ WithZero.exp (T₀ - 1)} ∂(selfDualHaarAt ℚ v) ≤
        ENNReal.ofReal (K₀ * (Ideal.absNorm v.asIdeal : ℝ) ^ (-c - 1)) *
            selfDualHaarAt ℚ v (v.adicCompletionIntegers ℚ : Set (v.adicCompletion ℚ)) *
            selfDualHaarAt ℚ v {y : v.adicCompletion ℚ | Valued.v y ≤ WithZero.exp (T₀ - 1)} *
          {y : v.adicCompletion ℚ | Valued.v y ≤ WithZero.exp n}.indicator 1 γ := by
    intro γ
    rcases eq_or_ne γ 0 with rfl | hγ
    · simp
    have hγpos : 0 < ‖γ‖ := norm_pos_iff.mpr hγ
    have hg : Measurable fun β : v.adicCompletion ℚ =>
        {z : v.adicCompletion ℚ | Valued.v z ≤ WithZero.exp (-c - 1)}.indicator (1 : v.adicCompletion ℚ → ℝ≥0∞)
          (β / γ) :=
      (measurable_one.indicator hBc).comp (measurable_div_const γ)
    have hre : ∀ β : v.adicCompletion ℚ,
        ENNReal.ofReal (K₀ * ‖γ‖⁻¹) * {z : v.adicCompletion ℚ | Valued.v z ≤ WithZero.exp n}.indicator 1 γ *
            {z : v.adicCompletion ℚ | Valued.v z ≤ WithZero.exp (-c - 1)}.indicator 1 (β / γ) *
          selfDualHaarAt ℚ v {z : v.adicCompletion ℚ | Valued.v z ≤ WithZero.exp (T₀ - 1)} =
        (ENNReal.ofReal (K₀ * ‖γ‖⁻¹) * {z : v.adicCompletion ℚ | Valued.v z ≤ WithZero.exp n}.indicator 1 γ *
            selfDualHaarAt ℚ v {z : v.adicCompletion ℚ | Valued.v z ≤ WithZero.exp (T₀ - 1)}) *
          {z : v.adicCompletion ℚ | Valued.v z ≤ WithZero.exp (-c - 1)}.indicator (1 : v.adicCompletion ℚ → ℝ≥0∞)
            (β / γ) := by
      intro β
      ring
    have hA : ENNReal.ofReal (K₀ * ‖γ‖⁻¹) * ENNReal.ofReal (‖γ‖ * (Ideal.absNorm v.asIdeal : ℝ) ^ (-c - 1)) =
        ENNReal.ofReal (K₀ * (Ideal.absNorm v.asIdeal : ℝ) ^ (-c - 1)) := by
      have hp : 0 ≤ K₀ * ‖γ‖⁻¹ := by positivity
      rw [← ENNReal.ofReal_mul hp]
      congr 1
      calc K₀ * ‖γ‖⁻¹ * (‖γ‖ * (Ideal.absNorm v.asIdeal : ℝ) ^ (-c - 1))
          = K₀ * (Ideal.absNorm v.asIdeal : ℝ) ^ (-c - 1) * (‖γ‖⁻¹ * ‖γ‖) := by ring
        _ = K₀ * (Ideal.absNorm v.asIdeal : ℝ) ^ (-c - 1) := by rw [inv_mul_cancel₀ hγpos.ne', mul_one]
    simp only [hre]
    rw [lintegral_const_mul _ hg, lintegral_indicator_one_comp v hBc (measurable_div_const γ),
      measure_preimage_div_valued_le v hγ c]
    refine le_of_eq ?_
    calc ENNReal.ofReal (K₀ * ‖γ‖⁻¹) * {z : v.adicCompletion ℚ | Valued.v z ≤ WithZero.exp n}.indicator 1 γ *
            selfDualHaarAt ℚ v {z : v.adicCompletion ℚ | Valued.v z ≤ WithZero.exp (T₀ - 1)} *
          (ENNReal.ofReal (‖γ‖ * (Ideal.absNorm v.asIdeal : ℝ) ^ (-c - 1)) *
            selfDualHaarAt ℚ v (v.adicCompletionIntegers ℚ : Set (v.adicCompletion ℚ)))
        = (ENNReal.ofReal (K₀ * ‖γ‖⁻¹) * ENNReal.ofReal (‖γ‖ * (Ideal.absNorm v.asIdeal : ℝ) ^ (-c - 1))) *
            selfDualHaarAt ℚ v (v.adicCompletionIntegers ℚ : Set (v.adicCompletion ℚ)) *
            selfDualHaarAt ℚ v {z : v.adicCompletion ℚ | Valued.v z ≤ WithZero.exp (T₀ - 1)} *
          {z : v.adicCompletion ℚ | Valued.v z ≤ WithZero.exp n}.indicator 1 γ := by ring
      _ = _ := by rw [hA]

  unfold jacquetHaar3
  rw [lintegral_prod_symm _ (measurable_wedgeMajorant v K₀ n c T₀ a x).aemeasurable]
  simp only [hinner]
  rw [lintegral_prod_symm _ hmeas₂.aemeasurable]
  calc ∫⁻ γ, ∫⁻ β, ENNReal.ofReal (K₀ * ‖γ‖⁻¹) *
            {z : v.adicCompletion ℚ | Valued.v z ≤ WithZero.exp n}.indicator 1 γ *
            {z : v.adicCompletion ℚ | Valued.v z ≤ WithZero.exp (-c - 1)}.indicator 1 (β / γ) *
          selfDualHaarAt ℚ v {z : v.adicCompletion ℚ | Valued.v z ≤ WithZero.exp (T₀ - 1)}
          ∂(selfDualHaarAt ℚ v) ∂(selfDualHaarAt ℚ v)
      ≤ ∫⁻ γ, ENNReal.ofReal (K₀ * (Ideal.absNorm v.asIdeal : ℝ) ^ (-c - 1)) *
            selfDualHaarAt ℚ v (v.adicCompletionIntegers ℚ : Set (v.adicCompletion ℚ)) *
            selfDualHaarAt ℚ v {y : v.adicCompletion ℚ | Valued.v y ≤ WithZero.exp (T₀ - 1)} *
          {y : v.adicCompletion ℚ | Valued.v y ≤ WithZero.exp n}.indicator 1 γ ∂(selfDualHaarAt ℚ v) :=
        lintegral_mono fun γ => hkey γ
    _ = ENNReal.ofReal (K₀ * (Ideal.absNorm v.asIdeal : ℝ) ^ (-c - 1)) *
            selfDualHaarAt ℚ v (v.adicCompletionIntegers ℚ : Set (v.adicCompletion ℚ)) *
            selfDualHaarAt ℚ v {y : v.adicCompletion ℚ | Valued.v y ≤ WithZero.exp (T₀ - 1)} *
          selfDualHaarAt ℚ v {y : v.adicCompletion ℚ | Valued.v y ≤ WithZero.exp n} := by
        rw [lintegral_const_mul _ (measurable_one.indicator hBn), lintegral_indicator_one hBn]
    _ = _ := by rw [measure_valued_le_eq_ofReal v n]

private theorem exists_forall_norm_setIntegral_wedge_near_le (hν : ∀ i, IsLocallyConstant (ν i))
    (hΦl : IsLocallyConstant Φ) (hΦc : HasCompactSupport Φ)
    (h10 : ‖(((ν 1 * (ν 0)⁻¹) (NumberField.AdelicLevel.uniformizerUnit ℚ v) : ℂˣ) : ℂ)‖ = 1)
    (h21 : ‖(((ν 2 * (ν 1)⁻¹) (NumberField.AdelicLevel.uniformizerUnit ℚ v) : ℂˣ) : ℂ)‖ = 1) (T₀ : ℤ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (c : ℤ) (a : (v.adicCompletion ℚ)ˣ) (x : v.adicCompletion ℚ),
      ‖∫ p in unipotentBall3 v c ∩ {p | WithZero.exp c * Valued.v p.2.1 < Valued.v p.2.2} ∩
          {p | Valued.v (p.1 - p.2.2 / (a : v.adicCompletion ℚ) * x) < WithZero.exp T₀},
          psiLocal ℚ v (-(p.1 + p.2.1)) * cellSectionOf v ν Φ (dualCellPoint v p.1 p.2.1 p.2.2 a x)
            ∂(jacquetHaar3 v)‖ ≤
        C * (‖((((ν 0) a)⁻¹ : ℂˣ) : ℂ)‖ * (modulus (a : v.adicCompletion ℚ) : ℝ)) *
          (Ideal.absNorm v.asIdeal : ℝ) ^ (-c) := by
  haveI := isAddHaarMeasure_selfDualHaarAt ℚ v
  obtain ⟨M₁, hM₁0, hM₁⟩ := exists_forall_norm_charExt_le v (ν 1 * (ν 0)⁻¹) ((hν 1).mul (hν 0).inv) h10
  obtain ⟨M₂, hM₂0, hM₂⟩ := exists_forall_norm_charExt_le v (ν 2 * (ν 1)⁻¹) ((hν 2).mul (hν 1).inv) h21
  obtain ⟨MΦ, hMΦ0, hMΦ⟩ := exists_forall_norm_apply_le v Φ hΦl hΦc
  obtain ⟨R₀, hR₀⟩ := exists_support_radius v Φ hΦc
  have hR : (0 : ℝ) < max R₀ 1 := lt_of_lt_of_le zero_lt_one (le_max_right _ _)
  have hsupp : ∀ q : Fin 3 → v.adicCompletion ℚ, Φ q ≠ 0 → ∀ i, ‖q i‖ ≤ max R₀ 1 :=
    fun q hq i => (hR₀ q hq i).trans (le_max_left _ _)
  have hq1 : (1 : ℝ) < (Ideal.absNorm v.asIdeal : ℝ) := one_lt_absNorm_real v
  have hq0 : (0 : ℝ) < (Ideal.absNorm v.asIdeal : ℝ) := absNorm_pos v

  have hO : selfDualHaarAt ℚ v (v.adicCompletionIntegers ℚ : Set (v.adicCompletion ℚ)) ≠ ⊤ := by
    have hK : IsCompact (v.adicCompletionIntegers ℚ : Set (v.adicCompletion ℚ)) := by
      rw [← coe_integersPositiveCompacts]
      exact (integersPositiveCompacts ℚ v).isCompact
    exact hK.measure_lt_top.ne
  have hB : selfDualHaarAt ℚ v {y : v.adicCompletion ℚ | Valued.v y ≤ WithZero.exp (T₀ - 1)} ≠ ⊤ :=
    (isCompact_setOf_valued_le_exp v (T₀ - 1)).measure_lt_top.ne
  refine ⟨M₁ * M₂ * max R₀ 1 * max R₀ 1 * MΦ * max R₀ 1 * (Ideal.absNorm v.asIdeal : ℝ) ^ T₀ *
      (selfDualHaarAt ℚ v (v.adicCompletionIntegers ℚ : Set (v.adicCompletion ℚ))).toReal *
      (selfDualHaarAt ℚ v (v.adicCompletionIntegers ℚ : Set (v.adicCompletion ℚ))).toReal *
      (selfDualHaarAt ℚ v {y : v.adicCompletion ℚ | Valued.v y ≤ WithZero.exp (T₀ - 1)}).toReal,
    by positivity, fun c a x => ?_⟩
  have hapos : 0 < ‖(a : v.adicCompletion ℚ)‖ := norm_pos_iff.mpr a.ne_zero
  have hK₀ : 0 ≤ ‖((((ν 0) a)⁻¹ : ℂˣ) : ℂ)‖ * (M₁ * M₂ * max R₀ 1 * max R₀ 1 * MΦ) := by positivity

  have hρ : 0 < max R₀ 1 * ‖(a : v.adicCompletion ℚ)‖ * (Ideal.absNorm v.asIdeal : ℝ) ^ T₀ := by positivity
  obtain ⟨n, hn⟩ := exists_mem_Ico_zpow hρ hq1
  rw [Set.mem_Ico] at hn

  have hpt : ∀ p ∈ unipotentBall3 v c ∩ {p | WithZero.exp c * Valued.v p.2.1 < Valued.v p.2.2} ∩
      {p | Valued.v (p.1 - p.2.2 / (a : v.adicCompletion ℚ) * x) < WithZero.exp T₀},
      ENNReal.ofReal ‖psiLocal ℚ v (-(p.1 + p.2.1)) * cellSectionOf v ν Φ (dualCellPoint v p.1 p.2.1 p.2.2 a x)‖ ≤
        wedgeMajorant v (‖((((ν 0) a)⁻¹ : ℂˣ) : ℂ)‖ * (M₁ * M₂ * max R₀ 1 * max R₀ 1 * MΦ)) n c T₀ a x p := by
    rintro p ⟨⟨hball, hw⟩, hnear⟩
    have hball' : Valued.v p.1 ≤ WithZero.exp c := ((mem_unipotentBall3_iff v c p).mp hball).1
    have hw' : WithZero.exp c * Valued.v p.2.1 < Valued.v p.2.2 := hw
    have hnear' : Valued.v (p.1 - p.2.2 / (a : v.adicCompletion ℚ) * x) < WithZero.exp T₀ := hnear
    simp only [wedgeMajorant]
    rcases norm_wedge_integrand v ν Φ hM₁ hM₂ hM₁0 hM₂0 hMΦ hMΦ0 hR hsupp a x hball' hw' hnear' with h0 | ⟨hle, hγle⟩
    · rw [h0, norm_zero, ENNReal.ofReal_zero]
      exact zero_le
    obtain ⟨hγ0, hwn⟩ := wedge_norm v hw'
    have hγpos : 0 < ‖p.2.2‖ := norm_pos_iff.mpr hγ0

    have hγm : p.2.2 ∈ {y : v.adicCompletion ℚ | Valued.v y ≤ WithZero.exp n} :=
      valued_le_exp_of_lt_exp_succ v (valued_lt_of_norm_lt v (hγle.trans_lt hn.2))
    have hβm : p.2.1 / p.2.2 ∈ {y : v.adicCompletion ℚ | Valued.v y ≤ WithZero.exp (-c - 1)} := by
      refine valued_le_exp_of_lt_exp_succ v ?_
      rw [sub_add_cancel]
      refine valued_lt_of_norm_lt v ?_
      rw [norm_div, div_lt_iff₀ hγpos, zpow_neg, ← div_eq_inv_mul, lt_div_iff₀ (zpow_pos hq0 c)]
      linarith [hwn]
    have hαm : p.1 + -(p.2.2 / (a : v.adicCompletion ℚ) * x) ∈
        {y : v.adicCompletion ℚ | Valued.v y ≤ WithZero.exp (T₀ - 1)} := by
      refine valued_le_exp_of_lt_exp_succ v ?_
      rw [sub_add_cancel, ← sub_eq_add_neg]
      exact hnear'
    simp only [Set.indicator_of_mem hγm, Set.indicator_of_mem hβm, Set.indicator_of_mem hαm, Pi.one_apply, mul_one]
    exact ENNReal.ofReal_le_ofReal hle

  have hfin : ENNReal.ofReal (‖((((ν 0) a)⁻¹ : ℂˣ) : ℂ)‖ * (M₁ * M₂ * max R₀ 1 * max R₀ 1 * MΦ) *
        (Ideal.absNorm v.asIdeal : ℝ) ^ (-c - 1)) *
          selfDualHaarAt ℚ v (v.adicCompletionIntegers ℚ : Set (v.adicCompletion ℚ)) *
          selfDualHaarAt ℚ v {y : v.adicCompletion ℚ | Valued.v y ≤ WithZero.exp (T₀ - 1)} *
        (ENNReal.ofReal ((Ideal.absNorm v.asIdeal : ℝ) ^ n) *
          selfDualHaarAt ℚ v (v.adicCompletionIntegers ℚ : Set (v.adicCompletion ℚ))) ≠ ⊤ :=
    ENNReal.mul_ne_top (ENNReal.mul_ne_top (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hO) hB)
      (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hO)

  refine (norm_integral_le_lintegral_norm _).trans ?_
  refine (ENNReal.toReal_mono hfin ?_).trans ?_
  · calc ∫⁻ p in unipotentBall3 v c ∩ {p | WithZero.exp c * Valued.v p.2.1 < Valued.v p.2.2} ∩
            {p | Valued.v (p.1 - p.2.2 / (a : v.adicCompletion ℚ) * x) < WithZero.exp T₀},
          ENNReal.ofReal ‖psiLocal ℚ v (-(p.1 + p.2.1)) * cellSectionOf v ν Φ (dualCellPoint v p.1 p.2.1 p.2.2 a x)‖
            ∂(jacquetHaar3 v)
        ≤ ∫⁻ p in unipotentBall3 v c ∩ {p | WithZero.exp c * Valued.v p.2.1 < Valued.v p.2.2} ∩
            {p | Valued.v (p.1 - p.2.2 / (a : v.adicCompletion ℚ) * x) < WithZero.exp T₀},
          wedgeMajorant v (‖((((ν 0) a)⁻¹ : ℂˣ) : ℂ)‖ * (M₁ * M₂ * max R₀ 1 * max R₀ 1 * MΦ)) n c T₀ a x p
            ∂(jacquetHaar3 v) := setLIntegral_mono (measurable_wedgeMajorant v _ n c T₀ a x) hpt
      _ ≤ ∫⁻ p, wedgeMajorant v (‖((((ν 0) a)⁻¹ : ℂˣ) : ℂ)‖ * (M₁ * M₂ * max R₀ 1 * max R₀ 1 * MΦ)) n c T₀ a x p
            ∂(jacquetHaar3 v) := setLIntegral_le_lintegral _ _
      _ ≤ _ := lintegral_wedgeMajorant_le v hK₀ n c T₀ a x
  ·
    have hz : (Ideal.absNorm v.asIdeal : ℝ) ^ (-c - 1) ≤ (Ideal.absNorm v.asIdeal : ℝ) ^ (-c) :=
      zpow_le_zpow_right₀ hq1.le (by omega)
    have hnn : (0 : ℝ) ≤ (Ideal.absNorm v.asIdeal : ℝ) ^ (-c - 1) := (zpow_pos hq0 _).le
    have hA0 : 0 ≤ ‖((((ν 0) a)⁻¹ : ℂˣ) : ℂ)‖ * (M₁ * M₂ * max R₀ 1 * max R₀ 1 * MΦ) *
        (Ideal.absNorm v.asIdeal : ℝ) ^ (-c - 1) := mul_nonneg hK₀ hnn
    have hn0 : (0 : ℝ) ≤ (Ideal.absNorm v.asIdeal : ℝ) ^ n := (zpow_pos hq0 n).le
    rw [ENNReal.toReal_mul, ENNReal.toReal_mul, ENNReal.toReal_mul, ENNReal.toReal_mul, ENNReal.toReal_ofReal hA0,
      ENNReal.toReal_ofReal hn0, modulus_real_eq_norm]
    calc ‖((((ν 0) a)⁻¹ : ℂˣ) : ℂ)‖ * (M₁ * M₂ * max R₀ 1 * max R₀ 1 * MΦ) * (Ideal.absNorm v.asIdeal : ℝ) ^ (-c - 1) *
            (selfDualHaarAt ℚ v (v.adicCompletionIntegers ℚ : Set (v.adicCompletion ℚ))).toReal *
            (selfDualHaarAt ℚ v {y : v.adicCompletion ℚ | Valued.v y ≤ WithZero.exp (T₀ - 1)}).toReal *
          ((Ideal.absNorm v.asIdeal : ℝ) ^ n *
            (selfDualHaarAt ℚ v (v.adicCompletionIntegers ℚ : Set (v.adicCompletion ℚ))).toReal)
        = (‖((((ν 0) a)⁻¹ : ℂˣ) : ℂ)‖ * (M₁ * M₂ * max R₀ 1 * max R₀ 1 * MΦ) *
              (selfDualHaarAt ℚ v (v.adicCompletionIntegers ℚ : Set (v.adicCompletion ℚ))).toReal *
              (selfDualHaarAt ℚ v {y : v.adicCompletion ℚ | Valued.v y ≤ WithZero.exp (T₀ - 1)}).toReal *
              (selfDualHaarAt ℚ v (v.adicCompletionIntegers ℚ : Set (v.adicCompletion ℚ))).toReal *
            (Ideal.absNorm v.asIdeal : ℝ) ^ n) * (Ideal.absNorm v.asIdeal : ℝ) ^ (-c - 1) := by ring
      _ ≤ (‖((((ν 0) a)⁻¹ : ℂˣ) : ℂ)‖ * (M₁ * M₂ * max R₀ 1 * max R₀ 1 * MΦ) *
              (selfDualHaarAt ℚ v (v.adicCompletionIntegers ℚ : Set (v.adicCompletion ℚ))).toReal *
              (selfDualHaarAt ℚ v {y : v.adicCompletion ℚ | Valued.v y ≤ WithZero.exp (T₀ - 1)}).toReal *
              (selfDualHaarAt ℚ v (v.adicCompletionIntegers ℚ : Set (v.adicCompletion ℚ))).toReal *
            (max R₀ 1 * ‖(a : v.adicCompletion ℚ)‖ * (Ideal.absNorm v.asIdeal : ℝ) ^ T₀)) *
          (Ideal.absNorm v.asIdeal : ℝ) ^ (-c) :=
          mul_le_mul (mul_le_mul_of_nonneg_left hn.1 (by positivity)) hz hnn (by positivity)
      _ = _ := by ring

end WedgeNear
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_tendsto_setIntegral_annulus_setIntegral_ball_jacquetWindow_sub_jacquetValue.LaurentZetaSlot"

end LanglandsTunnell.CubicInduction
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_tendsto_setIntegral_annulus_setIntegral_ball_jacquetWindow_sub_jacquetValue.LaurentZetaSlot"
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_tendsto_setIntegral_annulus_setIntegral_ball_jacquetWindow_sub_jacquetValue.LaurentZetaSlot"

end Part29
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_tendsto_setIntegral_annulus_setIntegral_ball_jacquetWindow_sub_jacquetValue.LaurentZetaSlot"

section Part30
set_option autoImplicit false

open MeasureTheory
open IsDedekindDomain
open NumberField
p2m_open "LanglandsTunnell.TateLocal P2MW.S_LanglandsTunnell_CubicInduction_tendsto_setIntegral_annulus_setIntegral_ball_jacquetWindow_sub_jacquetValue.LanglandsTunnell.TateLocal"
open NumberField.StandardAddChar

attribute [local instance] LanglandsTunnell.TateLocal.localBorel
attribute [local instance] LanglandsTunnell.TateLocal.borelSpace_localBorel

namespace LanglandsTunnell
p2m_export "LanglandsTunnell" "TateLocal.localBorel TateLocal.borelSpace_localBorel TateLocal.integersPositiveCompacts TateLocal.coe_integersPositiveCompacts"
namespace CubicInduction
p2m_export "LanglandsTunnell.CubicInduction" "unipotentBall3 mem_unipotentBall3_iff jacquetHaar3 jacquetTruncated3 jacquetLevel jacquetValue jacquetTruncated3_eq_jacquetValue bigCell3 mem_bigCell3_iff cellSectionOf cellSectionOf_apply_of_mem cellSectionOf_apply_of_notMem cellSectionOf_upperUnipotent3_mul cellSectionOf_diagonal3_mul principalSeries3 gl3Entry cornerEntry lowerMinor outerMinor gl3Det gl3Det_ne_zero cellRatio cellValue antidiagonal3 antidiagonal3_coe eventually_valued_eq eventually_valued_lt eventually_norm_eq eventually_charExt_eq continuous_gl3Entry continuous_cornerEntry continuous_lowerMinor continuous_outerMinor continuous_gl3Det exists_bottom_entry_ne_zero_of_cornerEntry_eq_zero outerMinor_ne_zero_of_lowerMinor_eq_zero gl3AmbientRightTranslate gl3AmbientRightTranslate_apply transposeInv3 upperUnipotent3 upperUnipotent3_coe embedMat2 iotaGL coe_iotaGL LocalGL3 diagUnitGL2 coe_diagUnitGL2 lowerUnipotent21 longWeyl3 longWeyl3_coe weylPrime3 weylPrime3_coe transposeInv3_weylPrime3 transposeInv3_lowerUnipotent21 exists_forall_le_integrableOn_and_jacquetTruncated3_eq_of_cellSectionOf exists_forall_gl3AmbientRightTranslate_eq_of_mem_principalSeries3"
p2m_open "LanglandsTunnell.CubicInduction LanglandsTunnell"

variable (v : HeightOneSpectrum (𝓞 ℚ))

section WedgeFar

private theorem exp_le_valued_iff {y : v.adicCompletion ℚ} (n : ℤ) :
    WithZero.exp n ≤ Valued.v y ↔ ¬ Valued.v y ≤ WithZero.exp (n - 1) := by
  by_cases hy : y = 0
  · subst hy
    rw [map_zero]
    constructor
    · intro h
      exact absurd h (not_le.mpr WithZero.exp_pos)
    · intro h
      exact absurd zero_le' h
  · obtain ⟨j, hj⟩ := LaurentZetaSlot.exists_mem_shell v hy
    have hvy : Valued.v y = WithZero.exp (-j) := hj
    rw [hvy, WithZero.exp_le_exp, WithZero.exp_le_exp]
    constructor <;> intro h <;> omega

private theorem wedge_iff {β γ : v.adicCompletion ℚ} (c : ℤ) :
    WithZero.exp c * Valued.v β < Valued.v γ ↔
      ∃ j : ℤ, γ ∈ LaurentZetaSlot.shell v j ∧ Valued.v β ≤ WithZero.exp (-j - c - 1) := by
  constructor
  · intro h
    have hγ : γ ≠ 0 := by
      rintro rfl
      rw [map_zero] at h
      exact (not_lt.mpr zero_le') h
    obtain ⟨j, hj⟩ := LaurentZetaSlot.exists_mem_shell v hγ
    have hvγ : Valued.v γ = WithZero.exp (-j) := hj
    refine ⟨j, hj, ?_⟩
    by_cases hβ : β = 0
    · rw [hβ, map_zero]
      exact zero_le'
    · obtain ⟨i, hi⟩ := LaurentZetaSlot.exists_mem_shell v hβ
      have hvβ : Valued.v β = WithZero.exp (-i) := hi
      rw [hvβ, hvγ, ← WithZero.exp_add, WithZero.exp_lt_exp] at h
      rw [hvβ, WithZero.exp_le_exp]
      omega
  · rintro ⟨j, hj, hβ⟩
    have hvγ : Valued.v γ = WithZero.exp (-j) := hj
    rw [hvγ]
    calc WithZero.exp c * Valued.v β ≤ WithZero.exp c * WithZero.exp (-j - c - 1) := mul_le_mul' le_rfl hβ
      _ = WithZero.exp (-j - 1) := by
          rw [← WithZero.exp_add]
          congr 1
          ring
      _ < WithZero.exp (-j) := by
          rw [WithZero.exp_lt_exp]
          omega

private theorem measurableSet_wedge (c : ℤ) :
    MeasurableSet {p : v.adicCompletion ℚ × v.adicCompletion ℚ × v.adicCompletion ℚ |
      WithZero.exp c * Valued.v p.2.1 < Valued.v p.2.2} := by
  have hset : {p : v.adicCompletion ℚ × v.adicCompletion ℚ × v.adicCompletion ℚ |
        WithZero.exp c * Valued.v p.2.1 < Valued.v p.2.2} =
      ⋃ j : ℤ, ((fun p : v.adicCompletion ℚ × v.adicCompletion ℚ × v.adicCompletion ℚ => p.2.2) ⁻¹'
          LaurentZetaSlot.shell v j ∩
        (fun p : v.adicCompletion ℚ × v.adicCompletion ℚ × v.adicCompletion ℚ => p.2.1) ⁻¹'
          {y : v.adicCompletion ℚ | Valued.v y ≤ WithZero.exp (-j - c - 1)}) := by
    ext p
    simp only [Set.mem_setOf_eq, Set.mem_iUnion, Set.mem_inter_iff, Set.mem_preimage]
    exact wedge_iff v c
  rw [hset]
  refine MeasurableSet.iUnion fun j => MeasurableSet.inter ?_ ?_
  · exact (LaurentZetaSlot.measurableSet_shell v j).preimage measurable_snd.snd
  · exact (isClosed_valued_le v _).measurableSet.preimage measurable_snd.fst

private theorem measurableSet_far (T₀ : ℤ) (a : (v.adicCompletion ℚ)ˣ) (x : v.adicCompletion ℚ) :
    MeasurableSet {p : v.adicCompletion ℚ × v.adicCompletion ℚ × v.adicCompletion ℚ |
      WithZero.exp T₀ ≤ Valued.v (p.1 - p.2.2 / (a : v.adicCompletion ℚ) * x)} := by
  have hset : {p : v.adicCompletion ℚ × v.adicCompletion ℚ × v.adicCompletion ℚ |
        WithZero.exp T₀ ≤ Valued.v (p.1 - p.2.2 / (a : v.adicCompletion ℚ) * x)} =
      ((fun p : v.adicCompletion ℚ × v.adicCompletion ℚ × v.adicCompletion ℚ =>
          p.1 - p.2.2 / (a : v.adicCompletion ℚ) * x) ⁻¹'
        {y : v.adicCompletion ℚ | Valued.v y ≤ WithZero.exp (T₀ - 1)})ᶜ := by
    ext p
    simp only [Set.mem_setOf_eq, Set.mem_compl_iff, Set.mem_preimage]
    exact exp_le_valued_iff v T₀
  rw [hset]
  refine ((isClosed_valued_le v _).measurableSet.preimage ?_).compl
  exact (continuous_fst.sub ((continuous_snd.snd.div_const _).mul continuous_const)).measurable

variable (ν : Fin 3 → ((v.adicCompletion ℚ)ˣ →* ℂˣ)) (Φ : (Fin 3 → v.adicCompletion ℚ) → ℂ)

private theorem exists_forall_setIntegral_wedge_far_eq_zero (hν : ∀ i, IsLocallyConstant (ν i))
    (hΦl : IsLocallyConstant Φ) (hΦc : HasCompactSupport Φ) :
    ∃ T₀ c₀ : ℤ, ∀ c : ℤ, c₀ ≤ c → ∀ (a : (v.adicCompletion ℚ)ˣ) (x : v.adicCompletion ℚ),
      ∫ p in unipotentBall3 v c ∩ {p | WithZero.exp c * Valued.v p.2.1 < Valued.v p.2.2} ∩
          {p | WithZero.exp T₀ ≤ Valued.v (p.1 - p.2.2 / (a : v.adicCompletion ℚ) * x)},
        psiLocal ℚ v (-(p.1 + p.2.1)) * cellSectionOf v ν Φ (dualCellPoint v p.1 p.2.1 p.2.2 a x)
          ∂(jacquetHaar3 v) = 0 := by

  obtain ⟨n, hn⟩ := exists_hasConductorExponentAt_of_isLocallyConstant ℚ v (ν 2 * (ν 1)⁻¹) ((hν 2).mul (hν 1).inv)
  obtain ⟨δ, hδpos, hδ⟩ := exists_invariance_radius v Φ hΦl hΦc
  obtain ⟨R₀, hR₀⟩ := exists_support_radius v Φ hΦc
  obtain ⟨ε, hψε, mε, hvε, hmε⟩ := exists_translate v
  have hq : (1 : ℝ) < (Ideal.absNorm v.asIdeal : ℝ) := one_lt_absNorm_real v
  have hq0 : (0 : ℝ) < (Ideal.absNorm v.asIdeal : ℝ) := zero_lt_one.trans hq

  have hR : ∀ p : Fin 3 → v.adicCompletion ℚ, Φ p ≠ 0 → ∀ i, ‖p i‖ ≤ max R₀ 0 :=
    fun p hp i => (hR₀ p hp i).trans (le_max_left _ _)

  obtain ⟨m₀, hm₀⟩ := pow_unbounded_of_one_lt
    (max ((Ideal.absNorm v.asIdeal : ℝ) / δ) (max ((Ideal.absNorm v.asIdeal : ℝ) * max R₀ 0 / δ) (2 * max R₀ 0 / δ)))
    hq
  have hm₀z : ∀ t : ℤ, (m₀ : ℤ) ≤ t →
      max ((Ideal.absNorm v.asIdeal : ℝ) / δ)
          (max ((Ideal.absNorm v.asIdeal : ℝ) * max R₀ 0 / δ) (2 * max R₀ 0 / δ)) ≤
        (Ideal.absNorm v.asIdeal : ℝ) ^ t := fun t ht => by
    refine hm₀.le.trans ?_
    rw [← zpow_natCast]
    exact zpow_le_zpow_right₀ hq.le ht
  refine ⟨(m₀ : ℤ) + n + 2, (m₀ : ℤ) + 1, fun c hc a x => ?_⟩

  have hκ : psiLocal ℚ v (-ε) ≠ 1 := by
    rw [AddChar.map_neg_eq_inv]
    exact fun h => hψε (inv_eq_one.mp h)
  have hvε_c : Valued.v ε ≤ WithZero.exp c := by
    rw [hvε, WithZero.exp_le_exp]
    omega
  have hεnorm : ‖ε‖ ≤ (Ideal.absNorm v.asIdeal : ℝ) := by
    have h1 : Valued.v ε ≤ WithZero.exp (1 : ℤ) := by
      rw [hvε, WithZero.exp_le_exp]
      exact hmε
    have h := norm_le_zpow_of_valued_le v h1
    rwa [zpow_one] at h

  haveI := sFinite_selfDualHaarAt ℚ v
  haveI := isAddHaarMeasure_selfDualHaarAt ℚ v
  set S : Set (v.adicCompletion ℚ × v.adicCompletion ℚ × v.adicCompletion ℚ) :=
    unipotentBall3 v c ∩ {p | WithZero.exp c * Valued.v p.2.1 < Valued.v p.2.2} ∩
      {p | WithZero.exp ((m₀ : ℤ) + n + 2) ≤ Valued.v (p.1 - p.2.2 / (a : v.adicCompletion ℚ) * x)} with hS
  have hball : MeasurableSet (unipotentBall3 v c) := measurableSet_unipotentBall3 v c
  have hSmeas : MeasurableSet S :=
    (hball.inter (measurableSet_wedge v c)).inter (measurableSet_far v ((m₀ : ℤ) + n + 2) a x)
  set e : v.adicCompletion ℚ × v.adicCompletion ℚ × v.adicCompletion ℚ ≃ᵐ
      v.adicCompletion ℚ × v.adicCompletion ℚ × v.adicCompletion ℚ :=
    (MeasurableEquiv.addLeft ε).prodCongr (MeasurableEquiv.refl (v.adicCompletion ℚ × v.adicCompletion ℚ))
  have hecoe : (⇑e) = Prod.map (fun y : v.adicCompletion ℚ => ε + y) id := rfl
  have hjac : jacquetHaar3 v = (selfDualHaarAt ℚ v).prod ((selfDualHaarAt ℚ v).prod (selfDualHaarAt ℚ v)) := rfl
  have hadd : Measurable fun y : v.adicCompletion ℚ => ε + y := (continuous_const.add continuous_id).measurable
  have hmap : Measure.map e (jacquetHaar3 v) = jacquetHaar3 v := by
    rw [hjac, hecoe, ← Measure.map_prod_map (selfDualHaarAt ℚ v) ((selfDualHaarAt ℚ v).prod (selfDualHaarAt ℚ v))
      hadd measurable_id, map_add_left_eq_self (selfDualHaarAt ℚ v) ε, Measure.map_id]

  have hstable : ∀ α β γ : v.adicCompletion ℚ, (α, β, γ) ∈ S ↔ (ε + α, β, γ) ∈ S := by
    intro α β γ
    simp only [hS, Set.mem_inter_iff, Set.mem_setOf_eq, mem_unipotentBall3_iff]
    have hfar : ∀ α' : v.adicCompletion ℚ,
        WithZero.exp ((m₀ : ℤ) + n + 2) ≤ Valued.v (α' - γ / (a : v.adicCompletion ℚ) * x) →
          Valued.v ε < Valued.v (α' - γ / (a : v.adicCompletion ℚ) * x) := fun α' h =>
      lt_of_lt_of_le (by rw [hvε, WithZero.exp_lt_exp]; omega) h
    constructor
    · rintro ⟨⟨⟨h₁, h₂, h₃⟩, hw⟩, hf⟩
      refine ⟨⟨⟨(Valuation.map_add _ _ _).trans (max_le hvε_c h₁), h₂, h₃⟩, hw⟩, ?_⟩
      rw [add_sub_assoc, Valuation.map_add_eq_of_lt_right _ (hfar α hf)]
      exact hf
    · rintro ⟨⟨⟨h₁, h₂, h₃⟩, hw⟩, hf⟩
      refine ⟨⟨⟨?_, h₂, h₃⟩, hw⟩, ?_⟩
      · calc Valued.v α = Valued.v (ε + α - ε) := by rw [add_sub_cancel_left]
          _ ≤ max (Valued.v (ε + α)) (Valued.v ε) := Valuation.map_sub _ _ _
          _ ≤ WithZero.exp c := max_le h₁ hvε_c
      · rw [add_sub_assoc] at hf
        have hlt : Valued.v ε < Valued.v (α - γ / (a : v.adicCompletion ℚ) * x) := by
          by_contra hcon
          rw [not_lt] at hcon
          have h1 : Valued.v (ε + (α - γ / (a : v.adicCompletion ℚ) * x)) ≤ Valued.v ε :=
            (Valuation.map_add _ _ _).trans (max_le le_rfl hcon)
          have h2 : Valued.v ε < WithZero.exp ((m₀ : ℤ) + n + 2) := by
            rw [hvε, WithZero.exp_lt_exp]
            omega
          exact absurd (hf.trans h1) (not_le.mpr h2)
        rwa [Valuation.map_add_eq_of_lt_right _ hlt] at hf

  have hvalue : ∀ α β γ : v.adicCompletion ℚ, (α, β, γ) ∈ S →
      cellSectionOf v ν Φ (dualCellPoint v (ε + α) β γ a x) = cellSectionOf v ν Φ (dualCellPoint v α β γ a x) := by
    intro α β γ hmem
    have hmem' := hmem
    simp only [hS, Set.mem_inter_iff, Set.mem_setOf_eq, mem_unipotentBall3_iff] at hmem'
    obtain ⟨⟨⟨hα, hβ, -⟩, hw⟩, hf⟩ := hmem'
    rw [cellSectionOf_dualCellPoint, cellSectionOf_dualCellPoint, add_sub_assoc]
    obtain ⟨U, hU⟩ : ∃ U : v.adicCompletion ℚ, U = α - γ / (a : v.adicCompletion ℚ) * x := ⟨_, rfl⟩
    obtain ⟨L, hL⟩ : ∃ L : v.adicCompletion ℚ, L = 1 - β / (a : v.adicCompletion ℚ) * x := ⟨_, rfl⟩
    obtain ⟨g, hg⟩ : ∃ g : v.adicCompletion ℚ, g = γ / (a : v.adicCompletion ℚ) := ⟨_, rfl⟩
    obtain ⟨b, hb⟩ : ∃ b : v.adicCompletion ℚ, b = β / (a : v.adicCompletion ℚ) := ⟨_, rfl⟩
    rw [← hU] at hf ⊢
    rw [← hL, ← hg, ← hb]

    have hU0 : U ≠ 0 := by
      rintro rfl
      rw [map_zero] at hf
      exact (not_le.mpr WithZero.exp_pos) hf
    obtain ⟨jU, hjU⟩ := LaurentZetaSlot.exists_mem_shell v hU0
    have hvU : Valued.v U = WithZero.exp (-jU) := hjU
    have hjU_le : (m₀ : ℤ) + n + 2 ≤ -jU := by
      rw [hvU, WithZero.exp_le_exp] at hf
      exact hf
    have hvεU : Valued.v (ε + U) = Valued.v U :=
      Valuation.map_add_eq_of_lt_right _ (by rw [hvε, hvU, WithZero.exp_lt_exp]; omega)
    have hεU0 : ε + U ≠ 0 := fun h => by
      rw [h, map_zero] at hvεU
      exact hU0 ((Valuation.zero_iff Valued.v).mp hvεU.symm)
    have hnU : ‖ε + U‖ = ‖U‖ := by
      rw [← modulus_real_eq_norm v, ← modulus_real_eq_norm v, modulus_eq_of_valued_eq v hεU0 hvεU]
    have hchar : charExt (ν 2 * (ν 1)⁻¹) (ε + U) = charExt (ν 2 * (ν 1)⁻¹) U := by
      refine charExt_eq_of_hasConductorExponentAt v hn hU0 hεU0 ?_
      rw [add_div, div_self hU0, add_sub_cancel_right, map_div₀, hvε, hvU, ← WithZero.exp_sub, WithZero.exp_le_exp]
      omega

    have hUnorm : (Ideal.absNorm v.asIdeal : ℝ) ^ (-jU) = ‖U‖ := by
      rw [← modulus_real_eq_norm v, LaurentZetaSlot.coe_modulus_eq_of_mem_shell v hjU]
    have hUpos : (0 : ℝ) < ‖U‖ := norm_pos_iff.mpr hU0
    have hUbig : max ((Ideal.absNorm v.asIdeal : ℝ) / δ)
        (max ((Ideal.absNorm v.asIdeal : ℝ) * max R₀ 0 / δ) (2 * max R₀ 0 / δ)) ≤ ‖U‖ := by
      rw [← hUnorm]
      exact hm₀z _ (by omega)
    have hU1 : (Ideal.absNorm v.asIdeal : ℝ) / δ ≤ ‖U‖ := (le_max_left _ _).trans hUbig
    have hU2 : (Ideal.absNorm v.asIdeal : ℝ) * max R₀ 0 / δ ≤ ‖U‖ :=
      ((le_max_left _ _).trans (le_max_right _ _)).trans hUbig
    have hUge1 : (1 : ℝ) ≤ ‖U‖ := by
      rw [← hUnorm]
      exact one_le_zpow₀ hq.le (by omega)

    obtain ⟨jγ, hjγ, hβw⟩ := (wedge_iff v c).mp hw
    have ha0 : (a : v.adicCompletion ℚ) ≠ 0 := a.ne_zero
    have hanorm : (0 : ℝ) < ‖(a : v.adicCompletion ℚ)‖ := norm_pos_iff.mpr ha0
    have hgnorm : ‖g‖ = ‖γ‖ / ‖(a : v.adicCompletion ℚ)‖ := by rw [hg, norm_div]
    have hbnorm : ‖b‖ = ‖β‖ / ‖(a : v.adicCompletion ℚ)‖ := by rw [hb, norm_div]
    have hγnorm : ‖γ‖ = (Ideal.absNorm v.asIdeal : ℝ) ^ (-jγ) := by
      rw [← modulus_real_eq_norm v, LaurentZetaSlot.coe_modulus_eq_of_mem_shell v hjγ]
    have hβγ : ‖β‖ ≤ ‖γ‖ * (Ideal.absNorm v.asIdeal : ℝ) ^ (-c - 1) := by
      rw [hγnorm, ← zpow_add₀ hq0.ne']
      exact (norm_le_zpow_of_valued_le v hβw).trans (le_of_eq (by congr 1; ring))
    have hbg : ‖b‖ ≤ ‖g‖ * (Ideal.absNorm v.asIdeal : ℝ) ^ (-c - 1) := by
      rw [hbnorm, hgnorm, div_mul_eq_mul_div]
      exact div_le_div_of_nonneg_right hβγ hanorm.le
    have hqc : (Ideal.absNorm v.asIdeal : ℝ) ^ c * (Ideal.absNorm v.asIdeal : ℝ) ^ (-c - 1) ≤ 1 / 2 := by
      rw [← zpow_add₀ hq0.ne', show c + (-c - 1) = -1 by ring, zpow_neg_one, inv_eq_one_div]
      have h2 : (2 : ℝ) ≤ (Ideal.absNorm v.asIdeal : ℝ) := by
        have h1 : 1 < Ideal.absNorm v.asIdeal := Nat.one_lt_cast.mp hq
        exact_mod_cast h1
      exact one_div_le_one_div_of_le two_pos h2
    have hsplit : (Ideal.absNorm v.asIdeal : ℝ) * (Ideal.absNorm v.asIdeal : ℝ) ^ (-c - 1) =
        (Ideal.absNorm v.asIdeal : ℝ) ^ (-c) := by
      calc (Ideal.absNorm v.asIdeal : ℝ) * (Ideal.absNorm v.asIdeal : ℝ) ^ (-c - 1)
          = (Ideal.absNorm v.asIdeal : ℝ) ^ (1 : ℤ) * (Ideal.absNorm v.asIdeal : ℝ) ^ (-c - 1) := by rw [zpow_one]
        _ = (Ideal.absNorm v.asIdeal : ℝ) ^ (1 + (-c - 1)) := (zpow_add₀ hq0.ne' _ _).symm
        _ = (Ideal.absNorm v.asIdeal : ℝ) ^ (-c) := by
            congr 1
            ring
    have hεb : ‖ε‖ * ‖b‖ ≤ (Ideal.absNorm v.asIdeal : ℝ) ^ (-c) * ‖g‖ := by
      calc ‖ε‖ * ‖b‖ ≤ (Ideal.absNorm v.asIdeal : ℝ) * (‖g‖ * (Ideal.absNorm v.asIdeal : ℝ) ^ (-c - 1)) :=
            mul_le_mul hεnorm hbg (norm_nonneg _) hq0.le
        _ = (Ideal.absNorm v.asIdeal : ℝ) ^ (-c) * ‖g‖ := by
            rw [← hsplit]
            ring
    have hqcR : (Ideal.absNorm v.asIdeal : ℝ) ^ (-c) * (2 * max R₀ 0) ≤ δ := by
      have h3 : 2 * max R₀ 0 / δ ≤ (Ideal.absNorm v.asIdeal : ℝ) ^ c := by
        have hbig := hm₀z c (by omega)
        exact ((le_max_right _ _).trans (le_max_right _ _)).trans hbig
      rw [div_le_iff₀ hδpos] at h3
      calc (Ideal.absNorm v.asIdeal : ℝ) ^ (-c) * (2 * max R₀ 0)
          ≤ (Ideal.absNorm v.asIdeal : ℝ) ^ (-c) * ((Ideal.absNorm v.asIdeal : ℝ) ^ c * δ) :=
            mul_le_mul_of_nonneg_left h3 (zpow_nonneg hq0.le _)
        _ = δ := by rw [← mul_assoc, ← zpow_add₀ hq0.ne', neg_add_cancel, zpow_zero, one_mul]

    have hΦeq : Φ ![(ε + U)⁻¹, g / (ε + U), (g - (ε + α) * b) / L] = Φ ![U⁻¹, g / U, (g - α * b) / L] := by
      by_cases hz : Φ ![(ε + U)⁻¹, g / (ε + U), (g - (ε + α) * b) / L] = 0 ∧ Φ ![U⁻¹, g / U, (g - α * b) / L] = 0
      · rw [hz.1, hz.2]

      have hsupp : ‖g‖ ≤ max R₀ 0 * ‖U‖ ∧ (L ≠ 0 → ‖g‖ ≤ 2 * max R₀ 0 * ‖L‖) := by
        have key : ∀ (α' U' : v.adicCompletion ℚ), ‖U'‖ = ‖U‖ →
            ‖α'‖ ≤ (Ideal.absNorm v.asIdeal : ℝ) ^ c → ‖g / U'‖ ≤ max R₀ 0 → ‖(g - α' * b) / L‖ ≤ max R₀ 0 →
            ‖g‖ ≤ max R₀ 0 * ‖U‖ ∧ (L ≠ 0 → ‖g‖ ≤ 2 * max R₀ 0 * ‖L‖) := by
          intro α' U' hU' hα' h1 h2
          rw [norm_div, hU', div_le_iff₀ hUpos] at h1
          refine ⟨h1, fun hL0 => ?_⟩
          rw [norm_div, div_le_iff₀ (norm_pos_iff.mpr hL0)] at h2
          have hαb : ‖α' * b‖ ≤ ‖g‖ * (1 / 2) := by
            rw [norm_mul]
            calc ‖α'‖ * ‖b‖ ≤ (Ideal.absNorm v.asIdeal : ℝ) ^ c * (‖g‖ * (Ideal.absNorm v.asIdeal : ℝ) ^ (-c - 1)) :=
                  mul_le_mul hα' hbg (norm_nonneg _) (zpow_nonneg hq0.le _)
              _ = ‖g‖ * ((Ideal.absNorm v.asIdeal : ℝ) ^ c * (Ideal.absNorm v.asIdeal : ℝ) ^ (-c - 1)) := by ring
              _ ≤ ‖g‖ * (1 / 2) := mul_le_mul_of_nonneg_left hqc (norm_nonneg _)
          have htri : ‖g‖ ≤ ‖g - α' * b‖ + ‖α' * b‖ := by
            calc ‖g‖ = ‖g - α' * b + α' * b‖ := by rw [sub_add_cancel]
              _ ≤ ‖g - α' * b‖ + ‖α' * b‖ := norm_add_le _ _
          linarith
        rcases not_and_or.mp hz with hz' | hz'
        · have h := hR _ hz'
          exact key (ε + α) (ε + U) hnU
            (norm_le_zpow_of_valued_le v ((Valuation.map_add _ _ _).trans (max_le hvε_c hα)))
            (h 1) (h 2)
        · have h := hR _ hz'
          exact key α U rfl (norm_le_zpow_of_valued_le v hα) (h 1) (h 2)
      refine hδ _ _ fun i => ?_
      fin_cases i
      ·
        show ‖(ε + U)⁻¹ - U⁻¹‖ ≤ δ
        rw [inv_sub_inv hεU0 hU0, show U - (ε + U) = -ε by ring, norm_div, norm_neg, norm_mul, hnU,
          div_le_iff₀ (mul_pos hUpos hUpos)]
        calc ‖ε‖ ≤ (Ideal.absNorm v.asIdeal : ℝ) := hεnorm
          _ ≤ δ * ‖U‖ := by rwa [div_le_iff₀ hδpos, mul_comm ‖U‖ δ] at hU1
          _ ≤ δ * (‖U‖ * ‖U‖) :=
              mul_le_mul_of_nonneg_left (le_mul_of_one_le_left hUpos.le hUge1) hδpos.le
      ·
        show ‖g / (ε + U) - g / U‖ ≤ δ
        rw [div_sub_div _ _ hεU0 hU0, show g * U - (ε + U) * g = -(ε * g) by ring, norm_div, norm_neg, norm_mul,
          norm_mul, hnU, div_le_iff₀ (mul_pos hUpos hUpos)]
        calc ‖ε‖ * ‖g‖ ≤ (Ideal.absNorm v.asIdeal : ℝ) * (max R₀ 0 * ‖U‖) :=
              mul_le_mul hεnorm hsupp.1 (norm_nonneg _) hq0.le
          _ = (Ideal.absNorm v.asIdeal : ℝ) * max R₀ 0 * ‖U‖ := by ring
          _ ≤ δ * ‖U‖ * ‖U‖ := by
              refine mul_le_mul_of_nonneg_right ?_ hUpos.le
              rwa [div_le_iff₀ hδpos, mul_comm ‖U‖ δ] at hU2
          _ = δ * (‖U‖ * ‖U‖) := by ring
      ·
        show ‖(g - (ε + α) * b) / L - (g - α * b) / L‖ ≤ δ
        by_cases hL0 : L = 0
        · rw [hL0, div_zero, div_zero, sub_zero, norm_zero]
          exact hδpos.le
        have hLpos : (0 : ℝ) < ‖L‖ := norm_pos_iff.mpr hL0
        rw [← sub_div, show g - (ε + α) * b - (g - α * b) = -(ε * b) by ring, norm_div, norm_neg, norm_mul,
          div_le_iff₀ hLpos]
        calc ‖ε‖ * ‖b‖ ≤ (Ideal.absNorm v.asIdeal : ℝ) ^ (-c) * ‖g‖ := hεb
          _ ≤ (Ideal.absNorm v.asIdeal : ℝ) ^ (-c) * (2 * max R₀ 0 * ‖L‖) :=
              mul_le_mul_of_nonneg_left (hsupp.2 hL0) (zpow_nonneg hq0.le _)
          _ = (Ideal.absNorm v.asIdeal : ℝ) ^ (-c) * (2 * max R₀ 0) * ‖L‖ := by ring
          _ ≤ δ * ‖L‖ := mul_le_mul_of_nonneg_right hqcR hLpos.le
    rw [hchar, hnU, hΦeq]

  rw [← integral_indicator hSmeas]
  refine integral_eq_zero_of_forall_apply_eq_const_mul e hmap hκ fun p => ?_
  obtain ⟨α, β, γ⟩ := p
  show S.indicator (fun p : v.adicCompletion ℚ × v.adicCompletion ℚ × v.adicCompletion ℚ =>
      psiLocal ℚ v (-(p.1 + p.2.1)) * cellSectionOf v ν Φ (dualCellPoint v p.1 p.2.1 p.2.2 a x)) (ε + α, β, γ) =
    psiLocal ℚ v (-ε) * S.indicator (fun p : v.adicCompletion ℚ × v.adicCompletion ℚ × v.adicCompletion ℚ =>
      psiLocal ℚ v (-(p.1 + p.2.1)) * cellSectionOf v ν Φ (dualCellPoint v p.1 p.2.1 p.2.2 a x)) (α, β, γ)
  by_cases hmem : (α, β, γ) ∈ S
  · rw [Set.indicator_of_mem ((hstable α β γ).mp hmem), Set.indicator_of_mem hmem]
    show psiLocal ℚ v (-(ε + α + β)) * cellSectionOf v ν Φ (dualCellPoint v (ε + α) β γ a x) =
      psiLocal ℚ v (-ε) * (psiLocal ℚ v (-(α + β)) * cellSectionOf v ν Φ (dualCellPoint v α β γ a x))
    rw [hvalue α β γ hmem, show -(ε + α + β) = -ε + -(α + β) by ring, AddChar.map_add_eq_mul, mul_assoc]
  · rw [Set.indicator_of_notMem (fun h => hmem ((hstable α β γ).mpr h)), Set.indicator_of_notMem hmem, mul_zero]

end WedgeFar
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_tendsto_setIntegral_annulus_setIntegral_ball_jacquetWindow_sub_jacquetValue.LaurentZetaSlot"

end LanglandsTunnell.CubicInduction
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_tendsto_setIntegral_annulus_setIntegral_ball_jacquetWindow_sub_jacquetValue.LaurentZetaSlot"
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_tendsto_setIntegral_annulus_setIntegral_ball_jacquetWindow_sub_jacquetValue.LaurentZetaSlot"

end Part30
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_tendsto_setIntegral_annulus_setIntegral_ball_jacquetWindow_sub_jacquetValue.LaurentZetaSlot"

section Part34

set_option autoImplicit false

p2m_open "MeasureTheory IsDedekindDomain NumberField LanglandsTunnell.TateLocal P2MW.S_LanglandsTunnell_CubicInduction_tendsto_setIntegral_annulus_setIntegral_ball_jacquetWindow_sub_jacquetValue.LanglandsTunnell.TateLocal NumberField.StandardAddChar"
open scoped ENNReal NNReal

attribute [local instance] LanglandsTunnell.TateLocal.localBorel

namespace LanglandsTunnell
p2m_export "LanglandsTunnell" "TateLocal.localBorel TateLocal.borelSpace_localBorel TateLocal.integersPositiveCompacts TateLocal.coe_integersPositiveCompacts"
namespace CubicInduction
p2m_export "LanglandsTunnell.CubicInduction" "unipotentBall3 mem_unipotentBall3_iff jacquetHaar3 jacquetTruncated3 jacquetLevel jacquetValue jacquetTruncated3_eq_jacquetValue bigCell3 mem_bigCell3_iff cellSectionOf cellSectionOf_apply_of_mem cellSectionOf_apply_of_notMem cellSectionOf_upperUnipotent3_mul cellSectionOf_diagonal3_mul principalSeries3 gl3Entry cornerEntry lowerMinor outerMinor gl3Det gl3Det_ne_zero cellRatio cellValue antidiagonal3 antidiagonal3_coe eventually_valued_eq eventually_valued_lt eventually_norm_eq eventually_charExt_eq continuous_gl3Entry continuous_cornerEntry continuous_lowerMinor continuous_outerMinor continuous_gl3Det exists_bottom_entry_ne_zero_of_cornerEntry_eq_zero outerMinor_ne_zero_of_lowerMinor_eq_zero gl3AmbientRightTranslate gl3AmbientRightTranslate_apply transposeInv3 upperUnipotent3 upperUnipotent3_coe embedMat2 iotaGL coe_iotaGL LocalGL3 diagUnitGL2 coe_diagUnitGL2 lowerUnipotent21 longWeyl3 longWeyl3_coe weylPrime3 weylPrime3_coe transposeInv3_weylPrime3 transposeInv3_lowerUnipotent21 exists_forall_le_integrableOn_and_jacquetTruncated3_eq_of_cellSectionOf exists_forall_gl3AmbientRightTranslate_eq_of_mem_principalSeries3"
p2m_open "LanglandsTunnell.CubicInduction LanglandsTunnell"

section DualFiniteLevel

variable (v : HeightOneSpectrum (𝓞 ℚ))

private def primedBall3 (c : ℤ) : Set (v.adicCompletion ℚ × v.adicCompletion ℚ × v.adicCompletion ℚ) :=
  {p | Valued.v p.2.1 ≤ WithZero.exp c ∧ Valued.v p.2.2 ≤ WithZero.exp c * Valued.v p.2.1 ∧
    Valued.v (p.1 - p.2.2 / p.2.1) ≤ WithZero.exp c}

private noncomputable def jacquetPrimed3 (ν : Fin 3 → ((v.adicCompletion ℚ)ˣ →* ℂˣ))
    (Φ : (Fin 3 → v.adicCompletion ℚ) → ℂ) (c : ℤ) (a : (v.adicCompletion ℚ)ˣ) (x : v.adicCompletion ℚ) : ℂ :=
  ∫ p in primedBall3 v c,
    NumberField.StandardAddChar.psiLocal ℚ v (-(p.1 + p.2.1)) *
      cellSectionOf v ν Φ (dualCellPoint v p.1 p.2.1 p.2.2 a x) ∂(jacquetHaar3 v)

private theorem setOf_valued_snd_le_eq (c : ℤ) :
    {p : v.adicCompletion ℚ × v.adicCompletion ℚ × v.adicCompletion ℚ |
        Valued.v p.2.2 ≤ WithZero.exp c * Valued.v p.2.1} =
      {p | p.2.1 = 0 ∧ p.2.2 = 0} ∪ {p | p.2.1 ≠ 0 ∧ Valued.v (p.2.2 / p.2.1) ≤ WithZero.exp c} := by
  ext p
  simp only [Set.mem_setOf_eq, Set.mem_union]
  by_cases hβ : p.2.1 = 0
  · rw [hβ, map_zero, mul_zero, le_zero_iff, map_eq_zero]
    exact ⟨fun h => Or.inl ⟨rfl, h⟩, fun h => h.elim (fun h => h.2) fun h => absurd rfl h.1⟩
  · have hpos : 0 < Valued.v p.2.1 := zero_lt_iff.mpr ((Valuation.ne_zero_iff Valued.v).mpr hβ)
    rw [map_div₀, div_le_iff₀ hpos]
    exact ⟨fun h => Or.inr ⟨hβ, h⟩, fun h => h.elim (fun h => absurd h.1 hβ) fun h => h.2⟩

private theorem measurableSet_primedBall3 (c : ℤ) : MeasurableSet (primedBall3 v c) := by
  haveI : BorelSpace (v.adicCompletion ℚ) := borelSpace_localBorel ℚ v
  have hc : MeasurableSet {x : v.adicCompletion ℚ | Valued.v x ≤ WithZero.exp c} :=
    (isClosed_valued_le v c).measurableSet
  have h₁ : MeasurableSet {p : v.adicCompletion ℚ × v.adicCompletion ℚ × v.adicCompletion ℚ |
      Valued.v p.2.1 ≤ WithZero.exp c} :=
    hc.preimage measurable_snd.fst
  have h₂ : MeasurableSet {p : v.adicCompletion ℚ × v.adicCompletion ℚ × v.adicCompletion ℚ |
      Valued.v p.2.2 ≤ WithZero.exp c * Valued.v p.2.1} := by
    rw [setOf_valued_snd_le_eq]
    refine (((measurableSet_singleton 0).preimage measurable_snd.fst).inter
      ((measurableSet_singleton 0).preimage measurable_snd.snd)).union
      (((measurableSet_singleton 0).preimage measurable_snd.fst).compl.inter
        (hc.preimage (measurable_snd.snd.div measurable_snd.fst)))
  have h₃ : MeasurableSet {p : v.adicCompletion ℚ × v.adicCompletion ℚ × v.adicCompletion ℚ |
      Valued.v (p.1 - p.2.2 / p.2.1) ≤ WithZero.exp c} :=
    hc.preimage (measurable_fst.sub (measurable_snd.snd.div measurable_snd.fst))
  have hset : primedBall3 v c = {p : v.adicCompletion ℚ × v.adicCompletion ℚ × v.adicCompletion ℚ |
      Valued.v p.2.1 ≤ WithZero.exp c} ∩ {p | Valued.v p.2.2 ≤ WithZero.exp c * Valued.v p.2.1} ∩
      {p | Valued.v (p.1 - p.2.2 / p.2.1) ≤ WithZero.exp c} := by
    ext p
    simp only [primedBall3, Set.mem_setOf_eq, Set.mem_inter_iff, and_assoc]
  rw [hset]
  exact (h₁.inter h₂).inter h₃

end DualFiniteLevel
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_tendsto_setIntegral_annulus_setIntegral_ball_jacquetWindow_sub_jacquetValue.LaurentZetaSlot"

end LanglandsTunnell.CubicInduction
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_tendsto_setIntegral_annulus_setIntegral_ball_jacquetWindow_sub_jacquetValue.LaurentZetaSlot"
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_tendsto_setIntegral_annulus_setIntegral_ball_jacquetWindow_sub_jacquetValue.LaurentZetaSlot"
end Part34
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_tendsto_setIntegral_annulus_setIntegral_ball_jacquetWindow_sub_jacquetValue.LaurentZetaSlot"

section Part35

set_option autoImplicit false

p2m_open "MeasureTheory IsDedekindDomain NumberField LanglandsTunnell.TateLocal P2MW.S_LanglandsTunnell_CubicInduction_tendsto_setIntegral_annulus_setIntegral_ball_jacquetWindow_sub_jacquetValue.LanglandsTunnell.TateLocal NumberField.StandardAddChar"
open scoped ENNReal NNReal

attribute [local instance] LanglandsTunnell.TateLocal.localBorel

namespace LanglandsTunnell
p2m_export "LanglandsTunnell" "TateLocal.localBorel TateLocal.borelSpace_localBorel TateLocal.integersPositiveCompacts TateLocal.coe_integersPositiveCompacts"
namespace CubicInduction
p2m_export "LanglandsTunnell.CubicInduction" "unipotentBall3 mem_unipotentBall3_iff jacquetHaar3 jacquetTruncated3 jacquetLevel jacquetValue jacquetTruncated3_eq_jacquetValue bigCell3 mem_bigCell3_iff cellSectionOf cellSectionOf_apply_of_mem cellSectionOf_apply_of_notMem cellSectionOf_upperUnipotent3_mul cellSectionOf_diagonal3_mul principalSeries3 gl3Entry cornerEntry lowerMinor outerMinor gl3Det gl3Det_ne_zero cellRatio cellValue antidiagonal3 antidiagonal3_coe eventually_valued_eq eventually_valued_lt eventually_norm_eq eventually_charExt_eq continuous_gl3Entry continuous_cornerEntry continuous_lowerMinor continuous_outerMinor continuous_gl3Det exists_bottom_entry_ne_zero_of_cornerEntry_eq_zero outerMinor_ne_zero_of_lowerMinor_eq_zero gl3AmbientRightTranslate gl3AmbientRightTranslate_apply transposeInv3 upperUnipotent3 upperUnipotent3_coe embedMat2 iotaGL coe_iotaGL LocalGL3 diagUnitGL2 coe_diagUnitGL2 lowerUnipotent21 longWeyl3 longWeyl3_coe weylPrime3 weylPrime3_coe transposeInv3_weylPrime3 transposeInv3_lowerUnipotent21 exists_forall_le_integrableOn_and_jacquetTruncated3_eq_of_cellSectionOf exists_forall_gl3AmbientRightTranslate_eq_of_mem_principalSeries3"
p2m_open "LanglandsTunnell.CubicInduction LanglandsTunnell"

section DualRemainder

variable (v : HeightOneSpectrum (𝓞 ℚ))

open Classical in
private noncomputable def primedKernel (ν : Fin 3 → ((v.adicCompletion ℚ)ˣ →* ℂˣ))
    (Φ : (Fin 3 → v.adicCompletion ℚ) → ℂ) (c : ℤ) (a x : v.adicCompletion ℚ) : ℂ :=
  if h : a = 0 then 0 else jacquetPrimed3 v ν Φ c (Units.mk0 a h) x

open Classical in
private noncomputable def valueKernel (ν : Fin 3 → ((v.adicCompletion ℚ)ˣ →* ℂˣ))
    (Φ : (Fin 3 → v.adicCompletion ℚ) → ℂ) (a x : v.adicCompletion ℚ) : ℂ :=
  if h : a = 0 then 0 else jacquetValue v (dualTranslate v ν Φ (Units.mk0 a h) x)

private noncomputable def dualWeight (χ : (v.adicCompletion ℚ)ˣ →* ℂˣ) (s : ℂ) (a : v.adicCompletion ℚ) : ℂ :=
  ((modulus a : ℝ) : ℂ)⁻¹ * charExt χ⁻¹ a * ((modulus a : ℝ) : ℂ) ^ (1 - s)

private def xBall (R : ℕ) : Set (v.adicCompletion ℚ) :=
  {x | Valued.v x ≤ WithZero.exp (R : ℤ)}

private noncomputable def pieceW (ν : Fin 3 → ((v.adicCompletion ℚ)ˣ →* ℂˣ))
    (Φ : (Fin 3 → v.adicCompletion ℚ) → ℂ) (χ : (v.adicCompletion ℚ)ˣ →* ℂˣ) (s : ℂ) (N R : ℕ) (c : ℤ) : ℂ :=
  ∫ a in annulus v N, dualWeight v χ s a *
    ∫ x in xBall v R, (primedKernel v ν Φ c a x - valueKernel v ν Φ a x) ∂(selfDualHaarAt ℚ v)
    ∂(mulMeasure (selfDualHaarAt ℚ v))

end DualRemainder
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_tendsto_setIntegral_annulus_setIntegral_ball_jacquetWindow_sub_jacquetValue.LaurentZetaSlot"

end LanglandsTunnell.CubicInduction
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_tendsto_setIntegral_annulus_setIntegral_ball_jacquetWindow_sub_jacquetValue.LaurentZetaSlot"
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_tendsto_setIntegral_annulus_setIntegral_ball_jacquetWindow_sub_jacquetValue.LaurentZetaSlot"
end Part35
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_tendsto_setIntegral_annulus_setIntegral_ball_jacquetWindow_sub_jacquetValue.LaurentZetaSlot"

section Part37
set_option autoImplicit false

p2m_open "MeasureTheory IsDedekindDomain NumberField LanglandsTunnell.TateLocal P2MW.S_LanglandsTunnell_CubicInduction_tendsto_setIntegral_annulus_setIntegral_ball_jacquetWindow_sub_jacquetValue.LanglandsTunnell.TateLocal NumberField.StandardAddChar"
open scoped ENNReal NNReal

attribute [local instance] LanglandsTunnell.TateLocal.localBorel

namespace LanglandsTunnell
p2m_export "LanglandsTunnell" "TateLocal.localBorel TateLocal.borelSpace_localBorel TateLocal.integersPositiveCompacts TateLocal.coe_integersPositiveCompacts"
namespace CubicInduction
p2m_export "LanglandsTunnell.CubicInduction" "unipotentBall3 mem_unipotentBall3_iff jacquetHaar3 jacquetTruncated3 jacquetLevel jacquetValue jacquetTruncated3_eq_jacquetValue bigCell3 mem_bigCell3_iff cellSectionOf cellSectionOf_apply_of_mem cellSectionOf_apply_of_notMem cellSectionOf_upperUnipotent3_mul cellSectionOf_diagonal3_mul principalSeries3 gl3Entry cornerEntry lowerMinor outerMinor gl3Det gl3Det_ne_zero cellRatio cellValue antidiagonal3 antidiagonal3_coe eventually_valued_eq eventually_valued_lt eventually_norm_eq eventually_charExt_eq continuous_gl3Entry continuous_cornerEntry continuous_lowerMinor continuous_outerMinor continuous_gl3Det exists_bottom_entry_ne_zero_of_cornerEntry_eq_zero outerMinor_ne_zero_of_lowerMinor_eq_zero gl3AmbientRightTranslate gl3AmbientRightTranslate_apply transposeInv3 upperUnipotent3 upperUnipotent3_coe embedMat2 iotaGL coe_iotaGL LocalGL3 diagUnitGL2 coe_diagUnitGL2 lowerUnipotent21 longWeyl3 longWeyl3_coe weylPrime3 weylPrime3_coe transposeInv3_weylPrime3 transposeInv3_lowerUnipotent21 exists_forall_le_integrableOn_and_jacquetTruncated3_eq_of_cellSectionOf exists_forall_gl3AmbientRightTranslate_eq_of_mem_principalSeries3"
p2m_open "LanglandsTunnell.CubicInduction LanglandsTunnell"

section DualRemainderWedge

variable (v : HeightOneSpectrum (𝓞 ℚ))

private scoped instance instBorelSpaceWedge : BorelSpace (v.adicCompletion ℚ) := borelSpace_localBorel ℚ v

private scoped instance instSFiniteSelfDualHaarAtWedge : SFinite (selfDualHaarAt ℚ v) := sFinite_selfDualHaarAt ℚ v

private scoped instance instSFiniteMulMeasureWedge : SFinite (mulMeasure (selfDualHaarAt ℚ v)) :=
  sFinite_mulMeasure_selfDualHaarAt ℚ v

private scoped instance instIsAddHaarMeasureSelfDualHaarAtWedge : (selfDualHaarAt ℚ v).IsAddHaarMeasure :=
  isAddHaarMeasure_selfDualHaarAt ℚ v

private theorem primedBall3_eq_inter (c : ℤ) :
    primedBall3 v c = unipotentBall3 v c ∩ {p | Valued.v p.2.2 ≤ WithZero.exp c * Valued.v p.2.1} := by
  ext ⟨α, β, γ⟩
  simp only [primedBall3, unipotentBall3, Set.mem_inter_iff, Set.mem_setOf_eq]
  have hquot : Valued.v γ ≤ WithZero.exp c * Valued.v β → Valued.v (γ / β) ≤ WithZero.exp c := fun h => by
    by_cases hβ : β = 0
    · simp [hβ]
    · rw [map_div₀, div_le_iff₀ (zero_lt_iff.mpr ((map_ne_zero _).mpr hβ))]
      exact h
  constructor
  · rintro ⟨hβ, hγ, hα⟩
    refine ⟨⟨?_, hβ, ?_⟩, hγ⟩
    · have hsum : α = (α - γ / β) + γ / β := by ring
      rw [hsum]
      exact (Valued.v.map_add _ _).trans (max_le hα (hquot hγ))
    · calc Valued.v γ ≤ WithZero.exp c * Valued.v β := hγ
        _ ≤ WithZero.exp c * WithZero.exp c := mul_le_mul' le_rfl hβ
        _ = WithZero.exp (2 * c) := by rw [← WithZero.exp_add, two_mul]
  · rintro ⟨⟨hα, hβ, -⟩, hγ⟩
    exact ⟨hβ, hγ, (Valued.v.map_sub _ _).trans (max_le hα (hquot hγ))⟩

private theorem unipotentBall3_diff_primedBall3 (c : ℤ) :
    unipotentBall3 v c \ primedBall3 v c =
      unipotentBall3 v c ∩ {p | WithZero.exp c * Valued.v p.2.1 < Valued.v p.2.2} := by
  rw [primedBall3_eq_inter, Set.diff_self_inter, Set.diff_eq]
  congr 1
  ext p
  simp only [Set.mem_compl_iff, Set.mem_setOf_eq, not_le]

private theorem valued_lt_exp_iff (y : v.adicCompletion ℚ) (n : ℤ) :
    Valued.v y < WithZero.exp n ↔ Valued.v y ≤ WithZero.exp (n - 1) := by
  by_cases hy : y = 0
  · subst hy
    simp only [map_zero]
    exact ⟨fun _ => zero_le', fun _ => zero_lt_iff.mpr WithZero.exp_ne_zero⟩
  · have hy' : Valued.v y ≠ 0 := (Valuation.ne_zero_iff _).mpr hy
    rw [← WithZero.exp_log hy', WithZero.exp_lt_exp, WithZero.exp_le_exp]
    omega

private theorem continuous_upperUnipotent3 :
    Continuous fun p : v.adicCompletion ℚ × v.adicCompletion ℚ × v.adicCompletion ℚ =>
      (upperUnipotent3 p.1 p.2.1 p.2.2 : LocalGL3 v) := by
  refine Units.continuous_iff.mpr ⟨?_, ?_⟩
  · show Continuous fun p : v.adicCompletion ℚ × v.adicCompletion ℚ × v.adicCompletion ℚ =>
      !![(1 : v.adicCompletion ℚ), p.1, p.2.2; 0, 1, p.2.1; 0, 0, 1]
    refine continuous_matrix fun i j => ?_
    fin_cases i <;> fin_cases j <;> simp only [Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.cons_val_two, Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk, Matrix.empty_val',
      Matrix.cons_val_fin_one] <;>
      first
        | exact continuous_const
        | exact continuous_fst
        | exact continuous_snd.fst
        | exact continuous_snd.snd
  · show Continuous fun p : v.adicCompletion ℚ × v.adicCompletion ℚ × v.adicCompletion ℚ =>
      !![(1 : v.adicCompletion ℚ), -p.1, p.1 * p.2.1 - p.2.2; 0, 1, -p.2.1; 0, 0, 1]
    refine continuous_matrix fun i j => ?_
    fin_cases i <;> fin_cases j <;> simp only [Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.cons_val_two, Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk, Matrix.empty_val',
      Matrix.cons_val_fin_one] <;>
      first
        | exact continuous_const
        | exact continuous_fst.neg
        | exact continuous_snd.fst.neg
        | exact (continuous_fst.mul continuous_snd.fst).sub continuous_snd.snd

private theorem continuous_dualCellPoint (a : (v.adicCompletion ℚ)ˣ) (x : v.adicCompletion ℚ) :
    Continuous fun p : v.adicCompletion ℚ × v.adicCompletion ℚ × v.adicCompletion ℚ =>
      dualCellPoint v p.1 p.2.1 p.2.2 a x := by
  unfold dualCellPoint
  exact (continuous_const.mul (continuous_upperUnipotent3 v)).mul continuous_const

private theorem integrableOn_psiLocal_mul_cellSectionOf_dualCellPoint
    (ν : Fin 3 → ((v.adicCompletion ℚ)ˣ →* ℂˣ)) (hν : ∀ i, IsLocallyConstant (ν i))
    (Φ : (Fin 3 → v.adicCompletion ℚ) → ℂ) (hΦl : IsLocallyConstant Φ) (hΦc : HasCompactSupport Φ) (c : ℤ)
    (a : (v.adicCompletion ℚ)ˣ) (x : v.adicCompletion ℚ) :
    IntegrableOn (fun p : v.adicCompletion ℚ × v.adicCompletion ℚ × v.adicCompletion ℚ =>
      psiLocal ℚ v (-(p.1 + p.2.1)) * cellSectionOf v ν Φ (dualCellPoint v p.1 p.2.1 p.2.2 a x))
      (unipotentBall3 v c) (jacquetHaar3 v) := by
  have hcont : Continuous fun p : v.adicCompletion ℚ × v.adicCompletion ℚ × v.adicCompletion ℚ =>
      psiLocal ℚ v (-(p.1 + p.2.1)) * cellSectionOf v ν Φ (dualCellPoint v p.1 p.2.1 p.2.2 a x) :=
    ((continuous_psiLocal ℚ v).comp (continuous_fst.add continuous_snd.fst).neg).mul
      ((isLocallyConstant_cellSectionOf v ν Φ hν hΦl hΦc).continuous.comp (continuous_dualCellPoint v a x))
  have hball : unipotentBall3 v c = {y : v.adicCompletion ℚ | Valued.v y ≤ WithZero.exp c} ×ˢ
      ({y : v.adicCompletion ℚ | Valued.v y ≤ WithZero.exp c} ×ˢ
        {y : v.adicCompletion ℚ | Valued.v y ≤ WithZero.exp (2 * c)}) := by
    ext p
    simp only [unipotentBall3, Set.mem_setOf_eq, Set.mem_prod]
  have hK : IsCompact (unipotentBall3 v c) := by
    rw [hball]
    exact (isCompact_valued_le v c).prod ((isCompact_valued_le v c).prod (isCompact_valued_le v (2 * c)))
  have hfin : jacquetHaar3 v (unipotentBall3 v c) ≠ ∞ := by
    show (selfDualHaarAt ℚ v).prod ((selfDualHaarAt ℚ v).prod (selfDualHaarAt ℚ v)) (unipotentBall3 v c) ≠ ∞
    rw [hball, Measure.prod_prod, Measure.prod_prod]
    exact ENNReal.mul_ne_top (isCompact_valued_le v c).measure_lt_top.ne
      (ENNReal.mul_ne_top (isCompact_valued_le v c).measure_lt_top.ne
        (isCompact_valued_le v (2 * c)).measure_lt_top.ne)
  obtain ⟨C, hC⟩ := hK.exists_bound_of_continuousOn hcont.continuousOn
  exact Measure.integrableOn_of_bounded hfin hcont.aestronglyMeasurable
    (ae_restrict_of_forall_mem (measurableSet_unipotentBall3 v c) hC)

private theorem norm_mul_inv_uniformizerUnit (ν : Fin 3 → ((v.adicCompletion ℚ)ˣ →* ℂˣ))
    (χ : (v.adicCompletion ℚ)ˣ →* ℂˣ)
    (hu : ∀ i, ‖(((ν i * χ) (NumberField.AdelicLevel.uniformizerUnit ℚ v) : ℂˣ) : ℂ)‖ = 1) (i j : Fin 3) :
    ‖(((ν i * (ν j)⁻¹) (NumberField.AdelicLevel.uniformizerUnit ℚ v) : ℂˣ) : ℂ)‖ = 1 := by
  have hn : ∀ k, ‖((ν k (NumberField.AdelicLevel.uniformizerUnit ℚ v) : ℂˣ) : ℂ)‖ =
      ‖((χ (NumberField.AdelicLevel.uniformizerUnit ℚ v) : ℂˣ) : ℂ)‖⁻¹ := fun k => by
    have hk := hu k
    rw [MonoidHom.mul_apply, Units.val_mul, norm_mul] at hk
    exact eq_inv_of_mul_eq_one_left hk
  rw [MonoidHom.mul_apply, MonoidHom.inv_apply, Units.val_mul, Units.val_inv_eq_inv_val, norm_mul, norm_inv, hn i,
    hn j, inv_inv]
  exact inv_mul_cancel₀ (norm_ne_zero_iff.mpr (Units.ne_zero _))

private theorem norm_dualWeight_mul_eq (ν₀ χ : (v.adicCompletion ℚ)ˣ →* ℂˣ) (s : ℂ) {a : v.adicCompletion ℚ}
    (ha : a ≠ 0) :
    ‖dualWeight v χ s a‖ * (‖(((ν₀ (Units.mk0 a ha))⁻¹ : ℂˣ) : ℂ)‖ * (modulus a : ℝ)) =
      ‖charExt (ν₀ * χ)⁻¹ a‖ * (modulus a : ℝ) ^ (1 - s.re) := by
  have hN : (0 : ℝ) < (modulus a : ℝ) := by
    rw [modulus_real_eq_norm]
    exact norm_pos_iff.mpr ha
  have h1 : ‖(((modulus a : ℝ) : ℂ))⁻¹‖ = (modulus a : ℝ)⁻¹ := by
    rw [norm_inv, Complex.norm_real, Real.norm_of_nonneg hN.le]
  have h2 : ‖((modulus a : ℝ) : ℂ) ^ (1 - s)‖ = (modulus a : ℝ) ^ (1 - s.re) := by
    rw [Complex.norm_cpow_eq_rpow_re_of_pos hN, Complex.sub_re, Complex.one_re]
  have h3 :
      ‖charExt χ⁻¹ a‖ * ‖(((ν₀ (Units.mk0 a ha))⁻¹ : ℂˣ) : ℂ)‖ = ‖charExt (ν₀ * χ)⁻¹ a‖ := by
    rw [charExt_of_ne_zero χ⁻¹ ha, charExt_of_ne_zero (ν₀ * χ)⁻¹ ha, MonoidHom.inv_apply,
      MonoidHom.inv_apply,
      MonoidHom.mul_apply, mul_inv, Units.val_mul, norm_mul, mul_comm]
  rw [dualWeight, norm_mul, norm_mul, h1, h2, ← h3]
  calc (modulus a : ℝ)⁻¹ * ‖charExt χ⁻¹ a‖ * (modulus a : ℝ) ^ (1 - s.re) *
        (‖(((ν₀ (Units.mk0 a ha))⁻¹ : ℂˣ) : ℂ)‖ * (modulus a : ℝ))
      = (modulus a : ℝ)⁻¹ * (modulus a : ℝ) *
          (‖charExt χ⁻¹ a‖ * ‖(((ν₀ (Units.mk0 a ha))⁻¹ : ℂˣ) : ℂ)‖ * (modulus a : ℝ) ^ (1 - s.re)) := by
          ring
    _ = ‖charExt χ⁻¹ a‖ * ‖(((ν₀ (Units.mk0 a ha))⁻¹ : ℂˣ) : ℂ)‖ * (modulus a : ℝ) ^ (1 - s.re) := by
          rw [inv_mul_cancel₀ hN.ne', one_mul]

private theorem primedKernel_sub_valueKernel_eq (ν : Fin 3 → ((v.adicCompletion ℚ)ˣ →* ℂˣ))
    (hν : ∀ i, IsLocallyConstant (ν i)) (Φ : (Fin 3 → v.adicCompletion ℚ) → ℂ) (hΦl : IsLocallyConstant Φ)
    (hΦc : HasCompactSupport Φ) {N R : ℕ} {T₀ c₀ : ℤ} {c₁ : ℕ}
    (hfar : ∀ c : ℤ, c₀ ≤ c → ∀ (a : (v.adicCompletion ℚ)ˣ) (x : v.adicCompletion ℚ),
      ∫ p in unipotentBall3 v c ∩ {p | WithZero.exp c * Valued.v p.2.1 < Valued.v p.2.2} ∩
          {p | WithZero.exp T₀ ≤ Valued.v (p.1 - p.2.2 / (a : v.adicCompletion ℚ) * x)},
        psiLocal ℚ v (-(p.1 + p.2.1)) * cellSectionOf v ν Φ (dualCellPoint v p.1 p.2.1 p.2.2 a x)
        ∂(jacquetHaar3 v) = 0)
    (hc₁ : ∀ (a : (v.adicCompletion ℚ)ˣ) (x : v.adicCompletion ℚ),
      (a, x) ∈ paramSet v N ((Ideal.absNorm v.asIdeal : ℝ) ^ (R : ℤ)) → ∀ c : ℤ, (c₁ : ℤ) ≤ c →
        jacquetTruncated3 v c (dualTranslate v ν Φ a x) = jacquetValue v (dualTranslate v ν Φ a x))
    {c : ℤ} (hc₀ : c₀ ≤ c) (hc : (c₁ : ℤ) ≤ c) {a : v.adicCompletion ℚ} (haA : a ∈ annulus v N)
    {x : v.adicCompletion ℚ} (hx : x ∈ xBall v R) :
    primedKernel v ν Φ c a x - valueKernel v ν Φ a x =
      -∫ p in unipotentBall3 v c ∩ {p | WithZero.exp c * Valued.v p.2.1 < Valued.v p.2.2} ∩
          {p | Valued.v
              (p.1 - p.2.2 / (Units.mk0 a (ne_zero_of_mem_annulus v haA) : v.adicCompletion ℚ) * x) <
            WithZero.exp T₀},
          psiLocal ℚ v (-(p.1 + p.2.1)) *
            cellSectionOf v ν Φ (dualCellPoint v p.1 p.2.1 p.2.2 (Units.mk0 a (ne_zero_of_mem_annulus v haA)) x)
          ∂(jacquetHaar3 v) := by
  have ha : a ≠ 0 := ne_zero_of_mem_annulus v haA
  have hmem : (Units.mk0 a ha, x) ∈ paramSet v N ((Ideal.absNorm v.asIdeal : ℝ) ^ (R : ℤ)) :=
    (mem_paramSet v).mpr ⟨haA, norm_le_zpow_of_valued_le v hx⟩
  have hInt := integrableOn_psiLocal_mul_cellSectionOf_dualCellPoint v ν hν Φ hΦl hΦc c (Units.mk0 a ha) x
  have hsub : primedBall3 v c ⊆ unipotentBall3 v c := by
    rw [primedBall3_eq_inter]
    exact Set.inter_subset_left
  have hU : Measurable fun p : v.adicCompletion ℚ × v.adicCompletion ℚ × v.adicCompletion ℚ =>
      p.1 - p.2.2 / (Units.mk0 a ha : v.adicCompletion ℚ) * x :=
    measurable_fst.sub ((measurable_snd.snd.div_const _).mul_const _)
  have hnear : MeasurableSet {p : v.adicCompletion ℚ × v.adicCompletion ℚ × v.adicCompletion ℚ |
      Valued.v (p.1 - p.2.2 / (Units.mk0 a ha : v.adicCompletion ℚ) * x) < WithZero.exp T₀} := by
    have hpre : {p : v.adicCompletion ℚ × v.adicCompletion ℚ × v.adicCompletion ℚ |
        Valued.v (p.1 - p.2.2 / (Units.mk0 a ha : v.adicCompletion ℚ) * x) < WithZero.exp T₀} =
          (fun p : v.adicCompletion ℚ × v.adicCompletion ℚ × v.adicCompletion ℚ =>
            p.1 - p.2.2 / (Units.mk0 a ha : v.adicCompletion ℚ) * x) ⁻¹' {y | Valued.v y ≤ WithZero.exp (T₀ - 1)} := by
      ext p
      simp only [Set.mem_setOf_eq, Set.mem_preimage, valued_lt_exp_iff]
    rw [hpre]
    exact (isClosed_valued_le v (T₀ - 1)).measurableSet.preimage hU
  have hcompl : {p : v.adicCompletion ℚ × v.adicCompletion ℚ × v.adicCompletion ℚ |
      Valued.v (p.1 - p.2.2 / (Units.mk0 a ha : v.adicCompletion ℚ) * x) < WithZero.exp T₀}ᶜ =
        {p | WithZero.exp T₀ ≤ Valued.v (p.1 - p.2.2 / (Units.mk0 a ha : v.adicCompletion ℚ) * x)} := by
    ext p
    simp only [Set.mem_compl_iff, Set.mem_setOf_eq, not_lt]
  have hP : primedKernel v ν Φ c a x = jacquetPrimed3 v ν Φ c (Units.mk0 a ha) x := by
    simp only [primedKernel, dif_neg ha]
  have hV : valueKernel v ν Φ a x = jacquetTruncated3 v c (dualTranslate v ν Φ (Units.mk0 a ha) x) := by
    simp only [valueKernel, dif_neg ha]
    exact (hc₁ (Units.mk0 a ha) x hmem c hc).symm
  have hJ : jacquetTruncated3 v c (dualTranslate v ν Φ (Units.mk0 a ha) x) =
      ∫ p in unipotentBall3 v c, psiLocal ℚ v (-(p.1 + p.2.1)) *
              cellSectionOf v ν Φ (dualCellPoint v p.1 p.2.1 p.2.2 (Units.mk0 a ha) x) ∂(jacquetHaar3 v) := rfl
  have hJ' : jacquetPrimed3 v ν Φ c (Units.mk0 a ha) x =
      ∫ p in primedBall3 v c, psiLocal ℚ v (-(p.1 + p.2.1)) *
              cellSectionOf v ν Φ (dualCellPoint v p.1 p.2.1 p.2.2 (Units.mk0 a ha) x) ∂(jacquetHaar3 v) := rfl
  rw [hP, hV, hJ, hJ', ← neg_sub, ← setIntegral_diff (measurableSet_primedBall3 v c) hInt hsub,
    unipotentBall3_diff_primedBall3, ← integral_inter_add_diff hnear (hInt.mono_set Set.inter_subset_left),
    Set.diff_eq, hcompl, hfar c hc₀ (Units.mk0 a ha) x, add_zero]

private theorem modulus_rpow_one_sub_le_of_mem_annulus (σ : ℝ) {N : ℕ} {a : v.adicCompletion ℚ}
    (haA : a ∈ annulus v N) :
    (modulus a : ℝ) ^ (1 - σ) ≤ ((Ideal.absNorm v.asIdeal : ℝ) ^ (N : ℤ)) ^ |σ| * (modulus a : ℝ) := by
  have hq1 : (1 : ℝ) < (Ideal.absNorm v.asIdeal : ℝ) := one_lt_absNorm_real v
  have hq0 : (0 : ℝ) < (Ideal.absNorm v.asIdeal : ℝ) := one_pos.trans hq1
  obtain ⟨j, hj⟩ := LaurentZetaSlot.exists_mem_shell v (ne_zero_of_mem_annulus v haA)
  have hva : Valued.v a = WithZero.exp (-j) := hj
  have hm : (modulus a : ℝ) = (Ideal.absNorm v.asIdeal : ℝ) ^ (-j) := LaurentZetaSlot.coe_modulus_eq_of_mem_shell v hj
  have hlow : -(N : ℤ) ≤ -j := by
    have h := haA.1
    rw [hva, WithZero.exp_le_exp] at h
    exact h
  have hupp : -j ≤ (N : ℤ) := by
    have h := haA.2
    rw [hva, WithZero.exp_le_exp] at h
    exact h
  have hQ0 : (0 : ℝ) < (Ideal.absNorm v.asIdeal : ℝ) ^ (N : ℤ) := zpow_pos hq0 _
  have hm0 : (0 : ℝ) < (modulus a : ℝ) := by
    rw [hm]
    exact zpow_pos hq0 _
  have hmQ : (modulus a : ℝ) ≤ (Ideal.absNorm v.asIdeal : ℝ) ^ (N : ℤ) := by
    rw [hm]
    exact zpow_le_zpow_right₀ hq1.le hupp
  have hQm : ((Ideal.absNorm v.asIdeal : ℝ) ^ (N : ℤ))⁻¹ ≤ (modulus a : ℝ) := by
    rw [hm, ← zpow_neg]
    exact zpow_le_zpow_right₀ hq1.le hlow
  have hpow : (modulus a : ℝ) ^ (-σ) ≤ ((Ideal.absNorm v.asIdeal : ℝ) ^ (N : ℤ)) ^ |σ| := by
    rcases le_or_gt 0 σ with hσ | hσ
    · calc (modulus a : ℝ) ^ (-σ)
          ≤ ((Ideal.absNorm v.asIdeal : ℝ) ^ (N : ℤ))⁻¹ ^ (-σ) :=
            Real.rpow_le_rpow_of_nonpos (inv_pos.mpr hQ0) hQm (neg_nonpos.mpr hσ)
        _ = ((Ideal.absNorm v.asIdeal : ℝ) ^ (N : ℤ)) ^ |σ| := by
            rw [Real.inv_rpow hQ0.le, Real.rpow_neg hQ0.le, inv_inv, abs_of_nonneg hσ]
    · calc (modulus a : ℝ) ^ (-σ)
          ≤ ((Ideal.absNorm v.asIdeal : ℝ) ^ (N : ℤ)) ^ (-σ) := Real.rpow_le_rpow hm0.le hmQ (neg_nonneg.mpr hσ.le)
        _ = ((Ideal.absNorm v.asIdeal : ℝ) ^ (N : ℤ)) ^ |σ| := by rw [abs_of_neg hσ]
  calc (modulus a : ℝ) ^ (1 - σ) = (modulus a : ℝ) ^ (-σ) * (modulus a : ℝ) := by
        rw [sub_eq_neg_add, Real.rpow_add_one hm0.ne' (-σ)]
    _ ≤ ((Ideal.absNorm v.asIdeal : ℝ) ^ (N : ℤ)) ^ |σ| * (modulus a : ℝ) := mul_le_mul_of_nonneg_right hpow hm0.le

private theorem tendsto_pieceW₀
    (ν : Fin 3 → ((v.adicCompletion ℚ)ˣ →* ℂˣ)) (hν : ∀ i, IsLocallyConstant (ν i))
    (Φ : (Fin 3 → v.adicCompletion ℚ) → ℂ) (hΦl : IsLocallyConstant Φ) (hΦc : HasCompactSupport Φ)
    (χ : (v.adicCompletion ℚ)ˣ →* ℂˣ) (hχ : IsLocallyConstant χ)
    (hu : ∀ i, ‖(((ν i * χ) (NumberField.AdelicLevel.uniformizerUnit ℚ v) : ℂˣ) : ℂ)‖ = 1)
    (s : ℂ) (N R : ℕ) :
    Filter.Tendsto (fun c : ℤ => pieceW v ν Φ χ s N R c) Filter.atTop (nhds 0) := by
  have hq1 : (1 : ℝ) < (Ideal.absNorm v.asIdeal : ℝ) := one_lt_absNorm_real v
  have hq0 : (0 : ℝ) < (Ideal.absNorm v.asIdeal : ℝ) := one_pos.trans hq1
  have hA : MeasurableSet (annulus v N) := (isClosed_annulus v N).measurableSet
  have hBfin : selfDualHaarAt ℚ v (xBall v R) < ∞ := (isCompact_valued_le v (R : ℤ)).measure_lt_top

  obtain ⟨c₁, hc₁⟩ := exists_level_forall_dualTranslate_of_isCompact v ν Φ hν hΦl hΦc
    (isCompact_paramSet v N ((Ideal.absNorm v.asIdeal : ℝ) ^ (R : ℤ)))
  obtain ⟨T₀, c₀, hfar⟩ := exists_forall_setIntegral_wedge_far_eq_zero v ν Φ hν hΦl hΦc
  obtain ⟨C, hC0, hnear⟩ := exists_forall_norm_setIntegral_wedge_near_le v ν Φ hν hΦl hΦc
    (norm_mul_inv_uniformizerUnit v ν χ hu 1 0) (norm_mul_inv_uniformizerUnit v ν χ hu 2 1) T₀
  have hξ1 : ‖((((ν 0 * χ)⁻¹) (NumberField.AdelicLevel.uniformizerUnit ℚ v) : ℂˣ) : ℂ)‖ = 1 := by
    rw [MonoidHom.inv_apply, Units.val_inv_eq_inv_val, norm_inv, hu 0, inv_one]
  obtain ⟨Mξ₀, hMξ₀0, hMξ₀⟩ := exists_forall_norm_charExt_le v (ν 0 * χ)⁻¹ ((hν 0).mul hχ).inv hξ1
  obtain ⟨g, hg, hg0, hgle⟩ := exists_integrable_modulus_rpow_le v 1 one_pos ((Ideal.absNorm v.asIdeal : ℝ) ^ (N : ℤ))

  obtain ⟨Mξ, hMξ0, hMξ⟩ : ∃ M : ℝ, 0 ≤ M ∧ ∀ a ∈ annulus v N, a ≠ 0 →
      ‖charExt (ν 0 * χ)⁻¹ a‖ * (modulus a : ℝ) ^ (1 - s.re) ≤ M * g a := by
    refine ⟨Mξ₀ * ((Ideal.absNorm v.asIdeal : ℝ) ^ (N : ℤ)) ^ |s.re|,
      mul_nonneg hMξ₀0 (Real.rpow_nonneg (zpow_nonneg hq0.le _) _), fun a haA ha => ?_⟩
    have hmod : (modulus a : ℝ) ≤ (Ideal.absNorm v.asIdeal : ℝ) ^ (N : ℤ) := by
      rw [modulus_real_eq_norm]
      exact norm_le_zpow_of_valued_le v haA.2
    have hga : (modulus a : ℝ) ≤ g a := by simpa only [Real.rpow_one] using hgle a ha hmod
    calc ‖charExt (ν 0 * χ)⁻¹ a‖ * (modulus a : ℝ) ^ (1 - s.re)
        ≤ Mξ₀ * (((Ideal.absNorm v.asIdeal : ℝ) ^ (N : ℤ)) ^ |s.re| * (modulus a : ℝ)) :=
          mul_le_mul (hMξ₀ a ha) (modulus_rpow_one_sub_le_of_mem_annulus v s.re haA)
            (Real.rpow_nonneg (NNReal.coe_nonneg _) _) hMξ₀0
      _ ≤ Mξ₀ * (((Ideal.absNorm v.asIdeal : ℝ) ^ (N : ℤ)) ^ |s.re| * g a) :=
          mul_le_mul_of_nonneg_left
            (mul_le_mul_of_nonneg_left hga (Real.rpow_nonneg (zpow_nonneg hq0.le _) _)) hMξ₀0
      _ = Mξ₀ * ((Ideal.absNorm v.asIdeal : ℝ) ^ (N : ℤ)) ^ |s.re| * g a := by ring

  have hbd : ∀ c : ℤ, c₀ ≤ c → (c₁ : ℤ) ≤ c → ∀ a ∈ annulus v N,
      ‖dualWeight v χ s a * ∫ x in xBall v R, (primedKernel v ν Φ c a x - valueKernel v ν Φ a x)
          ∂(selfDualHaarAt ℚ v)‖ ≤
        (C * (selfDualHaarAt ℚ v).real (xBall v R) * Mξ * (Ideal.absNorm v.asIdeal : ℝ) ^ (-c)) * g a := by
    intro c hc₀ hc a haA
    have ha : a ≠ 0 := ne_zero_of_mem_annulus v haA
    have hinner :
        ‖∫ x in xBall v R, (primedKernel v ν Φ c a x - valueKernel v ν Φ a x) ∂(selfDualHaarAt ℚ v)‖ ≤
          C * (‖(((ν 0 (Units.mk0 a ha))⁻¹ : ℂˣ) : ℂ)‖ * (modulus a : ℝ)) * (Ideal.absNorm v.asIdeal : ℝ) ^ (-c) *
            (selfDualHaarAt ℚ v).real (xBall v R) := by
      refine norm_setIntegral_le_of_norm_le_const hBfin fun x hx => ?_
      have hnear' : ‖∫ p in unipotentBall3 v c ∩ {p | WithZero.exp c * Valued.v p.2.1 < Valued.v p.2.2} ∩
          {p | Valued.v (p.1 - p.2.2 / (Units.mk0 a ha : v.adicCompletion ℚ) * x) <
            WithZero.exp T₀},
          psiLocal ℚ v (-(p.1 + p.2.1)) *
              cellSectionOf v ν Φ (dualCellPoint v p.1 p.2.1 p.2.2 (Units.mk0 a ha) x) ∂(jacquetHaar3 v)‖ ≤
            C * (‖(((ν 0 (Units.mk0 a ha))⁻¹ : ℂˣ) : ℂ)‖ * (modulus a : ℝ)) *
              (Ideal.absNorm v.asIdeal : ℝ) ^ (-c) := hnear c (Units.mk0 a ha) x
      show ‖primedKernel v ν Φ c a x - valueKernel v ν Φ a x‖ ≤ _
      rw [primedKernel_sub_valueKernel_eq v ν hν Φ hΦl hΦc hfar hc₁ hc₀ hc haA hx, norm_neg]
      exact hnear'
    rw [norm_mul]
    calc ‖dualWeight v χ s a‖ *
          ‖∫ x in xBall v R, (primedKernel v ν Φ c a x - valueKernel v ν Φ a x) ∂(selfDualHaarAt ℚ v)‖
        ≤ ‖dualWeight v χ s a‖ *
            (C * (‖(((ν 0 (Units.mk0 a ha))⁻¹ : ℂˣ) : ℂ)‖ * (modulus a : ℝ)) *
              (Ideal.absNorm v.asIdeal : ℝ) ^ (-c) * (selfDualHaarAt ℚ v).real (xBall v R)) :=
          mul_le_mul_of_nonneg_left hinner (norm_nonneg _)
      _ = (C * (selfDualHaarAt ℚ v).real (xBall v R) * (Ideal.absNorm v.asIdeal : ℝ) ^ (-c)) *
            (‖dualWeight v χ s a‖ * (‖(((ν 0 (Units.mk0 a ha))⁻¹ : ℂˣ) : ℂ)‖ * (modulus a : ℝ))) := by
          ring
      _ = (C * (selfDualHaarAt ℚ v).real (xBall v R) * (Ideal.absNorm v.asIdeal : ℝ) ^ (-c)) *
            (‖charExt (ν 0 * χ)⁻¹ a‖ * (modulus a : ℝ) ^ (1 - s.re)) := by
          rw [norm_dualWeight_mul_eq v (ν 0) χ s ha]
      _ ≤ (C * (selfDualHaarAt ℚ v).real (xBall v R) * (Ideal.absNorm v.asIdeal : ℝ) ^ (-c)) * (Mξ * g a) := by
          refine mul_le_mul_of_nonneg_left ?_ (by positivity)
          exact hMξ a haA ha
      _ = (C * (selfDualHaarAt ℚ v).real (xBall v R) * Mξ * (Ideal.absNorm v.asIdeal : ℝ) ^ (-c)) * g a := by ring

  have hW : ∀ c : ℤ, c₀ ≤ c → (c₁ : ℤ) ≤ c → ‖pieceW v ν Φ χ s N R c‖ ≤
      (C * (selfDualHaarAt ℚ v).real (xBall v R) * Mξ * ∫ a, g a ∂(mulMeasure (selfDualHaarAt ℚ v))) *
        (Ideal.absNorm v.asIdeal : ℝ) ^ (-c) := by
    intro c hc₀ hc
    have hKc :
        (0 : ℝ) ≤ C * (selfDualHaarAt ℚ v).real (xBall v R) * Mξ * (Ideal.absNorm v.asIdeal : ℝ) ^ (-c) := by
      positivity
    rw [pieceW]
    calc ‖∫ a in annulus v N, dualWeight v χ s a *
            ∫ x in xBall v R, (primedKernel v ν Φ c a x - valueKernel v ν Φ a x) ∂(selfDualHaarAt ℚ v)
            ∂(mulMeasure (selfDualHaarAt ℚ v))‖
        ≤ ∫ a in annulus v N,
            (C * (selfDualHaarAt ℚ v).real (xBall v R) * Mξ * (Ideal.absNorm v.asIdeal : ℝ) ^ (-c)) * g a
            ∂(mulMeasure (selfDualHaarAt ℚ v)) :=
          norm_integral_le_of_norm_le ((hg.const_mul _).integrableOn)
            (ae_restrict_of_forall_mem hA (hbd c hc₀ hc))
      _ = (C * (selfDualHaarAt ℚ v).real (xBall v R) * Mξ * (Ideal.absNorm v.asIdeal : ℝ) ^ (-c)) *
            ∫ a in annulus v N, g a ∂(mulMeasure (selfDualHaarAt ℚ v)) := integral_const_mul _ _
      _ ≤ (C * (selfDualHaarAt ℚ v).real (xBall v R) * Mξ * (Ideal.absNorm v.asIdeal : ℝ) ^ (-c)) *
            ∫ a, g a ∂(mulMeasure (selfDualHaarAt ℚ v)) :=
          mul_le_mul_of_nonneg_left (setIntegral_le_integral hg (ae_of_all _ hg0)) hKc
      _ = (C * (selfDualHaarAt ℚ v).real (xBall v R) * Mξ * ∫ a, g a ∂(mulMeasure (selfDualHaarAt ℚ v))) *
            (Ideal.absNorm v.asIdeal : ℝ) ^ (-c) := by ring

  have hK₀ :
      (0 : ℝ) ≤ C * (selfDualHaarAt ℚ v).real (xBall v R) * Mξ * ∫ a, g a ∂(mulMeasure (selfDualHaarAt ℚ v)) :=
    mul_nonneg (by positivity) (integral_nonneg hg0)
  refine Metric.tendsto_atTop.mpr fun ε hε => ?_
  obtain ⟨n, hn⟩ := pow_unbounded_of_one_lt
    ((C * (selfDualHaarAt ℚ v).real (xBall v R) * Mξ * ∫ a, g a ∂(mulMeasure (selfDualHaarAt ℚ v))) / ε) hq1
  refine ⟨max (max c₀ (c₁ : ℤ)) (n : ℤ), fun c hc => ?_⟩
  have hc₀ : c₀ ≤ c := ((le_max_left _ _).trans (le_max_left _ _)).trans hc
  have hc₁' : (c₁ : ℤ) ≤ c := ((le_max_right _ _).trans (le_max_left _ _)).trans hc
  have hcn : (n : ℤ) ≤ c := (le_max_right _ _).trans hc
  rw [dist_zero_right]
  refine (hW c hc₀ hc₁').trans_lt ?_
  calc (C * (selfDualHaarAt ℚ v).real (xBall v R) * Mξ * ∫ a, g a ∂(mulMeasure (selfDualHaarAt ℚ v))) *
        (Ideal.absNorm v.asIdeal : ℝ) ^ (-c)
      ≤ (C * (selfDualHaarAt ℚ v).real (xBall v R) * Mξ * ∫ a, g a ∂(mulMeasure (selfDualHaarAt ℚ v))) *
          (Ideal.absNorm v.asIdeal : ℝ) ^ (-(n : ℤ)) :=
        mul_le_mul_of_nonneg_left (zpow_le_zpow_right₀ hq1.le (neg_le_neg hcn)) hK₀
    _ < ε := by
        rw [zpow_neg, zpow_natCast, ← div_eq_mul_inv, div_lt_iff₀ (pow_pos hq0 n), mul_comm ε]
        exact (div_lt_iff₀ hε).mp hn

end DualRemainderWedge
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_tendsto_setIntegral_annulus_setIntegral_ball_jacquetWindow_sub_jacquetValue.LaurentZetaSlot"

end LanglandsTunnell.CubicInduction
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_tendsto_setIntegral_annulus_setIntegral_ball_jacquetWindow_sub_jacquetValue.LaurentZetaSlot P2MW.S_LanglandsTunnell_CubicInduction_tendsto_setIntegral_annulus_setIntegral_ball_jacquetWindow_sub_jacquetValue.LanglandsTunnell P2MW.S_LanglandsTunnell_CubicInduction_tendsto_setIntegral_annulus_setIntegral_ball_jacquetWindow_sub_jacquetValue.LanglandsTunnell.CubicInduction"
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_tendsto_setIntegral_annulus_setIntegral_ball_jacquetWindow_sub_jacquetValue.LaurentZetaSlot P2MW.S_LanglandsTunnell_CubicInduction_tendsto_setIntegral_annulus_setIntegral_ball_jacquetWindow_sub_jacquetValue.LanglandsTunnell"

end Part37
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_tendsto_setIntegral_annulus_setIntegral_ball_jacquetWindow_sub_jacquetValue.LaurentZetaSlot P2MW.S_LanglandsTunnell_CubicInduction_tendsto_setIntegral_annulus_setIntegral_ball_jacquetWindow_sub_jacquetValue.LanglandsTunnell P2MW.S_LanglandsTunnell_CubicInduction_tendsto_setIntegral_annulus_setIntegral_ball_jacquetWindow_sub_jacquetValue.LanglandsTunnell.CubicInduction"

set_option autoImplicit false

p2m_open "MeasureTheory IsDedekindDomain NumberField LanglandsTunnell.TateLocal P2MW.S_LanglandsTunnell_CubicInduction_tendsto_setIntegral_annulus_setIntegral_ball_jacquetWindow_sub_jacquetValue.LanglandsTunnell.TateLocal NumberField.StandardAddChar"
open scoped ENNReal NNReal

attribute [local instance] LanglandsTunnell.TateLocal.localBorel

namespace LanglandsTunnell
p2m_export "LanglandsTunnell" "TateLocal.localBorel TateLocal.borelSpace_localBorel TateLocal.integersPositiveCompacts TateLocal.coe_integersPositiveCompacts"
namespace CubicInduction
p2m_export "LanglandsTunnell.CubicInduction" "unipotentBall3 mem_unipotentBall3_iff jacquetHaar3 jacquetTruncated3 jacquetLevel jacquetValue jacquetTruncated3_eq_jacquetValue bigCell3 mem_bigCell3_iff cellSectionOf cellSectionOf_apply_of_mem cellSectionOf_apply_of_notMem cellSectionOf_upperUnipotent3_mul cellSectionOf_diagonal3_mul principalSeries3 gl3Entry cornerEntry lowerMinor outerMinor gl3Det gl3Det_ne_zero cellRatio cellValue antidiagonal3 antidiagonal3_coe eventually_valued_eq eventually_valued_lt eventually_norm_eq eventually_charExt_eq continuous_gl3Entry continuous_cornerEntry continuous_lowerMinor continuous_outerMinor continuous_gl3Det exists_bottom_entry_ne_zero_of_cornerEntry_eq_zero outerMinor_ne_zero_of_lowerMinor_eq_zero gl3AmbientRightTranslate gl3AmbientRightTranslate_apply transposeInv3 upperUnipotent3 upperUnipotent3_coe embedMat2 iotaGL coe_iotaGL LocalGL3 diagUnitGL2 coe_diagUnitGL2 lowerUnipotent21 longWeyl3 longWeyl3_coe weylPrime3 weylPrime3_coe transposeInv3_weylPrime3 transposeInv3_lowerUnipotent21 exists_forall_le_integrableOn_and_jacquetTruncated3_eq_of_cellSectionOf exists_forall_gl3AmbientRightTranslate_eq_of_mem_principalSeries3"
p2m_open "LanglandsTunnell.CubicInduction LanglandsTunnell"

section WedgeLimit

private theorem tendsto_setIntegral_annulus_setIntegral_ball_sub_of_forall_eq
    (v : HeightOneSpectrum (𝓞 ℚ))
    (ν : Fin 3 → ((v.adicCompletion ℚ)ˣ →* ℂˣ)) (hν : ∀ i, IsLocallyConstant (ν i))
    (Φ : (Fin 3 → v.adicCompletion ℚ) → ℂ) (hΦl : IsLocallyConstant Φ) (hΦc : HasCompactSupport Φ)
    (χ : (v.adicCompletion ℚ)ˣ →* ℂˣ) (hχ : IsLocallyConstant χ)
    (hu : ∀ i, ‖(((ν i * χ) (NumberField.AdelicLevel.uniformizerUnit ℚ v) : ℂˣ) : ℂ)‖ = 1)
    (s : ℂ)
    (K : ℤ → v.adicCompletion ℚ → v.adicCompletion ℚ → ℂ)
    (hK : ∀ (c : ℤ) (a : (v.adicCompletion ℚ)ˣ) (x : v.adicCompletion ℚ),
      letI := localBorel ℚ v
      K c a x =
        ∫ p in {p : v.adicCompletion ℚ × v.adicCompletion ℚ × v.adicCompletion ℚ |
            Valued.v p.2.1 ≤ WithZero.exp c ∧ Valued.v p.2.2 ≤ WithZero.exp c * Valued.v p.2.1 ∧
              Valued.v (p.1 - p.2.2 / p.2.1) ≤ WithZero.exp c},
          (psiLocal ℚ v (-(p.1 + p.2.1)) : ℂ) *
            cellSectionOf v ν Φ
              (antidiagonal3 v * upperUnipotent3 p.1 p.2.1 p.2.2 *
                (longWeyl3 * transposeInv3 (iotaGL (diagUnitGL2 a) * lowerUnipotent21 x *
                  (weylPrime3 * transposeInv3 1)) * antidiagonal3 v))
          ∂(jacquetHaar3 v))
    (J : v.adicCompletion ℚ → v.adicCompletion ℚ → ℂ)
    (hJ : ∀ (a : (v.adicCompletion ℚ)ˣ) (x : v.adicCompletion ℚ),
      J a x =
        jacquetValue v (gl3AmbientRightTranslate (R := ℂ)
          (longWeyl3 * transposeInv3 (iotaGL (diagUnitGL2 a) * lowerUnipotent21 x *
            (weylPrime3 * transposeInv3 1)) * antidiagonal3 v) (cellSectionOf v ν Φ)))
    (N R : ℕ) :
    letI := localBorel ℚ v
    Filter.Tendsto
      (fun c : ℤ =>
        ∫ a in {t : v.adicCompletion ℚ | WithZero.exp (-(N : ℤ)) ≤ Valued.v t ∧ Valued.v t ≤ WithZero.exp (N : ℤ)},
          ((modulus a : ℝ) : ℂ)⁻¹ * charExt χ⁻¹ a * ((modulus a : ℝ) : ℂ) ^ (1 - s) *
            ∫ x in {x : v.adicCompletion ℚ | Valued.v x ≤ WithZero.exp (R : ℤ)}, (K c a x - J a x)
              ∂(selfDualHaarAt ℚ v)
          ∂(mulMeasure (selfDualHaarAt ℚ v)))
      Filter.atTop (nhds 0) := by

  have hKp : ∀ (c : ℤ) (a x : v.adicCompletion ℚ), ∀ ha : a ≠ 0, K c a x = primedKernel v ν Φ c a x :=
      fun c a x ha => by
    have h := hK c (Units.mk0 a ha) x
    simp only [Units.val_mk0] at h
    rw [primedKernel, dif_neg ha, h]
    rfl
  have hJp : ∀ a x : v.adicCompletion ℚ, ∀ ha : a ≠ 0, J a x = valueKernel v ν Φ a x := fun a x ha => by
    have h := hJ (Units.mk0 a ha) x
    simp only [Units.val_mk0] at h
    rw [valueKernel, dif_neg ha, h]
    rfl
  refine Filter.Tendsto.congr (fun c => ?_) (tendsto_pieceW₀ v ν hν Φ hΦl hΦc χ hχ hu s N R)
  dsimp only [pieceW, annulus, xBall, dualWeight]
  refine setIntegral_congr_fun (isClosed_annulus v N).measurableSet fun a ha => ?_
  have ha₀ : a ≠ 0 := ne_zero_of_mem_annulus v ha
  congr 1
  refine setIntegral_congr_fun (isCompact_valued_le v (R : ℤ)).measurableSet fun x _ => ?_
  rw [hKp c a x ha₀, hJp a x ha₀]

end WedgeLimit
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_tendsto_setIntegral_annulus_setIntegral_ball_jacquetWindow_sub_jacquetValue.LaurentZetaSlot P2MW.S_LanglandsTunnell_CubicInduction_tendsto_setIntegral_annulus_setIntegral_ball_jacquetWindow_sub_jacquetValue.LanglandsTunnell P2MW.S_LanglandsTunnell_CubicInduction_tendsto_setIntegral_annulus_setIntegral_ball_jacquetWindow_sub_jacquetValue.LanglandsTunnell.CubicInduction"

end LanglandsTunnell.CubicInduction
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_tendsto_setIntegral_annulus_setIntegral_ball_jacquetWindow_sub_jacquetValue.LaurentZetaSlot P2MW.S_LanglandsTunnell_CubicInduction_tendsto_setIntegral_annulus_setIntegral_ball_jacquetWindow_sub_jacquetValue.LanglandsTunnell P2MW.S_LanglandsTunnell_CubicInduction_tendsto_setIntegral_annulus_setIntegral_ball_jacquetWindow_sub_jacquetValue.LanglandsTunnell.CubicInduction"
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_tendsto_setIntegral_annulus_setIntegral_ball_jacquetWindow_sub_jacquetValue.LaurentZetaSlot P2MW.S_LanglandsTunnell_CubicInduction_tendsto_setIntegral_annulus_setIntegral_ball_jacquetWindow_sub_jacquetValue.LanglandsTunnell P2MW.S_LanglandsTunnell_CubicInduction_tendsto_setIntegral_annulus_setIntegral_ball_jacquetWindow_sub_jacquetValue.LanglandsTunnell.CubicInduction"

open MeasureTheory IsDedekindDomain NumberField NumberField.StandardAddChar _root_.LanglandsTunnell.TateLocal _root_.P2MW.S_LanglandsTunnell_CubicInduction_tendsto_setIntegral_annulus_setIntegral_ball_jacquetWindow_sub_jacquetValue.LanglandsTunnell.TateLocal in
open _root_.LanglandsTunnell.CubicInduction _root_.P2MW.S_LanglandsTunnell_CubicInduction_tendsto_setIntegral_annulus_setIntegral_ball_jacquetWindow_sub_jacquetValue.LanglandsTunnell.CubicInduction in

theorem solution
    (v : HeightOneSpectrum (𝓞 ℚ))
    (ν : Fin 3 → ((v.adicCompletion ℚ)ˣ →* ℂˣ)) (hν : ∀ i, IsLocallyConstant (ν i))
    (Φ : (Fin 3 → v.adicCompletion ℚ) → ℂ) (hΦl : IsLocallyConstant Φ) (hΦc : HasCompactSupport Φ)
    (χ : (v.adicCompletion ℚ)ˣ →* ℂˣ) (hχ : IsLocallyConstant χ)
    (hu : ∀ i, ‖(((ν i * χ) (NumberField.AdelicLevel.uniformizerUnit ℚ v) : ℂˣ) : ℂ)‖ = 1)
    (s : ℂ)
    (K : ℤ → v.adicCompletion ℚ → v.adicCompletion ℚ → ℂ)
    (hK : ∀ (c : ℤ) (a : (v.adicCompletion ℚ)ˣ) (x : v.adicCompletion ℚ),
      letI := localBorel ℚ v
      K c a x =
        ∫ p in {p : v.adicCompletion ℚ × v.adicCompletion ℚ × v.adicCompletion ℚ |
            Valued.v p.2.1 ≤ WithZero.exp c ∧ Valued.v p.2.2 ≤ WithZero.exp c * Valued.v p.2.1 ∧
              Valued.v (p.1 - p.2.2 / p.2.1) ≤ WithZero.exp c},
          (psiLocal ℚ v (-(p.1 + p.2.1)) : ℂ) *
            cellSectionOf v ν Φ
              (antidiagonal3 v * upperUnipotent3 p.1 p.2.1 p.2.2 *
                (longWeyl3 * transposeInv3 (iotaGL (diagUnitGL2 a) * lowerUnipotent21 x *
                  (weylPrime3 * transposeInv3 1)) * antidiagonal3 v))
          ∂(jacquetHaar3 v))
    (J : v.adicCompletion ℚ → v.adicCompletion ℚ → ℂ)
    (hJ : ∀ (a : (v.adicCompletion ℚ)ˣ) (x : v.adicCompletion ℚ),
      J a x =
        jacquetValue v (gl3AmbientRightTranslate (R := ℂ)
          (longWeyl3 * transposeInv3 (iotaGL (diagUnitGL2 a) * lowerUnipotent21 x *
            (weylPrime3 * transposeInv3 1)) * antidiagonal3 v) (cellSectionOf v ν Φ)))
    (N R : ℕ) :
    letI := localBorel ℚ v
    Filter.Tendsto
      (fun c : ℤ =>
        ∫ a in {t : v.adicCompletion ℚ | WithZero.exp (-(N : ℤ)) ≤ Valued.v t ∧ Valued.v t ≤ WithZero.exp (N : ℤ)},
          ((modulus a : ℝ) : ℂ)⁻¹ * charExt χ⁻¹ a * ((modulus a : ℝ) : ℂ) ^ (1 - s) *
            ∫ x in {x : v.adicCompletion ℚ | Valued.v x ≤ WithZero.exp (R : ℤ)}, (K c a x - J a x)
              ∂(selfDualHaarAt ℚ v)
          ∂(mulMeasure (selfDualHaarAt ℚ v)))
      Filter.atTop (nhds 0) := by
  exact tendsto_setIntegral_annulus_setIntegral_ball_sub_of_forall_eq v ν hν Φ hΦl hΦc χ hχ hu s K hK J hJ N R

end S_LanglandsTunnell_CubicInduction_tendsto_setIntegral_annulus_setIntegral_ball_jacquetWindow_sub_jacquetValue
end P2MW
export P2MW.S_LanglandsTunnell_CubicInduction_tendsto_setIntegral_annulus_setIntegral_ball_jacquetWindow_sub_jacquetValue (solution)
