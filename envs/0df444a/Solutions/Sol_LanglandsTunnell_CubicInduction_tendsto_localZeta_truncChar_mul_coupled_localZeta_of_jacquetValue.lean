-- Prove2me | solution 1 for LanglandsTunnell.CubicInduction.tendsto_localZeta_truncChar_mul_coupled_localZeta_of_jacquetValue
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:08.670037+00:00
-- url     : https://prove2.me/submissions/e9ca7e21-ed99-508b-aa20-c39e2ecfd852

import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Analysis.SpecialFunctions.Pow.Complex
import Mathlib.MeasureTheory.Integral.Prod
import Definitions.Def_LanglandsTunnell_CubicInduction_GlobalZeta31
import Definitions.Def_LanglandsTunnell_CubicInduction_IotaTorus
import Definitions.Def_LanglandsTunnell_CubicInduction_JacquetWhittaker
import Definitions.Def_LanglandsTunnell_CubicInduction_LocalZeta31
import Definitions.Def_LanglandsTunnell_CubicInduction_PrincipalSeries3
import Definitions.Def_LanglandsTunnell_StandardLocalConstantsAt
import Definitions.Def_LanglandsTunnell_TateLocalZeta
import Theorems.Thm_LanglandsTunnell_CubicInduction_exists_forall_le_integrableOn_and_jacquetTruncated3_eq_of_cellSectionOf
import Theorems.Thm_LanglandsTunnell_CubicInduction_exists_forall_setIntegral_shell_psiLocal_mul_charExt_mul_cpow_eq_zero
import Theorems.Thm_LanglandsTunnell_CubicInduction_exists_integrable_levelUniform_dominant_coupledInner
import Theorems.Thm_LanglandsTunnell_CubicInduction_exists_norm_setIntegral_ball_truncChar_mul_charExt_mul_cpow_le
import Theorems.Thm_LanglandsTunnell_CubicInduction_integrable_coupledIntegrand
import Theorems.Thm_LanglandsTunnell_CubicInduction_setIntegral_tallBoxJacquet_div_norm_mul_charExt_mul_cpow_eq
import Theorems.Thm_LanglandsTunnell_TateLocal_addCharLevel_psiLocal_rat
import Theorems.Thm_LanglandsTunnell_TateLocal_exists_hasConductorExponentAt_of_continuous
import Theorems.Thm_LanglandsTunnell_TateLocal_modulus_adicCompletion_eq_nnnorm
import Theorems.Thm_LanglandsTunnell_TateLocal_psiLocal_ne_one
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_LanglandsTunnell_CubicInduction_tendsto_localZeta_truncChar_mul_coupled_localZeta_of_jacquetValue
p2m_attr_erase "instance" "IsDedekindDomain.HeightOneSpectrum.Extension.instAlgebraSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersValEqUnder IsDedekindDomain.HeightOneSpectrum.Extension.instAlgebraSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersValEqUnder_1 IsDedekindDomain.HeightOneSpectrum.instMulActionHomClassAlgHomTensorProductAdicCompletionForallValEqUnder_definitions IsDedekindDomain.HeightOneSpectrum.Extension.instAlgebraAdicCompletionValEqUnder IsDedekindDomain.HeightOneSpectrum.adicCompletion.instFiniteForallValEqUnderOfFiniteDimensional_definitions IsDedekindDomain.HeightOneSpectrum.instIsBiscalarSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersTensorProductCoeAlgHomTensorAdicCompletionIntegersTo IsDedekindDomain.HeightOneSpectrum.Extension.instContinuousSMulAdicCompletionValEqUnder IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsModuleTopology IsDedekindDomain.HeightOneSpectrum.Extension.instFiniteSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersValEqUnderOfFiniteDimensional IsDedekindDomain.HeightOneSpectrum.adicCompletion.instFiniteValEqUnderOfFiniteDimensional_definitions instIsBiscalarTensorProductCoeAlgHomBaseChange_of_algebraMap IsDedekindDomain.HeightOneSpectrum.instIsScalarTowerSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersValEqUnder_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsModuleTopologyPi IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions Submodule.instIsTopologicalModuleSubtypeMem Pi.instTopologicalModule IsTopologicalModule.toContinuousSMul IsTopologicalModule.toContinuousAdd instFunLike SemialgHomClass.toSemilinearMapClass instCoeTCSemialgHom SemialgHomClass.toRingHomClass SemialgHomClass.instSemialgHom instFiniteResidueFieldAdicCompletionRingOfIntegersWithZeroMultiplicativeInt_definitions NumberField.instCompactSpaceAdicCompletionIntegers Rat.adicCompletion.locallyCompactSpace NumberField.instFiniteResidueFieldAdicCompletionIntegers instWeaklyLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instCountableOfNumberField_definitions"
p2m_attr_erase "simp" "LanglandsTunnell.CubicInduction.translateRepStep_apply_coe LanglandsTunnell.CubicInduction.translateFn_apply SemialgHom.baseChange_of_algebraMap_tmul_left SemialgHom.baseChangeRightOfAlgebraMap_apply Pi.semialgHomPi_apply Pi.semialgHom_apply Module.Basis.rightBaseChange_apply LinearEquiv.coe_mulLeft LinearEquiv.coe_mulRight WithVal.semialgebraMap_toFun_ofVal Module.Basis.rightBaseChange_repr IsDedekindDomain.HeightOneSpectrum.adicCompletionIntegers.tensorCoe_tmul IsDedekindDomain.HeightOneSpectrum.tensorAdicCompletionIntegersTo_tmul SemialgHom.baseChangeRightOfAlgebraMap_coe IsDedekindDomain.HeightOneSpectrum.adicCompletion.integerBaseChangeLinearEquiv_tmul_apply SemialgHom.baseChange_of_algebraMap_tmul_right IsLocalization.map_moduleTensorEquiv_symm_tmul IsLocalization.leftModuleTensorEquiv_apply IsLocalization.moduleLid_symm_apply IsLocalization.leftModuleTensorEquiv_symm_apply IsLocalization.map_moduleTensorEquiv_tmul IsModuleTopology.continuousLinearEquiv_apply AlgEquiv.extendScalars_symm_apply IsModuleTopology.Module.Basis.equivFun_homeo_symm_apply IsModuleTopology.Module.Basis.equivFun_homeo_apply IsModuleTopology.continuousAlgEquivOfIsBiscalar_apply AlgEquiv.extendScalars_apply IsModuleTopology.continuousLinearEquiv_symm_apply SemialgHom.restrictScalars_toFun SemialgHom.mk.sizeOf_spec SemialgHom.mk.injEq SemialgHom.coe_coe coe_mk TensorProduct.RightActions.smul_def TensorProduct.RightActions.Module.TensorProduct.comm_symm_apply_tmul TensorProduct.RightActions.LinearMap.baseChange_id TensorProduct.RightActions.algebraMap_eval TensorProduct.RightActions.Module.TensorProduct.comm_apply_tmul TensorProduct.RightActions.Algebra.TensorProduct.comm_symm_apply_tmul TensorProduct.RightActions.Algebra.TensorProduct.comm_apply_tmul"

set_option autoImplicit false

section
set_option autoImplicit false

open NumberField NumberField.AdelicLevel IsDedekindDomain MeasureTheory
p2m_open "LanglandsTunnell.TateLocal P2MW.S_LanglandsTunnell_CubicInduction_tendsto_localZeta_truncChar_mul_coupled_localZeta_of_jacquetValue.LanglandsTunnell.TateLocal"
open scoped NNReal ENNReal

namespace LaurentLocalZeta

variable (v : HeightOneSpectrum (𝓞 ℚ))

attribute [local instance] LanglandsTunnell.TateLocal.localBorel
attribute [local instance] LanglandsTunnell.TateLocal.borelSpace_localBorel

private theorem one_lt_absNorm_real : (1 : ℝ) < (Ideal.absNorm v.asIdeal : ℝ) := by
  exact_mod_cast NumberField.HeightOneSpectrum.one_lt_absNorm (v := v)

private theorem _root_.LaurentLocalZeta.absNorm_ne_zero : (Ideal.absNorm v.asIdeal : ℕ) ≠ 0 := by
  intro h0
  have h := one_lt_absNorm_real v
  rw [h0] at h
  norm_num at h

p2m_export "LaurentLocalZeta" "absNorm_ne_zero"
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

private theorem exists_mem_shell {x : v.adicCompletion ℚ} (hx : x ≠ 0) : ∃ j : ℤ, x ∈ shell v j := by
  have hv : Valued.v x ≠ 0 := (Valuation.ne_zero_iff _).mpr hx
  refine ⟨-WithZero.log (Valued.v x), ?_⟩
  show Valued.v x = WithZero.exp (- -WithZero.log (Valued.v x))
  rw [neg_neg, WithZero.exp_log hv]

private theorem coe_modulus_eq_of_mem_shell {j : ℤ} {x : v.adicCompletion ℚ} (hx : x ∈ shell v j) :
    (modulus x : ℝ) = (Ideal.absNorm v.asIdeal : ℝ) ^ (-j) := by
  rw [modulus_eq_of_mem_shell v hx, NNReal.coe_zpow, NNReal.coe_natCast]

private theorem exists_bound_charExt_unitShell (χ : (v.adicCompletion ℚ)ˣ →* ℂˣ) (hχ : IsLocallyConstant χ) :
    ∃ Mχ : ℝ, ∀ u ∈ unitShell v, ‖charExt χ u‖ ≤ Mχ :=
  (isCompact_unitShell v).exists_bound_of_continuousOn ((continuousOn_charExt_compl v χ hχ).mono
    (by rw [unitShell_eq_shell_zero]; exact shell_subset_compl_zero v 0))

end LaurentLocalZeta
end

section
set_option autoImplicit false

open IsDedekindDomain NumberField MeasureTheory
open scoped NNReal ENNReal Pointwise

namespace LanglandsTunnell
p2m_export "LanglandsTunnell" "TateLocal.localBorel TateLocal.borelSpace_localBorel"
namespace TateLocal
p2m_export "LanglandsTunnell.TateLocal" "addCharLevel addCharLevel_def localBorel borelSpace_localBorel integersPositiveCompacts coe_integersPositiveCompacts selfDualHaarAt higherUnitsAt mem_higherUnitsAt_iff modulus modulus_of_ne_zero modulus_ne_zero modulus_mul charExt charExt_zero charExt_of_ne_zero charExt_coe_units mulMeasure localZeta addCharLevel_psiLocal_rat exists_hasConductorExponentAt_of_continuous modulus_adicCompletion_eq_nnnorm psiLocal_ne_one"
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

private theorem integral_mul_left_selfDualHaarAt (u : (v.adicCompletion K)ˣ) (F : v.adicCompletion K → ℂ) :
    letI := localBorel K v
    ∫ x, F ((u : v.adicCompletion K) * x) ∂(selfDualHaarAt K v) =
      ((modulus (u : v.adicCompletion K) : ℝ≥0∞)⁻¹).toReal • ∫ x, F x ∂(selfDualHaarAt K v) := by
  letI := localBorel K v
  haveI : BorelSpace (v.adicCompletion K) := borelSpace_localBorel K v
  rw [← (measurableEmbedding_mulLeft₀ u.ne_zero).integral_map F, map_mul_left_selfDualHaarAt,
    integral_smul_measure]

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

private theorem integral_mul_left_mulMeasure (c : v.adicCompletion K) (hc : c ≠ 0) (F : v.adicCompletion K → ℂ) :
    letI := localBorel K v
    ∫ x, F (c * x) ∂(mulMeasure (selfDualHaarAt K v)) = ∫ x, F x ∂(mulMeasure (selfDualHaarAt K v)) := by
  letI := localBorel K v
  haveI : BorelSpace (v.adicCompletion K) := borelSpace_localBorel K v
  have h := map_mul_left_mulMeasure K v (Units.mk0 c hc)
  simp only [Units.val_mk0] at h
  rw [← (measurableEmbedding_mulLeft₀ hc).integral_map F, h]

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

private theorem measurableSingletonClass_adicCompletion :
    letI := localBorel K v
    MeasurableSingletonClass (v.adicCompletion K) := by
  letI := localBorel K v
  haveI : BorelSpace (v.adicCompletion K) := borelSpace_localBorel K v
  infer_instance

end MeasureClasses

end LanglandsTunnell.TateLocal
end

section
set_option autoImplicit false

p2m_open "Matrix IsDedekindDomain NumberField LanglandsTunnell.TateLocal P2MW.S_LanglandsTunnell_CubicInduction_tendsto_localZeta_truncChar_mul_coupled_localZeta_of_jacquetValue.LanglandsTunnell.TateLocal"

namespace LanglandsTunnell
p2m_export "LanglandsTunnell" "TateLocal.localBorel TateLocal.borelSpace_localBorel"
namespace CubicInduction
p2m_export "LanglandsTunnell.CubicInduction" "gl3AmbientRightTranslate gl3AmbientRightTranslate_apply upperUnipotent3 embedMat2 iotaGL LocalGL3 diagUnitGL2 unipotentBall3 mem_unipotentBall3_iff jacquetHaar3 jacquetTruncated3 jacquetLevel jacquetValue jacquetTruncated3_eq_jacquetValue bigCell3 mem_bigCell3_iff cellSectionOf cellSectionOf_apply_of_mem cellSectionOf_apply_of_notMem gl3Entry cornerEntry lowerMinor outerMinor gl3Det cellRatio cellValue antidiagonal3 antidiagonal3_coe eventually_valued_lt continuous_gl3Entry exists_forall_le_integrableOn_and_jacquetTruncated3_eq_of_cellSectionOf exists_forall_setIntegral_shell_psiLocal_mul_charExt_mul_cpow_eq_zero exists_integrable_levelUniform_dominant_coupledInner exists_norm_setIntegral_ball_truncChar_mul_charExt_mul_cpow_le integrable_coupledIntegrand setIntegral_tallBoxJacquet_div_norm_mul_charExt_mul_cpow_eq"
p2m_open "LanglandsTunnell.CubicInduction LanglandsTunnell"

variable (v : HeightOneSpectrum (𝓞 ℚ))

private noncomputable def torusCellPoint (x y z : v.adicCompletion ℚ) (a : (v.adicCompletion ℚ)ˣ) : LocalGL3 v :=
  antidiagonal3 v * upperUnipotent3 x y z * (iotaGL (diagUnitGL2 a) * antidiagonal3 v)

private theorem torusCellPoint_coe (x y z : v.adicCompletion ℚ) (a : (v.adicCompletion ℚ)ˣ) :
    (torusCellPoint v x y z a : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)) =
      !![1, 0, 0; y, 1, 0; z, x, (a : v.adicCompletion ℚ)] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [torusCellPoint, antidiagonal3_coe, embedMat2, Matrix.mul_apply, Fin.sum_univ_three]

private theorem gl3Entry_torusCellPoint (x y z : v.adicCompletion ℚ) (a : (v.adicCompletion ℚ)ˣ) (i j : Fin 3) :
    gl3Entry v (torusCellPoint v x y z a) i j = !![1, 0, 0; y, 1, 0; z, x, (a : v.adicCompletion ℚ)] i j := by
  rw [gl3Entry, torusCellPoint_coe]

private theorem cornerEntry_torusCellPoint (x y z : v.adicCompletion ℚ) (a : (v.adicCompletion ℚ)ˣ) :
    cornerEntry v (torusCellPoint v x y z a) = z := by
  simp [cornerEntry, gl3Entry_torusCellPoint]

private theorem lowerMinor_torusCellPoint (x y z : v.adicCompletion ℚ) (a : (v.adicCompletion ℚ)ˣ) :
    lowerMinor v (torusCellPoint v x y z a) = x * y - z := by
  simp only [lowerMinor, gl3Entry_torusCellPoint]
  simp
  ring

private theorem outerMinor_torusCellPoint (x y z : v.adicCompletion ℚ) (a : (v.adicCompletion ℚ)ˣ) :
    outerMinor v (torusCellPoint v x y z a) = (a : v.adicCompletion ℚ) * y := by
  simp only [outerMinor, gl3Entry_torusCellPoint]
  simp
  ring

private theorem gl3Det_torusCellPoint (x y z : v.adicCompletion ℚ) (a : (v.adicCompletion ℚ)ˣ) :
    gl3Det v (torusCellPoint v x y z a) = (a : v.adicCompletion ℚ) := by
  rw [gl3Det, torusCellPoint_coe, Matrix.det_fin_three]
  simp

private theorem cellRatio_torusCellPoint (x y z : v.adicCompletion ℚ) (a : (v.adicCompletion ℚ)ˣ) :
    cellRatio v (torusCellPoint v x y z a) =
      ![x / z, (a : v.adicCompletion ℚ) / z, (a : v.adicCompletion ℚ) * y / (x * y - z)] := by
  rw [cellRatio, cornerEntry_torusCellPoint, outerMinor_torusCellPoint, lowerMinor_torusCellPoint]
  simp [gl3Entry_torusCellPoint]

private theorem cellValue_torusCellPoint (χ : Fin 3 → ((v.adicCompletion ℚ)ˣ →* ℂˣ)) (x y z : v.adicCompletion ℚ)
    (a : (v.adicCompletion ℚ)ˣ) :
    cellValue v χ (torusCellPoint v x y z a) =
      charExt (χ 0) ((a : v.adicCompletion ℚ) / (x * y - z)) * charExt (χ 1) ((x * y - z) / z) * charExt (χ 2) z *
        ((‖(a : v.adicCompletion ℚ) / (x * y - z)‖ / ‖z‖ : ℝ) : ℂ) := by
  rw [cellValue, gl3Det_torusCellPoint, lowerMinor_torusCellPoint, cornerEntry_torusCellPoint]

end LanglandsTunnell.CubicInduction
end

section
set_option autoImplicit false

open MeasureTheory
open IsDedekindDomain
open NumberField
p2m_open "LanglandsTunnell.TateLocal P2MW.S_LanglandsTunnell_CubicInduction_tendsto_localZeta_truncChar_mul_coupled_localZeta_of_jacquetValue.LanglandsTunnell.TateLocal"
open NumberField.StandardAddChar
open scoped Topology

namespace LanglandsTunnell
p2m_export "LanglandsTunnell" "TateLocal.localBorel TateLocal.borelSpace_localBorel"
namespace CubicInduction
p2m_export "LanglandsTunnell.CubicInduction" "gl3AmbientRightTranslate gl3AmbientRightTranslate_apply upperUnipotent3 embedMat2 iotaGL LocalGL3 diagUnitGL2 unipotentBall3 mem_unipotentBall3_iff jacquetHaar3 jacquetTruncated3 jacquetLevel jacquetValue jacquetTruncated3_eq_jacquetValue bigCell3 mem_bigCell3_iff cellSectionOf cellSectionOf_apply_of_mem cellSectionOf_apply_of_notMem gl3Entry cornerEntry lowerMinor outerMinor gl3Det cellRatio cellValue antidiagonal3 antidiagonal3_coe eventually_valued_lt continuous_gl3Entry exists_forall_le_integrableOn_and_jacquetTruncated3_eq_of_cellSectionOf exists_forall_setIntegral_shell_psiLocal_mul_charExt_mul_cpow_eq_zero exists_integrable_levelUniform_dominant_coupledInner exists_norm_setIntegral_ball_truncChar_mul_charExt_mul_cpow_le integrable_coupledIntegrand setIntegral_tallBoxJacquet_div_norm_mul_charExt_mul_cpow_eq"
p2m_open "LanglandsTunnell.CubicInduction LanglandsTunnell"

section TorusValues

variable (v : HeightOneSpectrum (𝓞 ℚ))
variable (ν : Fin 3 → ((v.adicCompletion ℚ)ˣ →* ℂˣ)) (Φ : (Fin 3 → v.adicCompletion ℚ) → ℂ)

private noncomputable def torusTranslate (a : (v.adicCompletion ℚ)ˣ) : LocalGL3 v → ℂ :=
  gl3AmbientRightTranslate (R := ℂ) (iotaGL (diagUnitGL2 a) * antidiagonal3 v) (cellSectionOf v ν Φ)

open Classical in
private noncomputable def torusFn : v.adicCompletion ℚ → ℂ := fun t =>
  if h : t = 0 then 0 else
    jacquetValue v (torusTranslate v ν Φ (Units.mk0 t h)) * ((modulus t : ℝ) : ℂ)⁻¹

private theorem torusFn_coe_units (a : (v.adicCompletion ℚ)ˣ) :
    torusFn v ν Φ a = jacquetValue v (torusTranslate v ν Φ a) * ((modulus (a : v.adicCompletion ℚ) : ℝ) : ℂ)⁻¹ := by
  simp [torusFn, a.ne_zero]

private theorem jacquetTruncated3_torusTranslate (c : ℤ) (a : (v.adicCompletion ℚ)ˣ) :
    letI := localBorel ℚ v
    jacquetTruncated3 v c (torusTranslate v ν Φ a) =
      ∫ p in unipotentBall3 v c,
        psiLocal ℚ v (-(p.1 + p.2.1)) * cellSectionOf v ν Φ (torusCellPoint v p.1 p.2.1 p.2.2 a)
          ∂(jacquetHaar3 v) := by
  letI := localBorel ℚ v
  unfold jacquetTruncated3
  congr 1

private theorem exists_level_torusTranslate (hν : ∀ i, IsLocallyConstant (ν i)) (hΦl : IsLocallyConstant Φ)
    (hΦc : HasCompactSupport Φ) (a : (v.adicCompletion ℚ)ˣ) :
    ∃ c₀ : ℕ, ∀ c : ℤ, (c₀ : ℤ) ≤ c →
      jacquetTruncated3 v c (torusTranslate v ν Φ a) = jacquetTruncated3 v c₀ (torusTranslate v ν Φ a) := by
  obtain ⟨c₀, h⟩ := exists_forall_le_integrableOn_and_jacquetTruncated3_eq_of_cellSectionOf v ν hν Φ ⟨hΦl, hΦc⟩
    (iotaGL (diagUnitGL2 a) * antidiagonal3 v)
  exact ⟨c₀, fun c hc => (h c hc).2⟩

private noncomputable def torusIntegrand (a : (v.adicCompletion ℚ)ˣ)
    (p : v.adicCompletion ℚ × v.adicCompletion ℚ × v.adicCompletion ℚ) : ℂ :=
  psiLocal ℚ v (-(p.1 + p.2.1)) * cellSectionOf v ν Φ (torusCellPoint v p.1 p.2.1 p.2.2 a)

private theorem jacquetTruncated3_torusTranslate_eq_integral (c : ℤ) (a : (v.adicCompletion ℚ)ˣ) :
    letI := localBorel ℚ v
    jacquetTruncated3 v c (torusTranslate v ν Φ a) =
      ∫ p in unipotentBall3 v c, torusIntegrand v ν Φ a p ∂(jacquetHaar3 v) :=
  jacquetTruncated3_torusTranslate v ν Φ c a

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

  have hmain : ∀ p q : Fin 3 → v.adicCompletion ℚ, (∀ i, ‖q i - p i‖ ≤ r) → p ∈ tsupport Φ → Φ q = Φ p := by
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
  · exact hmain p q hpq hp
  by_cases hq : q ∈ tsupport Φ
  · refine (hmain q p (fun i => ?_) hq).symm
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

private theorem norm_eq_one_of_valued_eq_one {u : v.adicCompletion ℚ} (hu : Valued.v u = 1) : ‖u‖ = 1 := by
  rw [NumberField.FinitePlace.norm_def v u, hu, map_one, NNReal.coe_one]

private theorem modulus_real_eq_norm (x : v.adicCompletion ℚ) : (modulus x : ℝ) = ‖x‖ := by
  rw [modulus_adicCompletion_eq_nnnorm ℚ v x, coe_nnnorm]

private theorem _root_.LanglandsTunnell.CubicInduction.one_lt_absNorm_real : (1 : ℝ) < (Ideal.absNorm v.asIdeal : ℝ) := by
  exact_mod_cast NumberField.HeightOneSpectrum.one_lt_absNorm (v := v)

p2m_export "LanglandsTunnell.CubicInduction" "one_lt_absNorm_real"
private theorem torusCellPoint_mem_bigCell3_iff (x y z : v.adicCompletion ℚ) (a : (v.adicCompletion ℚ)ˣ) :
    torusCellPoint v x y z a ∈ bigCell3 v ↔ z ≠ 0 ∧ x * y - z ≠ 0 := by
  rw [mem_bigCell3_iff, cornerEntry_torusCellPoint, lowerMinor_torusCellPoint]

private theorem valued_eq_one_of_valued_sub_one_le {u : v.adicCompletion ℚ} {k : ℕ} (hk : 1 ≤ k)
    (hu : Valued.v (u - 1) ≤ WithZero.exp (-(k : ℤ))) : Valued.v u = 1 := by
  have hlt : Valued.v (u - 1) < Valued.v (1 : v.adicCompletion ℚ) := by
    rw [Valuation.map_one]
    refine lt_of_le_of_lt hu ?_
    rw [← WithZero.exp_zero]
    exact WithZero.exp_lt_exp.mpr (by omega)
  have h := Valued.v.map_add_eq_of_lt_right hlt
  rwa [sub_add_cancel, Valuation.map_one] at h

private theorem exists_forall_charExt_mul_eq (η : (v.adicCompletion ℚ)ˣ →* ℂˣ) (hη : IsLocallyConstant η) :
    ∃ k : ℕ, ∀ u w : v.adicCompletion ℚ,
      Valued.v (u - 1) ≤ WithZero.exp (-(k : ℤ)) → charExt η (u * w) = charExt η w := by
  obtain ⟨c, hc⟩ := exists_hasConductorExponentAt_of_continuous ℚ v η hη.continuous
  refine ⟨max c 1, fun u w huk => ?_⟩
  have hu1 : Valued.v u = 1 := valued_eq_one_of_valued_sub_one_le v (le_max_right c 1) huk
  have hu0 : u ≠ 0 := by
    rintro rfl
    simp at hu1
  have hmem : Units.mk0 u hu0 ∈ higherUnitsAt ℚ v c := by
    rw [mem_higherUnitsAt_iff, Units.val_mk0]
    refine ⟨hu1, Or.inr (huk.trans ?_)⟩
    exact WithZero.exp_le_exp.mpr (neg_le_neg (by exact_mod_cast le_max_left c 1))
  have hη1 : η (Units.mk0 u hu0) = 1 := hc.1 _ hmem
  by_cases hw : w = 0
  · rw [hw, mul_zero]
  have hcoe : u * w = ((Units.mk0 u hu0 * Units.mk0 w hw : (v.adicCompletion ℚ)ˣ) : v.adicCompletion ℚ) := by
    rw [Units.val_mul, Units.val_mk0, Units.val_mk0]
  rw [hcoe, charExt_coe_units, map_mul, hη1, one_mul, ← charExt_coe_units, Units.val_mk0]

private theorem
    exists_forall_cellSectionOf_torusCellPoint_mul (hν : ∀ i, IsLocallyConstant (ν i)) (hΦl : IsLocallyConstant Φ)
    (hΦc : HasCompactSupport Φ) :
    ∃ k : ℕ, 1 ≤ k ∧ ∀ u : (v.adicCompletion ℚ)ˣ, Valued.v ((u : v.adicCompletion ℚ) - 1) ≤ WithZero.exp (-(k : ℤ)) →
      ∀ (x y z : v.adicCompletion ℚ) (a : (v.adicCompletion ℚ)ˣ),
        cellSectionOf v ν Φ (torusCellPoint v x y z (a * u)) = cellSectionOf v ν Φ (torusCellPoint v x y z a) := by
  obtain ⟨δ, hδpos, hδ⟩ := exists_invariance_radius v Φ hΦl hΦc
  obtain ⟨R, hR⟩ := exists_support_radius v Φ hΦc
  obtain ⟨k₀, hk₀⟩ := exists_forall_charExt_mul_eq v (ν 0) (hν 0)
  set q : ℝ := (Ideal.absNorm v.asIdeal : ℝ) with hq_def
  have hq1 : (1 : ℝ) < q := one_lt_absNorm_real v
  have hq0 : (0 : ℝ) < q := zero_lt_one.trans hq1
  set R' : ℝ := max R 1 with hR'_def
  have hR'0 : (0 : ℝ) < R' := zero_lt_one.trans_le (le_max_right _ _)
  have hRR' : R ≤ R' := le_max_left _ _

  obtain ⟨k₁, hk₁⟩ : ∃ k₁ : ℕ, q⁻¹ ^ k₁ * R' ≤ δ := by
    obtain ⟨n, hn⟩ := exists_pow_lt_of_lt_one (div_pos hδpos hR'0) (inv_lt_one_of_one_lt₀ hq1)
    exact ⟨n, (le_div_iff₀ hR'0).mp hn.le⟩
  set k : ℕ := max (max k₀ k₁) 1 with hk_def
  have hk1 : 1 ≤ k := le_max_right _ _
  have hk₀k : k₀ ≤ k := (le_max_left _ _).trans (le_max_left _ _)
  have hk₁k : k₁ ≤ k := (le_max_right _ _).trans (le_max_left _ _)
  refine ⟨k, hk1, fun u hu => ?_⟩
  have hu1 : Valued.v (u : v.adicCompletion ℚ) = 1 := valued_eq_one_of_valued_sub_one_le v hk1 hu
  have hun : ‖(u : v.adicCompletion ℚ)‖ = 1 := norm_eq_one_of_valued_eq_one v hu1
  have hu_small : ‖(u : v.adicCompletion ℚ) - 1‖ * R' ≤ δ := by
    refine le_trans ?_ hk₁
    gcongr
    calc ‖(u : v.adicCompletion ℚ) - 1‖ ≤ q ^ (-(k : ℤ)) := by simpa using norm_le_zpow_of_valued_le v hu
      _ = q⁻¹ ^ k := by rw [zpow_neg, zpow_natCast, inv_pow]
      _ ≤ q⁻¹ ^ k₁ := pow_le_pow_of_le_one (inv_nonneg.mpr hq0.le) (inv_le_one_of_one_le₀ hq1.le) hk₁k
  have hexp₀ : WithZero.exp (-(k : ℤ)) ≤ WithZero.exp (-(k₀ : ℤ)) := WithZero.exp_le_exp.mpr (by omega)

  have hmain : ∀ (u : (v.adicCompletion ℚ)ˣ), Valued.v ((u : v.adicCompletion ℚ) - 1) ≤ WithZero.exp (-(k : ℤ)) →
      ‖(u : v.adicCompletion ℚ)‖ = 1 → ‖(u : v.adicCompletion ℚ) - 1‖ * R' ≤ δ →
      ∀ (x y z : v.adicCompletion ℚ) (a : (v.adicCompletion ℚ)ˣ),
        cellSectionOf v ν Φ (torusCellPoint v x y z a) ≠ 0 →
        cellSectionOf v ν Φ (torusCellPoint v x y z (a * u)) = cellSectionOf v ν Φ (torusCellPoint v x y z a) := by
    intro u hu hun hsmall x y z a hne
    have hmem : torusCellPoint v x y z a ∈ bigCell3 v := by
      by_contra h
      exact hne (cellSectionOf_apply_of_notMem v ν Φ h)
    obtain ⟨hz, hm⟩ := (torusCellPoint_mem_bigCell3_iff v x y z a).mp hmem
    have hmem' : torusCellPoint v x y z (a * u) ∈ bigCell3 v :=
      (torusCellPoint_mem_bigCell3_iff v x y z (a * u)).mpr ⟨hz, hm⟩
    rw [cellSectionOf_apply_of_mem v ν Φ hmem] at hne
    have hΦne : Φ (cellRatio v (torusCellPoint v x y z a)) ≠ 0 := right_ne_zero_of_mul hne
    have hb := hR _ hΦne
    rw [cellRatio_torusCellPoint] at hb
    have h1 : ‖(a : v.adicCompletion ℚ) / z‖ ≤ R := by simpa using hb 1
    have h2 : ‖(a : v.adicCompletion ℚ) * y / (x * y - z)‖ ≤ R := by simpa using hb 2
    have hbound : ∀ w : v.adicCompletion ℚ, ‖w‖ ≤ R → ‖w * (u : v.adicCompletion ℚ) - w‖ ≤ δ := by
      intro w hw
      calc ‖w * (u : v.adicCompletion ℚ) - w‖ = ‖w‖ * ‖(u : v.adicCompletion ℚ) - 1‖ := by
            rw [← norm_mul]; congr 1; ring
        _ ≤ R' * ‖(u : v.adicCompletion ℚ) - 1‖ := by gcongr; exact hw.trans hRR'
        _ = ‖(u : v.adicCompletion ℚ) - 1‖ * R' := mul_comm _ _
        _ ≤ δ := hsmall
    rw [cellSectionOf_apply_of_mem v ν Φ hmem', cellSectionOf_apply_of_mem v ν Φ hmem,
      cellValue_torusCellPoint, cellValue_torusCellPoint, cellRatio_torusCellPoint, cellRatio_torusCellPoint,
      Units.val_mul]
    have e0 : charExt (ν 0) ((a : v.adicCompletion ℚ) * u / (x * y - z)) =
        charExt (ν 0) ((a : v.adicCompletion ℚ) / (x * y - z)) := by
      rw [show (a : v.adicCompletion ℚ) * u / (x * y - z) = u * ((a : v.adicCompletion ℚ) / (x * y - z)) by ring]
      exact hk₀ u _ (hu.trans hexp₀)
    have e3 : ‖(a : v.adicCompletion ℚ) * u / (x * y - z)‖ = ‖(a : v.adicCompletion ℚ) / (x * y - z)‖ := by
      rw [norm_div, norm_div, norm_mul, hun, mul_one]
    have eΦ : Φ ![x / z, (a : v.adicCompletion ℚ) * u / z, (a : v.adicCompletion ℚ) * u * y / (x * y - z)] =
        Φ ![x / z, (a : v.adicCompletion ℚ) / z, (a : v.adicCompletion ℚ) * y / (x * y - z)] := by
      refine hδ _ _ ?_
      intro i
      fin_cases i
      · show ‖x / z - x / z‖ ≤ δ
        rw [sub_self, norm_zero]
        exact hδpos.le
      · show ‖(a : v.adicCompletion ℚ) * u / z - (a : v.adicCompletion ℚ) / z‖ ≤ δ
        have := hbound _ h1
        rwa [show (a : v.adicCompletion ℚ) / z * u = (a : v.adicCompletion ℚ) * u / z by ring] at this
      · show ‖(a : v.adicCompletion ℚ) * u * y / (x * y - z) - (a : v.adicCompletion ℚ) * y / (x * y - z)‖ ≤ δ
        have := hbound _ h2
        rwa [show (a : v.adicCompletion ℚ) * y / (x * y - z) * u = (a : v.adicCompletion ℚ) * u * y / (x * y - z) by
          ring] at this
    rw [e0, e3, eΦ]
  intro x y z a
  by_cases ha : cellSectionOf v ν Φ (torusCellPoint v x y z a) = 0
  · by_cases hau : cellSectionOf v ν Φ (torusCellPoint v x y z (a * u)) = 0
    · rw [ha, hau]
    ·
      have hinv_val : Valued.v ((u⁻¹ : (v.adicCompletion ℚ)ˣ) - 1 : v.adicCompletion ℚ) ≤ WithZero.exp (-(k : ℤ)) := by
        have : ((u⁻¹ : (v.adicCompletion ℚ)ˣ) : v.adicCompletion ℚ) - 1 =
            -(((u⁻¹ : (v.adicCompletion ℚ)ˣ) : v.adicCompletion ℚ) * ((u : v.adicCompletion ℚ) - 1)) := by
          rw [Units.val_inv_eq_inv_val, mul_sub, inv_mul_cancel₀ u.ne_zero, mul_one, neg_sub]
        rw [this, Valuation.map_neg, Valuation.map_mul, Units.val_inv_eq_inv_val, map_inv₀, hu1, inv_one, one_mul]
        exact hu
      have hinv_n : ‖((u⁻¹ : (v.adicCompletion ℚ)ˣ) : v.adicCompletion ℚ)‖ = 1 := by
        rw [Units.val_inv_eq_inv_val, norm_inv, hun, inv_one]
      have hinv_small : ‖((u⁻¹ : (v.adicCompletion ℚ)ˣ) : v.adicCompletion ℚ) - 1‖ * R' ≤ δ := by
        have : ((u⁻¹ : (v.adicCompletion ℚ)ˣ) : v.adicCompletion ℚ) - 1 =
            -(((u⁻¹ : (v.adicCompletion ℚ)ˣ) : v.adicCompletion ℚ) * ((u : v.adicCompletion ℚ) - 1)) := by
          rw [Units.val_inv_eq_inv_val, mul_sub, inv_mul_cancel₀ u.ne_zero, mul_one, neg_sub]
        rw [this, norm_neg, norm_mul, hinv_n, one_mul]
        exact hu_small
      have h := hmain u⁻¹ hinv_val hinv_n hinv_small x y z (a * u) hau
      rw [mul_inv_cancel_right] at h
      exact absurd (h.symm.trans ha) hau
  · exact hmain u hu hun hu_small x y z a ha

private theorem isClosed_valued_le (n : ℤ) : IsClosed {x : v.adicCompletion ℚ | Valued.v x ≤ WithZero.exp n} := by
  obtain ⟨y₀, hy₀⟩ := HeightOneSpectrum.valuedAdicCompletion_surjective ℚ v (WithZero.exp n)
  have hset : {x : v.adicCompletion ℚ | Valued.v x ≤ WithZero.exp n}
      = {x | Valued.v.restrict x ≤ Valued.v.restrict y₀} := by
    ext x
    simp only [Set.mem_setOf_eq]
    rw [Valuation.restrict_le_iff, hy₀]
  rw [hset]
  exact Valued.isClosed_closedBall _ _

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

end LanglandsTunnell.CubicInduction
end

section
open MeasureTheory
open IsDedekindDomain
open NumberField
p2m_open "LanglandsTunnell.TateLocal P2MW.S_LanglandsTunnell_CubicInduction_tendsto_localZeta_truncChar_mul_coupled_localZeta_of_jacquetValue.LanglandsTunnell.TateLocal"

attribute [local instance] LanglandsTunnell.TateLocal.localBorel

namespace LanglandsTunnell
p2m_export "LanglandsTunnell" "TateLocal.localBorel TateLocal.borelSpace_localBorel"
namespace CubicInduction
p2m_export "LanglandsTunnell.CubicInduction" "gl3AmbientRightTranslate gl3AmbientRightTranslate_apply upperUnipotent3 embedMat2 iotaGL LocalGL3 diagUnitGL2 unipotentBall3 mem_unipotentBall3_iff jacquetHaar3 jacquetTruncated3 jacquetLevel jacquetValue jacquetTruncated3_eq_jacquetValue bigCell3 mem_bigCell3_iff cellSectionOf cellSectionOf_apply_of_mem cellSectionOf_apply_of_notMem gl3Entry cornerEntry lowerMinor outerMinor gl3Det cellRatio cellValue antidiagonal3 antidiagonal3_coe eventually_valued_lt continuous_gl3Entry exists_forall_le_integrableOn_and_jacquetTruncated3_eq_of_cellSectionOf exists_forall_setIntegral_shell_psiLocal_mul_charExt_mul_cpow_eq_zero exists_integrable_levelUniform_dominant_coupledInner exists_norm_setIntegral_ball_truncChar_mul_charExt_mul_cpow_le integrable_coupledIntegrand setIntegral_tallBoxJacquet_div_norm_mul_charExt_mul_cpow_eq"
p2m_open "LanglandsTunnell.CubicInduction LanglandsTunnell"

variable (v : HeightOneSpectrum (𝓞 ℚ))

private noncomputable def truncChar (c : ℤ) (t : v.adicCompletion ℚ) : ℂ :=
  if Valued.v t ≤ WithZero.exp c then (NumberField.StandardAddChar.psiLocal ℚ v t : ℂ) else 0

private noncomputable def gaussIntegral (η : (v.adicCompletion ℚ)ˣ →* ℂˣ) (z : ℂ) (c : ℤ) : ℂ :=
  localZeta (selfDualHaarAt ℚ v) (fun t => truncChar v c (-t)) η z

private noncomputable def coupledIntegral (ν : Fin 3 → ((v.adicCompletion ℚ)ˣ →* ℂˣ))
    (Φ : (Fin 3 → v.adicCompletion ℚ) → ℂ) (χ : (v.adicCompletion ℚ)ˣ →* ℂˣ) (s : ℂ) (c : ℤ) : ℂ :=
  ∫ p : v.adicCompletion ℚ × v.adicCompletion ℚ × v.adicCompletion ℚ,
      Φ ![p.1, p.2.1, p.2.2] *
        (charExt (ν 2 * χ)⁻¹ p.1 * ((modulus p.1 : ℝ) : ℂ) ^ (1 - s)) *
        (charExt (ν 1 * χ) p.2.1 * ((modulus p.2.1 : ℝ) : ℂ) ^ s) *
        (charExt (ν 0 * (ν 1)⁻¹) (p.2.1 - p.1 * p.2.2) * ((modulus (p.2.1 - p.1 * p.2.2) : ℝ) : ℂ)⁻¹) *
        truncChar v c (p.2.2 / (p.2.1 - p.1 * p.2.2))
    ∂((mulMeasure (selfDualHaarAt ℚ v)).prod ((mulMeasure (selfDualHaarAt ℚ v)).prod (selfDualHaarAt ℚ v)))

end LanglandsTunnell.CubicInduction
end

section
section
set_option autoImplicit false

open MeasureTheory
open IsDedekindDomain
open NumberField
p2m_open "LanglandsTunnell.TateLocal P2MW.S_LanglandsTunnell_CubicInduction_tendsto_localZeta_truncChar_mul_coupled_localZeta_of_jacquetValue.LanglandsTunnell.TateLocal"

attribute [local instance] LanglandsTunnell.TateLocal.localBorel

namespace LanglandsTunnell
p2m_export "LanglandsTunnell" "TateLocal.localBorel TateLocal.borelSpace_localBorel"
namespace CubicInduction
p2m_export "LanglandsTunnell.CubicInduction" "gl3AmbientRightTranslate gl3AmbientRightTranslate_apply upperUnipotent3 embedMat2 iotaGL LocalGL3 diagUnitGL2 unipotentBall3 mem_unipotentBall3_iff jacquetHaar3 jacquetTruncated3 jacquetLevel jacquetValue jacquetTruncated3_eq_jacquetValue bigCell3 mem_bigCell3_iff cellSectionOf cellSectionOf_apply_of_mem cellSectionOf_apply_of_notMem gl3Entry cornerEntry lowerMinor outerMinor gl3Det cellRatio cellValue antidiagonal3 antidiagonal3_coe eventually_valued_lt continuous_gl3Entry exists_forall_le_integrableOn_and_jacquetTruncated3_eq_of_cellSectionOf exists_forall_setIntegral_shell_psiLocal_mul_charExt_mul_cpow_eq_zero exists_integrable_levelUniform_dominant_coupledInner exists_norm_setIntegral_ball_truncChar_mul_charExt_mul_cpow_le integrable_coupledIntegrand setIntegral_tallBoxJacquet_div_norm_mul_charExt_mul_cpow_eq"
p2m_open "LanglandsTunnell.CubicInduction LanglandsTunnell"

variable (v : HeightOneSpectrum (𝓞 ℚ))

private theorem truncChar_eq_zero_of_lt {c : ℤ} {t : v.adicCompletion ℚ} (ht : WithZero.exp c < Valued.v t) :
    truncChar v c t = 0 := by
  simp only [truncChar, if_neg (not_le.mpr ht)]

private theorem truncChar_exists_norm_le (c : ℤ) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ (c' : ℤ) (t : v.adicCompletion ℚ), Valued.v t ≤ WithZero.exp c →
      ‖truncChar v c' t‖ ≤ B := by
  set w : (v.adicCompletion ℚ)ˣ := NumberField.AdelicLevel.uniformizerUnit ℚ v ^ c with hw
  have hO : IsCompact (v.adicCompletionIntegers ℚ : Set (v.adicCompletion ℚ)) := by
    rw [← coe_integersPositiveCompacts ℚ v]
    exact (integersPositiveCompacts ℚ v).isCompact
  have hcont : Continuous fun s : v.adicCompletion ℚ =>
      (NumberField.StandardAddChar.psiLocal ℚ v (((w⁻¹ : (v.adicCompletion ℚ)ˣ) : v.adicCompletion ℚ) * s) : ℂ) :=
    (NumberField.StandardAddChar.continuous_psiLocal ℚ v).comp (continuous_const.mul continuous_id)
  obtain ⟨B, hB⟩ := hO.exists_bound_of_continuousOn hcont.continuousOn
  refine ⟨max B 0, le_max_right _ _, fun c' t ht => ?_⟩
  by_cases htc : Valued.v t ≤ WithZero.exp c'
  · have hs : (w : v.adicCompletion ℚ) * t ∈ (v.adicCompletionIntegers ℚ : Set (v.adicCompletion ℚ)) := by
      rw [SetLike.mem_coe, IsDedekindDomain.HeightOneSpectrum.mem_adicCompletionIntegers, map_mul, hw,
        LaurentLocalZeta.valued_uniformizerUnit_zpow]
      calc WithZero.exp (-c) * Valued.v t ≤ WithZero.exp (-c) * WithZero.exp c := mul_le_mul_right ht _
        _ = 1 := by rw [← WithZero.exp_add, neg_add_cancel, WithZero.exp_zero]
    have hval : truncChar v c' t =
        NumberField.StandardAddChar.psiLocal ℚ v
          (((w⁻¹ : (v.adicCompletion ℚ)ˣ) : v.adicCompletion ℚ) * ((w : v.adicCompletion ℚ) * t)) := by
      simp only [truncChar, if_pos htc, Units.inv_mul_cancel_left]
    rw [hval]
    exact (hB _ hs).trans (le_max_left _ _)
  · rw [truncChar_eq_zero_of_lt v (not_le.mp htc), norm_zero]
    exact le_max_right _ _

private theorem gaussShell_ball_inter_compl_zero_eq (r : ℤ) :
    {t : v.adicCompletion ℚ | Valued.v t ≤ WithZero.exp r} ∩ ({0}ᶜ : Set (v.adicCompletion ℚ)) =
      ⋃ n : ℕ, {t : v.adicCompletion ℚ | Valued.v t = WithZero.exp (r - n)} := by
  ext t
  simp only [Set.mem_inter_iff, Set.mem_setOf_eq, Set.mem_compl_iff, Set.mem_singleton_iff, Set.mem_iUnion]
  constructor
  · rintro ⟨ht, ht0⟩
    obtain ⟨k, hk⟩ := LaurentLocalZeta.exists_mem_shell v ht0
    have hk' : Valued.v t = WithZero.exp (-k) := hk
    have hkr : -k ≤ r := by rw [hk'] at ht; exact WithZero.exp_le_exp.mp ht
    refine ⟨(r + k).toNat, ?_⟩
    rw [hk', Int.toNat_of_nonneg (by omega)]
    congr 1
    ring
  · rintro ⟨n, hn⟩
    refine ⟨?_, ?_⟩
    · rw [hn]
      exact WithZero.exp_le_exp.mpr (by omega)
    · rintro rfl
      rw [map_zero] at hn
      exact WithZero.exp_ne_zero hn.symm

private theorem gaussShell_exists_norm_charExt_le (η : (v.adicCompletion ℚ)ˣ →* ℂˣ) (hη : IsLocallyConstant η)
    (hη1 : ‖((η (NumberField.AdelicLevel.uniformizerUnit ℚ v) : ℂˣ) : ℂ)‖ = 1) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ t : v.adicCompletion ℚ, ‖charExt η t‖ ≤ M := by
  obtain ⟨M, hM⟩ := LaurentLocalZeta.exists_bound_charExt_unitShell v η hη
  refine ⟨max M 0, le_max_right _ _, fun t => ?_⟩
  by_cases ht0 : t = 0
  · rw [ht0, charExt_zero, norm_zero]
    exact le_max_right _ _
  obtain ⟨k, hk⟩ := LaurentLocalZeta.exists_mem_shell v ht0
  rw [← LaurentLocalZeta.image_unitShell_eq_shell] at hk
  obtain ⟨u, hu, rfl⟩ := hk
  rw [charExt_mul ℚ v, charExt_coe_units, map_zpow, Units.val_zpow_eq_zpow_val, norm_mul, norm_zpow, hη1,
    one_zpow, one_mul]
  exact (hM u hu).trans (le_max_left _ _)

private theorem gaussShell_coe_modulus_of_valued_eq {j : ℤ} {t : v.adicCompletion ℚ}
    (ht : Valued.v t = WithZero.exp j) : (modulus t : ℝ) = (Ideal.absNorm v.asIdeal : ℝ) ^ j := by
  have ht' : t ∈ LaurentLocalZeta.shell v (-j) := by
    show Valued.v t = WithZero.exp (- -j)
    rw [neg_neg]
    exact ht
  rw [LaurentLocalZeta.coe_modulus_eq_of_mem_shell v ht', neg_neg]

private theorem gaussShell_mulMeasure_eq (j : ℤ) :
    mulMeasure (selfDualHaarAt ℚ v) {t : v.adicCompletion ℚ | Valued.v t = WithZero.exp j} =
      mulMeasure (selfDualHaarAt ℚ v) {t : v.adicCompletion ℚ | Valued.v t = WithZero.exp (0 : ℤ)} := by
  haveI : BorelSpace (v.adicCompletion ℚ) := borelSpace_localBorel ℚ v
  have hS : {t : v.adicCompletion ℚ | Valued.v t = WithZero.exp j} = LaurentLocalZeta.shell v (-j) := by
    ext t
    simp only [Set.mem_setOf_eq, LaurentLocalZeta.shell, neg_neg]
  have hU : {t : v.adicCompletion ℚ | Valued.v t = WithZero.exp (0 : ℤ)} = LaurentLocalZeta.unitShell v := by
    ext t
    simp only [Set.mem_setOf_eq, LaurentLocalZeta.unitShell, WithZero.exp_zero]
  rw [hS, hU]
  set u : (v.adicCompletion ℚ)ˣ := NumberField.AdelicLevel.uniformizerUnit ℚ v ^ (-j) with hu
  have hmap : Measure.map (fun x : v.adicCompletion ℚ => (u : v.adicCompletion ℚ) * x)
      (mulMeasure (selfDualHaarAt ℚ v)) = mulMeasure (selfDualHaarAt ℚ v) := map_mul_left_mulMeasure ℚ v u
  have hmeas : Measurable fun x : v.adicCompletion ℚ => (u : v.adicCompletion ℚ) * x :=
    (continuous_const.mul continuous_id).measurable
  calc mulMeasure (selfDualHaarAt ℚ v) (LaurentLocalZeta.shell v (-j))
      = Measure.map (fun x : v.adicCompletion ℚ => (u : v.adicCompletion ℚ) * x) (mulMeasure (selfDualHaarAt ℚ v))
          (LaurentLocalZeta.shell v (-j)) := by rw [hmap]
    _ = mulMeasure (selfDualHaarAt ℚ v)
          ((fun x : v.adicCompletion ℚ => (u : v.adicCompletion ℚ) * x) ⁻¹' LaurentLocalZeta.shell v (-j)) :=
        Measure.map_apply hmeas (LaurentLocalZeta.measurableSet_shell v (-j))
    _ = mulMeasure (selfDualHaarAt ℚ v) (LaurentLocalZeta.unitShell v) := by
        rw [← LaurentLocalZeta.image_unitShell_eq_shell, hu,
          Set.preimage_image_eq _ (mul_right_injective₀ (Units.ne_zero _))]

private theorem gaussShell_mulMeasure_lt_top :
    mulMeasure (selfDualHaarAt ℚ v) {t : v.adicCompletion ℚ | Valued.v t = WithZero.exp (0 : ℤ)} < ⊤ := by
  haveI : BorelSpace (v.adicCompletion ℚ) := borelSpace_localBorel ℚ v
  haveI : (selfDualHaarAt ℚ v).IsAddHaarMeasure := isAddHaarMeasure_selfDualHaarAt ℚ v
  have hU : {t : v.adicCompletion ℚ | Valued.v t = WithZero.exp (0 : ℤ)} = LaurentLocalZeta.unitShell v := by
    ext t
    simp only [Set.mem_setOf_eq, LaurentLocalZeta.unitShell, WithZero.exp_zero]
  have hmeasU : MeasurableSet (LaurentLocalZeta.unitShell v) := LaurentLocalZeta.measurableSet_unitShell v
  have hfin : selfDualHaarAt ℚ v (LaurentLocalZeta.unitShell v) < ⊤ :=
    (LaurentLocalZeta.isCompact_unitShell v).measure_lt_top
  have hdens : ∀ t ∈ LaurentLocalZeta.unitShell v, ((modulus t : ENNReal))⁻¹ = 1 := by
    intro t ht
    have ht' : Valued.v t = WithZero.exp (0 : ℤ) := by
      have h : Valued.v t = 1 := ht
      rw [h, WithZero.exp_zero]
    have hm : (modulus t : ℝ) = 1 := by
      rw [gaussShell_coe_modulus_of_valued_eq v ht', zpow_zero]
    have hm' : modulus t = 1 := NNReal.coe_injective (by rw [hm, NNReal.coe_one])
    rw [hm', ENNReal.coe_one, inv_one]
  rw [hU]
  unfold mulMeasure
  rw [MeasureTheory.withDensity_apply _ hmeasU, Measure.restrict_restrict hmeasU,
    MeasureTheory.setLIntegral_congr_fun (hmeasU.inter (measurableSet_singleton 0).compl)
      (fun t ht => hdens t ht.1),
    MeasureTheory.setLIntegral_one]
  exact (measure_mono Set.inter_subset_left).trans_lt hfin

private theorem gaussShell_integrableOn_and_integral_norm_le (η : (v.adicCompletion ℚ)ˣ →* ℂˣ)
    (hη : IsLocallyConstant η) (z : ℂ) (c j : ℤ) {B M : ℝ} (_ : 0 ≤ M)
    (hB : ∀ t : v.adicCompletion ℚ, Valued.v t = WithZero.exp j → ‖truncChar v c (-t)‖ ≤ B)
    (hM : ∀ t : v.adicCompletion ℚ, ‖charExt η t‖ ≤ M) :
    IntegrableOn (fun t : v.adicCompletion ℚ => truncChar v c (-t) * charExt η t * ((modulus t : ℝ) : ℂ) ^ z)
        {t : v.adicCompletion ℚ | Valued.v t = WithZero.exp j} (mulMeasure (selfDualHaarAt ℚ v)) ∧
      (∫ t in {t : v.adicCompletion ℚ | Valued.v t = WithZero.exp j},
          ‖truncChar v c (-t) * charExt η t * ((modulus t : ℝ) : ℂ) ^ z‖ ∂(mulMeasure (selfDualHaarAt ℚ v))) ≤
        (mulMeasure (selfDualHaarAt ℚ v)).real {t : v.adicCompletion ℚ | Valued.v t = WithZero.exp (0 : ℤ)} *
          (B * M * ((Ideal.absNorm v.asIdeal : ℝ) ^ j) ^ z.re) := by
  haveI : BorelSpace (v.adicCompletion ℚ) := borelSpace_localBorel ℚ v
  haveI : SFinite (mulMeasure (selfDualHaarAt ℚ v)) := sFinite_mulMeasure_selfDualHaarAt ℚ v
  set S : Set (v.adicCompletion ℚ) := {t : v.adicCompletion ℚ | Valued.v t = WithZero.exp j} with hSdef
  set K : ℝ := B * M * ((Ideal.absNorm v.asIdeal : ℝ) ^ j) ^ z.re with hK
  have hSmeas : MeasurableSet S := by
    have hS : S = LaurentLocalZeta.shell v (-j) := by
      ext t
      simp only [hSdef, Set.mem_setOf_eq, LaurentLocalZeta.shell, neg_neg]
    rw [hS]
    exact LaurentLocalZeta.measurableSet_shell v (-j)
  have hSfin : mulMeasure (selfDualHaarAt ℚ v) S ≠ ⊤ := by
    rw [hSdef, gaussShell_mulMeasure_eq v j]
    exact (gaussShell_mulMeasure_lt_top v).ne
  have hpt : ∀ t ∈ S, ‖truncChar v c (-t) * charExt η t * ((modulus t : ℝ) : ℂ) ^ z‖ ≤ K := by
    intro t ht
    have ht' : Valued.v t = WithZero.exp j := ht
    have hpos : (0 : ℝ) < (modulus t : ℝ) := by
      rw [gaussShell_coe_modulus_of_valued_eq v ht']
      exact zpow_pos (by exact_mod_cast Nat.pos_of_ne_zero (LaurentLocalZeta.absNorm_ne_zero v)) j
    rw [norm_mul, norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos hpos, gaussShell_coe_modulus_of_valued_eq v ht',
      hK]
    have hB0 : 0 ≤ B := (norm_nonneg _).trans (hB t ht')
    have hq : (0 : ℝ) ≤ ((Ideal.absNorm v.asIdeal : ℝ) ^ j) ^ z.re := Real.rpow_nonneg (by positivity) _
    gcongr
    · exact hB t ht'
    · exact hM t
  have hmeas : AEStronglyMeasurable
      (fun t : v.adicCompletion ℚ => truncChar v c (-t) * charExt η t * ((modulus t : ℝ) : ℂ) ^ z)
      (mulMeasure (selfDualHaarAt ℚ v)) := by
    have htr : Measurable fun t : v.adicCompletion ℚ => truncChar v c (-t) := by
      have hind : (fun t : v.adicCompletion ℚ => truncChar v c (-t)) =
          {t : v.adicCompletion ℚ | Valued.v t ≤ WithZero.exp c}.indicator
            fun t => (NumberField.StandardAddChar.psiLocal ℚ v (-t) : ℂ) := by
        ext t
        simp only [truncChar, Set.indicator, Set.mem_setOf_eq, Valuation.map_neg]
      rw [hind]
      exact Measurable.indicator
        ((NumberField.StandardAddChar.continuous_psiLocal ℚ v).comp continuous_neg).measurable
        (isClosed_valued_le v c).measurableSet
    exact ((htr.mul (LaurentLocalZeta.measurable_charExt v η hη)).mul
      (LaurentLocalZeta.measurable_modulus_cpow v z)).aestronglyMeasurable
  have hint : IntegrableOn
      (fun t : v.adicCompletion ℚ => truncChar v c (-t) * charExt η t * ((modulus t : ℝ) : ℂ) ^ z) S
      (mulMeasure (selfDualHaarAt ℚ v)) := by
    refine Measure.integrableOn_of_bounded hSfin hmeas (M := K) ?_
    exact (ae_restrict_mem hSmeas).mono hpt
  refine ⟨hint, ?_⟩
  calc (∫ t in S, ‖truncChar v c (-t) * charExt η t * ((modulus t : ℝ) : ℂ) ^ z‖
          ∂(mulMeasure (selfDualHaarAt ℚ v)))
      ≤ ∫ _ in S, K ∂(mulMeasure (selfDualHaarAt ℚ v)) :=
        setIntegral_mono_on hint.norm (integrableOn_const hSfin) hSmeas hpt
    _ = (mulMeasure (selfDualHaarAt ℚ v)).real S * K := by rw [setIntegral_const, smul_eq_mul]
    _ = (mulMeasure (selfDualHaarAt ℚ v)).real {t : v.adicCompletion ℚ | Valued.v t = WithZero.exp (0 : ℤ)} * K := by
        rw [measureReal_def, measureReal_def, hSdef, gaussShell_mulMeasure_eq v j]

private theorem truncChar_integrable (η : (v.adicCompletion ℚ)ˣ →* ℂˣ) (hη : IsLocallyConstant η)
    (hη1 : ‖((η (NumberField.AdelicLevel.uniformizerUnit ℚ v) : ℂˣ) : ℂ)‖ = 1)
    (z : ℂ) (hz : 0 < z.re) (c : ℤ) :
    Integrable (fun t : v.adicCompletion ℚ => truncChar v c (-t) * charExt η t * ((modulus t : ℝ) : ℂ) ^ z)
      (mulMeasure (selfDualHaarAt ℚ v)) := by
  obtain ⟨B, hB0, hB⟩ := truncChar_exists_norm_le v c
  obtain ⟨M, hM0, hM⟩ := gaussShell_exists_norm_charExt_le v η hη hη1
  set q : ℝ := (Ideal.absNorm v.asIdeal : ℝ) with hq
  have hq1 : (1 : ℝ) < q := LaurentLocalZeta.one_lt_absNorm_real v
  have hq0 : (0 : ℝ) < q := zero_lt_one.trans hq1
  set ρ : ℝ := q⁻¹ ^ z.re with hρ
  have hρ0 : 0 ≤ ρ := Real.rpow_nonneg (inv_nonneg.mpr hq0.le) _
  have hρ1 : ρ < 1 := Real.rpow_lt_one (inv_nonneg.mpr hq0.le) (inv_lt_one_of_one_lt₀ hq1) hz
  set V : ℝ := (mulMeasure (selfDualHaarAt ℚ v)).real {t : v.adicCompletion ℚ | Valued.v t = WithZero.exp (0 : ℤ)}
    with hV
  set F : v.adicCompletion ℚ → ℂ := fun t => truncChar v c (-t) * charExt η t * ((modulus t : ℝ) : ℂ) ^ z with hF

  have hshell : ∀ n : ℕ,
      IntegrableOn F {t : v.adicCompletion ℚ | Valued.v t = WithZero.exp (c - n)} (mulMeasure (selfDualHaarAt ℚ v)) ∧
        (∫ t in {t : v.adicCompletion ℚ | Valued.v t = WithZero.exp (c - n)}, ‖F t‖
            ∂(mulMeasure (selfDualHaarAt ℚ v))) ≤ (V * (B * M * (q ^ c) ^ z.re)) * ρ ^ n := by
    intro n
    have hBn : ∀ t : v.adicCompletion ℚ, Valued.v t = WithZero.exp (c - n) → ‖truncChar v c (-t)‖ ≤ B := by
      intro t ht
      apply hB c (-t)
      rw [Valuation.map_neg, ht]
      exact WithZero.exp_le_exp.mpr (by omega)
    obtain ⟨h1, h2⟩ := gaussShell_integrableOn_and_integral_norm_le v η hη z c (c - n) hM0 hBn hM
    refine ⟨h1, h2.trans (le_of_eq ?_)⟩
    have hsplit : ((q ^ (c - (n : ℤ))) ^ z.re : ℝ) = (q ^ c) ^ z.re * ρ ^ n := by
      rw [zpow_sub₀ hq0.ne', div_eq_mul_inv, ← inv_zpow, zpow_natCast,
        Real.mul_rpow (zpow_nonneg hq0.le _) (pow_nonneg (inv_nonneg.mpr hq0.le) _), hρ,
        ← Real.rpow_natCast, ← Real.rpow_mul (inv_nonneg.mpr hq0.le), mul_comm (n : ℝ),
        Real.rpow_mul (inv_nonneg.mpr hq0.le), Real.rpow_natCast]
    rw [← hV, ← hq, hsplit]
    ring

  have hsupp : Function.support F ⊆
      ⋃ n : ℕ, {t : v.adicCompletion ℚ | Valued.v t = WithZero.exp (c - n)} := by
    intro t ht
    rw [← gaussShell_ball_inter_compl_zero_eq v c]
    refine ⟨?_, ?_⟩
    · by_contra hlt
      apply ht
      simp only [hF, truncChar_eq_zero_of_lt v (by rw [Valuation.map_neg]; exact not_le.mp hlt), zero_mul]
    · rintro rfl
      apply ht
      simp only [hF, charExt_zero, mul_zero, zero_mul]
  have hunion : IntegrableOn F (⋃ n : ℕ, {t : v.adicCompletion ℚ | Valued.v t = WithZero.exp (c - n)})
      (mulMeasure (selfDualHaarAt ℚ v)) := by
    refine integrableOn_iUnion_of_summable_integral_norm (fun n => (hshell n).1) ?_
    refine Summable.of_nonneg_of_le (fun n => integral_nonneg fun t => norm_nonneg _) (fun n => (hshell n).2) ?_
    exact (summable_geometric_of_lt_one hρ0 hρ1).mul_left _
  exact (integrableOn_iff_integrable_of_support_subset hsupp).mp hunion

private theorem integrable_truncChar_mul_charExt_mul_cpow
    (η : (v.adicCompletion ℚ)ˣ →* ℂˣ) (hη : IsLocallyConstant η)
    (hη1 : ‖((η (NumberField.AdelicLevel.uniformizerUnit ℚ v) : ℂˣ) : ℂ)‖ = 1)
    (z : ℂ) (hz : 0 < z.re) (c : ℤ) :
    Integrable (fun t : v.adicCompletion ℚ => truncChar v c (-t) * charExt η t * ((modulus t : ℝ) : ℂ) ^ z)
      (mulMeasure (selfDualHaarAt ℚ v)) := by
  exact truncChar_integrable v η hη hη1 z hz c

end LanglandsTunnell.CubicInduction
end
end

section
set_option autoImplicit false

open MeasureTheory
open IsDedekindDomain
open NumberField

namespace LanglandsTunnell
p2m_export "LanglandsTunnell" "TateLocal.localBorel TateLocal.borelSpace_localBorel"
namespace CubicInduction
p2m_export "LanglandsTunnell.CubicInduction" "gl3AmbientRightTranslate gl3AmbientRightTranslate_apply upperUnipotent3 embedMat2 iotaGL LocalGL3 diagUnitGL2 unipotentBall3 mem_unipotentBall3_iff jacquetHaar3 jacquetTruncated3 jacquetLevel jacquetValue jacquetTruncated3_eq_jacquetValue bigCell3 mem_bigCell3_iff cellSectionOf cellSectionOf_apply_of_mem cellSectionOf_apply_of_notMem gl3Entry cornerEntry lowerMinor outerMinor gl3Det cellRatio cellValue antidiagonal3 antidiagonal3_coe eventually_valued_lt continuous_gl3Entry exists_forall_le_integrableOn_and_jacquetTruncated3_eq_of_cellSectionOf exists_forall_setIntegral_shell_psiLocal_mul_charExt_mul_cpow_eq_zero exists_integrable_levelUniform_dominant_coupledInner exists_norm_setIntegral_ball_truncChar_mul_charExt_mul_cpow_le integrable_coupledIntegrand setIntegral_tallBoxJacquet_div_norm_mul_charExt_mul_cpow_eq"
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

end LanglandsTunnell.CubicInduction
end

section
set_option autoImplicit false

open MeasureTheory
open IsDedekindDomain
open NumberField
p2m_open "LanglandsTunnell.TateLocal P2MW.S_LanglandsTunnell_CubicInduction_tendsto_localZeta_truncChar_mul_coupled_localZeta_of_jacquetValue.LanglandsTunnell.TateLocal"
open NumberField.StandardAddChar
open scoped Topology

namespace LanglandsTunnell
p2m_export "LanglandsTunnell" "TateLocal.localBorel TateLocal.borelSpace_localBorel"
namespace CubicInduction
p2m_export "LanglandsTunnell.CubicInduction" "gl3AmbientRightTranslate gl3AmbientRightTranslate_apply upperUnipotent3 embedMat2 iotaGL LocalGL3 diagUnitGL2 unipotentBall3 mem_unipotentBall3_iff jacquetHaar3 jacquetTruncated3 jacquetLevel jacquetValue jacquetTruncated3_eq_jacquetValue bigCell3 mem_bigCell3_iff cellSectionOf cellSectionOf_apply_of_mem cellSectionOf_apply_of_notMem gl3Entry cornerEntry lowerMinor outerMinor gl3Det cellRatio cellValue antidiagonal3 antidiagonal3_coe eventually_valued_lt continuous_gl3Entry exists_forall_le_integrableOn_and_jacquetTruncated3_eq_of_cellSectionOf exists_forall_setIntegral_shell_psiLocal_mul_charExt_mul_cpow_eq_zero exists_integrable_levelUniform_dominant_coupledInner exists_norm_setIntegral_ball_truncChar_mul_charExt_mul_cpow_le integrable_coupledIntegrand setIntegral_tallBoxJacquet_div_norm_mul_charExt_mul_cpow_eq"
p2m_open "LanglandsTunnell.CubicInduction LanglandsTunnell"

section BeyondTheBall

variable (v : HeightOneSpectrum (𝓞 ℚ))
variable (ν : Fin 3 → ((v.adicCompletion ℚ)ˣ →* ℂˣ)) (Φ : (Fin 3 → v.adicCompletion ℚ) → ℂ)

private theorem setIntegral_jacquetHaar3_eq_zero_of_forall_add_fst
    {S : Set (v.adicCompletion ℚ × v.adicCompletion ℚ × v.adicCompletion ℚ)}
    (hS : letI := localBorel ℚ v; MeasurableSet S) {ε : v.adicCompletion ℚ}
    (hSε : (fun p : v.adicCompletion ℚ × v.adicCompletion ℚ × v.adicCompletion ℚ =>
        p + (ε, (0 : v.adicCompletion ℚ × v.adicCompletion ℚ))) ⁻¹' S = S)
    (F : v.adicCompletion ℚ × v.adicCompletion ℚ × v.adicCompletion ℚ → ℂ) {γ : ℂ} (hγ : γ ≠ 1)
    (hF : ∀ p ∈ S, F (p.1 + ε, p.2) = γ * F p) :
    letI := localBorel ℚ v
    ∫ p in S, F p ∂(jacquetHaar3 v) = 0 := by
  letI := localBorel ℚ v
  haveI : BorelSpace (v.adicCompletion ℚ) := borelSpace_localBorel ℚ v
  haveI := isAddHaarMeasure_selfDualHaarAt ℚ v
  haveI := sFinite_selfDualHaarAt ℚ v

  have h1 : ∫ p in S, F (p.1 + ε, p.2) ∂(jacquetHaar3 v) = ∫ p in S, F p ∂(jacquetHaar3 v) := by
    have hshift : S.indicator (fun p => F (p.1 + ε, p.2)) =
        fun p => S.indicator F (p + (ε, (0 : v.adicCompletion ℚ × v.adicCompletion ℚ))) := by
      funext p
      have h := Set.indicator_comp_right (M := ℂ)
        (fun q : v.adicCompletion ℚ × v.adicCompletion ℚ × v.adicCompletion ℚ =>
          q + (ε, (0 : v.adicCompletion ℚ × v.adicCompletion ℚ))) (s := S) (g := F) (x := p)
      rw [hSε] at h
      rw [← h]
      congr 1
      funext x
      simp only [Function.comp_apply]
      congr 1
      ext <;> simp
    unfold jacquetHaar3
    rw [← integral_indicator hS, ← integral_indicator hS, hshift, integral_add_right_eq_self]

  have h2 : ∫ p in S, F (p.1 + ε, p.2) ∂(jacquetHaar3 v) = γ * ∫ p in S, F p ∂(jacquetHaar3 v) := by
    rw [← integral_const_mul]
    exact setIntegral_congr_fun hS fun p hp => hF p hp
  have h3 : (1 - γ) * ∫ p in S, F p ∂(jacquetHaar3 v) = 0 := by
    rw [sub_mul, one_mul, ← h2, h1, sub_self]
  exact (mul_eq_zero.mp h3).resolve_left (sub_ne_zero.mpr (Ne.symm hγ))

private def beyondBall (c c' : ℤ) : Set (v.adicCompletion ℚ × v.adicCompletion ℚ × v.adicCompletion ℚ) :=
  {p | Valued.v p.1 ≤ WithZero.exp c ∧ Valued.v p.2.1 ≤ WithZero.exp c ∧
    WithZero.exp (2 * c) < Valued.v p.2.2 ∧ Valued.v p.2.2 ≤ WithZero.exp (2 * c')}

private def tallBox (c c' : ℤ) : Set (v.adicCompletion ℚ × v.adicCompletion ℚ × v.adicCompletion ℚ) :=
  {p | Valued.v p.1 ≤ WithZero.exp c ∧ Valued.v p.2.1 ≤ WithZero.exp c ∧ Valued.v p.2.2 ≤ WithZero.exp (2 * c')}

private theorem measurableSet_beyondBall (c c' : ℤ) :
    letI := localBorel ℚ v
    MeasurableSet (beyondBall v c c') := by
  letI := localBorel ℚ v
  haveI : BorelSpace (v.adicCompletion ℚ) := borelSpace_localBorel ℚ v
  have hset : beyondBall v c c' =
      (Prod.fst ⁻¹' {x : v.adicCompletion ℚ | Valued.v x ≤ WithZero.exp c}) ∩
        ((fun p : v.adicCompletion ℚ × v.adicCompletion ℚ × v.adicCompletion ℚ => p.2.1) ⁻¹'
          {x : v.adicCompletion ℚ | Valued.v x ≤ WithZero.exp c}) ∩
        ((fun p : v.adicCompletion ℚ × v.adicCompletion ℚ × v.adicCompletion ℚ => p.2.2) ⁻¹'
          {x : v.adicCompletion ℚ | Valued.v x ≤ WithZero.exp (2 * c)}ᶜ) ∩
        ((fun p : v.adicCompletion ℚ × v.adicCompletion ℚ × v.adicCompletion ℚ => p.2.2) ⁻¹'
          {x : v.adicCompletion ℚ | Valued.v x ≤ WithZero.exp (2 * c')}) := by
    ext p
    simp only [beyondBall, Set.mem_setOf_eq, Set.mem_inter_iff, Set.mem_preimage, Set.mem_compl_iff, not_le,
      and_assoc]
  rw [hset]
  exact ((((isClosed_valued_le v c).measurableSet.preimage measurable_fst).inter
    ((isClosed_valued_le v c).measurableSet.preimage (measurable_fst.comp measurable_snd))).inter
    (((isClosed_valued_le v (2 * c)).measurableSet.compl).preimage (measurable_snd.comp measurable_snd))).inter
    ((isClosed_valued_le v (2 * c')).measurableSet.preimage (measurable_snd.comp measurable_snd))

private theorem measurableSet_tallBox (c c' : ℤ) :
    letI := localBorel ℚ v
    MeasurableSet (tallBox v c c') := by
  letI := localBorel ℚ v
  haveI : BorelSpace (v.adicCompletion ℚ) := borelSpace_localBorel ℚ v
  have hset : tallBox v c c' =
      (Prod.fst ⁻¹' {x : v.adicCompletion ℚ | Valued.v x ≤ WithZero.exp c}) ∩
        ((fun p : v.adicCompletion ℚ × v.adicCompletion ℚ × v.adicCompletion ℚ => p.2.1) ⁻¹'
          {x : v.adicCompletion ℚ | Valued.v x ≤ WithZero.exp c}) ∩
        ((fun p : v.adicCompletion ℚ × v.adicCompletion ℚ × v.adicCompletion ℚ => p.2.2) ⁻¹'
          {x : v.adicCompletion ℚ | Valued.v x ≤ WithZero.exp (2 * c')}) := by
    ext p
    simp only [tallBox, Set.mem_setOf_eq, Set.mem_inter_iff, Set.mem_preimage, and_assoc]
  rw [hset]
  exact (((isClosed_valued_le v c).measurableSet.preimage measurable_fst).inter
    ((isClosed_valued_le v c).measurableSet.preimage (measurable_fst.comp measurable_snd))).inter
    ((isClosed_valued_le v (2 * c')).measurableSet.preimage (measurable_snd.comp measurable_snd))

private theorem preimage_add_beyondBall {c : ℤ} (hc : 1 ≤ c) (c' : ℤ) {ε : v.adicCompletion ℚ}
    (hε : Valued.v ε ≤ WithZero.exp (1 : ℤ)) :
    (fun p : v.adicCompletion ℚ × v.adicCompletion ℚ × v.adicCompletion ℚ =>
        p + (ε, (0 : v.adicCompletion ℚ × v.adicCompletion ℚ))) ⁻¹' beyondBall v c c' = beyondBall v c c' := by
  have hε' : Valued.v ε ≤ WithZero.exp c := hε.trans (WithZero.exp_le_exp.mpr hc)
  have hε'' : Valued.v (-ε) ≤ WithZero.exp c := by rwa [Valuation.map_neg]
  ext p
  simp only [Set.mem_preimage, beyondBall, Set.mem_setOf_eq, Prod.fst_add, Prod.snd_add, add_zero]
  constructor
  · rintro ⟨h1, h2, h3, h4⟩
    refine ⟨?_, h2, h3, h4⟩
    have hp : p.1 = (p.1 + ε) + -ε := by ring
    rw [hp]
    exact (Valuation.map_add _ _ _).trans (max_le h1 hε'')
  · rintro ⟨h1, h2, h3, h4⟩
    exact ⟨(Valuation.map_add _ _ _).trans (max_le h1 hε'), h2, h3, h4⟩

private theorem unipotentBall3_union_beyondBall {c c' : ℤ} (hcc' : c ≤ c') :
    unipotentBall3 v c ∪ beyondBall v c c' = tallBox v c c' := by
  have hexp : WithZero.exp (2 * c) ≤ WithZero.exp (2 * c') := WithZero.exp_le_exp.mpr (by omega)
  ext p
  simp only [Set.mem_union, mem_unipotentBall3_iff, beyondBall, tallBox, Set.mem_setOf_eq]
  constructor
  · rintro (⟨h1, h2, h3⟩ | ⟨h1, h2, -, h4⟩)
    · exact ⟨h1, h2, h3.trans hexp⟩
    · exact ⟨h1, h2, h4⟩
  · rintro ⟨h1, h2, h3⟩
    by_cases hz : Valued.v p.2.2 ≤ WithZero.exp (2 * c)
    · exact Or.inl ⟨h1, h2, hz⟩
    · exact Or.inr ⟨h1, h2, lt_of_not_ge hz, h3⟩

private theorem disjoint_unipotentBall3_beyondBall (c c' : ℤ) :
    Disjoint (unipotentBall3 v c) (beyondBall v c c') := by
  rw [Set.disjoint_left]
  rintro p ⟨-, -, h3⟩ ⟨-, -, h3', -⟩
  exact absurd h3 (not_le.mpr h3')

private theorem exists_forall_cellSectionOf_torusCellPoint_add_beyond (hν : ∀ i, IsLocallyConstant (ν i))
    (hΦl : IsLocallyConstant Φ) (hΦc : HasCompactSupport Φ) :
    ∃ c₂ : ℕ, 1 ≤ c₂ ∧ ∀ c : ℤ, (c₂ : ℤ) ≤ c → ∀ (a : (v.adicCompletion ℚ)ˣ) (ε : v.adicCompletion ℚ),
      Valued.v ε ≤ WithZero.exp (1 : ℤ) → ∀ x y z : v.adicCompletion ℚ,
        Valued.v x ≤ WithZero.exp c → Valued.v y ≤ WithZero.exp c → WithZero.exp (2 * c) < Valued.v z →
          cellSectionOf v ν Φ (torusCellPoint v (x + ε) y z a) = cellSectionOf v ν Φ (torusCellPoint v x y z a) := by
  obtain ⟨δ, hδpos, hδ⟩ := exists_invariance_radius v Φ hΦl hΦc
  obtain ⟨R, hR⟩ := exists_support_radius v Φ hΦc
  obtain ⟨k₀, hk₀⟩ := exists_forall_charExt_mul_eq v (ν 0) (hν 0)
  obtain ⟨k₁, hk₁⟩ := exists_forall_charExt_mul_eq v (ν 1) (hν 1)
  set q : ℝ := (Ideal.absNorm v.asIdeal : ℝ) with hq_def
  have hq1 : (1 : ℝ) < q := one_lt_absNorm_real v
  have hq0 : (0 : ℝ) < q := zero_lt_one.trans hq1
  set R' : ℝ := max R 1 with hR'_def
  have hR'1 : (1 : ℝ) ≤ R' := le_max_right _ _
  have hRR' : R ≤ R' := le_max_left _ _
  have hR'0 : (0 : ℝ) < R' := zero_lt_one.trans_le hR'1
  set k : ℕ := max (max k₀ k₁) 1 with hk_def
  have hk1 : 1 ≤ k := le_max_right _ _
  have hk₀k : k₀ ≤ k := (le_max_left _ _).trans (le_max_left _ _)
  have hk₁k : k₁ ≤ k := (le_max_right _ _).trans (le_max_left _ _)

  obtain ⟨n, hn⟩ : ∃ n : ℕ, q * (q⁻¹ ^ n * R') ≤ δ := by
    obtain ⟨n, hn⟩ := exists_pow_lt_of_lt_one (div_pos hδpos (mul_pos hq0 hR'0)) (inv_lt_one_of_one_lt₀ hq1)
    refine ⟨n, ?_⟩
    have h := (lt_div_iff₀ (mul_pos hq0 hR'0)).mp hn
    calc q * (q⁻¹ ^ n * R') = q⁻¹ ^ n * (q * R') := by ring
      _ ≤ δ := h.le
  refine ⟨max (k + 1) n, le_max_of_le_left (Nat.succ_le_succ (Nat.zero_le _)), fun c hc a ε hε => ?_⟩
  have hkc : (k : ℤ) + 1 ≤ c := le_trans (by exact_mod_cast le_max_left (k + 1) n) hc
  have hnc : (n : ℤ) ≤ c := le_trans (by exact_mod_cast le_max_right (k + 1) n) hc
  have hc1 : (1 : ℤ) ≤ c := by omega
  have ha0 : (0 : ℝ) < ‖(a : v.adicCompletion ℚ)‖ := norm_pos_iff.mpr a.ne_zero
  have hεn : ‖ε‖ ≤ q := by simpa using norm_le_zpow_of_valued_le v hε

  have hsmall_k : q ^ (1 - c) ≤ q ^ (-(k : ℤ)) := zpow_le_zpow_right₀ hq1.le (by omega)
  have hsmall_δ : q ^ (1 - c) * R' ≤ δ := by
    have hmono : q ^ (1 - c) ≤ q ^ (1 - (n : ℤ)) := zpow_le_zpow_right₀ hq1.le (by omega)
    have hrew : q ^ (1 - (n : ℤ)) = q * q⁻¹ ^ n := by
      rw [zpow_sub₀ hq0.ne', zpow_one, zpow_natCast, inv_pow, div_eq_mul_inv]
    calc q ^ (1 - c) * R' ≤ q ^ (1 - (n : ℤ)) * R' := mul_le_mul_of_nonneg_right hmono hR'0.le
      _ = q * (q⁻¹ ^ n * R') := by rw [hrew]; ring
      _ ≤ δ := hn

  have hsec : ∀ (x y z ε' : v.adicCompletion ℚ), ‖ε'‖ ≤ q → Valued.v x ≤ WithZero.exp c →
      Valued.v y ≤ WithZero.exp c → WithZero.exp (2 * c) < Valued.v z →
      cellSectionOf v ν Φ (torusCellPoint v x y z a) ≠ 0 →
      cellSectionOf v ν Φ (torusCellPoint v (x + ε') y z a) = cellSectionOf v ν Φ (torusCellPoint v x y z a) := by
    intro x y z ε' hε' hx hy hzv hne
    have hmem : torusCellPoint v x y z a ∈ bigCell3 v := by
      by_contra h
      exact hne (cellSectionOf_apply_of_notMem v ν Φ h)
    obtain ⟨hz, hm⟩ := (torusCellPoint_mem_bigCell3_iff v x y z a).mp hmem
    rw [cellSectionOf_apply_of_mem v ν Φ hmem] at hne
    have hΦne : Φ (cellRatio v (torusCellPoint v x y z a)) ≠ 0 := right_ne_zero_of_mul hne
    have hb := hR _ hΦne
    rw [cellRatio_torusCellPoint] at hb
    have h2 : ‖(a : v.adicCompletion ℚ) * y / (x * y - z)‖ ≤ R := by simpa using hb 2
    have hR0 : (0 : ℝ) ≤ R := (norm_nonneg _).trans h2

    have hxn : ‖x‖ ≤ q ^ c := norm_le_zpow_of_valued_le v hx
    have hyn : ‖y‖ ≤ q ^ c := norm_le_zpow_of_valued_le v hy
    have hzn : q ^ (2 * c) < ‖z‖ := by
      by_contra h
      exact absurd (valued_le_of_norm_le_zpow v (not_lt.mp h)) (not_le.mpr hzv)
    have hz0 : (0 : ℝ) < ‖z‖ := (zpow_pos hq0 _).trans hzn
    set m : v.adicCompletion ℚ := x * y - z with hm_def
    have hxy_lt : Valued.v (x * y) < Valued.v (-z) := by
      rw [Valuation.map_neg, Valuation.map_mul]
      refine lt_of_le_of_lt ?_ hzv
      rw [two_mul, WithZero.exp_add]
      exact mul_le_mul' hx hy
    have hvm : Valued.v m = Valued.v z := by
      rw [hm_def, sub_eq_add_neg, Valued.v.map_add_eq_of_lt_right hxy_lt, Valuation.map_neg]
    have hmn : ‖m‖ = ‖z‖ := by
      rw [NumberField.FinitePlace.norm_def v m, NumberField.FinitePlace.norm_def v z, hvm]
    set t : v.adicCompletion ℚ := ε' * y / m with ht_def

    have htn : ‖t‖ ≤ q ^ (1 - c) := by
      have hnum : ‖ε' * y‖ ≤ q * q ^ c := by
        rw [norm_mul]
        exact mul_le_mul hε' hyn (norm_nonneg _) hq0.le
      have hqq : q * q ^ c = q ^ (1 - c) * q ^ (2 * c) := by
        rw [← zpow_one_add₀ hq0.ne', ← zpow_add₀ hq0.ne']
        congr 1
        ring
      rw [ht_def, norm_div, hmn, div_le_iff₀ hz0]
      calc ‖ε' * y‖ ≤ q * q ^ c := hnum
        _ = q ^ (1 - c) * q ^ (2 * c) := hqq
        _ ≤ q ^ (1 - c) * ‖z‖ := mul_le_mul_of_nonneg_left hzn.le (zpow_nonneg hq0.le _)
    have ht_small : ‖t‖ ≤ q ^ (-(k : ℤ)) := htn.trans hsmall_k
    set u : v.adicCompletion ℚ := 1 + t with hu_def
    have hut : u - 1 = t := by rw [hu_def]; ring
    have hu_val : Valued.v (u - 1) ≤ WithZero.exp (-(k : ℤ)) := by
      rw [hut]
      exact valued_le_of_norm_le_zpow v ht_small
    have hu1 : Valued.v u = 1 := valued_eq_one_of_valued_sub_one_le v hk1 hu_val
    have hun : ‖u‖ = 1 := norm_eq_one_of_valued_eq_one v hu1
    have hu0 : u ≠ 0 := by
      intro h
      rw [h, map_zero] at hu1
      exact zero_ne_one hu1
    have hm' : (x + ε') * y - z = m * u := by
      have hcancel : m * (ε' * y / m) = ε' * y := by field_simp
      rw [hu_def, ht_def, mul_add, mul_one, hcancel, hm_def]
      ring
    have hmu : m * u ≠ 0 := mul_ne_zero hm hu0
    have hmem' : torusCellPoint v (x + ε') y z a ∈ bigCell3 v :=
      (torusCellPoint_mem_bigCell3_iff v (x + ε') y z a).mpr ⟨hz, by rw [hm']; exact hmu⟩

    have hinv_val : Valued.v (u⁻¹ - 1) ≤ WithZero.exp (-(k : ℤ)) := by
      have : u⁻¹ - 1 = -(u⁻¹ * (u - 1)) := by rw [mul_sub, inv_mul_cancel₀ hu0, mul_one, neg_sub]
      rw [this, Valuation.map_neg, Valuation.map_mul, map_inv₀, hu1, inv_one, one_mul]
      exact hu_val
    have hinv_n : ‖u⁻¹ - 1‖ = ‖t‖ := by
      have : u⁻¹ - 1 = -(u⁻¹ * (u - 1)) := by rw [mul_sub, inv_mul_cancel₀ hu0, mul_one, neg_sub]
      rw [this, norm_neg, norm_mul, norm_inv, hun, inv_one, one_mul, hut]
    have hexp₀ : WithZero.exp (-(k : ℤ)) ≤ WithZero.exp (-(k₀ : ℤ)) := WithZero.exp_le_exp.mpr (by omega)
    have hexp₁ : WithZero.exp (-(k : ℤ)) ≤ WithZero.exp (-(k₁ : ℤ)) := WithZero.exp_le_exp.mpr (by omega)

    rw [cellSectionOf_apply_of_mem v ν Φ hmem', cellSectionOf_apply_of_mem v ν Φ hmem,
      cellValue_torusCellPoint, cellValue_torusCellPoint, cellRatio_torusCellPoint, cellRatio_torusCellPoint, hm']
    have e0 : charExt (ν 0) ((a : v.adicCompletion ℚ) / (m * u)) = charExt (ν 0) ((a : v.adicCompletion ℚ) / m) := by
      rw [show (a : v.adicCompletion ℚ) / (m * u) = u⁻¹ * ((a : v.adicCompletion ℚ) / m) by field_simp]
      exact hk₀ u⁻¹ _ (hinv_val.trans hexp₀)
    have e1 : charExt (ν 1) (m * u / z) = charExt (ν 1) (m / z) := by
      rw [show m * u / z = u * (m / z) by ring]
      exact hk₁ u _ (hu_val.trans hexp₁)
    have e3 : ‖(a : v.adicCompletion ℚ) / (m * u)‖ = ‖(a : v.adicCompletion ℚ) / m‖ := by
      rw [norm_div, norm_div, norm_mul, hun, mul_one]
    have eΦ : Φ ![(x + ε') / z, (a : v.adicCompletion ℚ) / z, (a : v.adicCompletion ℚ) * y / (m * u)] =
        Φ ![x / z, (a : v.adicCompletion ℚ) / z, (a : v.adicCompletion ℚ) * y / m] := by
      refine hδ _ _ ?_
      intro i
      fin_cases i
      · show ‖(x + ε') / z - x / z‖ ≤ δ
        have hz1 : ‖(1 : v.adicCompletion ℚ) / z‖ ≤ (q ^ (2 * c))⁻¹ := by
          rw [norm_div, norm_one, one_div]
          exact inv_anti₀ (zpow_pos hq0 _) hzn.le
        have hqq : q * (q ^ (2 * c))⁻¹ ≤ q ^ (1 - c) := by
          rw [← zpow_neg, ← zpow_one_add₀ hq0.ne']
          exact zpow_le_zpow_right₀ hq1.le (by omega)
        calc ‖(x + ε') / z - x / z‖ = ‖ε' * (1 / z)‖ := by rw [add_div, add_sub_cancel_left, mul_one_div]
          _ = ‖ε'‖ * ‖(1 : v.adicCompletion ℚ) / z‖ := norm_mul _ _
          _ ≤ q * (q ^ (2 * c))⁻¹ := mul_le_mul hε' hz1 (norm_nonneg _) hq0.le
          _ ≤ q ^ (1 - c) := hqq
          _ ≤ q ^ (1 - c) * R' := le_mul_of_one_le_right (zpow_nonneg hq0.le _) hR'1
          _ ≤ δ := hsmall_δ
      · show ‖(a : v.adicCompletion ℚ) / z - (a : v.adicCompletion ℚ) / z‖ ≤ δ
        rw [sub_self, norm_zero]
        exact hδpos.le
      · show ‖(a : v.adicCompletion ℚ) * y / (m * u) - (a : v.adicCompletion ℚ) * y / m‖ ≤ δ
        calc ‖(a : v.adicCompletion ℚ) * y / (m * u) - (a : v.adicCompletion ℚ) * y / m‖
            = ‖(a : v.adicCompletion ℚ) * y / m‖ * ‖u⁻¹ - 1‖ := by rw [← norm_mul]; congr 1; field_simp
          _ = ‖(a : v.adicCompletion ℚ) * y / m‖ * ‖t‖ := by rw [hinv_n]
          _ ≤ R * q ^ (1 - c) := mul_le_mul h2 htn (norm_nonneg _) hR0
          _ ≤ R' * q ^ (1 - c) := mul_le_mul_of_nonneg_right hRR' (zpow_nonneg hq0.le _)
          _ = q ^ (1 - c) * R' := mul_comm _ _
          _ ≤ δ := hsmall_δ
    rw [e0, e1, e3, eΦ]

  intro x y z hx hy hzv
  have hεn' : ‖-ε‖ ≤ q := by rwa [norm_neg]
  have hxε : Valued.v (x + ε) ≤ WithZero.exp c :=
    (Valuation.map_add _ _ _).trans (max_le hx (hε.trans (WithZero.exp_le_exp.mpr hc1)))
  by_cases h0 : cellSectionOf v ν Φ (torusCellPoint v x y z a) = 0
  · by_cases h0' : cellSectionOf v ν Φ (torusCellPoint v (x + ε) y z a) = 0
    · rw [h0, h0']
    · have h := hsec (x + ε) y z (-ε) hεn' hxε hy hzv h0'
      rw [add_neg_cancel_right] at h
      rw [← h] at h0'
      exact (h0' h0).elim
  · exact hsec x y z ε hεn hx hy hzv h0

private theorem exists_forall_setIntegral_beyondBall_torusIntegrand_eq_zero (hν : ∀ i, IsLocallyConstant (ν i))
    (hΦl : IsLocallyConstant Φ) (hΦc : HasCompactSupport Φ) :
    ∃ c₂ : ℕ, 1 ≤ c₂ ∧ ∀ c : ℤ, (c₂ : ℤ) ≤ c → ∀ (c' : ℤ) (a : (v.adicCompletion ℚ)ˣ),
      letI := localBorel ℚ v
      ∫ p in beyondBall v c c', torusIntegrand v ν Φ a p ∂(jacquetHaar3 v) = 0 := by
  obtain ⟨c₂, hc₂, hinv⟩ := exists_forall_cellSectionOf_torusCellPoint_add_beyond v ν Φ hν hΦl hΦc
  obtain ⟨ε, hε, hψ⟩ := exists_psiLocal_neg_ne_one v
  refine ⟨c₂, hc₂, fun c hc c' a => ?_⟩
  have hc1 : (1 : ℤ) ≤ c := le_trans (by exact_mod_cast hc₂) hc
  refine setIntegral_jacquetHaar3_eq_zero_of_forall_add_fst v (measurableSet_beyondBall v c c')
    (preimage_add_beyondBall v hc1 c' hε) (torusIntegrand v ν Φ a) hψ fun p hp => ?_
  obtain ⟨hx, hy, hzv, -⟩ := hp
  simp only [torusIntegrand]
  rw [hinv c hc a ε hε p.1 p.2.1 p.2.2 hx hy hzv]
  have hsum : -((p.1 + ε) + p.2.1) = -ε + -(p.1 + p.2.1) := by ring
  rw [hsum, AddChar.map_add_eq_mul, mul_assoc]

private theorem exists_forall_integrableOn_torusIntegrand (hν : ∀ i, IsLocallyConstant (ν i))
    (hΦl : IsLocallyConstant Φ) (hΦc : HasCompactSupport Φ) (a : (v.adicCompletion ℚ)ˣ) :
    ∃ c₀ : ℕ, ∀ c : ℤ, (c₀ : ℤ) ≤ c →
      letI := localBorel ℚ v
      IntegrableOn (torusIntegrand v ν Φ a) (unipotentBall3 v c) (jacquetHaar3 v) := by
  obtain ⟨c₀, h⟩ := exists_forall_le_integrableOn_and_jacquetTruncated3_eq_of_cellSectionOf v ν hν Φ ⟨hΦl, hΦc⟩
    (iotaGL (diagUnitGL2 a) * antidiagonal3 v)
  exact ⟨c₀, fun c hc => (h c hc).1⟩

private theorem exists_forall_jacquetTruncated3_torusTranslate_eq_setIntegral_tallBox
    (hν : ∀ i, IsLocallyConstant (ν i)) (hΦl : IsLocallyConstant Φ) (hΦc : HasCompactSupport Φ) :
    ∃ c₂ : ℕ, 1 ≤ c₂ ∧ ∀ (a : (v.adicCompletion ℚ)ˣ) (c c' : ℤ), (c₂ : ℤ) ≤ c → c ≤ c' →
      letI := localBorel ℚ v
      IntegrableOn (torusIntegrand v ν Φ a) (tallBox v c c') (jacquetHaar3 v) ∧
        jacquetTruncated3 v c (torusTranslate v ν Φ a) =
          ∫ p in tallBox v c c', torusIntegrand v ν Φ a p ∂(jacquetHaar3 v) := by
  letI := localBorel ℚ v
  obtain ⟨c₂, hc₂, hzero⟩ := exists_forall_setIntegral_beyondBall_torusIntegrand_eq_zero v ν Φ hν hΦl hΦc
  refine ⟨c₂, hc₂, fun a c c' hc hcc' => ?_⟩
  obtain ⟨c₀, hint⟩ := exists_forall_integrableOn_torusIntegrand v ν Φ hν hΦl hΦc a

  set c'' : ℤ := max c' (c₀ : ℤ) with hc''_def
  have hsub : tallBox v c c' ⊆ unipotentBall3 v c'' := by
    rintro p ⟨h1, h2, h3⟩
    have hcc'' : c ≤ c'' := hcc'.trans (le_max_left _ _)
    have hc'c'' : c' ≤ c'' := le_max_left _ _
    exact ⟨h1.trans (WithZero.exp_le_exp.mpr hcc''), h2.trans (WithZero.exp_le_exp.mpr hcc''),
      h3.trans (WithZero.exp_le_exp.mpr (by omega))⟩
  have hbig : IntegrableOn (torusIntegrand v ν Φ a) (unipotentBall3 v c'') (jacquetHaar3 v) :=
    hint c'' (le_max_right _ _)
  have htall : IntegrableOn (torusIntegrand v ν Φ a) (tallBox v c c') (jacquetHaar3 v) := hbig.mono_set hsub
  refine ⟨htall, ?_⟩
  have hball : IntegrableOn (torusIntegrand v ν Φ a) (unipotentBall3 v c) (jacquetHaar3 v) :=
    htall.mono_set (by rw [← unipotentBall3_union_beyondBall v hcc']; exact Set.subset_union_left)
  have hbeyond : IntegrableOn (torusIntegrand v ν Φ a) (beyondBall v c c') (jacquetHaar3 v) :=
    htall.mono_set (by rw [← unipotentBall3_union_beyondBall v hcc']; exact Set.subset_union_right)
  rw [jacquetTruncated3_torusTranslate_eq_integral, ← unipotentBall3_union_beyondBall v hcc',
    setIntegral_union (disjoint_unipotentBall3_beyondBall v c c') (measurableSet_beyondBall v c c') hball hbeyond,
    hzero c hc c' a, add_zero]

end BeyondTheBall

end LanglandsTunnell.CubicInduction
end

section
open MeasureTheory
open IsDedekindDomain
open NumberField
p2m_open "LanglandsTunnell.TateLocal P2MW.S_LanglandsTunnell_CubicInduction_tendsto_localZeta_truncChar_mul_coupled_localZeta_of_jacquetValue.LanglandsTunnell.TateLocal"
open NumberField.StandardAddChar

namespace LanglandsTunnell
p2m_export "LanglandsTunnell" "TateLocal.localBorel TateLocal.borelSpace_localBorel"
namespace CubicInduction
p2m_export "LanglandsTunnell.CubicInduction" "gl3AmbientRightTranslate gl3AmbientRightTranslate_apply upperUnipotent3 embedMat2 iotaGL LocalGL3 diagUnitGL2 unipotentBall3 mem_unipotentBall3_iff jacquetHaar3 jacquetTruncated3 jacquetLevel jacquetValue jacquetTruncated3_eq_jacquetValue bigCell3 mem_bigCell3_iff cellSectionOf cellSectionOf_apply_of_mem cellSectionOf_apply_of_notMem gl3Entry cornerEntry lowerMinor outerMinor gl3Det cellRatio cellValue antidiagonal3 antidiagonal3_coe eventually_valued_lt continuous_gl3Entry exists_forall_le_integrableOn_and_jacquetTruncated3_eq_of_cellSectionOf exists_forall_setIntegral_shell_psiLocal_mul_charExt_mul_cpow_eq_zero exists_integrable_levelUniform_dominant_coupledInner exists_norm_setIntegral_ball_truncChar_mul_charExt_mul_cpow_le integrable_coupledIntegrand setIntegral_tallBoxJacquet_div_norm_mul_charExt_mul_cpow_eq"
p2m_open "LanglandsTunnell.CubicInduction LanglandsTunnell"

section TallBoxCoupled

variable (v : HeightOneSpectrum (𝓞 ℚ))
variable (ν : Fin 3 → ((v.adicCompletion ℚ)ˣ →* ℂˣ)) (Φ : (Fin 3 → v.adicCompletion ℚ) → ℂ)

attribute [local instance] LanglandsTunnell.TateLocal.localBorel

private noncomputable def innerK (c : ℤ) (u r w : v.adicCompletion ℚ) : ℂ :=
  Φ ![u, r, w] *
    (charExt (ν 0 * (ν 1)⁻¹) (r - u * w) * ((modulus (r - u * w) : ℝ) : ℂ)⁻¹) *
    (if Valued.v (w / (r - u * w)) ≤ WithZero.exp c then (psiLocal ℚ v (w / (r - u * w)) : ℂ) else 0)

private noncomputable def innerI (c : ℤ) (u r : v.adicCompletion ℚ) : ℂ :=
  ∫ w, innerK v ν Φ c u r w ∂(selfDualHaarAt ℚ v)

end TallBoxCoupled
end LanglandsTunnell.CubicInduction
end

section
open MeasureTheory
open IsDedekindDomain
open NumberField
p2m_open "LanglandsTunnell.TateLocal P2MW.S_LanglandsTunnell_CubicInduction_tendsto_localZeta_truncChar_mul_coupled_localZeta_of_jacquetValue.LanglandsTunnell.TateLocal"
open scoped ENNReal

namespace LanglandsTunnell
p2m_export "LanglandsTunnell" "TateLocal.localBorel TateLocal.borelSpace_localBorel"
namespace CubicInduction
p2m_export "LanglandsTunnell.CubicInduction" "gl3AmbientRightTranslate gl3AmbientRightTranslate_apply upperUnipotent3 embedMat2 iotaGL LocalGL3 diagUnitGL2 unipotentBall3 mem_unipotentBall3_iff jacquetHaar3 jacquetTruncated3 jacquetLevel jacquetValue jacquetTruncated3_eq_jacquetValue bigCell3 mem_bigCell3_iff cellSectionOf cellSectionOf_apply_of_mem cellSectionOf_apply_of_notMem gl3Entry cornerEntry lowerMinor outerMinor gl3Det cellRatio cellValue antidiagonal3 antidiagonal3_coe eventually_valued_lt continuous_gl3Entry exists_forall_le_integrableOn_and_jacquetTruncated3_eq_of_cellSectionOf exists_forall_setIntegral_shell_psiLocal_mul_charExt_mul_cpow_eq_zero exists_integrable_levelUniform_dominant_coupledInner exists_norm_setIntegral_ball_truncChar_mul_charExt_mul_cpow_le integrable_coupledIntegrand setIntegral_tallBoxJacquet_div_norm_mul_charExt_mul_cpow_eq"
p2m_open "LanglandsTunnell.CubicInduction LanglandsTunnell"

section SwapDevice

variable (v : HeightOneSpectrum (𝓞 ℚ))

attribute [local instance] LanglandsTunnell.TateLocal.localBorel

local notation "dmul" => mulMeasure (selfDualHaarAt ℚ v)
local notation "Kv" => IsDedekindDomain.HeightOneSpectrum.adicCompletion ℚ v

private theorem mulMeasure_apply_singleton_zero :
    dmul ({0} : Set (Kv)) = 0 := by
  haveI : MeasurableSingletonClass (Kv) := measurableSingletonClass_adicCompletion ℚ v
  unfold mulMeasure
  rw [withDensity_apply _ (measurableSet_singleton 0), Measure.restrict_restrict (measurableSet_singleton 0),
    Set.inter_compl_self, Measure.restrict_empty, lintegral_zero_measure]

private theorem prod_mulMeasure_axes :
    (Measure.prod dmul dmul)
      ((({0} : Set (Kv)) ×ˢ Set.univ) ∪ (Set.univ ×ˢ ({0} : Set (Kv)))) = 0 := by
  haveI : SFinite dmul := sFinite_mulMeasure_selfDualHaarAt ℚ v
  have h0 := mulMeasure_apply_singleton_zero v
  exact measure_union_null (by rw [Measure.prod_prod, h0, zero_mul]) (by rw [Measure.prod_prod, h0, mul_zero])

private theorem ae_fst_ne_zero_and_snd_ne_zero :
    ∀ᵐ p ∂(Measure.prod dmul dmul), p.1 ≠ 0 ∧ p.2 ≠ 0 := by
  filter_upwards [compl_mem_ae_iff.mpr (prod_mulMeasure_axes v)] with p hp
  simpa only [Set.mem_compl_iff, Set.mem_union, Set.mem_prod, Set.mem_singleton_iff, Set.mem_univ, and_true,
    true_and, not_or, ne_eq] using hp

end SwapDevice
end LanglandsTunnell.CubicInduction
end

section
open MeasureTheory
open IsDedekindDomain
open NumberField
p2m_open "LanglandsTunnell.TateLocal P2MW.S_LanglandsTunnell_CubicInduction_tendsto_localZeta_truncChar_mul_coupled_localZeta_of_jacquetValue.LanglandsTunnell.TateLocal"
open NumberField.StandardAddChar

namespace LanglandsTunnell
p2m_export "LanglandsTunnell" "TateLocal.localBorel TateLocal.borelSpace_localBorel"
namespace CubicInduction
p2m_export "LanglandsTunnell.CubicInduction" "gl3AmbientRightTranslate gl3AmbientRightTranslate_apply upperUnipotent3 embedMat2 iotaGL LocalGL3 diagUnitGL2 unipotentBall3 mem_unipotentBall3_iff jacquetHaar3 jacquetTruncated3 jacquetLevel jacquetValue jacquetTruncated3_eq_jacquetValue bigCell3 mem_bigCell3_iff cellSectionOf cellSectionOf_apply_of_mem cellSectionOf_apply_of_notMem gl3Entry cornerEntry lowerMinor outerMinor gl3Det cellRatio cellValue antidiagonal3 antidiagonal3_coe eventually_valued_lt continuous_gl3Entry exists_forall_le_integrableOn_and_jacquetTruncated3_eq_of_cellSectionOf exists_forall_setIntegral_shell_psiLocal_mul_charExt_mul_cpow_eq_zero exists_integrable_levelUniform_dominant_coupledInner exists_norm_setIntegral_ball_truncChar_mul_charExt_mul_cpow_le integrable_coupledIntegrand setIntegral_tallBoxJacquet_div_norm_mul_charExt_mul_cpow_eq"
p2m_open "LanglandsTunnell.CubicInduction LanglandsTunnell"

section LevelIdentity

variable (v : HeightOneSpectrum (𝓞 ℚ))
variable (ν : Fin 3 → ((v.adicCompletion ℚ)ˣ →* ℂˣ)) (Φ : (Fin 3 → v.adicCompletion ℚ) → ℂ)

attribute [local instance] LanglandsTunnell.TateLocal.localBorel

local notation "dmul" => mulMeasure (selfDualHaarAt ℚ v)
local notation "Kv" => IsDedekindDomain.HeightOneSpectrum.adicCompletion ℚ v

private theorem charExt_ne_zero_of_ne_zero (η : Kvˣ →* ℂˣ) {x : Kv} (hx : x ≠ 0) : charExt η x ≠ 0 := by
  rw [charExt_of_ne_zero _ hx]
  exact Units.ne_zero _

private noncomputable def gaussKer (χ : Kvˣ →* ℂˣ) (s : ℂ) (c : ℤ) (t : Kv) : ℂ :=
  (if Valued.v (-t) ≤ WithZero.exp c then (psiLocal ℚ v (-t) : ℂ) else 0) * charExt (ν 2 * χ) t *
    ((modulus t : ℝ) : ℂ) ^ s

private noncomputable def cWeight (χ : Kvˣ →* ℂˣ) (s : ℂ) (u r : Kv) : ℂ :=
  charExt (ν 2 * χ)⁻¹ u * ((modulus u : ℝ) : ℂ) ^ (1 - s) * charExt (ν 1 * χ) r * ((modulus r : ℝ) : ℂ) ^ s

open scoped Classical in

private noncomputable def jacquetTallBox (c c' : ℤ) (b : Kv) : ℂ :=
  if hb : b = 0 then 0 else ∫ p in tallBox v c c', torusIntegrand v ν Φ (Units.mk0 b hb) p ∂(jacquetHaar3 v)

private theorem setIntegral_jacquetTallBox_mul_charExt_mul_cpow_eq (χ : Kvˣ →* ℂˣ) (s : ℂ) (c c' : ℤ)
    (S : Set Kv) (hS : MeasurableSet S)
    (hint : ∀ a : Kvˣ, IntegrableOn (torusIntegrand v ν Φ a) (tallBox v c c') (jacquetHaar3 v))
    (hIg : Integrable (gaussKer v ν χ s c) dmul)
    (hWI : Integrable (fun p : Kv × Kv => cWeight v ν χ s p.2 p.1 * innerI v ν Φ c p.2 p.1)
      (Measure.prod dmul dmul)) :
    ∫ b in S, jacquetTallBox v ν Φ c c' b / (‖b‖ : ℂ) * charExt χ b * ((modulus b : ℝ) : ℂ) ^ s ∂dmul =
      charExt (ν 0) (-1) * charExt (ν 1) (-1) *
        ∫ r, ∫ u, (∫ t, S.indicator (fun _ => (1 : ℂ)) (r * u⁻¹ * t) *
              (if Valued.v (u⁻¹ * t) ≤ WithZero.exp (2 * c') then (1 : ℂ) else 0) * gaussKer v ν χ s c t ∂dmul) *
            (cWeight v ν χ s u r * innerI v ν Φ c u r) ∂dmul ∂dmul :=
  setIntegral_tallBoxJacquet_div_norm_mul_charExt_mul_cpow_eq v ν Φ χ s c c' (jacquetTallBox v ν Φ c c')
    (fun a => by simp only [jacquetTallBox, dif_neg a.ne_zero, Units.mk0_val]; rfl)
    S hS hint hIg hWI

private noncomputable def torusT (χ : Kvˣ →* ℂˣ) (s : ℂ) (c c' : ℤ) (S : Set Kv) (q : (Kv × Kv) × Kv) : ℂ :=
  charExt (ν 0) (-1) * charExt (ν 1) (-1) *
    ((S.indicator (fun _ => (1 : ℂ)) (q.1.1 * (q.1.2)⁻¹ * q.2) *
          (if Valued.v ((q.1.2)⁻¹ * q.2) ≤ WithZero.exp (2 * c') then (1 : ℂ) else 0) * gaussKer v ν χ s c q.2) *
      (cWeight v ν χ s q.1.2 q.1.1 * innerI v ν Φ c q.1.2 q.1.1))

private theorem norm_indicator_one_mul_ite_le (S : Set Kv) (x y : Kv) (c' : ℤ) :
    ‖S.indicator (fun _ => (1 : ℂ)) x * (if Valued.v y ≤ WithZero.exp (2 * c') then (1 : ℂ) else 0)‖ ≤ 1 := by
  rw [norm_mul]
  refine mul_le_one₀ ?_ (norm_nonneg _) ?_
  · by_cases hx : x ∈ S
    · rw [Set.indicator_of_mem hx, norm_one]
    · rw [Set.indicator_of_notMem hx, norm_zero]
      exact zero_le_one
  · by_cases hy : Valued.v y ≤ WithZero.exp (2 * c')
    · rw [if_pos hy, norm_one]
    · rw [if_neg hy, norm_zero]
      exact zero_le_one

private theorem integrable_torusT (χ : Kvˣ →* ℂˣ) (s : ℂ) (c c' : ℤ) (S : Set Kv) (hS : MeasurableSet S)
    (hIg : Integrable (gaussKer v ν χ s c) dmul)
    (hWI : Integrable (fun p : Kv × Kv => cWeight v ν χ s p.2 p.1 * innerI v ν Φ c p.2 p.1)
      (Measure.prod dmul dmul)) :
    Integrable (torusT v ν Φ χ s c c' S) (Measure.prod (Measure.prod dmul dmul) dmul) := by
  haveI : BorelSpace Kv := borelSpace_localBorel ℚ v
  haveI : SFinite dmul := sFinite_mulMeasure_selfDualHaarAt ℚ v
  have hF := hWI.mul_prod hIg

  have hB : Measurable fun q : (Kv × Kv) × Kv =>
      S.indicator (fun _ => (1 : ℂ)) (q.1.1 * (q.1.2)⁻¹ * q.2) *
        (if Valued.v ((q.1.2)⁻¹ * q.2) ≤ WithZero.exp (2 * c') then (1 : ℂ) else 0) := by
    refine Measurable.mul ?_ ?_
    · exact (measurable_const.indicator hS).comp ((measurable_fst.fst.mul measurable_fst.snd.inv).mul measurable_snd)
    · refine Measurable.ite ?_ measurable_const measurable_const
      exact (isClosed_valued_le v (2 * c')).measurableSet.preimage (measurable_fst.snd.inv.mul measurable_snd)
  have hT := (hF.bdd_mul hB.aestronglyMeasurable (Filter.Eventually.of_forall fun q =>
    norm_indicator_one_mul_ite_le v S _ _ c')).const_mul (charExt (ν 0) (-1) * charExt (ν 1) (-1))
  refine hT.congr (Filter.Eventually.of_forall fun q => ?_)
  simp only [torusT]
  ring

end LevelIdentity
end LanglandsTunnell.CubicInduction
end

section
set_option autoImplicit false

open MeasureTheory
open IsDedekindDomain
open NumberField
p2m_open "LanglandsTunnell.TateLocal P2MW.S_LanglandsTunnell_CubicInduction_tendsto_localZeta_truncChar_mul_coupled_localZeta_of_jacquetValue.LanglandsTunnell.TateLocal"

attribute [local instance] LanglandsTunnell.TateLocal.localBorel

namespace LanglandsTunnell
p2m_export "LanglandsTunnell" "TateLocal.localBorel TateLocal.borelSpace_localBorel"
namespace CubicInduction
p2m_export "LanglandsTunnell.CubicInduction" "gl3AmbientRightTranslate gl3AmbientRightTranslate_apply upperUnipotent3 embedMat2 iotaGL LocalGL3 diagUnitGL2 unipotentBall3 mem_unipotentBall3_iff jacquetHaar3 jacquetTruncated3 jacquetLevel jacquetValue jacquetTruncated3_eq_jacquetValue bigCell3 mem_bigCell3_iff cellSectionOf cellSectionOf_apply_of_mem cellSectionOf_apply_of_notMem gl3Entry cornerEntry lowerMinor outerMinor gl3Det cellRatio cellValue antidiagonal3 antidiagonal3_coe eventually_valued_lt continuous_gl3Entry exists_forall_le_integrableOn_and_jacquetTruncated3_eq_of_cellSectionOf exists_forall_setIntegral_shell_psiLocal_mul_charExt_mul_cpow_eq_zero exists_integrable_levelUniform_dominant_coupledInner exists_norm_setIntegral_ball_truncChar_mul_charExt_mul_cpow_le integrable_coupledIntegrand setIntegral_tallBoxJacquet_div_norm_mul_charExt_mul_cpow_eq"
p2m_open "LanglandsTunnell.CubicInduction LanglandsTunnell"

variable (v : HeightOneSpectrum (𝓞 ℚ))

private theorem exists_integrable_dominant_coupledInner
    (ν : Fin 3 → ((v.adicCompletion ℚ)ˣ →* ℂˣ)) (hν : ∀ i, IsLocallyConstant (ν i))
    (Φ : (Fin 3 → v.adicCompletion ℚ) → ℂ) (hΦl : IsLocallyConstant Φ) (hΦc : HasCompactSupport Φ)
    (χ : (v.adicCompletion ℚ)ˣ →* ℂˣ) (hχ : IsLocallyConstant χ)
    (hu : ∀ i, ‖(((ν i * χ) (NumberField.AdelicLevel.uniformizerUnit ℚ v) : ℂˣ) : ℂ)‖ = 1)
    (s : ℂ) (hs : 0 < s.re) (hs' : s.re < 1) :
    (∃ D : v.adicCompletion ℚ × v.adicCompletion ℚ → ℝ,
      Integrable D ((mulMeasure (selfDualHaarAt ℚ v)).prod (mulMeasure (selfDualHaarAt ℚ v))) ∧
      ∀ (c : ℤ) (t : v.adicCompletion ℚ × v.adicCompletion ℚ),
        ‖(charExt (ν 2 * χ)⁻¹ t.1 * ((modulus t.1 : ℝ) : ℂ) ^ (1 - s)) *
            (charExt (ν 1 * χ) t.2 * ((modulus t.2 : ℝ) : ℂ) ^ s) *
            (∫ w : v.adicCompletion ℚ,
              Φ ![t.1, t.2, w] *
                (charExt (ν 0 * (ν 1)⁻¹) (t.2 - t.1 * w) * ((modulus (t.2 - t.1 * w) : ℝ) : ℂ)⁻¹) *
                truncChar v c (w / (t.2 - t.1 * w))
              ∂(selfDualHaarAt ℚ v))‖ ≤ D t) ∧
    (∃ E : ℕ → v.adicCompletion ℚ × v.adicCompletion ℚ → ℝ,
      (∀ m : ℕ, Integrable (E m) ((mulMeasure (selfDualHaarAt ℚ v)).prod (mulMeasure (selfDualHaarAt ℚ v)))) ∧
      (∀ (m : ℕ) (c : ℤ) (t : v.adicCompletion ℚ × v.adicCompletion ℚ),
        ‖(charExt (ν 2 * χ)⁻¹ t.1 * ((modulus t.1 : ℝ) : ℂ) ^ (1 - s)) *
            (charExt (ν 1 * χ) t.2 * ((modulus t.2 : ℝ) : ℂ) ^ s) *
            (∫ w in {w : v.adicCompletion ℚ | Valued.v (t.2 - t.1 * w) ≤ WithZero.exp (-(m : ℤ))},
              Φ ![t.1, t.2, w] *
                (charExt (ν 0 * (ν 1)⁻¹) (t.2 - t.1 * w) * ((modulus (t.2 - t.1 * w) : ℝ) : ℂ)⁻¹) *
                truncChar v c (w / (t.2 - t.1 * w))
              ∂(selfDualHaarAt ℚ v))‖ ≤ E m t) ∧
      Filter.Tendsto
        (fun m : ℕ =>
          ∫ t, E m t ∂((mulMeasure (selfDualHaarAt ℚ v)).prod (mulMeasure (selfDualHaarAt ℚ v))))
        Filter.atTop (nhds 0)) :=
  exists_integrable_levelUniform_dominant_coupledInner v ν hν Φ hΦl hΦc χ hχ hu s hs hs'

end LanglandsTunnell.CubicInduction
end

section
set_option autoImplicit false

open MeasureTheory
open IsDedekindDomain
open NumberField
p2m_open "LanglandsTunnell.TateLocal P2MW.S_LanglandsTunnell_CubicInduction_tendsto_localZeta_truncChar_mul_coupled_localZeta_of_jacquetValue.LanglandsTunnell.TateLocal"

namespace LanglandsTunnell
p2m_export "LanglandsTunnell" "TateLocal.localBorel TateLocal.borelSpace_localBorel"
namespace CubicInduction
p2m_export "LanglandsTunnell.CubicInduction" "gl3AmbientRightTranslate gl3AmbientRightTranslate_apply upperUnipotent3 embedMat2 iotaGL LocalGL3 diagUnitGL2 unipotentBall3 mem_unipotentBall3_iff jacquetHaar3 jacquetTruncated3 jacquetLevel jacquetValue jacquetTruncated3_eq_jacquetValue bigCell3 mem_bigCell3_iff cellSectionOf cellSectionOf_apply_of_mem cellSectionOf_apply_of_notMem gl3Entry cornerEntry lowerMinor outerMinor gl3Det cellRatio cellValue antidiagonal3 antidiagonal3_coe eventually_valued_lt continuous_gl3Entry exists_forall_le_integrableOn_and_jacquetTruncated3_eq_of_cellSectionOf exists_forall_setIntegral_shell_psiLocal_mul_charExt_mul_cpow_eq_zero exists_integrable_levelUniform_dominant_coupledInner exists_norm_setIntegral_ball_truncChar_mul_charExt_mul_cpow_le integrable_coupledIntegrand setIntegral_tallBoxJacquet_div_norm_mul_charExt_mul_cpow_eq"
p2m_open "LanglandsTunnell.CubicInduction LanglandsTunnell"

section GaussBalls

variable (v : HeightOneSpectrum (𝓞 ℚ))

attribute [local instance] LanglandsTunnell.TateLocal.localBorel

local notation "dmul" => mulMeasure (selfDualHaarAt ℚ v)
local notation "Kv" => IsDedekindDomain.HeightOneSpectrum.adicCompletion ℚ v

private def vball (R : ℤ) : Set Kv := {t : Kv | Valued.v t ≤ WithZero.exp R}

private def vshell (j : ℤ) : Set Kv := {t : Kv | Valued.v t = WithZero.exp j}

private theorem mem_vball (R : ℤ) (t : Kv) : t ∈ vball v R ↔ Valued.v t ≤ WithZero.exp R := Iff.rfl

private theorem mem_vshell (j : ℤ) (t : Kv) : t ∈ vshell v j ↔ Valued.v t = WithZero.exp j := Iff.rfl

private theorem measurableSet_vball (R : ℤ) : MeasurableSet (vball v R) := by
  haveI : BorelSpace Kv := borelSpace_localBorel ℚ v
  exact (isClosed_valued_le v R).measurableSet

private theorem vball_mono {R R' : ℤ} (h : R ≤ R') : vball v R ⊆ vball v R' :=
  fun _ ht => le_trans ht (WithZero.exp_le_exp.mpr h)

private theorem valued_eq_exp_succ_of_le_of_not_le {x : WithZero (Multiplicative ℤ)} {R : ℤ}
    (h1 : x ≤ WithZero.exp (R + 1)) (h2 : ¬ x ≤ WithZero.exp R) : x = WithZero.exp (R + 1) := by
  rcases h1.lt_or_eq with h | h
  · rw [WithZero.exp_add, WithZero.lt_mul_exp_iff_le WithZero.exp_ne_zero] at h
    exact absurd h h2
  · exact h

private theorem vball_succ_eq (R : ℤ) : vball v (R + 1) = vball v R ∪ vshell v (R + 1) := by
  ext t
  simp only [Set.mem_union, mem_vball, mem_vshell]
  constructor
  · intro h
    by_cases h' : Valued.v t ≤ WithZero.exp R
    · exact Or.inl h'
    · exact Or.inr (valued_eq_exp_succ_of_le_of_not_le h h')
  · rintro (h | h)
    · exact h.trans (WithZero.exp_le_exp.mpr (by omega))
    · exact h.le

private theorem disjoint_vball_vshell_succ (R : ℤ) : Disjoint (vball v R) (vshell v (R + 1)) := by
  rw [Set.disjoint_left]
  intro t h1 h2
  rw [mem_vball] at h1
  rw [mem_vshell] at h2
  rw [h2, WithZero.exp_le_exp] at h1
  omega

private theorem measurableSet_vshell (j : ℤ) : MeasurableSet (vshell v j) := by
  have h : vshell v j = vball v j \ vball v (j - 1) := by
    ext t
    simp only [Set.mem_diff, mem_vball, mem_vshell]
    constructor
    · intro h
      rw [h, WithZero.exp_le_exp, WithZero.exp_le_exp]
      omega
    · rintro ⟨h1, h2⟩
      have := valued_eq_exp_succ_of_le_of_not_le (R := j - 1) (by rwa [sub_add_cancel]) h2
      rwa [sub_add_cancel] at this
  rw [h]
  exact (measurableSet_vball v j).diff (measurableSet_vball v (j - 1))

private theorem iUnion_vball_natCast : (⋃ n : ℕ, vball v (n : ℤ)) = Set.univ := by
  refine Set.eq_univ_of_forall fun t => Set.mem_iUnion.mpr ?_
  refine ⟨(WithZero.log (Valued.v t)).toNat, ?_⟩
  rw [mem_vball]
  exact WithZero.le_exp_log.trans (WithZero.exp_le_exp.mpr (Int.self_le_toNat _))

private def vannulus (N : ℕ) : Set Kv :=
  {b : Kv | WithZero.exp (-(N : ℤ)) ≤ Valued.v b ∧ Valued.v b ≤ WithZero.exp (N : ℤ)}

private theorem mem_vannulus (N : ℕ) (b : Kv) :
    b ∈ vannulus v N ↔ WithZero.exp (-(N : ℤ)) ≤ Valued.v b ∧ Valued.v b ≤ WithZero.exp (N : ℤ) := Iff.rfl

private theorem indicator_vannulus_torusPoint (N : ℕ) {r u : Kv} {α β : ℤ} (hr : Valued.v r = WithZero.exp α)
    (hu : Valued.v u = WithZero.exp β) (t : Kv) :
    (vannulus v N).indicator (fun _ => (1 : ℂ)) (r * u⁻¹ * t) =
      (vball v (β - α + N)).indicator (fun _ => (1 : ℂ)) t -
        (vball v (β - α - N - 1)).indicator (fun _ => (1 : ℂ)) t := by
  by_cases ht : t = 0
  · subst ht
    have h1 : (0 : Kv) ∈ vball v (β - α + N) := by simp [mem_vball]
    have h2 : (0 : Kv) ∈ vball v (β - α - N - 1) := by simp [mem_vball]
    have h3 : r * u⁻¹ * 0 ∉ vannulus v N := by simp [mem_vannulus, WithZero.exp_ne_zero]
    rw [Set.indicator_of_mem h1, Set.indicator_of_mem h2, Set.indicator_of_notMem h3, sub_self]
  · obtain ⟨k, hk⟩ : ∃ k : ℤ, Valued.v t = WithZero.exp k :=
      ⟨WithZero.log (Valued.v t), (WithZero.exp_log ((Valuation.ne_zero_iff _).mpr ht)).symm⟩
    have hb : Valued.v (r * u⁻¹ * t) = WithZero.exp (α - β + k) := by
      rw [map_mul, map_mul, map_inv₀, hr, hu, hk, WithZero.exp_add, WithZero.exp_sub, div_eq_mul_inv]
    have hiff : r * u⁻¹ * t ∈ vannulus v N ↔ t ∈ vball v (β - α + N) ∧ t ∉ vball v (β - α - N - 1) := by
      simp only [mem_vannulus, mem_vball, hb, hk, WithZero.exp_le_exp]
      omega
    by_cases h2 : t ∈ vball v (β - α - N - 1)
    · have h1 : t ∈ vball v (β - α + N) := vball_mono v (by omega) h2
      rw [Set.indicator_of_mem h1, Set.indicator_of_mem h2, Set.indicator_of_notMem (fun h => (hiff.mp h).2 h2),
        sub_self]
    · by_cases h1 : t ∈ vball v (β - α + N)
      · rw [Set.indicator_of_mem h1, Set.indicator_of_notMem h2, Set.indicator_of_mem (hiff.mpr ⟨h1, h2⟩), sub_zero]
      · rw [Set.indicator_of_notMem h1, Set.indicator_of_notMem h2,
          Set.indicator_of_notMem (fun h => h1 (hiff.mp h).1), sub_zero]

private theorem indicator_one_mul (s : Set Kv) (g : Kv → ℂ) (t : Kv) :
    s.indicator (fun _ => (1 : ℂ)) t * g t = s.indicator g t := by
  by_cases ht : t ∈ s
  · rw [Set.indicator_of_mem ht, Set.indicator_of_mem ht, one_mul]
  · rw [Set.indicator_of_notMem ht, Set.indicator_of_notMem ht, zero_mul]

private theorem truncChar_neg_of_le {c j : ℤ} (hj : j ≤ c) {t : Kv} (ht : t ∈ vshell v j) :
    truncChar v c (-t) = (NumberField.StandardAddChar.psiLocal ℚ v (-t) : ℂ) := by
  rw [mem_vshell] at ht
  have h : Valued.v (-t) ≤ WithZero.exp c := by
    rw [Valuation.map_neg, ht]
    exact WithZero.exp_le_exp.mpr hj
  unfold truncChar
  rw [if_pos h]

private theorem truncChar_neg_of_lt {c j : ℤ} (hj : c < j) {t : Kv} (ht : t ∈ vshell v j) :
    truncChar v c (-t) = 0 := by
  rw [mem_vshell] at ht
  have h : ¬ Valued.v (-t) ≤ WithZero.exp c := by
    rw [Valuation.map_neg, ht, WithZero.exp_le_exp]
    omega
  unfold truncChar
  rw [if_neg h]

private noncomputable def gaussTrunc (η : Kvˣ →* ℂˣ) (z : ℂ) (c : ℤ) (t : Kv) : ℂ :=
  truncChar v c (-t) * charExt η t * ((modulus t : ℝ) : ℂ) ^ z

private theorem setIntegral_vshell_truncChar_eq_zero (η : Kvˣ →* ℂˣ) (z : ℂ) {c₁ : ℕ}
    (hΓ : ∀ j : ℤ, (c₁ : ℤ) < j → ∫ t in vshell v j,
      (NumberField.StandardAddChar.psiLocal ℚ v (-t) : ℂ) * charExt η t * ((modulus t : ℝ) : ℂ) ^ z ∂dmul = 0)
    (c : ℤ) {j : ℤ} (hj : (c₁ : ℤ) < j) :
    ∫ t in vshell v j, gaussTrunc v η z c t ∂dmul = 0 := by
  by_cases hjc : j ≤ c
  · refine Eq.trans (setIntegral_congr_fun (measurableSet_vshell v j) fun t ht => ?_) (hΓ j hj)
    simp only [gaussTrunc, truncChar_neg_of_le v hjc ht]
  · have h0 : Set.EqOn (gaussTrunc v η z c) (fun _ => 0) (vshell v j) :=
      fun t ht => by simp only [gaussTrunc, truncChar_neg_of_lt v (not_le.mp hjc) ht, zero_mul]
    rw [setIntegral_congr_fun (measurableSet_vshell v j) h0]
    simp

private theorem setIntegral_vball_truncChar_eq_of_le (η : Kvˣ →* ℂˣ) (z : ℂ) {c₁ : ℕ}
    (hΓ : ∀ j : ℤ, (c₁ : ℤ) < j → ∫ t in vshell v j,
      (NumberField.StandardAddChar.psiLocal ℚ v (-t) : ℂ) * charExt η t * ((modulus t : ℝ) : ℂ) ^ z ∂dmul = 0)
    (c : ℤ) (hI : Integrable (gaussTrunc v η z c) dmul) {R : ℤ} (hR : (c₁ : ℤ) ≤ R) :
    ∫ t in vball v R, gaussTrunc v η z c t ∂dmul = ∫ t in vball v c₁, gaussTrunc v η z c t ∂dmul := by
  obtain ⟨n, rfl⟩ : ∃ n : ℕ, R = c₁ + n := ⟨(R - c₁).toNat, by rw [Int.toNat_of_nonneg (by omega)]; ring⟩
  clear hR
  induction n with
  | zero => simp
  | succ n ih =>
      rw [show ((c₁ : ℤ) + ((n + 1 : ℕ) : ℤ)) = ((c₁ : ℤ) + n) + 1 by push_cast; ring, vball_succ_eq,
        setIntegral_union (disjoint_vball_vshell_succ v _) (measurableSet_vshell v _) hI.integrableOn hI.integrableOn,
        setIntegral_vshell_truncChar_eq_zero v η z hΓ c (by push_cast; omega), add_zero, ih]

private theorem integral_truncChar_eq_setIntegral_vball (η : Kvˣ →* ℂˣ) (z : ℂ) {c₁ : ℕ}
    (hΓ : ∀ j : ℤ, (c₁ : ℤ) < j → ∫ t in vshell v j,
      (NumberField.StandardAddChar.psiLocal ℚ v (-t) : ℂ) * charExt η t * ((modulus t : ℝ) : ℂ) ^ z ∂dmul = 0)
    (c : ℤ) (hI : Integrable (gaussTrunc v η z c) dmul) :
    ∫ t, gaussTrunc v η z c t ∂dmul = ∫ t in vball v c₁, gaussTrunc v η z c t ∂dmul := by
  have hmono : Monotone fun n : ℕ => vball v (n : ℤ) := fun a b hab => vball_mono v (by exact_mod_cast hab)
  have hlim := tendsto_setIntegral_of_monotone (μ := dmul) (f := fun t => gaussTrunc v η z c t)
    (fun n : ℕ => measurableSet_vball v (n : ℤ)) hmono hI.integrableOn
  rw [iUnion_vball_natCast, Measure.restrict_univ] at hlim
  have hconst : (fun n : ℕ => ∫ t in vball v (n : ℤ), gaussTrunc v η z c t ∂dmul) =ᶠ[Filter.atTop]
      fun _ => ∫ t in vball v c₁, gaussTrunc v η z c t ∂dmul :=
    Filter.eventually_atTop.mpr ⟨c₁, fun n hn =>
      setIntegral_vball_truncChar_eq_of_le v η z hΓ c hI (by exact_mod_cast hn)⟩
  exact tendsto_nhds_unique (hlim.congr' hconst) tendsto_const_nhds

private theorem integral_indicator_vannulus_mul_truncChar (η : Kvˣ →* ℂˣ) (z : ℂ) (N : ℕ) {r u : Kv} {α β : ℤ}
    (hr : Valued.v r = WithZero.exp α) (hu : Valued.v u = WithZero.exp β) (c : ℤ)
    (hI : Integrable (gaussTrunc v η z c) dmul) :
    ∫ t, (vannulus v N).indicator (fun _ => (1 : ℂ)) (r * u⁻¹ * t) * gaussTrunc v η z c t ∂dmul =
      ∫ t in vball v (β - α + N), gaussTrunc v η z c t ∂dmul -
        ∫ t in vball v (β - α - N - 1), gaussTrunc v η z c t ∂dmul := by
  simp_rw [indicator_vannulus_torusPoint v N hr hu, sub_mul, indicator_one_mul]
  rw [integral_sub (hI.indicator (measurableSet_vball v _)) (hI.indicator (measurableSet_vball v _)),
    integral_indicator (measurableSet_vball v _), integral_indicator (measurableSet_vball v _)]

private theorem zpow_min_rpow_le {c₁' : ℕ} (r : ℤ) {σ : ℝ} (hσ : 0 ≤ σ) :
    (((Ideal.absNorm v.asIdeal : ℝ) ^ min r (c₁' : ℤ)) ^ σ : ℝ) ≤ ((Ideal.absNorm v.asIdeal : ℝ) ^ (c₁' : ℤ)) ^ σ :=
  Real.rpow_le_rpow (zpow_nonneg (zero_le_one.trans (one_lt_absNorm_real v).le) _)
    (zpow_le_zpow_right₀ (one_lt_absNorm_real v).le (min_le_right _ _)) hσ

private theorem norm_integral_sub_integral_indicator_vannulus_le (η : Kvˣ →* ℂˣ) (z : ℂ) {c₁ : ℕ}
    (hΓ : ∀ j : ℤ, (c₁ : ℤ) < j → ∫ t in vshell v j,
      (NumberField.StandardAddChar.psiLocal ℚ v (-t) : ℂ) * charExt η t * ((modulus t : ℝ) : ℂ) ^ z ∂dmul = 0)
    {c₁' : ℕ} {M : ℝ} (hM0 : 0 ≤ M)
    (hM : ∀ c r : ℤ, ‖∫ t in vball v r, gaussTrunc v η z c t ∂dmul‖ ≤
      M * ((Ideal.absNorm v.asIdeal : ℝ) ^ min r (c₁' : ℤ)) ^ z.re)
    (hz : 0 ≤ z.re) (c : ℤ) (hI : Integrable (gaussTrunc v η z c) dmul) (N : ℕ) {r u : Kv} {α β : ℤ}
    (hr : Valued.v r = WithZero.exp α) (hu : Valued.v u = WithZero.exp β) :
    ‖∫ t, gaussTrunc v η z c t ∂dmul -
        ∫ t, (vannulus v N).indicator (fun _ => (1 : ℂ)) (r * u⁻¹ * t) * gaussTrunc v η z c t ∂dmul‖ ≤
      (if β - α + N < c₁ then 2 * M * ((Ideal.absNorm v.asIdeal : ℝ) ^ (c₁' : ℤ)) ^ z.re else 0) +
        M * ((Ideal.absNorm v.asIdeal : ℝ) ^ min (β - α - N - 1) (c₁' : ℤ)) ^ z.re := by
  rw [integral_indicator_vannulus_mul_truncChar v η z N hr hu c hI,
    integral_truncChar_eq_setIntegral_vball v η z hΓ c hI, sub_sub_eq_add_sub, ← sub_add_eq_add_sub]
  refine (norm_add_le _ _).trans (add_le_add ?_ (hM c _))
  split_ifs with hlt
  · refine (norm_sub_le _ _).trans ?_
    have h1 := (hM c c₁).trans (mul_le_mul_of_nonneg_left (zpow_min_rpow_le v (c₁ : ℤ) hz) hM0)
    have h2 := (hM c (β - α + N)).trans (mul_le_mul_of_nonneg_left (zpow_min_rpow_le v (β - α + N) hz) hM0)
    linarith
  · rw [setIntegral_vball_truncChar_eq_of_le v η z hΓ c hI (not_lt.mp hlt), sub_self, norm_zero]

end GaussBalls

end LanglandsTunnell.CubicInduction
end

section
set_option autoImplicit false

open MeasureTheory
open IsDedekindDomain
open NumberField
p2m_open "LanglandsTunnell.TateLocal P2MW.S_LanglandsTunnell_CubicInduction_tendsto_localZeta_truncChar_mul_coupled_localZeta_of_jacquetValue.LanglandsTunnell.TateLocal"

namespace LanglandsTunnell
p2m_export "LanglandsTunnell" "TateLocal.localBorel TateLocal.borelSpace_localBorel"
namespace CubicInduction
p2m_export "LanglandsTunnell.CubicInduction" "gl3AmbientRightTranslate gl3AmbientRightTranslate_apply upperUnipotent3 embedMat2 iotaGL LocalGL3 diagUnitGL2 unipotentBall3 mem_unipotentBall3_iff jacquetHaar3 jacquetTruncated3 jacquetLevel jacquetValue jacquetTruncated3_eq_jacquetValue bigCell3 mem_bigCell3_iff cellSectionOf cellSectionOf_apply_of_mem cellSectionOf_apply_of_notMem gl3Entry cornerEntry lowerMinor outerMinor gl3Det cellRatio cellValue antidiagonal3 antidiagonal3_coe eventually_valued_lt continuous_gl3Entry exists_forall_le_integrableOn_and_jacquetTruncated3_eq_of_cellSectionOf exists_forall_setIntegral_shell_psiLocal_mul_charExt_mul_cpow_eq_zero exists_integrable_levelUniform_dominant_coupledInner exists_norm_setIntegral_ball_truncChar_mul_charExt_mul_cpow_le integrable_coupledIntegrand setIntegral_tallBoxJacquet_div_norm_mul_charExt_mul_cpow_eq"
p2m_open "LanglandsTunnell.CubicInduction LanglandsTunnell"

section TailDevice

variable (v : HeightOneSpectrum (𝓞 ℚ))

attribute [local instance] LanglandsTunnell.TateLocal.localBorel

local notation "dmul" => mulMeasure (selfDualHaarAt ℚ v)
local notation "Kv" => IsDedekindDomain.HeightOneSpectrum.adicCompletion ℚ v

private theorem norm_eq_zpow_of_valued_eq {x : Kv} {n : ℤ} (hx : Valued.v x = WithZero.exp n) :
    ‖x‖ = (Ideal.absNorm v.asIdeal : ℝ) ^ n := by
  have hexp : WithZeroMulInt.toNNReal (NumberField.HeightOneSpectrum.absNorm_ne_zero v) (WithZero.exp n) =
      (Ideal.absNorm v.asIdeal : NNReal) ^ n := by
    rw [WithZeroMulInt.toNNReal_neg_apply _ WithZero.exp_ne_zero]
    rfl
  rw [NumberField.FinitePlace.norm_def v x, hx, hexp, NNReal.coe_zpow, NNReal.coe_natCast]

variable (c₁ c₁' : ℕ) (M σ : ℝ)

private noncomputable def tailBound (N : ℕ) (p : Kv × Kv) : ℝ :=
  (if ‖p.1‖ / ‖p.2‖ * (Ideal.absNorm v.asIdeal : ℝ) ^ (N : ℤ) < (Ideal.absNorm v.asIdeal : ℝ) ^ (c₁ : ℤ) then
      2 * M * ((Ideal.absNorm v.asIdeal : ℝ) ^ (c₁' : ℤ)) ^ σ else 0) +
    M * (min (‖p.1‖ / ‖p.2‖ * (Ideal.absNorm v.asIdeal : ℝ) ^ (-((N : ℤ) + 1)))
      ((Ideal.absNorm v.asIdeal : ℝ) ^ (c₁' : ℤ))) ^ σ

private theorem tailBound_eq {r u : Kv} {α β : ℤ} (hr : Valued.v r = WithZero.exp α)
    (hu : Valued.v u = WithZero.exp β) (N : ℕ) :
    tailBound v c₁ c₁' M σ N (u, r) =
      (if β - α + N < c₁ then 2 * M * ((Ideal.absNorm v.asIdeal : ℝ) ^ (c₁' : ℤ)) ^ σ else 0) +
        M * ((Ideal.absNorm v.asIdeal : ℝ) ^ min (β - α - N - 1) (c₁' : ℤ)) ^ σ := by
  have hq1 : (1 : ℝ) < (Ideal.absNorm v.asIdeal : ℝ) := one_lt_absNorm_real v
  have hq0 : (0 : ℝ) < (Ideal.absNorm v.asIdeal : ℝ) := one_pos.trans hq1
  have hρ : ‖u‖ / ‖r‖ = (Ideal.absNorm v.asIdeal : ℝ) ^ (β - α) := by
    rw [norm_eq_zpow_of_valued_eq v hu, norm_eq_zpow_of_valued_eq v hr, ← zpow_sub₀ hq0.ne']
  have hcond : ‖u‖ / ‖r‖ * (Ideal.absNorm v.asIdeal : ℝ) ^ (N : ℤ) < (Ideal.absNorm v.asIdeal : ℝ) ^ (c₁ : ℤ) ↔
      β - α + N < c₁ := by
    rw [hρ, ← zpow_add₀ hq0.ne', zpow_lt_zpow_iff_right₀ hq1]
  have hmin : min (‖u‖ / ‖r‖ * (Ideal.absNorm v.asIdeal : ℝ) ^ (-((N : ℤ) + 1)))
      ((Ideal.absNorm v.asIdeal : ℝ) ^ (c₁' : ℤ)) = (Ideal.absNorm v.asIdeal : ℝ) ^ min (β - α - N - 1) (c₁' : ℤ) := by
    rw [hρ, ← zpow_add₀ hq0.ne', show β - α + -((N : ℤ) + 1) = β - α - N - 1 by ring]
    exact ((zpow_right_strictMono₀ hq1).monotone.map_min).symm
  unfold tailBound
  rw [hmin]
  by_cases h : β - α + N < c₁
  · rw [if_pos h, if_pos (hcond.mpr h)]
  · rw [if_neg h, if_neg (fun h' => h (hcond.mp h'))]

private theorem tailBound_nonneg (hM : 0 ≤ M) (N : ℕ) (p : Kv × Kv) : 0 ≤ tailBound v c₁ c₁' M σ N p := by
  have hq0 : (0 : ℝ) < (Ideal.absNorm v.asIdeal : ℝ) := one_pos.trans (one_lt_absNorm_real v)
  have hX : 0 ≤ ((Ideal.absNorm v.asIdeal : ℝ) ^ (c₁' : ℤ)) ^ σ := Real.rpow_nonneg (zpow_nonneg hq0.le _) σ
  refine add_nonneg ?_ (mul_nonneg hM (Real.rpow_nonneg (le_min (by positivity) (by positivity)) σ))
  split_ifs
  · exact mul_nonneg (mul_nonneg zero_le_two hM) hX
  · exact le_rfl

private theorem tailBound_le (hM : 0 ≤ M) (hσ : 0 ≤ σ) (N : ℕ) (p : Kv × Kv) :
    tailBound v c₁ c₁' M σ N p ≤ 3 * M * ((Ideal.absNorm v.asIdeal : ℝ) ^ (c₁' : ℤ)) ^ σ := by
  have hq0 : (0 : ℝ) < (Ideal.absNorm v.asIdeal : ℝ) := one_pos.trans (one_lt_absNorm_real v)
  have hX : 0 ≤ ((Ideal.absNorm v.asIdeal : ℝ) ^ (c₁' : ℤ)) ^ σ := Real.rpow_nonneg (zpow_nonneg hq0.le _) σ
  have h1 : (if ‖p.1‖ / ‖p.2‖ * (Ideal.absNorm v.asIdeal : ℝ) ^ (N : ℤ) < (Ideal.absNorm v.asIdeal : ℝ) ^ (c₁ : ℤ)
      then 2 * M * ((Ideal.absNorm v.asIdeal : ℝ) ^ (c₁' : ℤ)) ^ σ else 0) ≤
      2 * M * ((Ideal.absNorm v.asIdeal : ℝ) ^ (c₁' : ℤ)) ^ σ := by
    split_ifs
    · exact le_rfl
    · exact mul_nonneg (mul_nonneg zero_le_two hM) hX
  have h2 : M * (min (‖p.1‖ / ‖p.2‖ * (Ideal.absNorm v.asIdeal : ℝ) ^ (-((N : ℤ) + 1)))
      ((Ideal.absNorm v.asIdeal : ℝ) ^ (c₁' : ℤ))) ^ σ ≤ M * ((Ideal.absNorm v.asIdeal : ℝ) ^ (c₁' : ℤ)) ^ σ :=
    mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow (le_min (by positivity) (by positivity)) (min_le_right _ _) hσ) hM
  unfold tailBound
  linarith

private theorem measurable_tailBound (N : ℕ) : Measurable (tailBound v c₁ c₁' M σ N) := by
  haveI : BorelSpace Kv := borelSpace_localBorel ℚ v
  have hρ : Measurable fun p : Kv × Kv => ‖p.1‖ / ‖p.2‖ := measurable_fst.norm.div measurable_snd.norm
  unfold tailBound
  refine Measurable.add ?_ ?_
  · refine Measurable.ite ?_ measurable_const measurable_const
    exact measurableSet_lt (hρ.mul_const _) measurable_const
  · exact (((hρ.mul_const _).min measurable_const).pow_const σ).const_mul M

private theorem tendsto_tailBound (hM : 0 ≤ M) (hσ : 0 < σ) {p : Kv × Kv} (hp1 : p.1 ≠ 0) (hp2 : p.2 ≠ 0) :
    Filter.Tendsto (fun N : ℕ => tailBound v c₁ c₁' M σ N p) Filter.atTop (nhds 0) := by
  have hq1 : (1 : ℝ) < (Ideal.absNorm v.asIdeal : ℝ) := one_lt_absNorm_real v
  have hq0 : (0 : ℝ) < (Ideal.absNorm v.asIdeal : ℝ) := one_pos.trans hq1
  have hρ : 0 < ‖p.1‖ / ‖p.2‖ := div_pos (norm_pos_iff.mpr hp1) (norm_pos_iff.mpr hp2)

  have hev : ∀ᶠ N : ℕ in Filter.atTop,
      ¬ (‖p.1‖ / ‖p.2‖ * (Ideal.absNorm v.asIdeal : ℝ) ^ (N : ℤ) < (Ideal.absNorm v.asIdeal : ℝ) ^ (c₁ : ℤ)) := by
    filter_upwards [(tendsto_pow_atTop_atTop_of_one_lt hq1).eventually_ge_atTop
      ((Ideal.absNorm v.asIdeal : ℝ) ^ (c₁ : ℤ) / (‖p.1‖ / ‖p.2‖))] with N hN
    rw [not_lt, zpow_natCast _ N, ← div_le_iff₀' hρ]
    exact hN
  have h1 : Filter.Tendsto (fun N : ℕ =>
      if ‖p.1‖ / ‖p.2‖ * (Ideal.absNorm v.asIdeal : ℝ) ^ (N : ℤ) < (Ideal.absNorm v.asIdeal : ℝ) ^ (c₁ : ℤ) then
        2 * M * ((Ideal.absNorm v.asIdeal : ℝ) ^ (c₁' : ℤ)) ^ σ else 0) Filter.atTop (nhds 0) :=
    tendsto_const_nhds.congr' (hev.mono fun N hN => (if_neg hN).symm)

  have hre : ∀ N : ℕ, ‖p.1‖ / ‖p.2‖ * (Ideal.absNorm v.asIdeal : ℝ) ^ (-((N : ℤ) + 1)) =
      ‖p.1‖ / ‖p.2‖ * ((Ideal.absNorm v.asIdeal : ℝ)⁻¹) ^ (N + 1) := fun N => by
    rw [inv_pow, ← zpow_natCast, ← zpow_neg]
    norm_cast
  have hgeo : Filter.Tendsto (fun N : ℕ => ‖p.1‖ / ‖p.2‖ * (Ideal.absNorm v.asIdeal : ℝ) ^ (-((N : ℤ) + 1)))
      Filter.atTop (nhds 0) := by
    have h := (tendsto_pow_atTop_nhds_zero_of_lt_one (inv_nonneg.mpr hq0.le)
      (inv_lt_one_of_one_lt₀ hq1)).const_mul (‖p.1‖ / ‖p.2‖)
    rw [mul_zero] at h
    simp_rw [hre]
    exact h.comp (Filter.tendsto_add_atTop_nat 1)
  have h2 : Filter.Tendsto (fun N : ℕ => M * (min (‖p.1‖ / ‖p.2‖ * (Ideal.absNorm v.asIdeal : ℝ) ^ (-((N : ℤ) + 1)))
      ((Ideal.absNorm v.asIdeal : ℝ) ^ (c₁' : ℤ))) ^ σ) Filter.atTop (nhds 0) := by
    have hlim : Filter.Tendsto
        (fun N : ℕ => M * (‖p.1‖ / ‖p.2‖ * (Ideal.absNorm v.asIdeal : ℝ) ^ (-((N : ℤ) + 1))) ^ σ)
        Filter.atTop (nhds 0) := by
      have h := (hgeo.rpow_const_nhds_zero hσ).const_mul M
      rwa [mul_zero] at h
    refine squeeze_zero (fun N => mul_nonneg hM (Real.rpow_nonneg (le_min ?_ ?_) σ)) (fun N => ?_) hlim
    · positivity
    · positivity
    · exact mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow (le_min (by positivity) (by positivity)) (min_le_left _ _) hσ.le) hM
  have h := h1.add h2
  rw [add_zero] at h
  exact h

private theorem tendsto_integral_tailBound_mul (hM : 0 ≤ M) (hσ : 0 < σ) {D : Kv × Kv → ℝ}
    (hD : Integrable D (Measure.prod dmul dmul)) :
    Filter.Tendsto (fun N : ℕ => ∫ p, tailBound v c₁ c₁' M σ N p * D p ∂(Measure.prod dmul dmul)) Filter.atTop
      (nhds 0) := by
  haveI : SFinite dmul := sFinite_mulMeasure_selfDualHaarAt ℚ v
  have hmeas : ∀ N : ℕ, AEStronglyMeasurable (fun p => tailBound v c₁ c₁' M σ N p * D p) (Measure.prod dmul dmul) :=
    fun N => (measurable_tailBound v c₁ c₁' M σ N).aestronglyMeasurable.mul hD.aestronglyMeasurable
  have hbound : ∀ N : ℕ, ∀ᵐ p ∂(Measure.prod dmul dmul),
      ‖tailBound v c₁ c₁' M σ N p * D p‖ ≤ 3 * M * ((Ideal.absNorm v.asIdeal : ℝ) ^ (c₁' : ℤ)) ^ σ * ‖D p‖ :=
    fun N => Filter.Eventually.of_forall fun p => by
      rw [norm_mul, Real.norm_of_nonneg (tailBound_nonneg v c₁ c₁' M σ hM N p)]
      exact mul_le_mul_of_nonneg_right (tailBound_le v c₁ c₁' M σ hM hσ.le N p) (norm_nonneg _)
  have hlim : ∀ᵐ p ∂(Measure.prod dmul dmul),
      Filter.Tendsto (fun N : ℕ => tailBound v c₁ c₁' M σ N p * D p) Filter.atTop (nhds 0) := by
    filter_upwards [ae_fst_ne_zero_and_snd_ne_zero v] with p hp
    have h := (tendsto_tailBound v c₁ c₁' M σ hM hσ hp.1 hp.2).mul_const (D p)
    rwa [zero_mul] at h
  have h := tendsto_integral_of_dominated_convergence
    (fun p => 3 * M * ((Ideal.absNorm v.asIdeal : ℝ) ^ (c₁' : ℤ)) ^ σ * ‖D p‖) hmeas (hD.norm.const_mul _) hbound hlim
  simpa only [integral_zero] using h

private theorem integrable_tailBound_mul (hM : 0 ≤ M) (hσ : 0 ≤ σ) (N : ℕ) {D : Kv × Kv → ℝ}
    (hD : Integrable D (Measure.prod dmul dmul)) :
    Integrable (fun p => tailBound v c₁ c₁' M σ N p * D p) (Measure.prod dmul dmul) :=
  hD.bdd_mul (measurable_tailBound v c₁ c₁' M σ N).aestronglyMeasurable
    (Filter.Eventually.of_forall fun p => by
      rw [Real.norm_of_nonneg (tailBound_nonneg v c₁ c₁' M σ hM N p)]
      exact tailBound_le v c₁ c₁' M σ hM hσ N p)

private theorem norm_integral_gaussTail_mul_le (η : Kvˣ →* ℂˣ) (z : ℂ) {c₁₀ : ℕ}
    (hΓ : ∀ j : ℤ, (c₁₀ : ℤ) < j → ∫ t in vshell v j,
      (NumberField.StandardAddChar.psiLocal ℚ v (-t) : ℂ) * charExt η t * ((modulus t : ℝ) : ℂ) ^ z ∂dmul = 0)
    (hM0 : 0 ≤ M)
    (hM : ∀ c r : ℤ, ‖∫ t in vball v r, gaussTrunc v η z c t ∂dmul‖ ≤
      M * ((Ideal.absNorm v.asIdeal : ℝ) ^ min r (c₁' : ℤ)) ^ z.re)
    (hz : 0 ≤ z.re) (c : ℤ) (hI : Integrable (gaussTrunc v η z c) dmul) (N : ℕ)
    {K : Kv × Kv → ℂ} {D : Kv × Kv → ℝ} (hdom : ∀ p, ‖K p‖ ≤ D p) (hD : Integrable D (Measure.prod dmul dmul)) :
    ‖∫ p : Kv × Kv, (∫ t, gaussTrunc v η z c t ∂dmul -
        ∫ t, (vannulus v N).indicator (fun _ => (1 : ℂ)) (p.2 * (p.1)⁻¹ * t) * gaussTrunc v η z c t ∂dmul) * K p
      ∂(Measure.prod dmul dmul)‖ ≤
      ∫ p, tailBound v c₁₀ c₁' M z.re N p * D p ∂(Measure.prod dmul dmul) := by
  haveI : SFinite dmul := sFinite_mulMeasure_selfDualHaarAt ℚ v
  refine norm_integral_le_of_norm_le (integrable_tailBound_mul v c₁₀ c₁' M z.re hM0 hz N hD) ?_
  filter_upwards [ae_fst_ne_zero_and_snd_ne_zero v] with p hp
  have hu : Valued.v p.1 = WithZero.exp (WithZero.log (Valued.v p.1)) :=
    (WithZero.exp_log ((Valuation.ne_zero_iff _).mpr hp.1)).symm
  have hr : Valued.v p.2 = WithZero.exp (WithZero.log (Valued.v p.2)) :=
    (WithZero.exp_log ((Valuation.ne_zero_iff _).mpr hp.2)).symm
  rw [norm_mul]
  refine mul_le_mul ?_ (hdom p) (norm_nonneg _) (tailBound_nonneg v c₁₀ c₁' M z.re hM0 N p)
  have h := norm_integral_sub_integral_indicator_vannulus_le v η z hΓ hM0 hM hz c hI N hr hu
  rw [← tailBound_eq v c₁₀ c₁' M z.re hr hu N] at h
  exact h

end TailDevice

end LanglandsTunnell.CubicInduction
end

section
set_option autoImplicit false

open MeasureTheory
open IsDedekindDomain
open NumberField
p2m_open "LanglandsTunnell.TateLocal P2MW.S_LanglandsTunnell_CubicInduction_tendsto_localZeta_truncChar_mul_coupled_localZeta_of_jacquetValue.LanglandsTunnell.TateLocal"

namespace LanglandsTunnell
p2m_export "LanglandsTunnell" "TateLocal.localBorel TateLocal.borelSpace_localBorel"
namespace CubicInduction
p2m_export "LanglandsTunnell.CubicInduction" "gl3AmbientRightTranslate gl3AmbientRightTranslate_apply upperUnipotent3 embedMat2 iotaGL LocalGL3 diagUnitGL2 unipotentBall3 mem_unipotentBall3_iff jacquetHaar3 jacquetTruncated3 jacquetLevel jacquetValue jacquetTruncated3_eq_jacquetValue bigCell3 mem_bigCell3_iff cellSectionOf cellSectionOf_apply_of_mem cellSectionOf_apply_of_notMem gl3Entry cornerEntry lowerMinor outerMinor gl3Det cellRatio cellValue antidiagonal3 antidiagonal3_coe eventually_valued_lt continuous_gl3Entry exists_forall_le_integrableOn_and_jacquetTruncated3_eq_of_cellSectionOf exists_forall_setIntegral_shell_psiLocal_mul_charExt_mul_cpow_eq_zero exists_integrable_levelUniform_dominant_coupledInner exists_norm_setIntegral_ball_truncChar_mul_charExt_mul_cpow_le integrable_coupledIntegrand setIntegral_tallBoxJacquet_div_norm_mul_charExt_mul_cpow_eq"
p2m_open "LanglandsTunnell.CubicInduction LanglandsTunnell"

section Assembly

variable (v : HeightOneSpectrum (𝓞 ℚ))

attribute [local instance] LanglandsTunnell.TateLocal.localBorel

local notation "dmul" => mulMeasure (selfDualHaarAt ℚ v)
local notation "Kv" => IsDedekindDomain.HeightOneSpectrum.adicCompletion ℚ v
local notation "Kv3" => Prod (Prod (IsDedekindDomain.HeightOneSpectrum.adicCompletion ℚ v)
  (IsDedekindDomain.HeightOneSpectrum.adicCompletion ℚ v)) (IsDedekindDomain.HeightOneSpectrum.adicCompletion ℚ v)

private theorem ne_zero_of_mem_vannulus {N : ℕ} {b : Kv} (hb : b ∈ vannulus v N) : b ≠ 0 := by
  rintro rfl
  rw [mem_vannulus, map_zero] at hb
  exact WithZero.exp_ne_zero (le_zero_iff.mp hb.1)

private theorem mem_vannulus_iff_of_valued_eq {N : ℕ} {b : Kv} {k : ℤ} (hk : Valued.v b = WithZero.exp k) :
    b ∈ vannulus v N ↔ -(N : ℤ) ≤ k ∧ k ≤ N := by
  rw [mem_vannulus, hk, WithZero.exp_le_exp, WithZero.exp_le_exp]

private theorem zero_notMem_vannulus (N : ℕ) : (0 : Kv) ∉ vannulus v N :=
  fun h => ne_zero_of_mem_vannulus v h rfl

private theorem exists_valued_eq_exp_of_ne_zero {b : Kv} (hb : b ≠ 0) : ∃ k : ℤ, Valued.v b = WithZero.exp k :=
  ⟨WithZero.log (Valued.v b), (WithZero.exp_log ((Valuation.ne_zero_iff _).mpr hb)).symm⟩

private theorem vannulus_eq_diff (N : ℕ) : vannulus v N = vball v N \ vball v (-(N : ℤ) - 1) := by
  ext b
  by_cases hb : b = 0
  · subst hb
    simp only [Set.mem_diff, mem_vball, map_zero, zero_le', not_true_eq_false, and_false, iff_false]
    exact zero_notMem_vannulus v N
  · obtain ⟨k, hk⟩ := exists_valued_eq_exp_of_ne_zero v hb
    rw [mem_vannulus_iff_of_valued_eq v hk, Set.mem_diff, mem_vball, mem_vball, hk, WithZero.exp_le_exp,
      WithZero.exp_le_exp]
    omega

private theorem measurableSet_vannulus (N : ℕ) : MeasurableSet (vannulus v N) := by
  rw [vannulus_eq_diff]
  exact (measurableSet_vball v _).diff (measurableSet_vball v _)

private theorem vannulus_mono : Monotone fun N : ℕ => vannulus v N := by
  intro N N' h
  show vannulus v N ⊆ vannulus v N'
  intro b hb
  rw [mem_vannulus] at hb ⊢
  exact ⟨(WithZero.exp_le_exp.mpr (by omega)).trans hb.1, hb.2.trans (WithZero.exp_le_exp.mpr (by omega))⟩

private theorem iUnion_vannulus : (⋃ N : ℕ, vannulus v N) = ({0} : Set Kv)ᶜ := by
  ext b
  simp only [Set.mem_iUnion, Set.mem_compl_iff, Set.mem_singleton_iff]
  constructor
  · rintro ⟨N, hN⟩
    exact ne_zero_of_mem_vannulus v hN
  · intro hb
    obtain ⟨k, hk⟩ := exists_valued_eq_exp_of_ne_zero v hb
    refine ⟨k.natAbs, (mem_vannulus_iff_of_valued_eq v hk).mpr ⟨?_, ?_⟩⟩ <;> omega

private theorem isCompact_vannulus (N : ℕ) : IsCompact (vannulus v N) := by
  have hq1 : (1 : ℝ) < (Ideal.absNorm v.asIdeal : ℝ) := one_lt_absNorm_real v
  have hq0 : (0 : ℝ) < (Ideal.absNorm v.asIdeal : ℝ) := one_pos.trans hq1
  have hset : vannulus v N = {b : Kv | (Ideal.absNorm v.asIdeal : ℝ) ^ (-(N : ℤ)) ≤ ‖b‖} ∩ vball v N := by
    ext b
    by_cases hb : b = 0
    · subst hb
      simp only [Set.mem_inter_iff, Set.mem_setOf_eq, norm_zero, mem_vball, map_zero, zero_le', and_true,
        iff_false_intro (zero_notMem_vannulus v N), false_iff, not_le]
      exact zpow_pos hq0 _
    · obtain ⟨k, hk⟩ := exists_valued_eq_exp_of_ne_zero v hb
      rw [mem_vannulus_iff_of_valued_eq v hk, Set.mem_inter_iff, Set.mem_setOf_eq, mem_vball, hk,
        norm_eq_zpow_of_valued_eq v hk, zpow_le_zpow_iff_right₀ hq1, WithZero.exp_le_exp]
  rw [hset]
  refine Metric.isCompact_of_isClosed_isBounded ?_ ?_
  · exact (isClosed_le continuous_const continuous_norm).inter (isClosed_valued_le v N)
  · refine isBounded_iff_forall_norm_le.mpr ⟨(Ideal.absNorm v.asIdeal : ℝ) ^ (N : ℤ), fun b hb => ?_⟩
    exact norm_le_zpow_of_valued_le v ((mem_vball v N b).mp (Set.mem_inter_iff _ _ _ |>.mp hb).2)

private theorem tendsto_setIntegral_vannulus (f : Kv → ℂ) (hf : Integrable f dmul) :
    Filter.Tendsto (fun N : ℕ => ∫ b in vannulus v N, f b ∂dmul) Filter.atTop (nhds (∫ b, f b ∂dmul)) := by
  have h := tendsto_setIntegral_of_monotone (μ := dmul) (f := f) (fun N => measurableSet_vannulus v N)
    (vannulus_mono v) hf.integrableOn
  have hae : (({0} : Set Kv)ᶜ : Set Kv) =ᵐ[dmul] (Set.univ : Set Kv) :=
    ae_eq_univ.mpr (by rw [compl_compl]; exact mulMeasure_apply_singleton_zero v)
  rw [iUnion_vannulus, Measure.restrict_congr_set hae, Measure.restrict_univ] at h
  exact h

variable (ν : Fin 3 → ((v.adicCompletion ℚ)ˣ →* ℂˣ)) (Φ : (Fin 3 → v.adicCompletion ℚ) → ℂ)

private theorem exists_forall_jacquetTruncated3_torusTranslate_mul (hν : ∀ i, IsLocallyConstant (ν i))
    (hΦl : IsLocallyConstant Φ) (hΦc : HasCompactSupport Φ) :
    ∃ k : ℕ, ∀ u : Kvˣ, Valued.v ((u : Kv) - 1) ≤ WithZero.exp (-(k : ℤ)) → ∀ (c : ℤ) (a : Kvˣ),
      jacquetTruncated3 v c (torusTranslate v ν Φ (a * u)) = jacquetTruncated3 v c (torusTranslate v ν Φ a) := by
  obtain ⟨k, -, hk⟩ := exists_forall_cellSectionOf_torusCellPoint_mul v ν Φ hν hΦl hΦc
  refine ⟨k, fun u hu c a => ?_⟩
  rw [jacquetTruncated3_torusTranslate_eq_integral, jacquetTruncated3_torusTranslate_eq_integral]
  congr 1
  funext p
  simp only [torusIntegrand, hk u hu]

private theorem exists_level_vannulus (hν : ∀ i, IsLocallyConstant (ν i)) (hΦl : IsLocallyConstant Φ)
    (hΦc : HasCompactSupport Φ) (N : ℕ) :
    ∃ c₁ : ℕ, ∀ (b : Kv) (hb : b ∈ vannulus v N) (c : ℤ), (c₁ : ℤ) ≤ c →
      jacquetTruncated3 v c (torusTranslate v ν Φ (Units.mk0 b (ne_zero_of_mem_vannulus v hb))) =
        jacquetValue v (torusTranslate v ν Φ (Units.mk0 b (ne_zero_of_mem_vannulus v hb))) := by
  have hq0 : (0 : ℝ) < (Ideal.absNorm v.asIdeal : ℝ) := one_pos.trans (one_lt_absNorm_real v)
  haveI : CompactSpace (vannulus v N) := isCompact_iff_compactSpace.mp (isCompact_vannulus v N)
  obtain ⟨k, hk⟩ := exists_forall_jacquetTruncated3_torusTranslate_mul v ν Φ hν hΦl hΦc
  have hstab : ∀ x : vannulus v N, ∃ c₀ : ℕ, ∀ c : ℤ, (c₀ : ℤ) ≤ c →
      jacquetTruncated3 v c (torusTranslate v ν Φ (Units.mk0 (x : Kv) (ne_zero_of_mem_vannulus v x.2))) =
        jacquetTruncated3 v c₀ (torusTranslate v ν Φ (Units.mk0 (x : Kv) (ne_zero_of_mem_vannulus v x.2))) :=
    fun x => exists_level_torusTranslate v ν Φ hν hΦl hΦc _
  have hlc : IsLocallyConstant fun x : vannulus v N => fun c : ℤ =>
      jacquetTruncated3 v c (torusTranslate v ν Φ (Units.mk0 (x : Kv) (ne_zero_of_mem_vannulus v x.2))) := by
    refine (IsLocallyConstant.iff_eventually_eq _).mpr fun x => ?_
    have hx0 : (x : Kv) ≠ 0 := ne_zero_of_mem_vannulus v x.2
    have hxn : 0 < ‖(x : Kv)‖ := norm_pos_iff.mpr hx0
    have hρ : 0 < (Ideal.absNorm v.asIdeal : ℝ) ^ (-(k : ℤ)) * ‖(x : Kv)‖ := mul_pos (zpow_pos hq0 _) hxn
    have hev : ∀ᶠ y : Kv in nhds (x : Kv), ‖y - x‖ < (Ideal.absNorm v.asIdeal : ℝ) ^ (-(k : ℤ)) * ‖(x : Kv)‖ :=
      Filter.eventually_of_mem (Metric.ball_mem_nhds _ hρ) fun y hy => by rwa [Metric.mem_ball, dist_eq_norm] at hy
    filter_upwards [(continuous_subtype_val.tendsto x).eventually hev] with y hy
    have hy0 : (y : Kv) ≠ 0 := ne_zero_of_mem_vannulus v y.2
    have hu : Valued.v ((Units.mk0 ((y : Kv) / x) (div_ne_zero hy0 hx0) : Kv) - 1) ≤ WithZero.exp (-(k : ℤ)) := by
      apply valued_le_of_norm_le_zpow v
      rw [Units.val_mk0, div_sub_one hx0, norm_div, div_le_iff₀ hxn]
      exact hy.le
    have hyu : Units.mk0 (y : Kv) hy0 = Units.mk0 (x : Kv) hx0 * Units.mk0 ((y : Kv) / x) (div_ne_zero hy0 hx0) :=
      Units.ext (by rw [Units.val_mul, Units.val_mk0, Units.val_mk0, Units.val_mk0, mul_div_cancel₀ _ hx0])
    funext c
    show jacquetTruncated3 v c (torusTranslate v ν Φ (Units.mk0 (y : Kv) hy0)) =
      jacquetTruncated3 v c (torusTranslate v ν Φ (Units.mk0 (x : Kv) hx0))
    rw [hyu]
    exact hk _ hu c _
  obtain ⟨c₁, hc₁⟩ := exists_level_forall_jacquetTruncated3_eq_jacquetValue_of_isLocallyConstant v
    (fun x : vannulus v N => torusTranslate v ν Φ (Units.mk0 (x : Kv) (ne_zero_of_mem_vannulus v x.2))) hlc hstab
  exact ⟨c₁, fun b hb c hc => hc₁ ⟨b, hb⟩ c hc⟩

private noncomputable def coupledKer (χ : Kvˣ →* ℂˣ) (s : ℂ) (c : ℤ) (q : Kv × Kv × Kv) : ℂ :=
  Φ ![q.1, q.2.1, q.2.2] *
    (charExt (ν 2 * χ)⁻¹ q.1 * ((modulus q.1 : ℝ) : ℂ) ^ (1 - s)) *
    (charExt (ν 1 * χ) q.2.1 * ((modulus q.2.1 : ℝ) : ℂ) ^ s) *
    (charExt (ν 0 * (ν 1)⁻¹) (q.2.1 - q.1 * q.2.2) * ((modulus (q.2.1 - q.1 * q.2.2) : ℝ) : ℂ)⁻¹) *
    truncChar v c (q.2.2 / (q.2.1 - q.1 * q.2.2))

private noncomputable def weightedInner (χ : Kvˣ →* ℂˣ) (s : ℂ) (c : ℤ) (p : Kv × Kv) : ℂ :=
  cWeight v ν χ s p.1 p.2 * innerI v ν Φ c p.1 p.2

private theorem coupledIntegrand_eq (χ : Kvˣ →* ℂˣ) (s : ℂ) (c : ℤ) (u r w : Kv) :
    Φ ![u, r, w] *
        (charExt (ν 2 * χ)⁻¹ u * ((modulus u : ℝ) : ℂ) ^ (1 - s)) *
        (charExt (ν 1 * χ) r * ((modulus r : ℝ) : ℂ) ^ s) *
        (charExt (ν 0 * (ν 1)⁻¹) (r - u * w) * ((modulus (r - u * w) : ℝ) : ℂ)⁻¹) *
        truncChar v c (w / (r - u * w)) =
      cWeight v ν χ s u r * innerK v ν Φ c u r w := by
  simp only [cWeight, innerK, truncChar]
  ring

private theorem integrable_weightedInner (χ : Kvˣ →* ℂˣ) (s : ℂ) (c : ℤ)
    (hIK : Integrable (coupledKer v ν Φ χ s c) (Measure.prod dmul (Measure.prod dmul (selfDualHaarAt ℚ v)))) :
    Integrable (weightedInner v ν Φ χ s c) (Measure.prod dmul dmul) := by
  haveI : SFinite dmul := sFinite_mulMeasure_selfDualHaarAt ℚ v
  haveI : SFinite (selfDualHaarAt ℚ v) := sFinite_selfDualHaarAt ℚ v
  have h3 : Integrable (coupledKer v ν Φ χ s c ∘ (MeasurableEquiv.prodAssoc : (Kv × Kv) × Kv ≃ᵐ Kv × Kv × Kv))
      (Measure.prod (Measure.prod dmul dmul) (selfDualHaarAt ℚ v)) :=
    ((measurePreserving_prodAssoc dmul dmul (selfDualHaarAt ℚ v)).integrable_comp_emb
      (MeasurableEquiv.measurableEmbedding _)).mpr hIK
  refine h3.integral_prod_left.congr (Filter.Eventually.of_forall fun p => ?_)
  show ∫ w, coupledKer v ν Φ χ s c (p.1, p.2, w) ∂(selfDualHaarAt ℚ v) =
    cWeight v ν χ s p.1 p.2 * innerI v ν Φ c p.1 p.2
  simp only [coupledKer, coupledIntegrand_eq, integral_const_mul, innerI]

private theorem coupledIntegral_eq_integral_weightedInner (χ : Kvˣ →* ℂˣ) (s : ℂ) (c : ℤ)
    (hIK : Integrable (coupledKer v ν Φ χ s c) (Measure.prod dmul (Measure.prod dmul (selfDualHaarAt ℚ v)))) :
    coupledIntegral v ν Φ χ s c = ∫ p, weightedInner v ν Φ χ s c p ∂(Measure.prod dmul dmul) := by
  haveI : SFinite dmul := sFinite_mulMeasure_selfDualHaarAt ℚ v
  haveI : SFinite (selfDualHaarAt ℚ v) := sFinite_selfDualHaarAt ℚ v
  have h3 : Integrable (coupledKer v ν Φ χ s c ∘ (MeasurableEquiv.prodAssoc : (Kv × Kv) × Kv ≃ᵐ Kv × Kv × Kv))
      (Measure.prod (Measure.prod dmul dmul) (selfDualHaarAt ℚ v)) :=
    ((measurePreserving_prodAssoc dmul dmul (selfDualHaarAt ℚ v)).integrable_comp_emb
      (MeasurableEquiv.measurableEmbedding _)).mpr hIK
  calc coupledIntegral v ν Φ χ s c
      = ∫ q, coupledKer v ν Φ χ s c q ∂(Measure.prod dmul (Measure.prod dmul (selfDualHaarAt ℚ v))) := rfl
    _ = ∫ q, (coupledKer v ν Φ χ s c ∘ (MeasurableEquiv.prodAssoc : (Kv × Kv) × Kv ≃ᵐ Kv × Kv × Kv)) q
          ∂(Measure.prod (Measure.prod dmul dmul) (selfDualHaarAt ℚ v)) :=
        ((measurePreserving_prodAssoc dmul dmul (selfDualHaarAt ℚ v)).integral_comp
          (MeasurableEquiv.measurableEmbedding _) _).symm
    _ = ∫ p, ∫ w, (coupledKer v ν Φ χ s c ∘ (MeasurableEquiv.prodAssoc : (Kv × Kv) × Kv ≃ᵐ Kv × Kv × Kv)) (p, w)
          ∂(selfDualHaarAt ℚ v) ∂(Measure.prod dmul dmul) := integral_prod _ h3
    _ = ∫ p, weightedInner v ν Φ χ s c p ∂(Measure.prod dmul dmul) := by
        refine integral_congr_ae (Filter.Eventually.of_forall fun p => ?_)
        show ∫ w, coupledKer v ν Φ χ s c (p.1, p.2, w) ∂(selfDualHaarAt ℚ v) =
          cWeight v ν χ s p.1 p.2 * innerI v ν Φ c p.1 p.2
        simp only [coupledKer, coupledIntegrand_eq, integral_const_mul, innerI]

private theorem norm_weightedInner_le (χ : Kvˣ →* ℂˣ) (s : ℂ) (c : ℤ) (p : Kv × Kv) {Dp : ℝ}
    (hdom : ‖(charExt (ν 2 * χ)⁻¹ p.1 * ((modulus p.1 : ℝ) : ℂ) ^ (1 - s)) *
        (charExt (ν 1 * χ) p.2 * ((modulus p.2 : ℝ) : ℂ) ^ s) *
        (∫ w : Kv, Φ ![p.1, p.2, w] *
            (charExt (ν 0 * (ν 1)⁻¹) (p.2 - p.1 * w) * ((modulus (p.2 - p.1 * w) : ℝ) : ℂ)⁻¹) *
            truncChar v c (w / (p.2 - p.1 * w)) ∂(selfDualHaarAt ℚ v))‖ ≤ Dp) :
    ‖weightedInner v ν Φ χ s c p‖ ≤ Dp := by
  refine le_trans (le_of_eq ?_) hdom
  congr 1
  simp only [weightedInner, cWeight, innerI, innerK, truncChar]
  ring

private noncomputable def torusTlim (χ : Kvˣ →* ℂˣ) (s : ℂ) (c : ℤ) (S : Set Kv) (q : Kv3) : ℂ :=
  charExt (ν 0) (-1) * charExt (ν 1) (-1) *
    (S.indicator (fun _ => (1 : ℂ)) (q.1.1 * (q.1.2)⁻¹ * q.2) * gaussKer v ν χ s c q.2 *
      (cWeight v ν χ s q.1.2 q.1.1 * innerI v ν Φ c q.1.2 q.1.1))

private theorem integral_torusT_eq (χ : Kvˣ →* ℂˣ) (s : ℂ) (c c' : ℤ) (S : Set Kv)
    (hT : Integrable (torusT v ν Φ χ s c c' S) (Measure.prod (Measure.prod dmul dmul) dmul)) :
    ∫ q, torusT v ν Φ χ s c c' S q ∂(Measure.prod (Measure.prod dmul dmul) dmul) =
      charExt (ν 0) (-1) * charExt (ν 1) (-1) *
        ∫ r, ∫ u, (∫ t, S.indicator (fun _ => (1 : ℂ)) (r * u⁻¹ * t) *
              (if Valued.v (u⁻¹ * t) ≤ WithZero.exp (2 * c') then (1 : ℂ) else 0) * gaussKer v ν χ s c t ∂dmul) *
            (cWeight v ν χ s u r * innerI v ν Φ c u r) ∂dmul ∂dmul := by
  haveI : SFinite dmul := sFinite_mulMeasure_selfDualHaarAt ℚ v
  rw [integral_prod _ hT, integral_prod _ hT.integral_prod_left]
  simp only [torusT]
  simp_rw [integral_const_mul, integral_mul_const]

private theorem integrable_torusTlim (χ : Kvˣ →* ℂˣ) (s : ℂ) (c : ℤ) (S : Set Kv) (hS : MeasurableSet S)
    (hIg : Integrable (gaussKer v ν χ s c) dmul)
    (hWI : Integrable (fun p : Kv × Kv => cWeight v ν χ s p.2 p.1 * innerI v ν Φ c p.2 p.1)
      (Measure.prod dmul dmul)) :
    Integrable (torusTlim v ν Φ χ s c S) (Measure.prod (Measure.prod dmul dmul) dmul) := by
  haveI : BorelSpace Kv := borelSpace_localBorel ℚ v
  haveI : SFinite dmul := sFinite_mulMeasure_selfDualHaarAt ℚ v
  have hF := hWI.mul_prod hIg
  have hB : Measurable fun q : Kv3 => S.indicator (fun _ => (1 : ℂ)) (q.1.1 * (q.1.2)⁻¹ * q.2) :=
    (measurable_const.indicator hS).comp ((measurable_fst.fst.mul measurable_fst.snd.inv).mul measurable_snd)
  have hT := (hF.bdd_mul hB.aestronglyMeasurable (Filter.Eventually.of_forall fun q =>
    (norm_indicator_le_norm_self _ _).trans (le_of_eq norm_one))).const_mul (charExt (ν 0) (-1) * charExt (ν 1) (-1))
  refine hT.congr (Filter.Eventually.of_forall fun q => ?_)
  simp only [torusTlim]
  ring

private theorem tendsto_integral_torusT (χ : Kvˣ →* ℂˣ) (s : ℂ) (c : ℤ) (S : Set Kv) (hS : MeasurableSet S)
    (hIg : Integrable (gaussKer v ν χ s c) dmul)
    (hWI : Integrable (fun p : Kv × Kv => cWeight v ν χ s p.2 p.1 * innerI v ν Φ c p.2 p.1)
      (Measure.prod dmul dmul)) :
    Filter.Tendsto (fun c' : ℤ => ∫ q, torusT v ν Φ χ s c c' S q ∂(Measure.prod (Measure.prod dmul dmul) dmul))
      Filter.atTop (nhds (∫ q, torusTlim v ν Φ χ s c S q ∂(Measure.prod (Measure.prod dmul dmul) dmul))) := by
  haveI : SFinite dmul := sFinite_mulMeasure_selfDualHaarAt ℚ v
  have hF := hWI.mul_prod hIg
  refine tendsto_integral_filter_of_dominated_convergence
    (fun q : Kv3 => ‖charExt (ν 0) (-1) * charExt (ν 1) (-1) *
      ((cWeight v ν χ s q.1.2 q.1.1 * innerI v ν Φ c q.1.2 q.1.1) * gaussKer v ν χ s c q.2)‖) ?_ ?_ ?_ ?_
  · exact Filter.Eventually.of_forall fun c' => (integrable_torusT v ν Φ χ s c c' S hS hIg hWI).aestronglyMeasurable
  · refine Filter.Eventually.of_forall fun c' => Filter.Eventually.of_forall fun q => ?_
    have h1 : ‖S.indicator (fun _ => (1 : ℂ)) (q.1.1 * (q.1.2)⁻¹ * q.2)‖ ≤ 1 :=
      (norm_indicator_le_norm_self _ _).trans (le_of_eq norm_one)
    have h2 : ‖(if Valued.v ((q.1.2)⁻¹ * q.2) ≤ WithZero.exp (2 * c') then (1 : ℂ) else 0)‖ ≤ 1 := by
      split_ifs
      · exact le_of_eq norm_one
      · rw [norm_zero]
        exact zero_le_one
    show ‖torusT v ν Φ χ s c c' S q‖ ≤ ‖charExt (ν 0) (-1) * charExt (ν 1) (-1) *
      ((cWeight v ν χ s q.1.2 q.1.1 * innerI v ν Φ c q.1.2 q.1.1) * gaussKer v ν χ s c q.2)‖
    rw [show torusT v ν Φ χ s c c' S q = S.indicator (fun _ => (1 : ℂ)) (q.1.1 * (q.1.2)⁻¹ * q.2) *
        (if Valued.v ((q.1.2)⁻¹ * q.2) ≤ WithZero.exp (2 * c') then (1 : ℂ) else 0) *
        (charExt (ν 0) (-1) * charExt (ν 1) (-1) *
          ((cWeight v ν χ s q.1.2 q.1.1 * innerI v ν Φ c q.1.2 q.1.1) * gaussKer v ν χ s c q.2)) by
      simp only [torusT]; ring, norm_mul, norm_mul]
    exact mul_le_of_le_one_left (norm_nonneg _) (mul_le_one₀ h1 (norm_nonneg _) h2)
  · exact (hF.const_mul _).norm
  · refine Filter.Eventually.of_forall fun q => ?_
    have hev : ∀ᶠ c' : ℤ in Filter.atTop, Valued.v ((q.1.2)⁻¹ * q.2) ≤ WithZero.exp (2 * c') := by
      refine Filter.eventually_atTop.mpr ⟨max (WithZero.log (Valued.v ((q.1.2)⁻¹ * q.2))) 0, fun c' hc' => ?_⟩
      have h := max_le_iff.mp hc'
      exact WithZero.le_exp_log.trans (WithZero.exp_le_exp.mpr (by omega))
    refine tendsto_const_nhds.congr' (hev.mono fun c' hc' => ?_)
    simp only [torusT, torusTlim, if_pos hc', mul_one]

private theorem integral_torusTlim_eq (χ : Kvˣ →* ℂˣ) (s : ℂ) (c : ℤ) (S : Set Kv) (hS : MeasurableSet S)
    (hIg : Integrable (gaussKer v ν χ s c) dmul)
    (hK : Integrable (weightedInner v ν Φ χ s c) (Measure.prod dmul dmul)) :
    ∫ q, torusTlim v ν Φ χ s c S q ∂(Measure.prod (Measure.prod dmul dmul) dmul) =
        charExt (ν 0) (-1) * charExt (ν 1) (-1) *
          ∫ p, (∫ t, S.indicator (fun _ => (1 : ℂ)) (p.2 * (p.1)⁻¹ * t) * gaussKer v ν χ s c t ∂dmul) *
            weightedInner v ν Φ χ s c p ∂(Measure.prod dmul dmul) ∧
      Integrable (fun p : Kv × Kv => (∫ t, S.indicator (fun _ => (1 : ℂ)) (p.2 * (p.1)⁻¹ * t) *
          gaussKer v ν χ s c t ∂dmul) * weightedInner v ν Φ χ s c p) (Measure.prod dmul dmul) := by
  haveI : SFinite dmul := sFinite_mulMeasure_selfDualHaarAt ℚ v
  have hWI : Integrable (fun p : Kv × Kv => cWeight v ν χ s p.2 p.1 * innerI v ν Φ c p.2 p.1)
      (Measure.prod dmul dmul) := hK.swap
  have hTl := integrable_torusTlim v ν Φ χ s c S hS hIg hWI
  have hν : charExt (ν 0) (-1) * charExt (ν 1) (-1) ≠ 0 :=
    mul_ne_zero (charExt_ne_zero_of_ne_zero v (ν 0) (neg_ne_zero.mpr one_ne_zero))
      (charExt_ne_zero_of_ne_zero v (ν 1) (neg_ne_zero.mpr one_ne_zero))

  have hfib : ∀ p : Kv × Kv, ∫ t, torusTlim v ν Φ χ s c S (p.swap, t) ∂dmul =
      charExt (ν 0) (-1) * charExt (ν 1) (-1) *
        ((∫ t, S.indicator (fun _ => (1 : ℂ)) (p.2 * (p.1)⁻¹ * t) * gaussKer v ν χ s c t ∂dmul) *
          weightedInner v ν Φ χ s c p) := fun p => by
    simp only [torusTlim, Prod.fst_swap, Prod.snd_swap, weightedInner]
    rw [integral_const_mul, integral_mul_const]
  have hswap : ∫ q, torusTlim v ν Φ χ s c S q ∂(Measure.prod (Measure.prod dmul dmul) dmul) =
      ∫ p, ∫ t, torusTlim v ν Φ χ s c S (p.swap, t) ∂dmul ∂(Measure.prod dmul dmul) := by
    rw [integral_prod _ hTl]
    exact (integral_prod_swap (fun p : Kv × Kv => ∫ t, torusTlim v ν Φ χ s c S (p, t) ∂dmul)).symm
  have hint : Integrable (fun p : Kv × Kv => ∫ t, torusTlim v ν Φ χ s c S (p.swap, t) ∂dmul)
      (Measure.prod dmul dmul) := hTl.integral_prod_left.swap
  refine ⟨?_, ?_⟩
  · rw [hswap]
    simp_rw [hfib]
    exact integral_const_mul _ _
  · refine ((hint.const_mul (charExt (ν 0) (-1) * charExt (ν 1) (-1))⁻¹)).congr
      (Filter.Eventually.of_forall fun p => ?_)
    show (charExt (ν 0) (-1) * charExt (ν 1) (-1))⁻¹ * ∫ t, torusTlim v ν Φ χ s c S (p.swap, t) ∂dmul = _
    rw [hfib, inv_mul_cancel_left₀ hν]

private theorem exists_forall_setIntegral_vannulus_eq (hν : ∀ i, IsLocallyConstant (ν i))
    (hΦl : IsLocallyConstant Φ) (hΦc : HasCompactSupport Φ) (χ : Kvˣ →* ℂˣ) (s : ℂ)
    (hIg : ∀ c : ℤ, Integrable (gaussKer v ν χ s c) dmul)
    (hK : ∀ c : ℤ, Integrable (weightedInner v ν Φ χ s c) (Measure.prod dmul dmul)) (N : ℕ) :
    ∃ C : ℤ, ∀ c : ℤ, C ≤ c →
      ∫ b in vannulus v N, torusFn v ν Φ b * charExt χ b * ((modulus b : ℝ) : ℂ) ^ s ∂dmul =
        charExt (ν 0) (-1) * charExt (ν 1) (-1) *
          ∫ p, (∫ t, (vannulus v N).indicator (fun _ => (1 : ℂ)) (p.2 * (p.1)⁻¹ * t) * gaussKer v ν χ s c t ∂dmul) *
            weightedInner v ν Φ χ s c p ∂(Measure.prod dmul dmul) := by
  haveI : SFinite dmul := sFinite_mulMeasure_selfDualHaarAt ℚ v
  obtain ⟨c₂, -, hu1⟩ := exists_forall_jacquetTruncated3_torusTranslate_eq_setIntegral_tallBox v ν Φ hν hΦl hΦc
  obtain ⟨cN, hcN⟩ := exists_level_vannulus v ν Φ hν hΦl hΦc N
  refine ⟨max (c₂ : ℤ) (cN : ℤ), fun c hc => ?_⟩
  have hc2 : (c₂ : ℤ) ≤ c := (le_max_left _ _).trans hc
  have hcN' : (cN : ℤ) ≤ c := (le_max_right _ _).trans hc
  have hS := measurableSet_vannulus v N
  have hWI : Integrable (fun p : Kv × Kv => cWeight v ν χ s p.2 p.1 * innerI v ν Φ c p.2 p.1)
      (Measure.prod dmul dmul) := (hK c).swap
  have hT : ∀ c' : ℤ, Integrable (torusT v ν Φ χ s c c' (vannulus v N)) (Measure.prod (Measure.prod dmul dmul) dmul) :=
    fun c' => integrable_torusT v ν Φ χ s c c' _ hS (hIg c) hWI

  have hconst : ∀ c' : ℤ, c ≤ c' →
      ∫ b in vannulus v N, torusFn v ν Φ b * charExt χ b * ((modulus b : ℝ) : ℂ) ^ s ∂dmul =
        ∫ q, torusT v ν Φ χ s c c' (vannulus v N) q ∂(Measure.prod (Measure.prod dmul dmul) dmul) := by
    intro c' hcc'
    have hint' : ∀ a : Kvˣ, IntegrableOn (torusIntegrand v ν Φ a) (tallBox v c c') (jacquetHaar3 v) :=
      fun a => (hu1 a c c' hc2 hcc').1
    rw [integral_torusT_eq v ν Φ χ s c c' _ (hT c'),
      ← setIntegral_jacquetTallBox_mul_charExt_mul_cpow_eq v ν Φ χ s c c' _ hS hint' (hIg c) hWI]
    refine setIntegral_congr_fun hS fun b hb => ?_
    have hb0 : b ≠ 0 := ne_zero_of_mem_vannulus v hb
    have h1 : torusFn v ν Φ b = jacquetValue v (torusTranslate v ν Φ (Units.mk0 b hb0)) * ((modulus b : ℝ) : ℂ)⁻¹ :=
      torusFn_coe_units v ν Φ (Units.mk0 b hb0)
    have h2 : jacquetValue v (torusTranslate v ν Φ (Units.mk0 b hb0)) = jacquetTallBox v ν Φ c c' b := by
      rw [← hcN b hb c hcN', (hu1 (Units.mk0 b hb0) c c' hc2 hcc').2]
      unfold jacquetTallBox
      rw [dif_neg hb0]
    show torusFn v ν Φ b * charExt χ b * ((modulus b : ℝ) : ℂ) ^ s =
      jacquetTallBox v ν Φ c c' b / (‖b‖ : ℂ) * charExt χ b * ((modulus b : ℝ) : ℂ) ^ s
    rw [h1, h2, modulus_real_eq_norm, div_eq_mul_inv]

  have hlim := tendsto_integral_torusT v ν Φ χ s c (vannulus v N) hS (hIg c) hWI
  have hev : (fun c' : ℤ => ∫ q, torusT v ν Φ χ s c c' (vannulus v N) q ∂(Measure.prod (Measure.prod dmul dmul) dmul))
      =ᶠ[Filter.atTop] fun _ => ∫ b in vannulus v N, torusFn v ν Φ b * charExt χ b * ((modulus b : ℝ) : ℂ) ^ s ∂dmul :=
    Filter.eventually_atTop.mpr ⟨c, fun c' hcc' => (hconst c' hcc').symm⟩
  have heq := tendsto_nhds_unique tendsto_const_nhds (hlim.congr' hev)
  rw [heq, (integral_torusTlim_eq v ν Φ χ s c _ hS (hIg c) (hK c)).1]

private theorem tendsto_gauss_mul_coupled_nhds_localZeta_torusFn
    (hν : ∀ i, IsLocallyConstant (ν i)) (hΦl : IsLocallyConstant Φ) (hΦc : HasCompactSupport Φ)
    (χ : (v.adicCompletion ℚ)ˣ →* ℂˣ) (hχ : IsLocallyConstant χ)
    (hu : ∀ i, ‖(((ν i * χ) (NumberField.AdelicLevel.uniformizerUnit ℚ v) : ℂˣ) : ℂ)‖ = 1)
    (s : ℂ) (hs : 0 < s.re) (hs' : s.re < 1)
    (hint : Integrable (fun x => torusFn v ν Φ x * charExt χ x * ((modulus x : ℝ) : ℂ) ^ s)
      (mulMeasure (selfDualHaarAt ℚ v))) :
    Filter.Tendsto
      (fun c : ℤ => charExt (ν 0) (-1) * charExt (ν 1) (-1) * gaussIntegral v (ν 2 * χ) s c *
        coupledIntegral v ν Φ χ s c)
      Filter.atTop (nhds (localZeta (selfDualHaarAt ℚ v) (torusFn v ν Φ) χ s)) := by
  haveI : SFinite dmul := sFinite_mulMeasure_selfDualHaarAt ℚ v

  have hν2χ : IsLocallyConstant (⇑(ν 2 * χ)) := (hν 2).mul hχ
  obtain ⟨j₁, hΓ⟩ := exists_forall_setIntegral_shell_psiLocal_mul_charExt_mul_cpow_eq_zero v (ν 2 * χ) hν2χ
  obtain ⟨j₂, M, hM0, hM⟩ :=
    exists_norm_setIntegral_ball_truncChar_mul_charExt_mul_cpow_le v (ν 2 * χ) hν2χ (hu 2) s hs
  have hIg : ∀ c : ℤ, Integrable (gaussTrunc v (ν 2 * χ) s c) dmul := fun c =>
    integrable_truncChar_mul_charExt_mul_cpow v (ν 2 * χ) hν2χ (hu 2) s hs c
  have hIK : ∀ c : ℤ, Integrable (coupledKer v ν Φ χ s c)
      (Measure.prod dmul (Measure.prod dmul (selfDualHaarAt ℚ v))) :=
    fun c => integrable_coupledIntegrand v ν hν Φ hΦl hΦc χ hχ hu s hs hs' c
  obtain ⟨⟨D, hD, hdom⟩, -⟩ := exists_integrable_dominant_coupledInner v ν hν Φ hΦl hΦc χ hχ hu s hs hs'
  have hK : ∀ c : ℤ, Integrable (weightedInner v ν Φ χ s c) (Measure.prod dmul dmul) := fun c =>
    integrable_weightedInner v ν Φ χ s c (hIK c)
  have hKD : ∀ (c : ℤ) (p : Kv × Kv), ‖weightedInner v ν Φ χ s c p‖ ≤ D p := fun c p =>
    norm_weightedInner_le v ν Φ χ s c p (hdom c p)
  have hgk : ∀ c : ℤ, gaussKer v ν χ s c = gaussTrunc v (ν 2 * χ) s c := fun c => rfl
  have hG : ∀ c : ℤ, gaussIntegral v (ν 2 * χ) s c = ∫ t, gaussTrunc v (ν 2 * χ) s c t ∂dmul := fun c => rfl

  have hZ : Filter.Tendsto
      (fun N : ℕ => ∫ b in vannulus v N, torusFn v ν Φ b * charExt χ b * ((modulus b : ℝ) : ℂ) ^ s ∂dmul)
      Filter.atTop (nhds (localZeta (selfDualHaarAt ℚ v) (torusFn v ν Φ) χ s)) :=
    tendsto_setIntegral_vannulus v _ hint
  have hδ := tendsto_integral_tailBound_mul v j₁ j₂ M s.re hM0 hs hD
  have hδ0 : ∀ N : ℕ, 0 ≤ ∫ p, tailBound v j₁ j₂ M s.re N p * D p ∂(Measure.prod dmul dmul) := fun N =>
    integral_nonneg fun p => mul_nonneg (tailBound_nonneg v j₁ j₂ M s.re hM0 N p) ((norm_nonneg _).trans (hKD 0 p))

  rw [Metric.tendsto_atTop]
  intro ε hε
  have hA : 0 < ‖charExt (ν 0) (-1) * charExt (ν 1) (-1)‖ + 1 := by positivity
  obtain ⟨N₁, hN₁⟩ := Metric.tendsto_atTop.mp hZ (ε / 2) (half_pos hε)
  obtain ⟨N₂, hN₂⟩ :=
    Metric.tendsto_atTop.mp hδ (ε / (2 * (‖charExt (ν 0) (-1) * charExt (ν 1) (-1)‖ + 1))) (by positivity)
  obtain ⟨C, hC⟩ := exists_forall_setIntegral_vannulus_eq v ν Φ hν hΦl hΦc χ s (fun c => hIg c) hK (max N₁ N₂)
  refine ⟨C, fun c hc => ?_⟩
  have h1 := hN₁ (max N₁ N₂) (le_max_left _ _)
  have h2 : ∫ p, tailBound v j₁ j₂ M s.re (max N₁ N₂) p * D p ∂(Measure.prod dmul dmul) <
      ε / (2 * (‖charExt (ν 0) (-1) * charExt (ν 1) (-1)‖ + 1)) := by
    have h := hN₂ (max N₁ N₂) (le_max_right _ _)
    rwa [Real.dist_eq, sub_zero, abs_of_nonneg (hδ0 _)] at h

  have hdiff : charExt (ν 0) (-1) * charExt (ν 1) (-1) * gaussIntegral v (ν 2 * χ) s c * coupledIntegral v ν Φ χ s c -
      ∫ b in vannulus v (max N₁ N₂), torusFn v ν Φ b * charExt χ b * ((modulus b : ℝ) : ℂ) ^ s ∂dmul =
      charExt (ν 0) (-1) * charExt (ν 1) (-1) *
        ∫ p : Kv × Kv, (∫ t, gaussTrunc v (ν 2 * χ) s c t ∂dmul -
            ∫ t, (vannulus v (max N₁ N₂)).indicator (fun _ => (1 : ℂ)) (p.2 * (p.1)⁻¹ * t) *
              gaussTrunc v (ν 2 * χ) s c t ∂dmul) * weightedInner v ν Φ χ s c p ∂(Measure.prod dmul dmul) := by
    have hI2 := (integral_torusTlim_eq v ν Φ χ s c _ (measurableSet_vannulus v (max N₁ N₂)) (hIg c) (hK c)).2
    rw [hC c hc, hG c, coupledIntegral_eq_integral_weightedInner v ν Φ χ s c (hIK c), mul_assoc, ← integral_const_mul,
      ← mul_sub, ← integral_sub ((hK c).const_mul _) hI2, hgk c]
    congr 1
    refine integral_congr_ae (Filter.Eventually.of_forall fun p => ?_)
    simp only [sub_mul]
  have h3 : ‖charExt (ν 0) (-1) * charExt (ν 1) (-1) * gaussIntegral v (ν 2 * χ) s c * coupledIntegral v ν Φ χ s c -
      ∫ b in vannulus v (max N₁ N₂), torusFn v ν Φ b * charExt χ b * ((modulus b : ℝ) : ℂ) ^ s ∂dmul‖ < ε / 2 := by
    rw [hdiff, norm_mul]
    have hle := norm_integral_gaussTail_mul_le v j₂ M (ν 2 * χ) s (c₁₀ := j₁) (hΓ s) hM0 hM hs.le c (hIg c)
      (max N₁ N₂) (hKD c) hD
    calc ‖charExt (ν 0) (-1) * charExt (ν 1) (-1)‖ * _ ≤ (‖charExt (ν 0) (-1) * charExt (ν 1) (-1)‖ + 1) *
          ∫ p, tailBound v j₁ j₂ M s.re (max N₁ N₂) p * D p ∂(Measure.prod dmul dmul) :=
        mul_le_mul (le_add_of_nonneg_right zero_le_one) hle (norm_nonneg _) hA.le
      _ < (‖charExt (ν 0) (-1) * charExt (ν 1) (-1)‖ + 1) *
          (ε / (2 * (‖charExt (ν 0) (-1) * charExt (ν 1) (-1)‖ + 1))) :=
        mul_lt_mul_of_pos_left h2 hA
      _ = ε / 2 := by
        rw [div_mul_eq_div_div, mul_div_cancel₀ _ hA.ne']
  calc dist (charExt (ν 0) (-1) * charExt (ν 1) (-1) * gaussIntegral v (ν 2 * χ) s c * coupledIntegral v ν Φ χ s c)
        (localZeta (selfDualHaarAt ℚ v) (torusFn v ν Φ) χ s)
      ≤ dist (charExt (ν 0) (-1) * charExt (ν 1) (-1) * gaussIntegral v (ν 2 * χ) s c * coupledIntegral v ν Φ χ s c)
          (∫ b in vannulus v (max N₁ N₂), torusFn v ν Φ b * charExt χ b * ((modulus b : ℝ) : ℂ) ^ s ∂dmul) +
        dist (∫ b in vannulus v (max N₁ N₂), torusFn v ν Φ b * charExt χ b * ((modulus b : ℝ) : ℂ) ^ s ∂dmul)
          (localZeta (selfDualHaarAt ℚ v) (torusFn v ν Φ) χ s) := dist_triangle _ _ _
    _ < ε / 2 + ε / 2 := add_lt_add (by rwa [dist_eq_norm]) h1
    _ = ε := add_halves ε

end Assembly

end LanglandsTunnell.CubicInduction
end

set_option autoImplicit false

open MeasureTheory IsDedekindDomain NumberField _root_.LanglandsTunnell.TateLocal _root_.P2MW.S_LanglandsTunnell_CubicInduction_tendsto_localZeta_truncChar_mul_coupled_localZeta_of_jacquetValue.LanglandsTunnell.TateLocal _root_.LanglandsTunnell.CubicInduction _root_.P2MW.S_LanglandsTunnell_CubicInduction_tendsto_localZeta_truncChar_mul_coupled_localZeta_of_jacquetValue.LanglandsTunnell.CubicInduction in
attribute [local instance] LanglandsTunnell.TateLocal.localBorel in
theorem solution
    (v : HeightOneSpectrum (𝓞 ℚ))
    (ν : Fin 3 → ((v.adicCompletion ℚ)ˣ →* ℂˣ)) (hν : ∀ i, IsLocallyConstant (ν i))
    (Φ : (Fin 3 → v.adicCompletion ℚ) → ℂ) (hΦl : IsLocallyConstant Φ) (hΦc : HasCompactSupport Φ)
    (T : v.adicCompletion ℚ → ℂ)
    (hT : ∀ a : (v.adicCompletion ℚ)ˣ, T a =
      jacquetValue v
          (gl3AmbientRightTranslate (R := ℂ) (iotaGL (diagUnitGL2 a) * antidiagonal3 v) (cellSectionOf v ν Φ)) *
        ((modulus (a : v.adicCompletion ℚ) : ℝ) : ℂ)⁻¹)
    (χ : (v.adicCompletion ℚ)ˣ →* ℂˣ) (hχ : IsLocallyConstant χ)
    (hu : ∀ i, ‖(((ν i * χ) (NumberField.AdelicLevel.uniformizerUnit ℚ v) : ℂˣ) : ℂ)‖ = 1)
    (s : ℂ) (hs : 0 < s.re) (hs' : s.re < 1)
    (hint : Integrable (fun x => T x * charExt χ x * ((modulus x : ℝ) : ℂ) ^ s) (mulMeasure (selfDualHaarAt ℚ v))) :
    Filter.Tendsto
      (fun c : ℤ => charExt (ν 0) (-1) * charExt (ν 1) (-1) *
        localZeta (selfDualHaarAt ℚ v)
          (fun t => if Valued.v (-t) ≤ WithZero.exp c then (NumberField.StandardAddChar.psiLocal ℚ v (-t) : ℂ) else 0)
          (ν 2 * χ) s *
        ∫ p : v.adicCompletion ℚ × v.adicCompletion ℚ × v.adicCompletion ℚ,
          Φ ![p.1, p.2.1, p.2.2] *
            (charExt (ν 2 * χ)⁻¹ p.1 * ((modulus p.1 : ℝ) : ℂ) ^ (1 - s)) *
            (charExt (ν 1 * χ) p.2.1 * ((modulus p.2.1 : ℝ) : ℂ) ^ s) *
            (charExt (ν 0 * (ν 1)⁻¹) (p.2.1 - p.1 * p.2.2) * ((modulus (p.2.1 - p.1 * p.2.2) : ℝ) : ℂ)⁻¹) *
            (if Valued.v (p.2.2 / (p.2.1 - p.1 * p.2.2)) ≤ WithZero.exp c then
              (NumberField.StandardAddChar.psiLocal ℚ v (p.2.2 / (p.2.1 - p.1 * p.2.2)) : ℂ) else 0)
        ∂((mulMeasure (selfDualHaarAt ℚ v)).prod ((mulMeasure (selfDualHaarAt ℚ v)).prod (selfDualHaarAt ℚ v))))
      Filter.atTop (nhds (localZeta (selfDualHaarAt ℚ v) T χ s)) := by

  have hfun : (fun x => T x * charExt χ x * ((modulus x : ℝ) : ℂ) ^ s) =
      fun x => torusFn v ν Φ x * charExt χ x * ((modulus x : ℝ) : ℂ) ^ s := by
    funext x
    by_cases h : x = 0
    · subst h
      simp only [charExt_zero, mul_zero, zero_mul]
    · have hx : T x = torusFn v ν Φ x := (hT (Units.mk0 x h)).trans (torusFn_coe_units v ν Φ (Units.mk0 x h)).symm
      rw [hx]
  have hZ : localZeta (selfDualHaarAt ℚ v) T χ s = localZeta (selfDualHaarAt ℚ v) (torusFn v ν Φ) χ s := by
    unfold localZeta
    rw [hfun]
  rw [hZ]
  rw [hfun] at hint
  exact tendsto_gauss_mul_coupled_nhds_localZeta_torusFn v ν Φ hν hΦl hΦc χ hχ hu s hs hs' hint

end S_LanglandsTunnell_CubicInduction_tendsto_localZeta_truncChar_mul_coupled_localZeta_of_jacquetValue
end P2MW
export P2MW.S_LanglandsTunnell_CubicInduction_tendsto_localZeta_truncChar_mul_coupled_localZeta_of_jacquetValue (solution)
