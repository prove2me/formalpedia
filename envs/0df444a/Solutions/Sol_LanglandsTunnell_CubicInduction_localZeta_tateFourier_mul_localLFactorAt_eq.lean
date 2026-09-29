-- Prove2me | solution 1 for LanglandsTunnell.CubicInduction.localZeta_tateFourier_mul_localLFactorAt_eq
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:08.670037+00:00
-- url     : https://prove2.me/submissions/cddb1c6b-f718-5557-adee-16937c5e1850

import Definitions.Def_LanglandsTunnell_StandardLocalConstantsAt
import Definitions.Def_LanglandsTunnell_TateLocalZeta
import Theorems.Thm_LanglandsTunnell_TateLocal_addCharLevel_psiLocal_rat
import Theorems.Thm_LanglandsTunnell_TateLocal_isSchwartzBruhat_tateFourier
import Theorems.Thm_LanglandsTunnell_TateLocal_localZeta_fourier_mul_symm
import Theorems.Thm_LanglandsTunnell_TateLocal_localZeta_stdTestFunAt_eq_of_unramified
import Theorems.Thm_LanglandsTunnell_TateLocal_localZeta_stdTestFunAt_eq_real_image_higherUnitsAt
import Theorems.Thm_LanglandsTunnell_TateLocal_localZeta_stdTestFunAt_ne_zero_of_unramified
import Theorems.Thm_LanglandsTunnell_TateLocal_localZeta_tateFourier_stdTestFunAt
import Theorems.Thm_LanglandsTunnell_TateLocal_modulus_adicCompletion_eq_nnnorm
import Theorems.Thm_LanglandsTunnell_TateLocal_psiLocal_eq_one_of_mem_integers
import Theorems.Thm_LanglandsTunnell_TateLocal_psiLocal_ne_one
import Theorems.Thm_LanglandsTunnell_TateLocal_selfDualHaarAt_real_image_higherUnitsAt
import Theorems.Thm_LanglandsTunnell_TateLocal_stdRootNumberAt_eq_one_of_hasConductorExponentAt_zero
import Theorems.Thm_LanglandsTunnell_TateLocal_tateFourier_indicator_setOf_valued_sub_le
import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Analysis.SpecialFunctions.Pow.Complex
import Mathlib.MeasureTheory.Integral.Prod
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_LanglandsTunnell_CubicInduction_localZeta_tateFourier_mul_localLFactorAt_eq
p2m_attr_erase "instance" "instFiniteResidueFieldAdicCompletionRingOfIntegersWithZeroMultiplicativeInt_definitions NumberField.instCompactSpaceAdicCompletionIntegers Rat.adicCompletion.locallyCompactSpace NumberField.instFiniteResidueFieldAdicCompletionIntegers instWeaklyLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions instCountableOfNumberField_definitions IsDedekindDomain.HeightOneSpectrum.Extension.instAlgebraSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersValEqUnder IsDedekindDomain.HeightOneSpectrum.Extension.instAlgebraSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersValEqUnder_1 IsDedekindDomain.HeightOneSpectrum.instMulActionHomClassAlgHomTensorProductAdicCompletionForallValEqUnder_definitions IsDedekindDomain.HeightOneSpectrum.Extension.instAlgebraAdicCompletionValEqUnder IsDedekindDomain.HeightOneSpectrum.adicCompletion.instFiniteForallValEqUnderOfFiniteDimensional_definitions IsDedekindDomain.HeightOneSpectrum.instIsBiscalarSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersTensorProductCoeAlgHomTensorAdicCompletionIntegersTo IsDedekindDomain.HeightOneSpectrum.Extension.instContinuousSMulAdicCompletionValEqUnder IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsModuleTopology IsDedekindDomain.HeightOneSpectrum.Extension.instFiniteSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersValEqUnderOfFiniteDimensional IsDedekindDomain.HeightOneSpectrum.adicCompletion.instFiniteValEqUnderOfFiniteDimensional_definitions instIsBiscalarTensorProductCoeAlgHomBaseChange_of_algebraMap IsDedekindDomain.HeightOneSpectrum.instIsScalarTowerSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersValEqUnder_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsModuleTopologyPi Submodule.instIsTopologicalModuleSubtypeMem Pi.instTopologicalModule IsTopologicalModule.toContinuousSMul IsTopologicalModule.toContinuousAdd instFunLike SemialgHomClass.toSemilinearMapClass instCoeTCSemialgHom SemialgHomClass.toRingHomClass SemialgHomClass.instSemialgHom"
p2m_attr_erase "simp" "SemialgHom.baseChange_of_algebraMap_tmul_left SemialgHom.baseChangeRightOfAlgebraMap_apply Pi.semialgHomPi_apply Pi.semialgHom_apply Module.Basis.rightBaseChange_apply LinearEquiv.coe_mulLeft LinearEquiv.coe_mulRight WithVal.semialgebraMap_toFun_ofVal Module.Basis.rightBaseChange_repr IsDedekindDomain.HeightOneSpectrum.adicCompletionIntegers.tensorCoe_tmul IsDedekindDomain.HeightOneSpectrum.tensorAdicCompletionIntegersTo_tmul SemialgHom.baseChangeRightOfAlgebraMap_coe IsDedekindDomain.HeightOneSpectrum.adicCompletion.integerBaseChangeLinearEquiv_tmul_apply SemialgHom.baseChange_of_algebraMap_tmul_right IsLocalization.map_moduleTensorEquiv_symm_tmul IsLocalization.leftModuleTensorEquiv_apply IsLocalization.moduleLid_symm_apply IsLocalization.leftModuleTensorEquiv_symm_apply IsLocalization.map_moduleTensorEquiv_tmul IsModuleTopology.continuousLinearEquiv_apply AlgEquiv.extendScalars_symm_apply IsModuleTopology.Module.Basis.equivFun_homeo_symm_apply IsModuleTopology.Module.Basis.equivFun_homeo_apply IsModuleTopology.continuousAlgEquivOfIsBiscalar_apply AlgEquiv.extendScalars_apply IsModuleTopology.continuousLinearEquiv_symm_apply SemialgHom.restrictScalars_toFun SemialgHom.mk.sizeOf_spec SemialgHom.mk.injEq SemialgHom.coe_coe coe_mk TensorProduct.RightActions.smul_def TensorProduct.RightActions.Module.TensorProduct.comm_symm_apply_tmul TensorProduct.RightActions.LinearMap.baseChange_id TensorProduct.RightActions.algebraMap_eval TensorProduct.RightActions.Module.TensorProduct.comm_apply_tmul TensorProduct.RightActions.Algebra.TensorProduct.comm_symm_apply_tmul TensorProduct.RightActions.Algebra.TensorProduct.comm_apply_tmul"

set_option autoImplicit false

section

set_option autoImplicit false

open IsDedekindDomain NumberField MeasureTheory
open scoped NNReal ENNReal Pointwise

namespace LanglandsTunnell
p2m_export "LanglandsTunnell" "TateLocal.localBorel TateLocal.borelSpace_localBorel"
namespace TateLocal
p2m_export "LanglandsTunnell.TateLocal" "addCharLevel addCharLevel_def localBorel borelSpace_localBorel integersPositiveCompacts coe_integersPositiveCompacts selfDualHaarAt stdTestFunAt stdEpsilonAt stdRootNumberAt stdRootNumberAt_def higherUnitsAt mem_higherUnitsAt_iff HasConductorExponentAt hasConductorExponentAt_unique conductorExponentAt_eq_of_hasConductorExponentAt localLFactorAt localLFactorAt_of_not_hasConductorExponentAt_zero localEpsilonAt_of_not_hasConductorExponentAt_zero modulus modulus_of_ne_zero modulus_ne_zero modulus_mul IsSchwartzBruhat tateFourier charExt charExt_of_ne_zero charExt_coe_units mulMeasure localZeta localGammaAt addCharLevel_psiLocal_rat isSchwartzBruhat_tateFourier localZeta_fourier_mul_symm localZeta_stdTestFunAt_eq_of_unramified localZeta_stdTestFunAt_eq_real_image_higherUnitsAt localZeta_stdTestFunAt_ne_zero_of_unramified localZeta_tateFourier_stdTestFunAt modulus_adicCompletion_eq_nnnorm psiLocal_eq_one_of_mem_integers psiLocal_ne_one selfDualHaarAt_real_image_higherUnitsAt stdRootNumberAt_eq_one_of_hasConductorExponentAt_zero tateFourier_indicator_setOf_valued_sub_le"
p2m_open "LanglandsTunnell.TateLocal LanglandsTunnell"

variable (K : Type) [Field K] [NumberField K] (v : HeightOneSpectrum (𝓞 K))

private theorem mulMeasure_restrict_compl_zero (μ : @Measure (v.adicCompletion K) (localBorel K v)) :
    letI := localBorel K v
    (mulMeasure μ).restrict {0}ᶜ = mulMeasure μ := by
  letI := localBorel K v
  haveI : BorelSpace (v.adicCompletion K) := borelSpace_localBorel K v
  have hc : MeasurableSet ({0}ᶜ : Set (v.adicCompletion K)) := isClosed_singleton.measurableSet.compl
  unfold mulMeasure
  rw [restrict_withDensity hc, Measure.restrict_restrict hc, Set.inter_self]

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

private theorem regular_selfDualHaarAt :
    letI := localBorel K v
    (selfDualHaarAt K v).Regular := by
  letI := localBorel K v
  haveI : BorelSpace (v.adicCompletion K) := borelSpace_localBorel K v
  unfold selfDualHaarAt
  infer_instance

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

open NumberField NumberField.AdelicLevel IsDedekindDomain MeasureTheory
p2m_open "LanglandsTunnell.TateLocal P2MW.S_LanglandsTunnell_CubicInduction_localZeta_tateFourier_mul_localLFactorAt_eq.LanglandsTunnell.TateLocal"
open scoped NNReal ENNReal

namespace IsLaurentInQPow

variable {q : ℂ}

end IsLaurentInQPow

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

private theorem isAddHaarMeasure_selfDualHaarAt' : (selfDualHaarAt ℚ v).IsAddHaarMeasure :=
  isAddHaarMeasure_selfDualHaarAt ℚ v

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
      mulMeasure (selfDualHaarAt ℚ v) :=
  map_mul_left_mulMeasure ℚ v u

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

private theorem charExt_mul' (χ : (v.adicCompletion ℚ)ˣ →* ℂˣ) (a b : v.adicCompletion ℚ) :
    charExt χ (a * b) = charExt χ a * charExt χ b :=
  charExt_mul ℚ v χ a b

private theorem measurable_of_eventually_eq {f : v.adicCompletion ℚ → ℂ}
    (hf : ∀ t : v.adicCompletion ℚ, t ≠ 0 → ∀ᶠ t' in nhds t, f t' = f t) : Measurable f :=
  measurable_of_continuousOn_compl_singleton (0 : v.adicCompletion ℚ) fun t ht =>
    (Filter.EventuallyEq.continuousAt (hf t ht)).continuousWithinAt

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

private theorem inv_modulus_pow_of_mem_shell {j : ℤ} {x : v.adicCompletion ℚ} (hx : x ∈ shell v j) (N : ℕ) :
    ((modulus x : ℝ) ^ N)⁻¹ = ((Ideal.absNorm v.asIdeal : ℝ) ^ N) ^ j := by
  rw [coe_modulus_eq_of_mem_shell v hx, ← zpow_natCast (Ideal.absNorm v.asIdeal : ℝ) N, ← zpow_mul,
    ← zpow_natCast ((Ideal.absNorm v.asIdeal : ℝ) ^ (-j)) N, ← zpow_mul, ← zpow_neg]
  congr 1
  ring

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

private theorem geomBoundFrom_of_bound {φ : v.adicCompletion ℚ → ℂ} {C : ℝ} {N : ℕ}
    (hbound : ∀ t : v.adicCompletion ℚ, t ≠ 0 → ‖φ t‖ ≤ C * ((modulus t : ℝ) ^ N)⁻¹) (j₀ : ℤ) :
    GeomBoundFrom v φ j₀ C ((Ideal.absNorm v.asIdeal : ℝ) ^ N) := by
  intro j _ x hx
  rw [← inv_modulus_pow_of_mem_shell v hx N]
  exact hbound x (shell_subset_compl_zero v j hx)

end LaurentLocalZeta

end

section

set_option autoImplicit false

open MeasureTheory
open IsDedekindDomain
open NumberField
open NumberField.StandardAddChar
open NumberField.AdelicLevel

namespace LanglandsTunnell
p2m_export "LanglandsTunnell" "TateLocal.localBorel TateLocal.borelSpace_localBorel"
namespace TateLocal
p2m_export "LanglandsTunnell.TateLocal" "addCharLevel addCharLevel_def localBorel borelSpace_localBorel integersPositiveCompacts coe_integersPositiveCompacts selfDualHaarAt stdTestFunAt stdEpsilonAt stdRootNumberAt stdRootNumberAt_def higherUnitsAt mem_higherUnitsAt_iff HasConductorExponentAt hasConductorExponentAt_unique conductorExponentAt_eq_of_hasConductorExponentAt localLFactorAt localLFactorAt_of_not_hasConductorExponentAt_zero localEpsilonAt_of_not_hasConductorExponentAt_zero modulus modulus_of_ne_zero modulus_ne_zero modulus_mul IsSchwartzBruhat tateFourier charExt charExt_of_ne_zero charExt_coe_units mulMeasure localZeta localGammaAt addCharLevel_psiLocal_rat isSchwartzBruhat_tateFourier localZeta_fourier_mul_symm localZeta_stdTestFunAt_eq_of_unramified localZeta_stdTestFunAt_eq_real_image_higherUnitsAt localZeta_stdTestFunAt_ne_zero_of_unramified localZeta_tateFourier_stdTestFunAt modulus_adicCompletion_eq_nnnorm psiLocal_eq_one_of_mem_integers psiLocal_ne_one selfDualHaarAt_real_image_higherUnitsAt stdRootNumberAt_eq_one_of_hasConductorExponentAt_zero tateFourier_indicator_setOf_valued_sub_le"
p2m_open "LanglandsTunnell.TateLocal LanglandsTunnell"

section RootNumber

variable (v : HeightOneSpectrum (𝓞 ℚ))

attribute [local instance] LanglandsTunnell.TateLocal.localBorel

private theorem one_lt_absNorm_asIdeal : 1 < Ideal.absNorm v.asIdeal := by
  have h0 : Ideal.absNorm v.asIdeal ≠ 0 := by
    rw [Ne, Ideal.absNorm_eq_zero_iff]
    exact v.ne_bot
  have h1 : Ideal.absNorm v.asIdeal ≠ 1 := by
    rw [Ne, Ideal.absNorm_eq_one_iff]
    exact v.isPrime.ne_top
  omega

private theorem not_hasConductorExponentAt_zero_of_pos {η : (v.adicCompletion ℚ)ˣ →* ℂˣ} {a : ℕ} (ha : 1 ≤ a)
    (hη : HasConductorExponentAt ℚ v η a) : ¬ HasConductorExponentAt ℚ v η 0 := fun h0 => by
  have := hasConductorExponentAt_unique ℚ v hη h0
  omega

private theorem norm_inv_uniformizerUnit_mul_cpow_lt_one {η : (v.adicCompletion ℚ)ˣ →* ℂˣ}
    (hu : ‖(η (uniformizerUnit ℚ v) : ℂ)‖ = 1) :
    ‖(η⁻¹ (uniformizerUnit ℚ v) : ℂ) * (Ideal.absNorm v.asIdeal : ℂ) ^ (-(1 - (1 / 2 : ℂ)))‖ < 1 := by
  have hq : 1 < (Ideal.absNorm v.asIdeal : ℝ) := by exact_mod_cast one_lt_absNorm_asIdeal v
  have hq0 : 0 < Ideal.absNorm v.asIdeal := lt_trans Nat.zero_lt_one (one_lt_absNorm_asIdeal v)
  have h1 : ‖(η⁻¹ (uniformizerUnit ℚ v) : ℂ)‖ = 1 := by
    rw [MonoidHom.inv_apply, Units.val_inv_eq_inv_val, norm_inv, hu, inv_one]
  have h2 : ‖(Ideal.absNorm v.asIdeal : ℂ) ^ (-(1 - (1 / 2 : ℂ)))‖
      = (Ideal.absNorm v.asIdeal : ℝ) ^ (-(1 / 2 : ℝ)) := by
    rw [Complex.norm_natCast_cpow_of_pos hq0]
    congr 1
    norm_num
  rw [norm_mul, h1, one_mul, h2]
  exact Real.rpow_lt_one_of_one_lt_of_neg hq (by norm_num)

private theorem stdRootNumberAt_eq_of_hasConductorExponentAt (η : (v.adicCompletion ℚ)ˣ →* ℂˣ) (a : ℕ) (ha : 1 ≤ a)
    (hη : HasConductorExponentAt ℚ v η a) (hu : ‖(η (uniformizerUnit ℚ v) : ℂ)‖ = 1)
    (hmass : (selfDualHaarAt ℚ v).real
      (((↑) : (v.adicCompletion ℚ)ˣ → v.adicCompletion ℚ) '' higherUnitsAt ℚ v a) ≠ 0) :
    stdRootNumberAt ℚ v η
      = (η (uniformizerUnit ℚ v) : ℂ) ^ (a : ℤ)
          * ((((Ideal.absNorm v.asIdeal : ℝ) ^ (a : ℤ) : ℝ) : ℂ)) ^ (1 - (1 / 2 : ℂ))
          * ∫ u in {u : v.adicCompletion ℚ | Valued.v u = 1},
              psiLocal ℚ v (((uniformizerUnit ℚ v ^ (-(a : ℤ)) : (v.adicCompletion ℚ)ˣ) : v.adicCompletion ℚ) * u)
                * charExt η⁻¹ u ∂(selfDualHaarAt ℚ v) := by
  have hn0 := not_hasConductorExponentAt_zero_of_pos v ha hη
  have hs := norm_inv_uniformizerUnit_mul_cpow_lt_one v hu
  have hZf := localZeta_stdTestFunAt_eq_real_image_higherUnitsAt ℚ v η a ha hη (1 / 2)
  have hZd := localZeta_tateFourier_stdTestFunAt ℚ v η a ha hη (1 / 2) hs
  have hlev : addCharLevel (psiLocal ℚ v) = 0 := addCharLevel_psiLocal_rat v
  have hmassC : ((((selfDualHaarAt ℚ v).real
      (((↑) : (v.adicCompletion ℚ)ˣ → v.adicCompletion ℚ) '' higherUnitsAt ℚ v a) : ℝ) : ℂ)) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr hmass
  rw [stdRootNumberAt_def]
  unfold stdEpsilonAt
  rw [localEpsilonAt_of_not_hasConductorExponentAt_zero ℚ v _ _ _ hn0]
  unfold localGammaAt
  rw [hZd, hZf, hlev]
  simp only [zero_add]
  rw [mul_assoc, mul_assoc, mul_div_cancel_left₀ _ hmassC, ← mul_assoc]

private theorem stdRootNumberAt_eq_one_of_unramified (η : (v.adicCompletion ℚ)ˣ →* ℂˣ)
    (h0 : HasConductorExponentAt ℚ v η 0) (hu : ‖(η (uniformizerUnit ℚ v) : ℂ)‖ = 1) :
    stdRootNumberAt ℚ v η = 1 :=
  stdRootNumberAt_eq_one_of_hasConductorExponentAt_zero ℚ v η h0 hu (addCharLevel_psiLocal_rat v)
    (psiLocal_ne_one ℚ v)

end RootNumber

end LanglandsTunnell.TateLocal

end

section

set_option autoImplicit false

open MeasureTheory
open IsDedekindDomain
open NumberField
open NumberField.StandardAddChar
open NumberField.AdelicLevel

namespace LanglandsTunnell
p2m_export "LanglandsTunnell" "TateLocal.localBorel TateLocal.borelSpace_localBorel"
namespace TateLocal
p2m_export "LanglandsTunnell.TateLocal" "addCharLevel addCharLevel_def localBorel borelSpace_localBorel integersPositiveCompacts coe_integersPositiveCompacts selfDualHaarAt stdTestFunAt stdEpsilonAt stdRootNumberAt stdRootNumberAt_def higherUnitsAt mem_higherUnitsAt_iff HasConductorExponentAt hasConductorExponentAt_unique conductorExponentAt_eq_of_hasConductorExponentAt localLFactorAt localLFactorAt_of_not_hasConductorExponentAt_zero localEpsilonAt_of_not_hasConductorExponentAt_zero modulus modulus_of_ne_zero modulus_ne_zero modulus_mul IsSchwartzBruhat tateFourier charExt charExt_of_ne_zero charExt_coe_units mulMeasure localZeta localGammaAt addCharLevel_psiLocal_rat isSchwartzBruhat_tateFourier localZeta_fourier_mul_symm localZeta_stdTestFunAt_eq_of_unramified localZeta_stdTestFunAt_eq_real_image_higherUnitsAt localZeta_stdTestFunAt_ne_zero_of_unramified localZeta_tateFourier_stdTestFunAt modulus_adicCompletion_eq_nnnorm psiLocal_eq_one_of_mem_integers psiLocal_ne_one selfDualHaarAt_real_image_higherUnitsAt stdRootNumberAt_eq_one_of_hasConductorExponentAt_zero tateFourier_indicator_setOf_valued_sub_le"
p2m_open "LanglandsTunnell.TateLocal LanglandsTunnell"

section GaussProductViaRootNumbers

variable (K : Type) [Field K] [NumberField K] (w : HeightOneSpectrum (𝓞 K))

private theorem hasConductorExponentAt_inv {η : (w.adicCompletion K)ˣ →* ℂˣ} {a : ℕ}
    (hη : HasConductorExponentAt K w η a) : HasConductorExponentAt K w η⁻¹ a := by
  refine ⟨fun u hu => ?_, fun m hm => ?_⟩
  · rw [MonoidHom.inv_apply, hη.1 u hu, inv_one]
  · obtain ⟨u, hu, hne⟩ := hη.2 m hm
    exact ⟨u, hu, by rwa [MonoidHom.inv_apply, Ne, inv_eq_one]⟩

private theorem norm_inv_apply_uniformizerUnit {η : (w.adicCompletion K)ˣ →* ℂˣ}
    (hu : ‖(η (uniformizerUnit K w) : ℂ)‖ = 1) : ‖(η⁻¹ (uniformizerUnit K w) : ℂ)‖ = 1 := by
  rw [MonoidHom.inv_apply, Units.val_inv_eq_inv_val, norm_inv, hu, inv_one]

end GaussProductViaRootNumbers

section GaussProductRat

variable (v : HeightOneSpectrum (𝓞 ℚ))

attribute [local instance] LanglandsTunnell.TateLocal.localBorel

end GaussProductRat

end LanglandsTunnell.TateLocal

end

open MeasureTheory
open IsDedekindDomain
open NumberField
p2m_open "LanglandsTunnell.TateLocal P2MW.S_LanglandsTunnell_CubicInduction_localZeta_tateFourier_mul_localLFactorAt_eq.LanglandsTunnell.TateLocal"

attribute [local instance] LanglandsTunnell.TateLocal.localBorel

namespace LanglandsTunnell
p2m_export "LanglandsTunnell" "TateLocal.localBorel TateLocal.borelSpace_localBorel"
namespace CubicInduction
p2m_open "LanglandsTunnell"

variable (v : HeightOneSpectrum (𝓞 ℚ))

section TateFunctionalEquationAtRat

attribute [local instance] LanglandsTunnell.TateLocal.borelSpace_localBorel
attribute [local instance] LanglandsTunnell.TateLocal.isAddHaarMeasure_selfDualHaarAt
attribute [local instance] LanglandsTunnell.TateLocal.regular_selfDualHaarAt
attribute [local instance] LanglandsTunnell.TateLocal.sFinite_selfDualHaarAt
attribute [local instance] LanglandsTunnell.TateLocal.sFinite_mulMeasure_selfDualHaarAt
attribute [local instance] LanglandsTunnell.TateLocal.measurableSingletonClass_adicCompletion

private theorem isClopen_setOf_valued_le_valued {x₀ : v.adicCompletion ℚ} (hx₀ : x₀ ≠ 0) :
    IsClopen {x : v.adicCompletion ℚ | Valued.v x ≤ Valued.v x₀} := by
  have hset : {x : v.adicCompletion ℚ | Valued.v x ≤ Valued.v x₀}
      = {x | Valued.v.restrict x ≤ Valued.v.restrict x₀} := by
    ext x
    simp only [Set.mem_setOf_eq, Valuation.restrict_le_iff]
  have hne : Valued.v.restrict x₀ ≠ 0 := by
    intro h0
    have h1 : Valued.v x₀ = Valued.v (0 : v.adicCompletion ℚ) :=
      (Valuation.restrict_inj Valued.v).mp (by rw [h0, map_zero])
    rw [map_zero] at h1
    exact hx₀ ((Valuation.zero_iff Valued.v).mp h1)
  rw [hset]
  exact ⟨Valued.isClosed_closedBall _ _, Valued.isOpen_closedBall _ hne⟩

private theorem isSchwartzBruhat_indicator_of_isClopen {S : Set (v.adicCompletion ℚ)} (hS : IsClopen S)
    (hK : IsCompact S) : IsSchwartzBruhat (S.indicator fun _ => (1 : ℂ)) := by
  refine ⟨(IsLocallyConstant.iff_eventually_eq _).mpr fun x => ?_,
    HasCompactSupport.intro hK fun x hx => Set.indicator_of_notMem hx _⟩
  by_cases hx : x ∈ S
  · filter_upwards [hS.isOpen.mem_nhds hx] with y hy
    rw [Set.indicator_of_mem hy, Set.indicator_of_mem hx]
  · filter_upwards [hS.isClosed.isOpen_compl.mem_nhds hx] with y hy
    rw [Set.indicator_of_notMem hy, Set.indicator_of_notMem hx]

private theorem isCompact_integers : IsCompact (v.adicCompletionIntegers ℚ : Set (v.adicCompletion ℚ)) := by
  rw [← coe_integersPositiveCompacts ℚ v]
  exact (integersPositiveCompacts ℚ v).isCompact

private theorem integers_eq_setOf_valued_le :
    (v.adicCompletionIntegers ℚ : Set (v.adicCompletion ℚ))
      = {x | Valued.v x ≤ Valued.v (1 : v.adicCompletion ℚ)} := by
  ext x
  rw [SetLike.mem_coe, HeightOneSpectrum.mem_adicCompletionIntegers, Set.mem_setOf_eq, map_one]

private theorem isSchwartzBruhat_indicator_integers :
    IsSchwartzBruhat ((v.adicCompletionIntegers ℚ : Set (v.adicCompletion ℚ)).indicator fun _ => (1 : ℂ)) := by
  refine isSchwartzBruhat_indicator_of_isClopen v ?_ (isCompact_integers v)
  rw [integers_eq_setOf_valued_le]
  exact isClopen_setOf_valued_le_valued v one_ne_zero

private theorem image_higherUnitsAt_eq_setOf {a : ℕ} (ha : 1 ≤ a) :
    ((↑) : (v.adicCompletion ℚ)ˣ → v.adicCompletion ℚ) '' higherUnitsAt ℚ v a
      = {x | Valued.v (x - 1) ≤ WithZero.exp (-(a : ℤ))} := by
  ext x
  constructor
  · rintro ⟨u, hu, rfl⟩
    exact (mem_higherUnitsAt_iff ℚ v).mp hu |>.2.resolve_left (by omega)
  · intro hx
    have hlt : Valued.v (x - 1) < Valued.v (1 : v.adicCompletion ℚ) := by
      rw [map_one]
      refine lt_of_le_of_lt hx ?_
      rw [← WithZero.exp_zero]
      exact WithZero.exp_lt_exp.mpr (by omega)
    have hv1 : Valued.v x = 1 := by
      have h := Valuation.map_add_eq_of_lt_right Valued.v hlt
      rwa [sub_add_cancel, map_one] at h
    have hx0 : x ≠ 0 := by
      intro h0
      rw [h0, map_zero] at hv1
      exact zero_ne_one hv1
    refine ⟨Units.mk0 x hx0, (mem_higherUnitsAt_iff ℚ v).mpr ⟨by simpa using hv1, Or.inr (by simpa using hx)⟩,
      Units.val_mk0 hx0⟩

private theorem isClopen_and_isCompact_ball_one {a : ℕ} (ha : 1 ≤ a) :
    IsClopen {x : v.adicCompletion ℚ | Valued.v (x - 1) ≤ WithZero.exp (-(a : ℤ))}
      ∧ IsCompact {x : v.adicCompletion ℚ | Valued.v (x - 1) ≤ WithZero.exp (-(a : ℤ))} := by
  obtain ⟨x₀, hx₀⟩ := HeightOneSpectrum.valuedAdicCompletion_surjective ℚ v (WithZero.exp (-(a : ℤ)))
  have hx₀0 : x₀ ≠ 0 := by
    intro h0
    rw [h0, map_zero] at hx₀
    exact WithZero.exp_ne_zero hx₀.symm
  have hset : {x : v.adicCompletion ℚ | Valued.v (x - 1) ≤ WithZero.exp (-(a : ℤ))}
      = (fun x : v.adicCompletion ℚ => x - 1) ⁻¹' {y | Valued.v y ≤ Valued.v x₀} := by
    ext x
    simp only [Set.mem_setOf_eq, Set.mem_preimage, hx₀]
  have hclopen : IsClopen {x : v.adicCompletion ℚ | Valued.v (x - 1) ≤ WithZero.exp (-(a : ℤ))} := by
    rw [hset]
    exact (isClopen_setOf_valued_le_valued v hx₀0).preimage (continuous_id.sub continuous_const)
  refine ⟨hclopen, (isCompact_integers v).of_isClosed_subset hclopen.isClosed fun x hx => ?_⟩
  rw [← image_higherUnitsAt_eq_setOf v ha] at hx
  obtain ⟨u, hu, rfl⟩ := hx
  rw [SetLike.mem_coe, HeightOneSpectrum.mem_adicCompletionIntegers]
  exact le_of_eq ((mem_higherUnitsAt_iff ℚ v).mp hu).1

private theorem isSchwartzBruhat_stdTestFunAt {η : (v.adicCompletion ℚ)ˣ →* ℂˣ} {a : ℕ}
    (hη : HasConductorExponentAt ℚ v η a) : IsSchwartzBruhat (stdTestFunAt ℚ v η) := by
  unfold stdTestFunAt
  split_ifs with h0
  · exact isSchwartzBruhat_indicator_integers v
  · have ha : 1 ≤ a := by
      rcases Nat.eq_zero_or_pos a with rfl | hpos
      · exact absurd hη h0
      · exact hpos
    rw [conductorExponentAt_eq_of_hasConductorExponentAt ℚ v hη, image_higherUnitsAt_eq_setOf v ha]
    obtain ⟨hclopen, hcompact⟩ := isClopen_and_isCompact_ball_one v ha
    exact isSchwartzBruhat_indicator_of_isClopen v hclopen hcompact

private theorem exists_forall_eq_zero_of_lt_modulus {φ : v.adicCompletion ℚ → ℂ} (hφ : IsSchwartzBruhat φ) :
    ∃ B : ℝ, ∀ t : v.adicCompletion ℚ, B < (modulus t : ℝ) → φ t = 0 := by
  obtain ⟨B, hB⟩ := hφ.2.isCompact.isBounded.exists_norm_le
  refine ⟨B, fun t ht => ?_⟩
  apply image_eq_zero_of_notMem_tsupport
  intro hmem
  have h1 := hB t hmem
  rw [modulus_adicCompletion_eq_nnnorm ℚ v t, coe_nnnorm] at ht
  exact absurd h1 (not_le.mpr ht)

private theorem strip_rpow_lt_one {r : ℝ} (hr : 0 < r) : (Ideal.absNorm v.asIdeal : ℝ) ^ (-r) < 1 :=
  Real.rpow_lt_one_of_one_lt_of_neg (LaurentLocalZeta.one_lt_absNorm_real v) (neg_neg_of_pos hr)

private theorem integrable_mul_charExt_mul_cpow {φ : v.adicCompletion ℚ → ℂ} (hφ : IsSchwartzBruhat φ)
    (η : (v.adicCompletion ℚ)ˣ →* ℂˣ) (hη : IsLocallyConstant η) (s : ℂ)
    (hs : ‖(η (NumberField.AdelicLevel.uniformizerUnit ℚ v) : ℂ)‖ * (Ideal.absNorm v.asIdeal : ℝ) ^ (-s.re) < 1) :
    Integrable (fun x => φ x * charExt η x * ((modulus x : ℝ) : ℂ) ^ s) (mulMeasure (selfDualHaarAt ℚ v)) := by
  obtain ⟨C, hC⟩ := hφ.1.continuous.bounded_above_of_compact_support hφ.2
  have hgeom : LaurentLocalZeta.GeomBoundFrom v φ 0 C ((Ideal.absNorm v.asIdeal : ℝ) ^ (0 : ℕ)) :=
    LaurentLocalZeta.geomBoundFrom_of_bound v (fun t _ => by simpa using hC t) 0
  refine LaurentLocalZeta.integrable_of_geomBoundFrom v η hη (fun t _ => hφ.1.eventually_eq t)
    (exists_forall_eq_zero_of_lt_modulus v hφ) (by simp) hgeom s ?_
  simpa using hs

private theorem strip_condition {η : (v.adicCompletion ℚ)ˣ →* ℂˣ}
    (hu : ‖(η (NumberField.AdelicLevel.uniformizerUnit ℚ v) : ℂ)‖ = 1) {s : ℂ} (hs : 0 < s.re) :
    ‖(η (NumberField.AdelicLevel.uniformizerUnit ℚ v) : ℂ)‖ * (Ideal.absNorm v.asIdeal : ℝ) ^ (-s.re) < 1 := by
  rw [hu, one_mul]
  exact strip_rpow_lt_one v hs

private theorem strip_condition_inv {η : (v.adicCompletion ℚ)ˣ →* ℂˣ}
    (hu : ‖(η (NumberField.AdelicLevel.uniformizerUnit ℚ v) : ℂ)‖ = 1) {s : ℂ} (hs' : s.re < 1) :
    ‖(η⁻¹ (NumberField.AdelicLevel.uniformizerUnit ℚ v) : ℂ)‖ * (Ideal.absNorm v.asIdeal : ℝ) ^ (-(1 - s).re)
      < 1 := by
  rw [norm_inv_apply_uniformizerUnit ℚ v hu, one_mul, Complex.sub_re, Complex.one_re]
  exact strip_rpow_lt_one v (by linarith)

private theorem ae_prod_ne_zero :
    ∀ᵐ p : v.adicCompletion ℚ × v.adicCompletion ℚ
      ∂((mulMeasure (selfDualHaarAt ℚ v)).prod (mulMeasure (selfDualHaarAt ℚ v))), p.1 ≠ 0 ∧ p.2 ≠ 0 := by
  have hr : (mulMeasure (selfDualHaarAt ℚ v)).prod (mulMeasure (selfDualHaarAt ℚ v))
      = ((mulMeasure (selfDualHaarAt ℚ v)).prod (mulMeasure (selfDualHaarAt ℚ v))).restrict
          (({0}ᶜ : Set (v.adicCompletion ℚ)) ×ˢ ({0}ᶜ : Set (v.adicCompletion ℚ))) := by
    have h : (mulMeasure (selfDualHaarAt ℚ v)).restrict {0}ᶜ = mulMeasure (selfDualHaarAt ℚ v) :=
      mulMeasure_restrict_compl_zero ℚ v (selfDualHaarAt ℚ v)
    rw [← Measure.prod_restrict, h]
  rw [hr]
  filter_upwards [ae_restrict_mem (((measurableSet_singleton (0 : v.adicCompletion ℚ)).compl).prod
    ((measurableSet_singleton (0 : v.adicCompletion ℚ)).compl))] with p hp
  exact ⟨hp.1, hp.2⟩

private theorem ae_ne_zero : ∀ᵐ y : v.adicCompletion ℚ ∂(mulMeasure (selfDualHaarAt ℚ v)), y ≠ 0 := by
  have h : (mulMeasure (selfDualHaarAt ℚ v)).restrict {0}ᶜ = mulMeasure (selfDualHaarAt ℚ v) :=
    mulMeasure_restrict_compl_zero ℚ v (selfDualHaarAt ℚ v)
  rw [← h]
  filter_upwards [ae_restrict_mem (measurableSet_singleton (0 : v.adicCompletion ℚ)).compl] with y hy
  exact hy

private theorem measurePreserving_mul_skew :
    MeasurePreserving (fun p : v.adicCompletion ℚ × v.adicCompletion ℚ => (p.1, p.1 * p.2))
      ((mulMeasure (selfDualHaarAt ℚ v)).prod (mulMeasure (selfDualHaarAt ℚ v)))
      ((mulMeasure (selfDualHaarAt ℚ v)).prod (mulMeasure (selfDualHaarAt ℚ v))) := by
  refine (MeasurePreserving.id (mulMeasure (selfDualHaarAt ℚ v))).skew_product
    (g := fun y x : v.adicCompletion ℚ => y * x) measurable_mul ?_
  filter_upwards [ae_ne_zero v] with y hy
  exact map_mul_left_mulMeasure ℚ v (Units.mk0 y hy)

private theorem integrable_uncurry_swap {φ θ : v.adicCompletion ℚ → ℂ} (hφ : IsSchwartzBruhat φ)
    (hθ : IsSchwartzBruhat θ) (η : (v.adicCompletion ℚ)ˣ →* ℂˣ) (hη : IsLocallyConstant η)
    (hu : ‖(η (NumberField.AdelicLevel.uniformizerUnit ℚ v) : ℂ)‖ = 1) (s : ℂ) (hs : 0 < s.re) (hs' : s.re < 1) :
    Integrable (Function.uncurry fun y x : v.adicCompletion ℚ =>
        φ y * ((modulus y : ℝ) : ℂ) * θ (y * x) * (charExt η⁻¹ x * ((modulus x : ℝ) : ℂ) ^ (1 - s)))
      ((mulMeasure (selfDualHaarAt ℚ v)).prod (mulMeasure (selfDualHaarAt ℚ v))) := by
  have hA : Integrable (fun y => φ y * charExt η y * ((modulus y : ℝ) : ℂ) ^ s) (mulMeasure (selfDualHaarAt ℚ v)) :=
    integrable_mul_charExt_mul_cpow v hφ η hη s (strip_condition v hu hs)
  have hB : Integrable (fun z => θ z * charExt η⁻¹ z * ((modulus z : ℝ) : ℂ) ^ (1 - s))
      (mulMeasure (selfDualHaarAt ℚ v)) :=
    integrable_mul_charExt_mul_cpow v hθ η⁻¹ hη.inv (1 - s) (strip_condition_inv v hu hs')
  have hprod := hA.mul_prod hB
  have hcomp := ((measurePreserving_mul_skew v).integrable_comp hprod.aestronglyMeasurable).mpr hprod
  refine hcomp.congr ?_
  filter_upwards [ae_prod_ne_zero v] with p hp
  obtain ⟨hy, hx⟩ := hp
  simp only [Function.comp_apply, Function.uncurry_def]
  have hbase : ((modulus p.1 : ℝ) : ℂ) ≠ 0 := by exact_mod_cast modulus_ne_zero hy
  have h1 : charExt η p.1 * charExt η⁻¹ p.1 = 1 := by
    rw [charExt_of_ne_zero η hy, charExt_of_ne_zero η⁻¹ hy, MonoidHom.inv_apply, Units.val_inv_eq_inv_val]
    exact mul_inv_cancel₀ (Units.ne_zero _)
  have h2 : ((modulus p.1 : ℝ) : ℂ) ^ s * ((modulus p.1 : ℝ) : ℂ) ^ (1 - s) = ((modulus p.1 : ℝ) : ℂ) := by
    rw [← Complex.cpow_add _ _ hbase, add_sub_cancel, Complex.cpow_one]
  rw [charExt_mul ℚ v, modulus_mul, NNReal.coe_mul, Complex.ofReal_mul,
    Complex.mul_cpow_ofReal_nonneg (NNReal.coe_nonneg _) (NNReal.coe_nonneg _)]
  linear_combination
    (φ p.1 * θ (p.1 * p.2) * charExt η⁻¹ p.2 * ((modulus p.2 : ℝ) : ℂ) ^ (1 - s)
        * (((modulus p.1 : ℝ) : ℂ) ^ s * ((modulus p.1 : ℝ) : ℂ) ^ (1 - s))) * h1
      + (φ p.1 * θ (p.1 * p.2) * charExt η⁻¹ p.2 * ((modulus p.2 : ℝ) : ℂ) ^ (1 - s)) * h2

private theorem integrable_kernel {φ θ : v.adicCompletion ℚ → ℂ} (hφ : IsSchwartzBruhat φ) (hθ : IsSchwartzBruhat θ)
    (x : v.adicCompletion ℚ) :
    Integrable (fun p : v.adicCompletion ℚ × v.adicCompletion ℚ =>
        φ p.1 * θ p.2 * (NumberField.StandardAddChar.psiLocal ℚ v (p.1 * p.2 * x) : ℂ))
      ((selfDualHaarAt ℚ v).prod (selfDualHaarAt ℚ v)) := by
  have hφi : Integrable φ (selfDualHaarAt ℚ v) := hφ.1.continuous.integrable_of_hasCompactSupport hφ.2
  have hθi : Integrable θ (selfDualHaarAt ℚ v) := hθ.1.continuous.integrable_of_hasCompactSupport hθ.2
  have hψm : Measurable fun p : v.adicCompletion ℚ × v.adicCompletion ℚ =>
      (NumberField.StandardAddChar.psiLocal ℚ v (p.1 * p.2 * x) : ℂ) :=
    (NumberField.StandardAddChar.continuous_psiLocal ℚ v).measurable.comp
      ((measurable_fst.mul measurable_snd).mul_const x)
  have hmeas : AEStronglyMeasurable (fun p : v.adicCompletion ℚ × v.adicCompletion ℚ =>
      φ p.1 * θ p.2 * (NumberField.StandardAddChar.psiLocal ℚ v (p.1 * p.2 * x) : ℂ))
      ((selfDualHaarAt ℚ v).prod (selfDualHaarAt ℚ v)) :=
    (((hφ.1.continuous.measurable.comp measurable_fst).mul
      (hθ.1.continuous.measurable.comp measurable_snd)).mul hψm).aestronglyMeasurable

  have hKc : IsCompact (tsupport φ ×ˢ tsupport θ) := hφ.2.isCompact.prod hθ.2.isCompact
  obtain ⟨C, hC⟩ := hKc.exists_bound_of_continuousOn
    ((NumberField.StandardAddChar.continuous_psiLocal ℚ v).comp
      ((continuous_fst.mul continuous_snd).mul continuous_const)).continuousOn
  have hg : Integrable (fun p : v.adicCompletion ℚ × v.adicCompletion ℚ => max C 0 * (‖φ p.1‖ * ‖θ p.2‖))
      ((selfDualHaarAt ℚ v).prod (selfDualHaarAt ℚ v)) :=
    (hφi.norm.mul_prod hθi.norm).const_mul _
  refine hg.mono' hmeas (Filter.Eventually.of_forall fun p => ?_)
  by_cases hp : p ∈ tsupport φ ×ˢ tsupport θ
  · have hψ := hC p hp
    rw [norm_mul, norm_mul]
    calc ‖φ p.1‖ * ‖θ p.2‖ * ‖(NumberField.StandardAddChar.psiLocal ℚ v (p.1 * p.2 * x) : ℂ)‖
        ≤ ‖φ p.1‖ * ‖θ p.2‖ * max C 0 :=
          mul_le_mul_of_nonneg_left (le_trans hψ (le_max_left _ _)) (by positivity)
      _ = max C 0 * (‖φ p.1‖ * ‖θ p.2‖) := by ring
  · have h0 : φ p.1 * θ p.2 = 0 := by
      rw [Set.mem_prod, not_and_or] at hp
      rcases hp with h | h
      · rw [image_eq_zero_of_notMem_tsupport h, zero_mul]
      · rw [image_eq_zero_of_notMem_tsupport h, mul_zero]
    rw [h0, zero_mul, norm_zero]
    positivity

private theorem psiLocal_eq_one_of_valued_le (x : v.adicCompletion ℚ) (hx : Valued.v x ≤ WithZero.exp (0 : ℤ)) :
    NumberField.StandardAddChar.psiLocal ℚ v x = 1 := by
  apply psiLocal_eq_one_of_mem_integers ℚ v
  rw [HeightOneSpectrum.mem_adicCompletionIntegers]
  simpa using hx

private theorem exists_valued_le_exp_one_and_psiLocal_ne_one :
    ∃ x : v.adicCompletion ℚ, Valued.v x ≤ WithZero.exp ((0 : ℤ) + 1)
      ∧ NumberField.StandardAddChar.psiLocal ℚ v x ≠ 1 := by
  by_contra hcon
  push Not at hcon

  have hlevel := addCharLevel_psiLocal_rat v
  have hne := psiLocal_ne_one ℚ v
  obtain ⟨x₀, hx₀⟩ : ∃ x₀ : v.adicCompletion ℚ, NumberField.StandardAddChar.psiLocal ℚ v x₀ ≠ 1 := by
    by_contra h
    push Not at h
    exact hne (AddChar.ext _ _ fun x => by simp [h x])
  have hx₀0 : x₀ ≠ 0 := by
    rintro rfl
    exact hx₀ (AddChar.map_zero_eq_one _)
  have hbdd : BddAbove {n : ℤ | ∀ x : v.adicCompletion ℚ, Valued.v x ≤ WithZero.exp n
      → NumberField.StandardAddChar.psiLocal ℚ v x = 1} := by
    refine ⟨WithZero.log (Valued.v x₀), fun n hn => ?_⟩
    by_contra hlt
    push Not at hlt
    apply hx₀
    apply hn
    rw [← WithZero.exp_log ((Valuation.ne_zero_iff Valued.v).mpr hx₀0)]
    exact WithZero.exp_le_exp.mpr hlt.le
  have hmem : (1 : ℤ) ∈ {n : ℤ | ∀ x : v.adicCompletion ℚ, Valued.v x ≤ WithZero.exp n
      → NumberField.StandardAddChar.psiLocal ℚ v x = 1} := fun x hx => hcon x (by simpa using hx)
  have hle : (1 : ℤ) ≤ addCharLevel (NumberField.StandardAddChar.psiLocal ℚ v) := by
    rw [addCharLevel_def]
    exact le_csSup hbdd hmem
  rw [hlevel] at hle
  omega

private theorem selfDualHaarAt_real_integers :
    (selfDualHaarAt ℚ v).real (v.adicCompletionIntegers ℚ : Set (v.adicCompletion ℚ)) = 1 := by
  have h := addCharLevel_psiLocal_rat v
  rw [measureReal_def, selfDualHaarAt, h]
  simp only [Int.cast_zero, neg_zero, zero_div, NNReal.rpow_zero, one_smul]
  rw [← coe_integersPositiveCompacts ℚ v, Measure.addHaarMeasure_self]
  simp

private theorem tateFourier_indicator_integers :
    tateFourier (NumberField.StandardAddChar.psiLocal ℚ v) (selfDualHaarAt ℚ v)
        ((v.adicCompletionIntegers ℚ : Set (v.adicCompletion ℚ)).indicator fun _ => (1 : ℂ))
      = (v.adicCompletionIntegers ℚ : Set (v.adicCompletion ℚ)).indicator fun _ => (1 : ℂ) := by
  have hset : (v.adicCompletionIntegers ℚ : Set (v.adicCompletion ℚ))
      = {x : v.adicCompletion ℚ | Valued.v (x - 0) ≤ WithZero.exp (-(0 : ℤ))} := by
    ext x
    rw [SetLike.mem_coe, HeightOneSpectrum.mem_adicCompletionIntegers]
    simp
  funext y
  have h := tateFourier_indicator_setOf_valued_sub_le ℚ v (selfDualHaarAt ℚ v)
    (NumberField.StandardAddChar.psiLocal ℚ v) 0 (psiLocal_eq_one_of_valued_le v)
    (exists_valued_le_exp_one_and_psiLocal_ne_one v) 0 0 y
  rw [hset, h]
  have hvol : (selfDualHaarAt ℚ v).real {x : v.adicCompletion ℚ | Valued.v x ≤ WithZero.exp (-(0 : ℤ))} = 1 := by
    rw [← selfDualHaarAt_real_integers v]
    congr 1
  rw [hvol, zero_mul, AddChar.map_zero_eq_one]
  simp

private theorem stdTestFunAt_functional_equation_of_unramified (η : (v.adicCompletion ℚ)ˣ →* ℂˣ)
    (hη0 : HasConductorExponentAt ℚ v η 0)
    (hu : ‖(η (NumberField.AdelicLevel.uniformizerUnit ℚ v) : ℂ)‖ = 1) (s : ℂ) (hs : 0 < s.re) (hs' : s.re < 1) :
    localZeta (selfDualHaarAt ℚ v)
          (tateFourier (NumberField.StandardAddChar.psiLocal ℚ v) (selfDualHaarAt ℚ v) (stdTestFunAt ℚ v η)) η⁻¹
          (1 - s) * localLFactorAt ℚ v η s
      = stdRootNumberAt ℚ v η * (Ideal.absNorm v.asIdeal : ℂ) ^ (((0 : ℕ) : ℂ) * (1 / 2 - s)) *
          (localLFactorAt ℚ v η⁻¹ (1 - s) * localZeta (selfDualHaarAt ℚ v) (stdTestFunAt ℚ v η) η s) := by
  have hstd : stdTestFunAt ℚ v η
      = (v.adicCompletionIntegers ℚ : Set (v.adicCompletion ℚ)).indicator fun _ => (1 : ℂ) := by
    rw [stdTestFunAt, if_pos hη0]
  have hstd' : stdTestFunAt ℚ v η⁻¹
      = (v.adicCompletionIntegers ℚ : Set (v.adicCompletion ℚ)).indicator fun _ => (1 : ℂ) := by
    rw [stdTestFunAt, if_pos (hasConductorExponentAt_inv ℚ v hη0)]
  have hF : tateFourier (NumberField.StandardAddChar.psiLocal ℚ v) (selfDualHaarAt ℚ v) (stdTestFunAt ℚ v η)
      = stdTestFunAt ℚ v η⁻¹ := by
    rw [hstd, hstd', tateFourier_indicator_integers]
  have hZ := localZeta_stdTestFunAt_eq_of_unramified ℚ v η s hη0 (strip_condition v hu hs)
  have hZ' := localZeta_stdTestFunAt_eq_of_unramified ℚ v η⁻¹ (1 - s) (hasConductorExponentAt_inv ℚ v hη0)
    (strip_condition_inv v hu hs')
  rw [hF, hZ, hZ', stdRootNumberAt_eq_one_of_unramified v η hη0 hu]
  simp only [Nat.cast_zero, zero_mul, Complex.cpow_zero]
  ring

private theorem stdTestFunAt_functional_equation_of_ramified (η : (v.adicCompletion ℚ)ˣ →* ℂˣ) {a : ℕ} (ha : 1 ≤ a)
    (hη : HasConductorExponentAt ℚ v η a)
    (hu : ‖(η (NumberField.AdelicLevel.uniformizerUnit ℚ v) : ℂ)‖ = 1) (s : ℂ) (hs' : s.re < 1) :
    localZeta (selfDualHaarAt ℚ v)
          (tateFourier (NumberField.StandardAddChar.psiLocal ℚ v) (selfDualHaarAt ℚ v) (stdTestFunAt ℚ v η)) η⁻¹
          (1 - s) * localLFactorAt ℚ v η s
      = stdRootNumberAt ℚ v η * (Ideal.absNorm v.asIdeal : ℂ) ^ ((a : ℂ) * (1 / 2 - s)) *
          (localLFactorAt ℚ v η⁻¹ (1 - s) * localZeta (selfDualHaarAt ℚ v) (stdTestFunAt ℚ v η) η s) := by
  have hq0 : (Ideal.absNorm v.asIdeal : ℂ) ≠ 0 := by
    exact_mod_cast (LaurentLocalZeta.absNorm_ne_zero v)
  have hn0 : ¬ HasConductorExponentAt ℚ v η 0 := not_hasConductorExponentAt_zero_of_pos v ha hη
  have hn0' : ¬ HasConductorExponentAt ℚ v η⁻¹ 0 :=
    not_hasConductorExponentAt_zero_of_pos v ha (hasConductorExponentAt_inv ℚ v hη)
  have hmassval := selfDualHaarAt_real_image_higherUnitsAt ℚ v a ha
  have hmass : (selfDualHaarAt ℚ v).real
      (((↑) : (v.adicCompletion ℚ)ˣ → v.adicCompletion ℚ) '' higherUnitsAt ℚ v a) ≠ 0 := by
    rw [hmassval]
    have hq : (0 : ℝ) < (Ideal.absNorm v.asIdeal : ℝ) := by
      exact_mod_cast Nat.pos_of_ne_zero (LaurentLocalZeta.absNorm_ne_zero v)
    positivity
  have hZ := localZeta_stdTestFunAt_eq_real_image_higherUnitsAt ℚ v η a ha hη s
  rw [localLFactorAt_of_not_hasConductorExponentAt_zero ℚ v hn0,
    localLFactorAt_of_not_hasConductorExponentAt_zero ℚ v hn0', hZ,
    stdRootNumberAt_eq_of_hasConductorExponentAt v η a ha hη hu hmass]
  have hconv : ‖(η⁻¹ (NumberField.AdelicLevel.uniformizerUnit ℚ v) : ℂ)
      * (Ideal.absNorm v.asIdeal : ℂ) ^ (-(1 - s))‖ < 1 := by
    rw [norm_mul, norm_inv_apply_uniformizerUnit ℚ v hu, one_mul,
      Complex.norm_natCast_cpow_of_pos (Nat.pos_of_ne_zero (LaurentLocalZeta.absNorm_ne_zero v))]
    simp only [Complex.neg_re, Complex.sub_re, Complex.one_re]
    exact strip_rpow_lt_one v (by linarith)
  have hFz := localZeta_tateFourier_stdTestFunAt ℚ v η a ha hη s hconv
  rw [hFz, addCharLevel_psiLocal_rat v]
  simp only [zero_add, mul_one, one_mul]

  have hpow : ∀ w : ℂ, ((((Ideal.absNorm v.asIdeal : ℝ) ^ (a : ℤ) : ℝ) : ℂ)) ^ w
      = (Ideal.absNorm v.asIdeal : ℂ) ^ ((a : ℂ) * w) := by
    intro w
    have h := Complex.cpow_mul_ofReal_nonneg (x := (Ideal.absNorm v.asIdeal : ℝ)) (Nat.cast_nonneg _) (a : ℝ) w
    simpa using h.symm
  have hsplit : (Ideal.absNorm v.asIdeal : ℂ) ^ ((a : ℂ) * (1 - s))
      = (Ideal.absNorm v.asIdeal : ℂ) ^ ((a : ℂ) * (1 - (1 / 2 : ℂ)))
        * (Ideal.absNorm v.asIdeal : ℂ) ^ ((a : ℂ) * (1 / 2 - s)) := by
    rw [← Complex.cpow_add _ _ hq0]
    congr 1
    ring
  rw [hpow, hpow, hsplit]
  ring

private theorem localZeta_stdTestFunAt_ne_zero (η : (v.adicCompletion ℚ)ˣ →* ℂˣ) {a : ℕ}
    (hη : HasConductorExponentAt ℚ v η a)
    (hu : ‖(η (NumberField.AdelicLevel.uniformizerUnit ℚ v) : ℂ)‖ = 1) (s : ℂ) (hs : 0 < s.re) :
    localZeta (selfDualHaarAt ℚ v) (stdTestFunAt ℚ v η) η s ≠ 0 := by
  rcases Nat.eq_zero_or_pos a with rfl | ha
  · exact localZeta_stdTestFunAt_ne_zero_of_unramified ℚ v η s hη (strip_condition v hu hs)
  · have hZ := localZeta_stdTestFunAt_eq_real_image_higherUnitsAt ℚ v η a ha hη s
    have hmassval := selfDualHaarAt_real_image_higherUnitsAt ℚ v a ha
    rw [hZ, hmassval]
    have hq : (0 : ℝ) < (Ideal.absNorm v.asIdeal : ℝ) := by
      exact_mod_cast Nat.pos_of_ne_zero (LaurentLocalZeta.absNorm_ne_zero v)
    exact_mod_cast (by positivity : (Ideal.absNorm v.asIdeal : ℝ) ^ (-(a : ℤ))
      * (Ideal.absNorm v.asIdeal : ℝ) ^ (-((addCharLevel (NumberField.StandardAddChar.psiLocal ℚ v) : ℤ) : ℝ) / 2) ≠ 0)

private theorem stdTestFunAt_functional_equation (η : (v.adicCompletion ℚ)ˣ →* ℂˣ) {a : ℕ}
    (hη : HasConductorExponentAt ℚ v η a)
    (hu : ‖(η (NumberField.AdelicLevel.uniformizerUnit ℚ v) : ℂ)‖ = 1) (s : ℂ) (hs : 0 < s.re) (hs' : s.re < 1) :
    localZeta (selfDualHaarAt ℚ v)
          (tateFourier (NumberField.StandardAddChar.psiLocal ℚ v) (selfDualHaarAt ℚ v) (stdTestFunAt ℚ v η)) η⁻¹
          (1 - s) * localLFactorAt ℚ v η s
      = stdRootNumberAt ℚ v η * (Ideal.absNorm v.asIdeal : ℂ) ^ ((a : ℂ) * (1 / 2 - s)) *
          (localLFactorAt ℚ v η⁻¹ (1 - s) * localZeta (selfDualHaarAt ℚ v) (stdTestFunAt ℚ v η) η s) := by
  rcases Nat.eq_zero_or_pos a with rfl | ha
  · exact stdTestFunAt_functional_equation_of_unramified v η hη hu s hs hs'
  · exact stdTestFunAt_functional_equation_of_ramified v η ha hη hu s hs'

private theorem noAtoms_selfDualHaarAt : NullSingletonClass (selfDualHaarAt ℚ v) := by
  have hq1 : (1 : ℝ) < (Ideal.absNorm v.asIdeal : ℝ) := LaurentLocalZeta.one_lt_absNorm_real v
  have hq0 : (0 : ℝ) < (Ideal.absNorm v.asIdeal : ℝ) := zero_lt_one.trans hq1
  have hone : (selfDualHaarAt ℚ v) {(1 : v.adicCompletion ℚ)} = 0 := by
    have h1fin : (selfDualHaarAt ℚ v) {(1 : v.adicCompletion ℚ)} ≠ ⊤ := by
      refine ((measure_mono (Set.singleton_subset_iff.mpr ?_)).trans_lt
        (isCompact_integers v).measure_lt_top).ne
      simp
    have hmassAll : ∀ n : ℕ, ((selfDualHaarAt ℚ v)
        (((↑) : (v.adicCompletion ℚ)ˣ → v.adicCompletion ℚ) '' higherUnitsAt ℚ v (n + 1))).toReal
        = (Ideal.absNorm v.asIdeal : ℝ) ^ (-((n + 1 : ℕ) : ℤ))
          * (Ideal.absNorm v.asIdeal : ℝ)
              ^ (-(addCharLevel (NumberField.StandardAddChar.psiLocal ℚ v) : ℝ) / 2) := by
      intro n
      have h := selfDualHaarAt_real_image_higherUnitsAt ℚ v (n + 1) (by omega)
      rw [measureReal_def] at h
      exact h
    generalize (Ideal.absNorm v.asIdeal : ℝ)
        ^ (-(addCharLevel (NumberField.StandardAddChar.psiLocal ℚ v) : ℝ) / 2) = C at hmassAll
    have hbound : ∀ n : ℕ, ((selfDualHaarAt ℚ v) {(1 : v.adicCompletion ℚ)}).toReal
        ≤ (Ideal.absNorm v.asIdeal : ℝ)⁻¹ ^ (n + 1) * C := by
      intro n
      have ha : 1 ≤ n + 1 := by omega
      have hsub : ({(1 : v.adicCompletion ℚ)} : Set (v.adicCompletion ℚ))
          ⊆ ((↑) : (v.adicCompletion ℚ)ˣ → v.adicCompletion ℚ) '' higherUnitsAt ℚ v (n + 1) :=
        Set.singleton_subset_iff.mpr ⟨1, (mem_higherUnitsAt_iff ℚ v).mpr (by simp), Units.val_one⟩
      have hfin : (selfDualHaarAt ℚ v)
          (((↑) : (v.adicCompletion ℚ)ˣ → v.adicCompletion ℚ) '' higherUnitsAt ℚ v (n + 1)) ≠ ⊤ := by
        rw [image_higherUnitsAt_eq_setOf v ha]
        exact (isClopen_and_isCompact_ball_one v ha).2.measure_lt_top.ne
      calc ((selfDualHaarAt ℚ v) {(1 : v.adicCompletion ℚ)}).toReal
          ≤ ((selfDualHaarAt ℚ v)
              (((↑) : (v.adicCompletion ℚ)ˣ → v.adicCompletion ℚ) '' higherUnitsAt ℚ v (n + 1))).toReal :=
            ENNReal.toReal_mono hfin (measure_mono hsub)
        _ = (Ideal.absNorm v.asIdeal : ℝ)⁻¹ ^ (n + 1) * C := by
            rw [hmassAll n, zpow_neg, zpow_natCast, ← inv_pow]
    have hlim : Filter.Tendsto (fun n : ℕ => (Ideal.absNorm v.asIdeal : ℝ)⁻¹ ^ (n + 1) * C)
        Filter.atTop (nhds 0) := by
      have h := tendsto_pow_atTop_nhds_zero_of_lt_one (inv_nonneg.mpr hq0.le) (inv_lt_one_of_one_lt₀ hq1)
      simpa using (h.comp (Filter.tendsto_add_atTop_nat 1)).mul_const C
    have hle : ((selfDualHaarAt ℚ v) {(1 : v.adicCompletion ℚ)}).toReal ≤ 0 := ge_of_tendsto' hlim hbound
    exact ((ENNReal.toReal_eq_zero_iff _).mp (le_antisymm hle ENNReal.toReal_nonneg)).resolve_right h1fin
  refine ⟨fun x => ?_⟩
  have hpre : (fun h : v.adicCompletion ℚ => x - 1 + h) ⁻¹' {x} = {(1 : v.adicCompletion ℚ)} := by
    ext h
    simp only [Set.mem_preimage, Set.mem_singleton_iff]
    constructor
    · intro hh
      linear_combination hh
    · rintro rfl
      ring
  rw [← measure_preimage_add (selfDualHaarAt ℚ v) (x - 1) {x}, hpre, hone]

end TateFunctionalEquationAtRat

private theorem localZeta_tateFourier_mul_localLFactorAt_eq_of_isSchwartzBruhat
    (η : (v.adicCompletion ℚ)ˣ →* ℂˣ) (hη : IsLocallyConstant η)
    (hη1 : ‖((η (NumberField.AdelicLevel.uniformizerUnit ℚ v) : ℂˣ) : ℂ)‖ = 1)
    (a : ℕ) (ha : HasConductorExponentAt ℚ v η a)
    (f : v.adicCompletion ℚ → ℂ) (hf : IsSchwartzBruhat f)
    (s : ℂ) (hs : 0 < s.re) (hs' : s.re < 1) :
    localZeta (selfDualHaarAt ℚ v)
          (tateFourier (NumberField.StandardAddChar.psiLocal ℚ v) (selfDualHaarAt ℚ v) f) η⁻¹ (1 - s) *
        localLFactorAt ℚ v η s =
      stdRootNumberAt ℚ v η * (Ideal.absNorm v.asIdeal : ℂ) ^ ((a : ℂ) * (1 / 2 - s)) *
        (localLFactorAt ℚ v η⁻¹ (1 - s) * localZeta (selfDualHaarAt ℚ v) f η s) := by
  haveI : BorelSpace (v.adicCompletion ℚ) := borelSpace_localBorel ℚ v
  haveI : (selfDualHaarAt ℚ v).IsAddHaarMeasure := isAddHaarMeasure_selfDualHaarAt ℚ v
  haveI : (selfDualHaarAt ℚ v).Regular := regular_selfDualHaarAt ℚ v
  haveI : SFinite (selfDualHaarAt ℚ v) := sFinite_selfDualHaarAt ℚ v
  haveI : MeasurableSingletonClass (v.adicCompletion ℚ) := measurableSingletonClass_adicCompletion ℚ v
  haveI : NullSingletonClass (selfDualHaarAt ℚ v) := noAtoms_selfDualHaarAt v
  have hf₀ : IsSchwartzBruhat (stdTestFunAt ℚ v η) := isSchwartzBruhat_stdTestFunAt v ha
  have hFf : IsSchwartzBruhat (tateFourier (NumberField.StandardAddChar.psiLocal ℚ v) (selfDualHaarAt ℚ v) f) :=
    isSchwartzBruhat_tateFourier ℚ v (selfDualHaarAt ℚ v) (NumberField.StandardAddChar.psiLocal ℚ v) 0
      (psiLocal_eq_one_of_valued_le v) (exists_valued_le_exp_one_and_psiLocal_ne_one v) f hf
  have hFf₀ : IsSchwartzBruhat
      (tateFourier (NumberField.StandardAddChar.psiLocal ℚ v) (selfDualHaarAt ℚ v) (stdTestFunAt ℚ v η)) :=
    isSchwartzBruhat_tateFourier ℚ v (selfDualHaarAt ℚ v) (NumberField.StandardAddChar.psiLocal ℚ v) 0
      (psiLocal_eq_one_of_valued_le v) (exists_valued_le_exp_one_and_psiLocal_ne_one v) _ hf₀
  have hm : AEMeasurable (fun x : v.adicCompletion ℚ => (modulus x)⁻¹) ((selfDualHaarAt ℚ v).restrict {0}ᶜ) :=
    ((measurable_coe_nnreal_real_iff.mp (LaurentLocalZeta.measurable_modulus v)).inv).aemeasurable
  have hsym := localZeta_fourier_mul_symm (selfDualHaarAt ℚ v) (NumberField.StandardAddChar.psiLocal ℚ v) f
    (stdTestFunAt ℚ v η) η s hm
    (integrable_uncurry_swap v hf₀ hFf η hη hη1 s hs hs')
    (integrable_uncurry_swap v hf hFf₀ η hη hη1 s hs hs')
    (fun x _ => integrable_kernel v hf hf₀ x)
  have hstd := stdTestFunAt_functional_equation v η ha hη1 s hs hs'
  have hne := localZeta_stdTestFunAt_ne_zero v η ha hη1 s hs
  apply mul_right_cancel₀ hne
  calc localZeta (selfDualHaarAt ℚ v)
          (tateFourier (NumberField.StandardAddChar.psiLocal ℚ v) (selfDualHaarAt ℚ v) f) η⁻¹ (1 - s)
          * localLFactorAt ℚ v η s * localZeta (selfDualHaarAt ℚ v) (stdTestFunAt ℚ v η) η s
      = localZeta (selfDualHaarAt ℚ v)
          (tateFourier (NumberField.StandardAddChar.psiLocal ℚ v) (selfDualHaarAt ℚ v) (stdTestFunAt ℚ v η)) η⁻¹
          (1 - s) * localLFactorAt ℚ v η s * localZeta (selfDualHaarAt ℚ v) f η s := by
          linear_combination (localLFactorAt ℚ v η s) * hsym
    _ = stdRootNumberAt ℚ v η * (Ideal.absNorm v.asIdeal : ℂ) ^ ((a : ℂ) * (1 / 2 - s)) *
          (localLFactorAt ℚ v η⁻¹ (1 - s) * localZeta (selfDualHaarAt ℚ v) f η s)
          * localZeta (selfDualHaarAt ℚ v) (stdTestFunAt ℚ v η) η s := by
          linear_combination (localZeta (selfDualHaarAt ℚ v) f η s) * hstd

end LanglandsTunnell.CubicInduction

open LanglandsTunnell.CubicInduction in
theorem solution
    (v : HeightOneSpectrum (𝓞 ℚ))
    (η : (v.adicCompletion ℚ)ˣ →* ℂˣ) (hη : IsLocallyConstant η)
    (hη1 : ‖((η (NumberField.AdelicLevel.uniformizerUnit ℚ v) : ℂˣ) : ℂ)‖ = 1)
    (a : ℕ) (ha : HasConductorExponentAt ℚ v η a)
    (f : v.adicCompletion ℚ → ℂ) (hf : IsSchwartzBruhat f)
    (s : ℂ) (hs : 0 < s.re) (hs' : s.re < 1) :
    localZeta (selfDualHaarAt ℚ v)
          (tateFourier (NumberField.StandardAddChar.psiLocal ℚ v) (selfDualHaarAt ℚ v) f) η⁻¹ (1 - s) *
        localLFactorAt ℚ v η s =
      stdRootNumberAt ℚ v η * (Ideal.absNorm v.asIdeal : ℂ) ^ ((a : ℂ) * (1 / 2 - s)) *
        (localLFactorAt ℚ v η⁻¹ (1 - s) * localZeta (selfDualHaarAt ℚ v) f η s) := by
  exact localZeta_tateFourier_mul_localLFactorAt_eq_of_isSchwartzBruhat v η hη hη1 a ha f hf s hs hs'

end S_LanglandsTunnell_CubicInduction_localZeta_tateFourier_mul_localLFactorAt_eq
end P2MW
export P2MW.S_LanglandsTunnell_CubicInduction_localZeta_tateFourier_mul_localLFactorAt_eq (solution)
