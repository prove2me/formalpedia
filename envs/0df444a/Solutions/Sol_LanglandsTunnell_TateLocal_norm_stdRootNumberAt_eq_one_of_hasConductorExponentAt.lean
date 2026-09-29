-- Prove2me | solution 1 for LanglandsTunnell.TateLocal.norm_stdRootNumberAt_eq_one_of_hasConductorExponentAt
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:08.670037+00:00
-- url     : https://prove2.me/submissions/3f5e5cb0-9683-50c4-903b-9f44b4b35489

import Mathlib
import Definitions.Def_LanglandsTunnell_StandardLocalConstantsAt
import Theorems.Thm_LanglandsTunnell_TateLocal_stdRootNumberAt_mul_stdRootNumberAt_inv_eq_apply_neg_one
import Theorems.Thm_LanglandsTunnell_TateLocal_stdRootNumberAt_mul_of_hasConductorExponentAt_zero
import Theorems.Thm_LanglandsTunnell_TateLocal_stdRootNumberAt_one
import Theorems.Thm_LanglandsTunnell_TateLocal_psiLocal_ne_one
import Theorems.Thm_LanglandsTunnell_TateLocal_modulus_adicCompletion_eq_nnnorm
import Theorems.Thm_NumberField_AdelicFourier_norm_apply_eq_one_of_isGlobalAddChar
import Theorems.Thm_NumberField_StandardAddChar_isGlobalAddChar_stdAddChar
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_LanglandsTunnell_TateLocal_norm_stdRootNumberAt_eq_one_of_hasConductorExponentAt
p2m_attr_erase "instance" "instFiniteResidueFieldAdicCompletionRingOfIntegersWithZeroMultiplicativeInt_definitions NumberField.instCompactSpaceAdicCompletionIntegers Rat.adicCompletion.locallyCompactSpace NumberField.instFiniteResidueFieldAdicCompletionIntegers instWeaklyLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions instCountableOfNumberField_definitions IsDedekindDomain.HeightOneSpectrum.Extension.instAlgebraSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersValEqUnder IsDedekindDomain.HeightOneSpectrum.Extension.instAlgebraSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersValEqUnder_1 IsDedekindDomain.HeightOneSpectrum.instMulActionHomClassAlgHomTensorProductAdicCompletionForallValEqUnder_definitions IsDedekindDomain.HeightOneSpectrum.Extension.instAlgebraAdicCompletionValEqUnder IsDedekindDomain.HeightOneSpectrum.adicCompletion.instFiniteForallValEqUnderOfFiniteDimensional_definitions IsDedekindDomain.HeightOneSpectrum.instIsBiscalarSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersTensorProductCoeAlgHomTensorAdicCompletionIntegersTo IsDedekindDomain.HeightOneSpectrum.Extension.instContinuousSMulAdicCompletionValEqUnder IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsModuleTopology IsDedekindDomain.HeightOneSpectrum.Extension.instFiniteSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersValEqUnderOfFiniteDimensional IsDedekindDomain.HeightOneSpectrum.adicCompletion.instFiniteValEqUnderOfFiniteDimensional_definitions instIsBiscalarTensorProductCoeAlgHomBaseChange_of_algebraMap IsDedekindDomain.HeightOneSpectrum.instIsScalarTowerSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersValEqUnder_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsModuleTopologyPi Submodule.instIsTopologicalModuleSubtypeMem Pi.instTopologicalModule IsTopologicalModule.toContinuousSMul IsTopologicalModule.toContinuousAdd instFunLike SemialgHomClass.toSemilinearMapClass instCoeTCSemialgHom SemialgHomClass.toRingHomClass SemialgHomClass.instSemialgHom"
p2m_attr_erase "simp" "SemialgHom.baseChange_of_algebraMap_tmul_left SemialgHom.baseChangeRightOfAlgebraMap_apply Pi.semialgHomPi_apply Pi.semialgHom_apply Module.Basis.rightBaseChange_apply LinearEquiv.coe_mulLeft LinearEquiv.coe_mulRight WithVal.semialgebraMap_toFun_ofVal Module.Basis.rightBaseChange_repr IsDedekindDomain.HeightOneSpectrum.adicCompletionIntegers.tensorCoe_tmul IsDedekindDomain.HeightOneSpectrum.tensorAdicCompletionIntegersTo_tmul SemialgHom.baseChangeRightOfAlgebraMap_coe IsDedekindDomain.HeightOneSpectrum.adicCompletion.integerBaseChangeLinearEquiv_tmul_apply SemialgHom.baseChange_of_algebraMap_tmul_right IsLocalization.map_moduleTensorEquiv_symm_tmul IsLocalization.leftModuleTensorEquiv_apply IsLocalization.moduleLid_symm_apply IsLocalization.leftModuleTensorEquiv_symm_apply IsLocalization.map_moduleTensorEquiv_tmul IsModuleTopology.continuousLinearEquiv_apply AlgEquiv.extendScalars_symm_apply IsModuleTopology.Module.Basis.equivFun_homeo_symm_apply IsModuleTopology.Module.Basis.equivFun_homeo_apply IsModuleTopology.continuousAlgEquivOfIsBiscalar_apply AlgEquiv.extendScalars_apply IsModuleTopology.continuousLinearEquiv_symm_apply SemialgHom.restrictScalars_toFun SemialgHom.mk.sizeOf_spec SemialgHom.mk.injEq SemialgHom.coe_coe coe_mk TensorProduct.RightActions.smul_def TensorProduct.RightActions.Module.TensorProduct.comm_symm_apply_tmul TensorProduct.RightActions.LinearMap.baseChange_id TensorProduct.RightActions.algebraMap_eval TensorProduct.RightActions.Module.TensorProduct.comm_apply_tmul TensorProduct.RightActions.Algebra.TensorProduct.comm_symm_apply_tmul TensorProduct.RightActions.Algebra.TensorProduct.comm_apply_tmul"

set_option autoImplicit false

noncomputable section

open NumberField NumberField.StandardAddChar NumberField.AdelicLevel IsDedekindDomain LanglandsTunnell.TateLocal
open MeasureTheory Complex
open scoped ComplexConjugate NNReal ENNReal

namespace R4H2

variable (K : Type) [Field K] [NumberField K] (v : HeightOneSpectrum (𝓞 K))

local instance instLC : LocallyCompactSpace (v.adicCompletion K) := inferInstance

theorem case_zero (χ : (v.adicCompletion K)ˣ →* ℂˣ) (hχ : HasConductorExponentAt K v χ 0)
    (hu : ∀ x : (v.adicCompletion K)ˣ, ‖((χ x : ℂˣ) : ℂ)‖ = 1) : ‖stdRootNumberAt K v χ‖ = 1 := by
  have h1 : HasConductorExponentAt K v (1 : (v.adicCompletion K)ˣ →* ℂˣ) 0 := hasConductorExponentAt_one_zero K v
  have hψ := LanglandsTunnell.TateLocal.psiLocal_ne_one K v
  have h := LanglandsTunnell.TateLocal.stdRootNumberAt_mul_of_hasConductorExponentAt_zero K v 1 χ 0 h1 hχ
    (by simp) (hu _) hψ
  have h1χ : (1 : (v.adicCompletion K)ˣ →* ℂˣ) * χ = χ := by ext; simp
  rw [h1χ, LanglandsTunnell.TateLocal.stdRootNumberAt_one, mul_one] at h
  rw [h, norm_zpow, hu, one_zpow]

theorem hasConductorExponentAt_inv {χ : (v.adicCompletion K)ˣ →* ℂˣ} {a : ℕ}
    (hχ : HasConductorExponentAt K v χ a) : HasConductorExponentAt K v χ⁻¹ a := by
  refine ⟨fun u hu => ?_, fun m hm => ?_⟩
  · rw [MonoidHom.inv_apply, hχ.1 u hu, inv_one]
  · obtain ⟨u, hu, hne⟩ := hχ.2 m hm
    exact ⟨u, hu, fun h => hne (by rwa [MonoidHom.inv_apply, inv_eq_one] at h)⟩

theorem not_hasConductorExponentAt_zero {χ : (v.adicCompletion K)ˣ →* ℂˣ} {a : ℕ} (ha : 1 ≤ a)
    (hχ : HasConductorExponentAt K v χ a) : ¬ HasConductorExponentAt K v χ 0 := fun h0 => by
  have := hasConductorExponentAt_unique K v hχ h0
  omega

theorem stdTestFunAt_eq {χ : (v.adicCompletion K)ˣ →* ℂˣ} {a : ℕ} (ha : 1 ≤ a)
    (hχ : HasConductorExponentAt K v χ a) :
    stdTestFunAt K v χ =
      (((↑) : (v.adicCompletion K)ˣ → v.adicCompletion K) '' higherUnitsAt K v a).indicator fun _ => (1 : ℂ) := by
  unfold stdTestFunAt
  rw [if_neg (not_hasConductorExponentAt_zero K v ha hχ), conductorExponentAt_eq_of_hasConductorExponentAt K v hχ]

theorem norm_psiLocal (x : v.adicCompletion K) : ‖psiLocal K v x‖ = 1 := by
  rw [psiLocal_apply]
  exact NumberField.AdelicFourier.norm_apply_eq_one_of_isGlobalAddChar K
    (NumberField.StandardAddChar.isGlobalAddChar_stdAddChar K) _

theorem conj_psiLocal (x : v.adicCompletion K) : conj (psiLocal K v x) = psiLocal K v (-x) := by
  rw [AddChar.map_neg_eq_inv, Complex.inv_eq_conj (norm_psiLocal K v x)]

theorem modulus_neg (x : v.adicCompletion K) : modulus (-x) = modulus x := by
  rw [LanglandsTunnell.TateLocal.modulus_adicCompletion_eq_nnnorm K v,
    LanglandsTunnell.TateLocal.modulus_adicCompletion_eq_nnnorm K v, nnnorm_neg]

theorem continuous_modulus : Continuous (fun x : v.adicCompletion K => modulus x) := by
  have : (fun x : v.adicCompletion K => modulus x) = fun x => ‖x‖₊ :=
    funext fun x => LanglandsTunnell.TateLocal.modulus_adicCompletion_eq_nnnorm K v x
  rw [this]; exact continuous_nnnorm

theorem conj_modulus_cpow (x : v.adicCompletion K) (e : ℂ) (he : conj e = e) :
    conj ((((modulus x : ℝ≥0) : ℝ) : ℂ) ^ e) = (((modulus x : ℝ≥0) : ℝ) : ℂ) ^ e := by
  have harg : ((((modulus x : ℝ≥0) : ℝ) : ℂ)).arg ≠ Real.pi := by
    rw [Complex.arg_ofReal_of_nonneg (NNReal.coe_nonneg _)]; exact Real.pi_ne_zero.symm
  have h := Complex.cpow_conj (((modulus x : ℝ≥0) : ℝ) : ℂ) e harg
  rw [Complex.conj_ofReal, he] at h

  exact h.symm

theorem conj_charExt_inv {χ : (v.adicCompletion K)ˣ →* ℂˣ}
    (hu : ∀ x : (v.adicCompletion K)ˣ, ‖((χ x : ℂˣ) : ℂ)‖ = 1) (y : v.adicCompletion K) :
    conj (charExt χ⁻¹ y) = charExt χ y := by
  by_cases hy : y = 0
  · subst hy; simp
  · rw [charExt_of_ne_zero _ hy, charExt_of_ne_zero _ hy, MonoidHom.inv_apply, Units.val_inv_eq_inv_val,
      Complex.inv_eq_conj (hu _), Complex.conj_conj]

theorem charExt_neg (χ : (v.adicCompletion K)ˣ →* ℂˣ) (y : v.adicCompletion K) :
    charExt χ (-y) = ((χ (-1) : ℂˣ) : ℂ) * charExt χ y := by
  by_cases hy : y = 0
  · subst hy; simp
  · have hy' : -y ≠ 0 := neg_ne_zero.mpr hy
    rw [charExt_of_ne_zero _ hy, charExt_of_ne_zero _ hy']
    have : Units.mk0 (-y) hy' = -1 * Units.mk0 y hy := by
      ext; simp
    rw [this, map_mul, Units.val_mul]

section measure

@[reducible] local instance instMS : MeasurableSpace (v.adicCompletion K) := localBorel K v
local instance instBS : BorelSpace (v.adicCompletion K) := borelSpace_localBorel K v

theorem measurable_modulus : Measurable (fun x : v.adicCompletion K => modulus x) :=
  (continuous_modulus K v).measurable

scoped instance isNegInvariant_selfDualHaarAt : (selfDualHaarAt K v).IsNegInvariant := by
  have hH : (Measure.addHaarMeasure (integersPositiveCompacts K v)).IsNegInvariant :=
    Measure.IsAddHaarMeasure.isNegInvariant_of_regular _
  constructor
  show Measure.map Neg.neg (selfDualHaarAt K v) = selfDualHaarAt K v
  unfold selfDualHaarAt
  rw [Measure.map_smul]
  congr 1
  exact hH.neg_eq_self

theorem integral_mulMeasure_comp_neg (g : v.adicCompletion K → ℂ) :
    ∫ y, g (-y) ∂(mulMeasure (selfDualHaarAt K v)) = ∫ y, g y ∂(mulMeasure (selfDualHaarAt K v)) := by
  set μ := selfDualHaarAt K v with hμ
  set d : v.adicCompletion K → ℝ≥0∞ := fun x => ((modulus x : ℝ≥0∞))⁻¹ with hd
  have hdm : Measurable d := (measurable_modulus K v).coe_nnreal_ennreal.inv
  have hS : MeasurableSet ({0}ᶜ : Set (v.adicCompletion K)) := (measurableSet_singleton 0).compl
  have hfin : ∀ᵐ x ∂(μ.restrict {0}ᶜ), d x < ∞ := by
    rw [ae_restrict_iff' hS]
    refine Filter.Eventually.of_forall fun x hx => ?_
    simp only [hd, ENNReal.inv_lt_top, ENNReal.coe_pos]
    exact modulus_pos hx
  have hrepr : ∀ h : v.adicCompletion K → ℂ,
      ∫ y, h y ∂(mulMeasure μ) = ∫ y, ({0}ᶜ : Set (v.adicCompletion K)).indicator (fun x => (d x).toReal • h x) y ∂μ := by
    intro h
    show ∫ y, h y ∂((μ.restrict {0}ᶜ).withDensity d) = _
    rw [integral_withDensity_eq_integral_toReal_smul hdm hfin, integral_indicator hS]
  rw [hrepr, hrepr]
  have hpt : (fun y => ({0}ᶜ : Set (v.adicCompletion K)).indicator (fun x => (d x).toReal • g (-x)) y) =
      fun y => (({0}ᶜ : Set (v.adicCompletion K)).indicator (fun x => (d x).toReal • g x)) (-y) := by
    funext y
    by_cases hy : y = 0
    · subst hy; simp
    · have hy' : -y ≠ 0 := neg_ne_zero.mpr hy
      rw [Set.indicator_of_mem (show y ∈ ({0}ᶜ : Set _) from hy),
        Set.indicator_of_mem (show -y ∈ ({0}ᶜ : Set _) from hy')]
      simp only [hd, modulus_neg]
  rw [hpt]
  exact integral_neg_eq_self _ μ

theorem conj_tateFourier (f : v.adicCompletion K → ℂ) (hf : ∀ x, conj (f x) = f x) (y : v.adicCompletion K) :
    conj (tateFourier (psiLocal K v) (selfDualHaarAt K v) f y) =
      tateFourier (psiLocal K v) (selfDualHaarAt K v) f (-y) := by
  unfold tateFourier
  rw [← integral_conj]
  refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
  simp only [map_mul, hf x, conj_psiLocal, mul_neg]

end measure

section ramified

@[reducible] local instance instMS' : MeasurableSpace (v.adicCompletion K) := localBorel K v
local instance instBS' : BorelSpace (v.adicCompletion K) := borelSpace_localBorel K v

theorem conj_half : conj ((1 : ℂ) / 2) = 1 / 2 := by
  rw [map_div₀, map_one, map_ofNat]

theorem conj_one_sub_half : conj ((1 : ℂ) - 1 / 2) = 1 - 1 / 2 := by
  rw [map_sub, map_one, conj_half]

theorem stdRootNumberAt_eq_localGammaAt (χ : (v.adicCompletion K)ˣ →* ℂˣ) {a : ℕ} (ha : 1 ≤ a)
    (hχ : HasConductorExponentAt K v χ a) :
    stdRootNumberAt K v χ = localGammaAt (selfDualHaarAt K v) (psiLocal K v)
      ((((↑) : (v.adicCompletion K)ˣ → v.adicCompletion K) '' higherUnitsAt K v a).indicator fun _ => (1 : ℂ))
      χ (1 / 2) := by
  rw [stdRootNumberAt_def]
  show localEpsilonAt K v (selfDualHaarAt K v) (psiLocal K v) (stdTestFunAt K v χ) χ (1 / 2) = _
  rw [localEpsilonAt_of_not_hasConductorExponentAt_zero K v _ _ _ (not_hasConductorExponentAt_zero K v ha hχ),
    stdTestFunAt_eq K v ha hχ]

theorem conj_symmetry (χ : (v.adicCompletion K)ˣ →* ℂˣ) {a : ℕ} (ha : 1 ≤ a)
    (hχ : HasConductorExponentAt K v χ a) (hu : ∀ x : (v.adicCompletion K)ˣ, ‖((χ x : ℂˣ) : ℂ)‖ = 1) :
    stdRootNumberAt K v χ⁻¹ = ((χ (-1) : ℂˣ) : ℂ) * conj (stdRootNumberAt K v χ) := by
  set U : Set (v.adicCompletion K) := ((↑) : (v.adicCompletion K)ˣ → v.adicCompletion K) '' higherUnitsAt K v a
    with hU
  set f : v.adicCompletion K → ℂ := U.indicator fun _ => (1 : ℂ) with hf
  set η : ℂ := ((χ (-1) : ℂˣ) : ℂ) with hη
  have hχ' : HasConductorExponentAt K v χ⁻¹ a := hasConductorExponentAt_inv K v hχ
  have hinv : χ⁻¹⁻¹ = χ := by ext; simp
  rw [stdRootNumberAt_eq_localGammaAt K v χ ha hχ, stdRootNumberAt_eq_localGammaAt K v χ⁻¹ ha hχ']
  unfold localGammaAt
  rw [hinv]

  have hfreal : ∀ x, conj (f x) = f x := fun x => by
    by_cases hx : x ∈ U
    · rw [hf, Set.indicator_of_mem hx, map_one]
    · rw [hf, Set.indicator_of_notMem hx, map_zero]

  have hfU : ∀ {x}, x ∉ U → f x = 0 := fun hx => Set.indicator_of_notMem hx _
  have hχU : ∀ {x} (_ : x ∈ U), charExt χ x = 1 ∧ charExt χ⁻¹ x = 1 := by
    rintro x ⟨u, hu', rfl⟩
    refine ⟨?_, ?_⟩
    · rw [charExt_coe_units, hχ.1 u hu', Units.val_one]
    · rw [charExt_coe_units, hχ'.1 u hu', Units.val_one]

  have hD : localZeta (selfDualHaarAt K v) f χ⁻¹ (1 / 2) = localZeta (selfDualHaarAt K v) f χ (1 / 2) := by
    unfold localZeta
    refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
    show f x * charExt χ⁻¹ x * _ = f x * charExt χ x * _
    by_cases hx : x ∈ U
    · rw [(hχU hx).1, (hχU hx).2]
    · rw [hfU hx, zero_mul, zero_mul, zero_mul, zero_mul]

  have hDreal : conj (localZeta (selfDualHaarAt K v) f χ (1 / 2)) = localZeta (selfDualHaarAt K v) f χ (1 / 2) := by
    unfold localZeta
    rw [← integral_conj]
    refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
    show conj (f x * charExt χ x * _) = f x * charExt χ x * _
    by_cases hx : x ∈ U
    · rw [(hχU hx).1, map_mul, map_mul, hfreal x, map_one, conj_modulus_cpow K v x _ conj_half]
    · rw [hfU hx, zero_mul, zero_mul, map_zero]

  have hN : conj (localZeta (selfDualHaarAt K v) (tateFourier (psiLocal K v) (selfDualHaarAt K v) f) χ⁻¹ (1 - 1 / 2)) =
      η * localZeta (selfDualHaarAt K v) (tateFourier (psiLocal K v) (selfDualHaarAt K v) f) χ (1 - 1 / 2) := by
    unfold localZeta
    rw [← integral_conj]
    have hpt : (fun y => conj (tateFourier (psiLocal K v) (selfDualHaarAt K v) f y * charExt χ⁻¹ y *
          (((modulus y : ℝ≥0) : ℝ) : ℂ) ^ ((1 : ℂ) - 1 / 2))) =
        fun y => (fun z => tateFourier (psiLocal K v) (selfDualHaarAt K v) f z * charExt χ (-z) *
          (((modulus (-z) : ℝ≥0) : ℝ) : ℂ) ^ ((1 : ℂ) - 1 / 2)) (-y) := by
      funext y
      show _ = tateFourier (psiLocal K v) (selfDualHaarAt K v) f (-y) * charExt χ (- -y) *
          (((modulus (- -y) : ℝ≥0) : ℝ) : ℂ) ^ ((1 : ℂ) - 1 / 2)
      rw [neg_neg, map_mul, map_mul, conj_tateFourier K v f hfreal, conj_charExt_inv K v hu,
        conj_modulus_cpow K v y _ conj_one_sub_half]
    have hcv := integral_mulMeasure_comp_neg K v (fun z => tateFourier (psiLocal K v) (selfDualHaarAt K v) f z *
      charExt χ (-z) * (((modulus (-z) : ℝ≥0) : ℝ) : ℂ) ^ ((1 : ℂ) - 1 / 2))
    rw [hpt, hcv, ← integral_const_mul]
    refine integral_congr_ae (Filter.Eventually.of_forall fun z => ?_)
    show tateFourier (psiLocal K v) (selfDualHaarAt K v) f z * charExt χ (-z) *
          (((modulus (-z) : ℝ≥0) : ℝ) : ℂ) ^ ((1 : ℂ) - 1 / 2) = _
    rw [charExt_neg K v χ z, modulus_neg K v z]
    ring
  have hη2 : η * η = 1 := by
    rw [hη, ← Units.val_mul, ← map_mul]
    have : (-1 : (v.adicCompletion K)ˣ) * -1 = 1 := by rw [neg_one_mul, neg_neg]
    rw [this, map_one, Units.val_one]
  rw [map_div₀, hN, hD, hDreal, ← mul_div_assoc, ← mul_assoc, hη2, one_mul]

theorem case_pos (χ : (v.adicCompletion K)ˣ →* ℂˣ) {a : ℕ} (ha : 1 ≤ a)
    (hχ : HasConductorExponentAt K v χ a) (hu : ∀ x : (v.adicCompletion K)ˣ, ‖((χ x : ℂˣ) : ℂ)‖ = 1) :
    ‖stdRootNumberAt K v χ‖ = 1 := by
  set ε := stdRootNumberAt K v χ with hε
  set η : ℂ := ((χ (-1) : ℂˣ) : ℂ) with hη
  have hFE := LanglandsTunnell.TateLocal.stdRootNumberAt_mul_stdRootNumberAt_inv_eq_apply_neg_one K v χ a ha hχ
    (hu _)
  rw [conj_symmetry K v χ ha hχ hu] at hFE

  have hη0 : η ≠ 0 := by rw [hη]; exact Units.ne_zero _
  have hkey : ε * conj ε = 1 := by
    have h2 : η * (ε * conj ε) = η * 1 := by rw [mul_one]; linear_combination hFE
    exact mul_left_cancel₀ hη0 h2
  have hsq : ‖ε‖ ^ 2 = 1 := by
    have := congrArg Complex.re hkey
    rw [Complex.mul_conj, Complex.ofReal_re, Complex.normSq_eq_norm_sq, Complex.one_re] at this
    exact this
  have h0 : 0 ≤ ‖ε‖ := norm_nonneg _
  nlinarith [hsq, h0]

end ramified

theorem main (χ : (v.adicCompletion K)ˣ →* ℂˣ) (a : ℕ) (hχ : HasConductorExponentAt K v χ a)
    (hu : ∀ x : (v.adicCompletion K)ˣ, ‖((χ x : ℂˣ) : ℂ)‖ = 1) : ‖stdRootNumberAt K v χ‖ = 1 := by
  rcases Nat.eq_zero_or_pos a with h0 | hpos
  · subst h0; exact case_zero K v χ hχ hu
  · exact case_pos K v χ hpos hχ hu

end R4H2
p2m_reactivate "P2MW.S_LanglandsTunnell_TateLocal_norm_stdRootNumberAt_eq_one_of_hasConductorExponentAt.R4H2"

end
p2m_reactivate "P2MW.S_LanglandsTunnell_TateLocal_norm_stdRootNumberAt_eq_one_of_hasConductorExponentAt.R4H2"

open NumberField NumberField.StandardAddChar NumberField.AdelicLevel IsDedekindDomain LanglandsTunnell.TateLocal in
theorem solution
    (K : Type) [Field K] [NumberField K] (v : HeightOneSpectrum (𝓞 K))
    (χ : (v.adicCompletion K)ˣ →* ℂˣ) (a : ℕ) (hχ : HasConductorExponentAt K v χ a)
    (hu : ∀ x : (v.adicCompletion K)ˣ, ‖((χ x : ℂˣ) : ℂ)‖ = 1) :
    ‖stdRootNumberAt K v χ‖ = 1 :=
  R4H2.main K v χ a hχ hu

end S_LanglandsTunnell_TateLocal_norm_stdRootNumberAt_eq_one_of_hasConductorExponentAt
end P2MW
export P2MW.S_LanglandsTunnell_TateLocal_norm_stdRootNumberAt_eq_one_of_hasConductorExponentAt (solution)
