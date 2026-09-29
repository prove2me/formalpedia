-- Prove2me | solution 1 for LanglandsTunnell.TateLocal.norm_stdRootNumberAt_eq_one
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:08.670037+00:00
-- url     : https://prove2.me/submissions/fc97c554-b4d5-5cc5-acb3-c6933a62df64

import Definitions.Def_LanglandsTunnell_StandardLocalConstantsAt
import Theorems.Thm_LanglandsTunnell_TateLocal_stdRootNumberAt_mul_stdRootNumberAt_inv_eq_apply_neg_one
import Theorems.Thm_LanglandsTunnell_TateLocal_localZeta_tateFourier_stdTestFunAt
import Theorems.Thm_LanglandsTunnell_TateLocal_localZeta_stdTestFunAt_eq_real_image_higherUnitsAt
import Theorems.Thm_LanglandsTunnell_TateLocal_selfDualHaarAt_real_image_higherUnitsAt
import Theorems.Thm_NumberField_AdelicFourier_norm_apply_eq_one_of_isGlobalAddChar
import Theorems.Thm_NumberField_StandardAddChar_isGlobalAddChar_stdAddChar
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_LanglandsTunnell_TateLocal_norm_stdRootNumberAt_eq_one
p2m_attr_erase "instance" "instFiniteResidueFieldAdicCompletionRingOfIntegersWithZeroMultiplicativeInt_definitions NumberField.instCompactSpaceAdicCompletionIntegers Rat.adicCompletion.locallyCompactSpace NumberField.instFiniteResidueFieldAdicCompletionIntegers instWeaklyLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions instCountableOfNumberField_definitions IsDedekindDomain.HeightOneSpectrum.Extension.instAlgebraSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersValEqUnder IsDedekindDomain.HeightOneSpectrum.Extension.instAlgebraSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersValEqUnder_1 IsDedekindDomain.HeightOneSpectrum.instMulActionHomClassAlgHomTensorProductAdicCompletionForallValEqUnder_definitions IsDedekindDomain.HeightOneSpectrum.Extension.instAlgebraAdicCompletionValEqUnder IsDedekindDomain.HeightOneSpectrum.adicCompletion.instFiniteForallValEqUnderOfFiniteDimensional_definitions IsDedekindDomain.HeightOneSpectrum.instIsBiscalarSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersTensorProductCoeAlgHomTensorAdicCompletionIntegersTo IsDedekindDomain.HeightOneSpectrum.Extension.instContinuousSMulAdicCompletionValEqUnder IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsModuleTopology IsDedekindDomain.HeightOneSpectrum.Extension.instFiniteSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersValEqUnderOfFiniteDimensional IsDedekindDomain.HeightOneSpectrum.adicCompletion.instFiniteValEqUnderOfFiniteDimensional_definitions instIsBiscalarTensorProductCoeAlgHomBaseChange_of_algebraMap IsDedekindDomain.HeightOneSpectrum.instIsScalarTowerSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersValEqUnder_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsModuleTopologyPi Submodule.instIsTopologicalModuleSubtypeMem Pi.instTopologicalModule IsTopologicalModule.toContinuousSMul IsTopologicalModule.toContinuousAdd instFunLike SemialgHomClass.toSemilinearMapClass instCoeTCSemialgHom SemialgHomClass.toRingHomClass SemialgHomClass.instSemialgHom"
p2m_attr_erase "simp" "SemialgHom.baseChange_of_algebraMap_tmul_left SemialgHom.baseChangeRightOfAlgebraMap_apply Pi.semialgHomPi_apply Pi.semialgHom_apply Module.Basis.rightBaseChange_apply LinearEquiv.coe_mulLeft LinearEquiv.coe_mulRight WithVal.semialgebraMap_toFun_ofVal Module.Basis.rightBaseChange_repr IsDedekindDomain.HeightOneSpectrum.adicCompletionIntegers.tensorCoe_tmul IsDedekindDomain.HeightOneSpectrum.tensorAdicCompletionIntegersTo_tmul SemialgHom.baseChangeRightOfAlgebraMap_coe IsDedekindDomain.HeightOneSpectrum.adicCompletion.integerBaseChangeLinearEquiv_tmul_apply SemialgHom.baseChange_of_algebraMap_tmul_right IsLocalization.map_moduleTensorEquiv_symm_tmul IsLocalization.leftModuleTensorEquiv_apply IsLocalization.moduleLid_symm_apply IsLocalization.leftModuleTensorEquiv_symm_apply IsLocalization.map_moduleTensorEquiv_tmul IsModuleTopology.continuousLinearEquiv_apply AlgEquiv.extendScalars_symm_apply IsModuleTopology.Module.Basis.equivFun_homeo_symm_apply IsModuleTopology.Module.Basis.equivFun_homeo_apply IsModuleTopology.continuousAlgEquivOfIsBiscalar_apply AlgEquiv.extendScalars_apply IsModuleTopology.continuousLinearEquiv_symm_apply SemialgHom.restrictScalars_toFun SemialgHom.mk.sizeOf_spec SemialgHom.mk.injEq SemialgHom.coe_coe coe_mk TensorProduct.RightActions.smul_def TensorProduct.RightActions.Module.TensorProduct.comm_symm_apply_tmul TensorProduct.RightActions.LinearMap.baseChange_id TensorProduct.RightActions.algebraMap_eval TensorProduct.RightActions.Module.TensorProduct.comm_apply_tmul TensorProduct.RightActions.Algebra.TensorProduct.comm_symm_apply_tmul TensorProduct.RightActions.Algebra.TensorProduct.comm_apply_tmul"

set_option autoImplicit false

open NumberField NumberField.StandardAddChar NumberField.AdelicLevel IsDedekindDomain
open LanglandsTunnell.TateLocal MeasureTheory AutomorphicForm

section Helpers

variable (K : Type) [Field K] [NumberField K] (v : HeightOneSpectrum (𝓞 K))

private theorem one_lt_absNorm_asIdeal : 1 < Ideal.absNorm v.asIdeal := by
  have h0 : Ideal.absNorm v.asIdeal ≠ 0 := by
    rw [Ne, Ideal.absNorm_eq_zero_iff]
    exact v.ne_bot
  have h1 : Ideal.absNorm v.asIdeal ≠ 1 := by
    rw [Ne, Ideal.absNorm_eq_one_iff]
    exact v.isPrime.ne_top
  omega

private theorem isAddHaarMeasure_selfDualHaarAt :
    letI := localBorel K v
    (selfDualHaarAt K v).IsAddHaarMeasure := by
  letI := localBorel K v
  haveI : BorelSpace (v.adicCompletion K) := ⟨rfl⟩
  have hN : (0 : NNReal) < (Ideal.absNorm v.asIdeal : NNReal) := by
    exact_mod_cast Nat.zero_lt_one.trans (one_lt_absNorm_asIdeal K v)
  unfold selfDualHaarAt
  exact Measure.IsAddHaarMeasure.nnreal_smul _ (NNReal.rpow_pos hN).ne'

private theorem not_hasConductorExponentAt_zero_of_one_le {χ : (v.adicCompletion K)ˣ →* ℂˣ} {a : ℕ} (ha : 1 ≤ a)
    (hχ : HasConductorExponentAt K v χ a) : ¬ HasConductorExponentAt K v χ 0 := fun h0 => by
  have := hasConductorExponentAt_unique K v hχ h0
  omega

private theorem hasConductorExponentAt_inv_aux {χ : (v.adicCompletion K)ˣ →* ℂˣ} {a : ℕ}
    (hχ : HasConductorExponentAt K v χ a) : HasConductorExponentAt K v χ⁻¹ a := by
  refine ⟨fun u hu => ?_, fun c hc => ?_⟩
  · rw [MonoidHom.inv_apply, hχ.1 u hu, inv_one]
  · obtain ⟨u, hu, hne⟩ := hχ.2 c hc
    exact ⟨u, hu, by rwa [MonoidHom.inv_apply, ne_eq, inv_eq_one]⟩

private noncomputable def shellGauss (ξ : (v.adicCompletion K)ˣ →* ℂˣ) (a : ℕ) : ℂ := by
  letI := localBorel K v
  exact ∫ u in {u : v.adicCompletion K | Valued.v u = 1},
    psiLocal K v
        (((uniformizerUnit K v ^ (-(addCharLevel (psiLocal K v) + a : ℤ)) : (v.adicCompletion K)ˣ) :
            v.adicCompletion K) * u)
      * charExt ξ u ∂(selfDualHaarAt K v)

private noncomputable def halfScale (a : ℕ) : ℂ :=
  ((((Ideal.absNorm v.asIdeal : ℝ) ^ (addCharLevel (psiLocal K v) + a : ℤ) : ℝ) : ℂ)) ^ (1 - (1 / 2 : ℂ))

private theorem norm_inv_apply_uniformizerUnit_mul_cpow_lt_one {χ : (v.adicCompletion K)ˣ →* ℂˣ}
    (hu : ‖(χ (uniformizerUnit K v) : ℂ)‖ = 1) :
    ‖(χ⁻¹ (uniformizerUnit K v) : ℂ) * (Ideal.absNorm v.asIdeal : ℂ) ^ (-(1 - (1 / 2 : ℂ)))‖ < 1 := by
  have hNpos : 0 < Ideal.absNorm v.asIdeal := Nat.zero_lt_one.trans (one_lt_absNorm_asIdeal K v)
  have h1 : ‖(χ⁻¹ (uniformizerUnit K v) : ℂ)‖ = 1 := by
    rw [MonoidHom.inv_apply, Units.val_inv_eq_inv_val, norm_inv, hu, inv_one]
  rw [norm_mul, h1, one_mul, Complex.norm_natCast_cpow_of_pos hNpos]
  have hre : (-(1 - (1 / 2 : ℂ))).re = -(1 / 2 : ℝ) := by norm_num
  rw [hre]
  have hN1 : (1 : ℝ) < (Ideal.absNorm v.asIdeal : ℝ) := by exact_mod_cast one_lt_absNorm_asIdeal K v
  exact Real.rpow_lt_one_of_one_lt_of_neg hN1 (by norm_num)

private theorem stdRootNumberAt_eq_of_hasConductorExponentAt {χ : (v.adicCompletion K)ˣ →* ℂˣ} {a : ℕ} (ha : 1 ≤ a)
    (hχ : HasConductorExponentAt K v χ a) (hu : ‖(χ (uniformizerUnit K v) : ℂ)‖ = 1) :
    stdRootNumberAt K v χ
      = (χ (uniformizerUnit K v) : ℂ) ^ (addCharLevel (psiLocal K v) + a : ℤ) * halfScale K v a
          * shellGauss K v χ⁻¹ a := by
  letI := localBorel K v
  have hA := localZeta_stdTestFunAt_eq_real_image_higherUnitsAt K v χ a ha hχ (1 / 2)
  have hB := localZeta_tateFourier_stdTestFunAt K v χ a ha hχ (1 / 2)
    (norm_inv_apply_uniformizerUnit_mul_cpow_lt_one K v hu)
  have hvol := selfDualHaarAt_real_image_higherUnitsAt K v a ha
  try dsimp only at hA
  try dsimp only at hB
  try dsimp only at hvol
  have hvol0 : ((((selfDualHaarAt K v).real
      (((↑) : (v.adicCompletion K)ˣ → v.adicCompletion K) '' higherUnitsAt K v a) : ℝ)) : ℂ) ≠ 0 := by
    rw [hvol]
    have hN : (0 : ℝ) < (Ideal.absNorm v.asIdeal : ℝ) := by
      exact_mod_cast (Nat.zero_lt_one.trans (one_lt_absNorm_asIdeal K v))
    exact_mod_cast (mul_pos (zpow_pos hN _) (Real.rpow_pos_of_pos hN _)).ne'
  rw [stdRootNumberAt_def]
  unfold stdEpsilonAt
  rw [localEpsilonAt_of_not_hasConductorExponentAt_zero K v _ _ _
    (not_hasConductorExponentAt_zero_of_one_le K v ha hχ), localGammaAt]
  show _ / localZeta (selfDualHaarAt K v) (stdTestFunAt K v χ) χ (1 / 2) = _
  rw [hB, hA]
  unfold shellGauss halfScale
  field_simp

private theorem norm_psiLocal_apply (x : v.adicCompletion K) : ‖psiLocal K v x‖ = 1 := by
  unfold psiLocal
  rw [AddChar.compAddMonoidHom_apply]
  exact NumberField.AdelicFourier.norm_apply_eq_one_of_isGlobalAddChar K (isGlobalAddChar_stdAddChar K) _

private theorem conj_psiLocal_apply (x : v.adicCompletion K) :
    (starRingEnd ℂ) (psiLocal K v x) = psiLocal K v (-x) := by
  rw [AddChar.map_neg_eq_inv, Complex.inv_eq_conj (norm_psiLocal_apply K v x)]

private theorem norm_le_one_of_forall_norm_pow_le {z : ℂ} {C : ℝ} (h : ∀ k : ℕ, ‖z ^ k‖ ≤ C) : ‖z‖ ≤ 1 := by
  by_contra hlt
  push Not at hlt
  obtain ⟨k, hk⟩ := pow_unbounded_of_one_lt C hlt
  have := h k
  rw [norm_pow] at this
  linarith

private noncomputable def unitShell : Set (v.adicCompletion K) := {x | Valued.v x = 1}

private theorem mem_unitShell {x : v.adicCompletion K} : x ∈ unitShell K v ↔ Valued.v x = 1 := Iff.rfl

private theorem ne_zero_of_mem_unitShell {x : v.adicCompletion K} (hx : x ∈ unitShell K v) : x ≠ 0 := by
  intro h
  have h1 : Valued.v x = 1 := hx
  rw [h, map_zero] at h1
  exact zero_ne_one h1

private theorem isClosed_unitShell : IsClosed (unitShell K v) := by
  rw [← isOpen_compl_iff, isOpen_iff_eventually]
  intro x hx
  by_cases hx0 : x = 0
  · subst hx0
    have h0 : ∀ᶠ y in nhds (0 : v.adicCompletion K), Valued.v y < Valued.v (1 : v.adicCompletion K) := by
      rw [Filter.Eventually, Valued.mem_nhds_zero]
      refine ⟨Units.mk0 (Valued.v.restrict (1 : v.adicCompletion K)) ((Valuation.ne_zero_iff _).mpr one_ne_zero),
        fun y hy => ?_⟩
      exact (Valuation.restrict_lt_iff _).mp hy
    filter_upwards [h0] with y hy
    intro hy1
    have hy1' : Valued.v y = 1 := hy1
    rw [map_one, hy1'] at hy
    exact lt_irrefl _ hy
  · have hxv : Valued.v x ≠ 0 := (Valuation.ne_zero_iff _).mpr hx0
    filter_upwards [Valued.locally_const hxv] with y hy
    intro hy1
    have hy1' : Valued.v y = 1 := hy1
    exact hx (show Valued.v x = 1 by rw [← hy, hy1'])

private theorem unitShell_subset_integers :
    unitShell K v ⊆ (v.adicCompletionIntegers K : Set (v.adicCompletion K)) := fun x hx => by
  rw [SetLike.mem_coe, HeightOneSpectrum.mem_adicCompletionIntegers]
  exact le_of_eq hx

private theorem isCompact_unitShell : IsCompact (unitShell K v) :=
  ((integersPositiveCompacts K v).isCompact).of_isClosed_subset (isClosed_unitShell K v)
    (by rw [coe_integersPositiveCompacts]; exact unitShell_subset_integers K v)

private theorem neg_mem_unitShell {x : v.adicCompletion K} (hx : x ∈ unitShell K v) : -x ∈ unitShell K v := by
  rw [mem_unitShell, Valuation.map_neg]
  exact hx

private theorem coe_pow_mem_unitShell {u : (v.adicCompletion K)ˣ} (hu : Valued.v (u : v.adicCompletion K) = 1)
    (k : ℕ) :
    ((u ^ k : (v.adicCompletion K)ˣ) : v.adicCompletion K) ∈ unitShell K v := by
  rw [mem_unitShell, Units.val_pow_eq_pow_val, map_pow, hu, one_pow]

private theorem eventually_charExt_eq_of_hasConductorExponentAt {χ : (v.adicCompletion K)ˣ →* ℂˣ} {a : ℕ}
    (hχ : HasConductorExponentAt K v χ a) {x : v.adicCompletion K} (hx : x ∈ unitShell K v) :
    ∀ᶠ y in nhds x, charExt χ y = charExt χ x := by
  have hx1 : Valued.v x = 1 := hx
  have hx0 : x ≠ 0 := ne_zero_of_mem_unitShell K v hx
  have hxv : Valued.v x ≠ 0 := (Valuation.ne_zero_iff _).mpr hx0
  have hϖ : ((uniformizerUnit K v : (v.adicCompletion K)ˣ) : v.adicCompletion K) ^ a ≠ 0 :=
    pow_ne_zero a (uniformizerUnit K v).ne_zero
  have hval : Valued.v (((uniformizerUnit K v : (v.adicCompletion K)ˣ) : v.adicCompletion K) ^ a)
      = WithZero.exp (-(a : ℤ)) := by
    rw [map_pow, valued_uniformizerUnit K v, ← WithZero.exp_nsmul, nsmul_eq_mul, mul_neg, mul_one]
  have h0 : ∀ᶠ y in nhds (0 : v.adicCompletion K),
      Valued.v y < Valued.v (((uniformizerUnit K v : (v.adicCompletion K)ˣ) : v.adicCompletion K) ^ a) := by
    rw [Filter.Eventually, Valued.mem_nhds_zero]
    refine ⟨Units.mk0 (Valued.v.restrict (((uniformizerUnit K v : (v.adicCompletion K)ˣ) : v.adicCompletion K) ^ a))
      ((Valuation.ne_zero_iff _).mpr hϖ), fun y hy => ?_⟩
    exact (Valuation.restrict_lt_iff _).mp hy
  have hsub : Filter.Tendsto (fun y : v.adicCompletion K => y - x) (nhds x) (nhds 0) := by
    have h := (continuous_sub_right x).tendsto x
    rwa [sub_self] at h
  filter_upwards [Valued.locally_const hxv, hsub.eventually h0] with y hy hyx
  have hy0 : y ≠ 0 := fun h => hxv (by rw [← hy, h, map_zero])
  have hmem : Units.mk0 y hy0 * (Units.mk0 x hx0)⁻¹ ∈ higherUnitsAt K v a := by
    refine (mem_higherUnitsAt_iff K v).mpr ⟨?_, Or.inr ?_⟩
    · rw [Units.val_mul, map_mul, Units.val_inv_eq_inv_val, map_inv₀, Units.val_mk0, Units.val_mk0, hy, hx1,
        inv_one, mul_one]
    · have hdiff : ((Units.mk0 y hy0 * (Units.mk0 x hx0)⁻¹ : (v.adicCompletion K)ˣ) : v.adicCompletion K) - 1
          = (y - x) * x⁻¹ := by
        rw [Units.val_mul, Units.val_inv_eq_inv_val, Units.val_mk0, Units.val_mk0, sub_mul,
          mul_inv_cancel₀ hx0]
      rw [hdiff, map_mul, map_inv₀, hx1, inv_one, mul_one, ← hval]
      exact hyx.le
  have hχ1 : χ (Units.mk0 y hy0 * (Units.mk0 x hx0)⁻¹) = 1 := hχ.1 _ hmem
  rw [charExt_of_ne_zero χ hy0, charExt_of_ne_zero χ hx0]
  have hsplit : Units.mk0 y hy0 = (Units.mk0 y hy0 * (Units.mk0 x hx0)⁻¹) * Units.mk0 x hx0 := by
    rw [inv_mul_cancel_right]
  rw [hsplit, map_mul, hχ1, one_mul]

private theorem continuousOn_charExt_unitShell {χ : (v.adicCompletion K)ˣ →* ℂˣ} {a : ℕ}
    (hχ : HasConductorExponentAt K v χ a) : ContinuousOn (charExt χ) (unitShell K v) := fun _ hx =>
  (continuousAt_const.congr
    ((eventually_charExt_eq_of_hasConductorExponentAt K v hχ hx).mono fun _ h => h.symm)).continuousWithinAt

private theorem norm_apply_eq_one_of_hasConductorExponentAt {χ : (v.adicCompletion K)ˣ →* ℂˣ} {a : ℕ}
    (hχ : HasConductorExponentAt K v χ a) {u : (v.adicCompletion K)ˣ} (hu : Valued.v (u : v.adicCompletion K) = 1) :
    ‖((χ u : ℂˣ) : ℂ)‖ = 1 := by
  obtain ⟨C, hC⟩ :=
    (isCompact_unitShell K v).exists_bound_of_continuousOn (continuousOn_charExt_unitShell K v hχ)
  have key : ∀ w : (v.adicCompletion K)ˣ, Valued.v (w : v.adicCompletion K) = 1 → ‖((χ w : ℂˣ) : ℂ)‖ ≤ 1 := by
    intro w hw
    refine norm_le_one_of_forall_norm_pow_le (C := C) fun k => ?_
    have h := hC _ (coe_pow_mem_unitShell K v hw k)
    rwa [charExt_coe_units, map_pow, Units.val_pow_eq_pow_val] at h
  have h1 := key u hu
  have hu' : Valued.v ((u⁻¹ : (v.adicCompletion K)ˣ) : v.adicCompletion K) = 1 := by
    rw [Units.val_inv_eq_inv_val, map_inv₀, hu, inv_one]
  have h2 := key u⁻¹ hu'
  rw [map_inv, Units.val_inv_eq_inv_val, norm_inv] at h2
  have hpos : 0 < ‖((χ u : ℂˣ) : ℂ)‖ := norm_pos_iff.mpr (Units.ne_zero _)
  exact le_antisymm h1 ((inv_le_one₀ hpos).mp h2)

private theorem conj_shellGauss_inv {χ : (v.adicCompletion K)ˣ →* ℂˣ} {a : ℕ} (hχ : HasConductorExponentAt K v χ a) :
    (starRingEnd ℂ) (shellGauss K v χ⁻¹ a) = ((χ (-1 : (v.adicCompletion K)ˣ) : ℂˣ) : ℂ) * shellGauss K v χ a := by
  letI := localBorel K v
  haveI : BorelSpace (v.adicCompletion K) := ⟨rfl⟩
  haveI : (selfDualHaarAt K v).IsAddHaarMeasure := isAddHaarMeasure_selfDualHaarAt K v
  haveI : LocallyCompactSpace (v.adicCompletion K) :=
    (integersPositiveCompacts K v).isCompact.locallyCompactSpace_of_mem_nhds_of_addGroup (x := 0)
      ((show IsOpen ((integersPositiveCompacts K v : Set (v.adicCompletion K))) from
        Valued.isOpen_valuationSubring _).mem_nhds (by rw [coe_integersPositiveCompacts]; exact zero_mem _))
  haveI : (selfDualHaarAt K v).Regular := by
    unfold selfDualHaarAt
    infer_instance
  haveI : (selfDualHaarAt K v).IsNegInvariant := inferInstance
  have hS : MeasurableSet (unitShell K v) := (isClosed_unitShell K v).measurableSet
  have hunit : ∀ u ∈ unitShell K v,
      (starRingEnd ℂ) (charExt χ⁻¹ u) = charExt χ u := fun u hu => by
    have hu0 : u ≠ 0 := ne_zero_of_mem_unitShell K v hu
    rw [charExt_of_ne_zero _ hu0, charExt_of_ne_zero _ hu0, MonoidHom.inv_apply, Units.val_inv_eq_inv_val, map_inv₀,
      ← Complex.inv_eq_conj (norm_apply_eq_one_of_hasConductorExponentAt K v hχ (u := Units.mk0 u hu0) hu),
      inv_inv]
  have hnegchar : ∀ u ∈ unitShell K v,
      charExt χ (-u) = ((χ (-1 : (v.adicCompletion K)ˣ) : ℂˣ) : ℂ) * charExt χ u := fun u hu => by
    have hu0 : u ≠ 0 := ne_zero_of_mem_unitShell K v hu
    have hneg : (-u) = ((-Units.mk0 u hu0 : (v.adicCompletion K)ˣ) : v.adicCompletion K) := by
      rw [Units.val_neg, Units.val_mk0]
    rw [hneg, charExt_coe_units, charExt_of_ne_zero _ hu0, neg_eq_neg_one_mul, map_mul, Units.val_mul]

  set c : v.adicCompletion K :=
    ((uniformizerUnit K v ^ (-(addCharLevel (psiLocal K v) + a : ℤ)) : (v.adicCompletion K)ˣ) : v.adicCompletion K)
    with hc

  have step1 : (starRingEnd ℂ) (shellGauss K v χ⁻¹ a)
      = ∫ u in unitShell K v, psiLocal K v (c * (-u)) * charExt χ u ∂(selfDualHaarAt K v) := by
    unfold shellGauss
    rw [← integral_conj]
    refine setIntegral_congr_fun hS fun u hu => ?_
    simp only [map_mul]
    rw [conj_psiLocal_apply, hunit u hu, mul_neg]

  have step2 : (∫ u in unitShell K v, psiLocal K v (c * (-u)) * charExt χ u ∂(selfDualHaarAt K v))
      = ∫ u in unitShell K v, psiLocal K v (c * u) * charExt χ (-u) ∂(selfDualHaarAt K v) := by
    rw [← integral_indicator hS, ← integral_indicator hS,
      ← integral_neg_eq_self (fun u => (unitShell K v).indicator
        (fun u => psiLocal K v (c * u) * charExt χ (-u)) u) (selfDualHaarAt K v)]
    refine integral_congr_ae (Filter.Eventually.of_forall fun u => ?_)
    show (unitShell K v).indicator _ u = (unitShell K v).indicator _ (-u)
    by_cases hu : u ∈ unitShell K v
    · rw [Set.indicator_of_mem hu, Set.indicator_of_mem (neg_mem_unitShell K v hu), neg_neg]
    · have hu' : -u ∉ unitShell K v := fun h => hu (by simpa using neg_mem_unitShell K v h)
      rw [Set.indicator_of_notMem hu, Set.indicator_of_notMem hu']

  have step3 : (∫ u in unitShell K v, psiLocal K v (c * u) * charExt χ (-u) ∂(selfDualHaarAt K v))
      = ((χ (-1 : (v.adicCompletion K)ˣ) : ℂˣ) : ℂ) * shellGauss K v χ a := by
    unfold shellGauss
    rw [← integral_const_mul]
    refine setIntegral_congr_fun hS fun u hu => ?_
    rw [hnegchar u hu]
    ring
  rw [step1, step2, step3]

end Helpers

theorem solution
    (K : Type) [Field K] [NumberField K] (v : HeightOneSpectrum (𝓞 K))
    (χ : (v.adicCompletion K)ˣ →* ℂˣ) (a : ℕ) (ha : 1 ≤ a) (hχ : HasConductorExponentAt K v χ a)
    (hu : ‖((χ (uniformizerUnit K v) : ℂˣ) : ℂ)‖ = 1) :
    ‖stdRootNumberAt K v χ‖ = 1 := by
  have hu' : ‖((χ⁻¹ (uniformizerUnit K v) : ℂˣ) : ℂ)‖ = 1 := by
    rw [MonoidHom.inv_apply, Units.val_inv_eq_inv_val, norm_inv, hu, inv_one]
  have hχ' := hasConductorExponentAt_inv_aux K v hχ
  have hA := LanglandsTunnell.TateLocal.stdRootNumberAt_mul_stdRootNumberAt_inv_eq_apply_neg_one K v χ a ha hχ hu

  have hm1 : ‖((χ (-1 : (v.adicCompletion K)ˣ) : ℂˣ) : ℂ)‖ = 1 := by
    have hsq : ((χ (-1 : (v.adicCompletion K)ˣ) : ℂˣ) : ℂ) * ((χ (-1 : (v.adicCompletion K)ˣ) : ℂˣ) : ℂ) = 1 := by
      rw [← Units.val_mul, ← map_mul, neg_one_mul, neg_neg, map_one, Units.val_one]
    have h2 : ‖((χ (-1 : (v.adicCompletion K)ˣ) : ℂˣ) : ℂ)‖ ^ 2 = 1 := by
      rw [sq, ← norm_mul, hsq, norm_one]
    exact (pow_eq_one_iff_of_nonneg (norm_nonneg _) two_ne_zero).mp h2
  have hprod : ‖stdRootNumberAt K v χ‖ * ‖stdRootNumberAt K v χ⁻¹‖ = 1 := by
    rw [← norm_mul, hA, hm1]

  have hGeq : ‖shellGauss K v χ⁻¹ a‖ = ‖shellGauss K v χ a‖ := by
    have h := congrArg (fun z : ℂ => ‖z‖) (conj_shellGauss_inv K v hχ)
    simp only [Complex.norm_conj, norm_mul] at h
    rw [h, hm1, one_mul]

  have hii : shellGauss K v χ⁻¹⁻¹ a = shellGauss K v χ a := by
    rw [show χ⁻¹⁻¹ = χ from inv_inv χ]

  have heq : ‖stdRootNumberAt K v χ⁻¹‖ = ‖stdRootNumberAt K v χ‖ := by
    rw [stdRootNumberAt_eq_of_hasConductorExponentAt K v ha hχ' hu',
      stdRootNumberAt_eq_of_hasConductorExponentAt K v ha hχ hu, hii, norm_mul, norm_mul, norm_mul, norm_mul,
      norm_zpow, norm_zpow, hu, hu', hGeq]
  have hsq : ‖stdRootNumberAt K v χ‖ ^ 2 = 1 := by
    calc ‖stdRootNumberAt K v χ‖ ^ 2 = ‖stdRootNumberAt K v χ‖ * ‖stdRootNumberAt K v χ⁻¹‖ := by rw [sq, heq]
      _ = 1 := hprod
  exact (pow_eq_one_iff_of_nonneg (norm_nonneg _) two_ne_zero).mp hsq

end S_LanglandsTunnell_TateLocal_norm_stdRootNumberAt_eq_one
end P2MW
export P2MW.S_LanglandsTunnell_TateLocal_norm_stdRootNumberAt_eq_one (solution)
