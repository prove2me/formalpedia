-- Prove2me | solution 1 for LanglandsTunnell.CubicInduction.integral_frame23_mul_eq_integral_matFourier23_dualFrame23_mul
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:08.353894+00:00
-- url     : https://prove2.me/submissions/91967b68-8bd3-524c-bf2e-5ead1ddf4f89

import Mathlib
import Definitions.Def_LanglandsTunnell_CubicInduction_GodementSection
import Definitions.Def_LanglandsTunnell_CubicInduction_JacquetWhittaker
import Theorems.Thm_LanglandsTunnell_TateLocal_tateFourier_tateFourier_selfDualHaarAt_of_isSchwartzBruhat
import Theorems.Thm_LanglandsTunnell_TateLocal_isSchwartzBruhat_tateFourier
import Theorems.Thm_LanglandsTunnell_TateLocal_psiLocal_ne_one
import Theorems.Thm_LanglandsTunnell_TateLocal_addCharLevel_psiLocal_rat
import Theorems.Thm_LanglandsTunnell_TateLocal_psiLocal_eq_one_of_mem_integers
import Theorems.Thm_LanglandsTunnell_TateLocal_forall_eq_one_and_exists_ne_one_of_addCharLevel
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_LanglandsTunnell_CubicInduction_integral_frame23_mul_eq_integral_matFourier23_dualFrame23_mul
p2m_attr_erase "instance" "instFiniteResidueFieldAdicCompletionRingOfIntegersWithZeroMultiplicativeInt_definitions NumberField.instCompactSpaceAdicCompletionIntegers Rat.adicCompletion.locallyCompactSpace NumberField.instFiniteResidueFieldAdicCompletionIntegers instWeaklyLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions instCountableOfNumberField_definitions IsDedekindDomain.HeightOneSpectrum.Extension.instAlgebraSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersValEqUnder IsDedekindDomain.HeightOneSpectrum.Extension.instAlgebraSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersValEqUnder_1 IsDedekindDomain.HeightOneSpectrum.instMulActionHomClassAlgHomTensorProductAdicCompletionForallValEqUnder_definitions IsDedekindDomain.HeightOneSpectrum.Extension.instAlgebraAdicCompletionValEqUnder IsDedekindDomain.HeightOneSpectrum.adicCompletion.instFiniteForallValEqUnderOfFiniteDimensional_definitions IsDedekindDomain.HeightOneSpectrum.instIsBiscalarSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersTensorProductCoeAlgHomTensorAdicCompletionIntegersTo IsDedekindDomain.HeightOneSpectrum.Extension.instContinuousSMulAdicCompletionValEqUnder IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsModuleTopology IsDedekindDomain.HeightOneSpectrum.Extension.instFiniteSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersValEqUnderOfFiniteDimensional IsDedekindDomain.HeightOneSpectrum.adicCompletion.instFiniteValEqUnderOfFiniteDimensional_definitions instIsBiscalarTensorProductCoeAlgHomBaseChange_of_algebraMap IsDedekindDomain.HeightOneSpectrum.instIsScalarTowerSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersValEqUnder_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsModuleTopologyPi Submodule.instIsTopologicalModuleSubtypeMem Pi.instTopologicalModule IsTopologicalModule.toContinuousSMul IsTopologicalModule.toContinuousAdd instFunLike SemialgHomClass.toSemilinearMapClass instCoeTCSemialgHom SemialgHomClass.toRingHomClass SemialgHomClass.instSemialgHom"
p2m_attr_erase "simp" "SemialgHom.baseChange_of_algebraMap_tmul_left SemialgHom.baseChangeRightOfAlgebraMap_apply Pi.semialgHomPi_apply Pi.semialgHom_apply Module.Basis.rightBaseChange_apply LinearEquiv.coe_mulLeft LinearEquiv.coe_mulRight WithVal.semialgebraMap_toFun_ofVal Module.Basis.rightBaseChange_repr IsDedekindDomain.HeightOneSpectrum.adicCompletionIntegers.tensorCoe_tmul IsDedekindDomain.HeightOneSpectrum.tensorAdicCompletionIntegersTo_tmul SemialgHom.baseChangeRightOfAlgebraMap_coe IsDedekindDomain.HeightOneSpectrum.adicCompletion.integerBaseChangeLinearEquiv_tmul_apply SemialgHom.baseChange_of_algebraMap_tmul_right IsLocalization.map_moduleTensorEquiv_symm_tmul IsLocalization.leftModuleTensorEquiv_apply IsLocalization.moduleLid_symm_apply IsLocalization.leftModuleTensorEquiv_symm_apply IsLocalization.map_moduleTensorEquiv_tmul IsModuleTopology.continuousLinearEquiv_apply AlgEquiv.extendScalars_symm_apply IsModuleTopology.Module.Basis.equivFun_homeo_symm_apply IsModuleTopology.Module.Basis.equivFun_homeo_apply IsModuleTopology.continuousAlgEquivOfIsBiscalar_apply AlgEquiv.extendScalars_apply IsModuleTopology.continuousLinearEquiv_symm_apply SemialgHom.restrictScalars_toFun SemialgHom.mk.sizeOf_spec SemialgHom.mk.injEq SemialgHom.coe_coe coe_mk TensorProduct.RightActions.smul_def TensorProduct.RightActions.Module.TensorProduct.comm_symm_apply_tmul TensorProduct.RightActions.LinearMap.baseChange_id TensorProduct.RightActions.algebraMap_eval TensorProduct.RightActions.Module.TensorProduct.comm_apply_tmul TensorProduct.RightActions.Algebra.TensorProduct.comm_symm_apply_tmul TensorProduct.RightActions.Algebra.TensorProduct.comm_apply_tmul"

set_option autoImplicit false

open MeasureTheory IsDedekindDomain NumberField NumberField.StandardAddChar LanglandsTunnell.TateLocal LanglandsTunnell.CubicInduction AutomorphicForm

open scoped BigOperators

noncomputable section

namespace E3ReduceSupplyF

variable (p : HeightOneSpectrum (𝓞 ℚ))

local notation "Qp" => p.adicCompletion ℚ

theorem level_zero :
    (∀ x : Qp, Valued.v x ≤ WithZero.exp (0 : ℤ) → NumberField.StandardAddChar.psiLocal ℚ p x = 1) ∧
      ∃ x : Qp, Valued.v x ≤ WithZero.exp ((0 : ℤ) + 1) ∧ NumberField.StandardAddChar.psiLocal ℚ p x ≠ 1 := by
  have hk : ∃ k : ℤ, ∀ x : Qp, Valued.v x ≤ WithZero.exp k → NumberField.StandardAddChar.psiLocal ℚ p x = 1 := by
    refine ⟨0, fun x hx => LanglandsTunnell.TateLocal.psiLocal_eq_one_of_mem_integers ℚ p x ?_⟩
    rw [HeightOneSpectrum.mem_adicCompletionIntegers]
    simpa using hx
  have h := LanglandsTunnell.TateLocal.forall_eq_one_and_exists_ne_one_of_addCharLevel ℚ p
    (NumberField.StandardAddChar.psiLocal ℚ p) hk (LanglandsTunnell.TateLocal.psiLocal_ne_one ℚ p)
  rwa [LanglandsTunnell.TateLocal.addCharLevel_psiLocal_rat p] at h

theorem level_zero_inv :
    (∀ x : Qp, Valued.v x ≤ WithZero.exp (0 : ℤ) → (NumberField.StandardAddChar.psiLocal ℚ p)⁻¹ x = 1) ∧
      ∃ x : Qp, Valued.v x ≤ WithZero.exp ((0 : ℤ) + 1) ∧ (NumberField.StandardAddChar.psiLocal ℚ p)⁻¹ x ≠ 1 := by
  obtain ⟨h0, h1⟩ := level_zero p
  refine ⟨fun x hx => ?_, ?_⟩
  · rw [AddChar.inv_apply]; exact h0 (-x) (by rwa [Valuation.map_neg])
  · obtain ⟨x, hx, hne⟩ := h1
    refine ⟨-x, by rwa [Valuation.map_neg], ?_⟩
    rwa [AddChar.inv_apply, neg_neg]

theorem selfDualHaarAt_eq :
    selfDualHaarAt ℚ p = @Measure.addHaarMeasure (p.adicCompletion ℚ) _ _ _ (localBorel ℚ p)
      (borelSpace_localBorel ℚ p) (integersPositiveCompacts ℚ p) := by
  letI := localBorel ℚ p
  haveI : BorelSpace (p.adicCompletion ℚ) := borelSpace_localBorel ℚ p
  unfold selfDualHaarAt
  rw [LanglandsTunnell.TateLocal.addCharLevel_psiLocal_rat p]
  simp

theorem isAddHaarMeasure_selfDualHaarAt :
    letI := localBorel ℚ p
    (selfDualHaarAt ℚ p).IsAddHaarMeasure := by
  letI := localBorel ℚ p
  haveI : BorelSpace (p.adicCompletion ℚ) := borelSpace_localBorel ℚ p
  rw [selfDualHaarAt_eq p]
  infer_instance

theorem isSchwartzBruhat_tateFourier_psiLocal_inv (φ : Qp → ℂ) (hφ : IsSchwartzBruhat φ) :
    letI := localBorel ℚ p
    IsSchwartzBruhat (tateFourier (NumberField.StandardAddChar.psiLocal ℚ p)⁻¹ (selfDualHaarAt ℚ p) φ) := by
  letI := localBorel ℚ p
  haveI : BorelSpace (p.adicCompletion ℚ) := borelSpace_localBorel ℚ p
  haveI := isAddHaarMeasure_selfDualHaarAt p
  obtain ⟨h0, h1⟩ := level_zero_inv p
  exact LanglandsTunnell.TateLocal.isSchwartzBruhat_tateFourier ℚ p (selfDualHaarAt ℚ p)
    ((NumberField.StandardAddChar.psiLocal ℚ p)⁻¹) 0 h0 h1 φ hφ

theorem continuous_tateFourier_of_isSchwartzBruhat (φ : Qp → ℂ) (hφ : IsSchwartzBruhat φ) :
    letI := localBorel ℚ p
    Continuous (tateFourier (NumberField.StandardAddChar.psiLocal ℚ p)⁻¹ (selfDualHaarAt ℚ p) φ) :=
  (isSchwartzBruhat_tateFourier_psiLocal_inv p φ hφ).1.continuous

end E3ReduceSupplyF

namespace ProdFourierInv

variable (p : HeightOneSpectrum (𝓞 ℚ))

local notation "F" => p.adicCompletion ℚ

scoped instance instIsUltrametricDistProd {X Y : Type*} [PseudoMetricSpace X] [PseudoMetricSpace Y]
    [IsUltrametricDist X] [IsUltrametricDist Y] : IsUltrametricDist (X × Y) := by
  constructor
  intro x y z
  simp only [Prod.dist_eq]
  refine max_le ?_ ?_
  · exact (IsUltrametricDist.dist_triangle_max x.1 y.1 z.1).trans
      (max_le_max (le_max_left _ _) (le_max_left _ _))
  · exact (IsUltrametricDist.dist_triangle_max x.2 y.2 z.2).trans
      (max_le_max (le_max_right _ _) (le_max_right _ _))

theorem isLocallyConstant_psiLocal : IsLocallyConstant (fun t : F => (psiLocal ℚ p t : ℂ)) := by
  rw [IsLocallyConstant.iff_eventually_eq]
  intro x
  have hopen : IsOpen ((fun y : F => y - x) ⁻¹' (p.adicCompletionIntegers ℚ : Set F)) :=
    (Valued.isOpen_valuationSubring _).preimage (continuous_id.sub continuous_const)
  have hmem : x ∈ (fun y : F => y - x) ⁻¹' (p.adicCompletionIntegers ℚ : Set F) := by
    simp only [Set.mem_preimage, sub_self, SetLike.mem_coe]; exact zero_mem _
  filter_upwards [hopen.mem_nhds hmem] with y hy
  have h1 : psiLocal ℚ p (y - x) = 1 := by
    apply (E3ReduceSupplyF.level_zero p).1
    rw [WithZero.exp_zero]
    exact (HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).1 hy
  have : y = (y - x) + x := by ring
  rw [this, AddChar.map_add_eq_mul, h1, one_mul]

theorem continuous_psiLocal : Continuous (fun t : F => (psiLocal ℚ p t : ℂ)) :=
  (isLocallyConstant_psiLocal p).continuous

section Structure

variable {X : Type*} [MetricSpace X]

theorem exists_radius_of_isLocallyConstant_of_hasCompactSupport (f : X → ℂ) (hlc : IsLocallyConstant f)
    (hcs : HasCompactSupport f) : ∃ δ > 0, ∀ x y : X, dist x y < δ → f x = f y := by
  obtain ⟨δ, hδ, hU⟩ := lebesgue_number_lemma_of_metric (ι := X) (c := fun i => {y | f y = f i}) hcs
    (fun i => hlc.isOpen_fiber (f i)) (fun x _ => Set.mem_iUnion.2 ⟨x, rfl⟩)
  refine ⟨δ, hδ, ?_⟩

  have key : ∀ x ∈ tsupport f, ∀ y, dist x y < δ → f x = f y := by
    intro x hx y hxy
    obtain ⟨i, hi⟩ := hU x hx
    have h1 : f x = f i := hi (Metric.mem_ball_self hδ)
    have h2 : f y = f i := hi (by rw [Metric.mem_ball, dist_comm]; exact hxy)
    rw [h1, h2]
  intro x y hxy
  by_cases hx : x ∈ tsupport f
  · exact key x hx y hxy
  by_cases hy : y ∈ tsupport f
  · exact (key y hy x (by rw [dist_comm]; exact hxy)).symm
  rw [image_eq_zero_of_notMem_tsupport hx, image_eq_zero_of_notMem_tsupport hy]

variable [IsUltrametricDist X]

theorem exists_finset_ball_eq_sum_indicator (f : X → ℂ) (hlc : IsLocallyConstant f) (hcs : HasCompactSupport f) :
    ∃ δ > 0, ∃ B : Finset (Set X),
      (∀ U ∈ B, ∃ a : X, U = Metric.ball a δ ∧ ∀ x ∈ U, f x = f a) ∧
      ∀ x, f x = ∑ U ∈ B, U.indicator f x := by
  classical
  obtain ⟨δ, hδ, hunif⟩ := exists_radius_of_isLocallyConstant_of_hasCompactSupport f hlc hcs
  obtain ⟨t, -, htfin, hcov⟩ := finite_cover_balls_of_compact hcs hδ
  refine ⟨δ, hδ, htfin.toFinset.image (fun a => Metric.ball a δ), ?_, ?_⟩
  · intro U hU
    obtain ⟨a, -, rfl⟩ := Finset.mem_image.1 hU
    exact ⟨a, rfl, fun x hx => (hunif a x (by rw [dist_comm]; exact hx)).symm⟩
  · intro x
    by_cases hx : x ∈ tsupport f
    ·
      obtain ⟨a, hat, hxa⟩ : ∃ a ∈ t, x ∈ Metric.ball a δ := by
        have := hcov hx; simpa only [Set.mem_iUnion, exists_prop] using this
      have hmem : Metric.ball a δ ∈ htfin.toFinset.image (fun a => Metric.ball a δ) :=
        Finset.mem_image.2 ⟨a, htfin.mem_toFinset.2 hat, rfl⟩
      rw [Finset.sum_eq_single_of_mem (Metric.ball a δ) hmem]
      · rw [Set.indicator_of_mem hxa]
      · intro U hU hne
        obtain ⟨b, -, rfl⟩ := Finset.mem_image.1 hU
        rw [Set.indicator_of_notMem]
        intro hxb
        apply hne
        rw [IsUltrametricDist.ball_eq_of_mem hxb, IsUltrametricDist.ball_eq_of_mem hxa]
    · have h0 : f x = 0 := image_eq_zero_of_notMem_tsupport hx
      rw [h0]; symm
      exact Finset.sum_eq_zero fun U _ => by
        by_cases hU : x ∈ U
        · rw [Set.indicator_of_mem hU, h0]
        · rw [Set.indicator_of_notMem hU]

end Structure

theorem isSchwartzBruhat_indicator_ball (a : F) (δ : ℝ) :
    IsSchwartzBruhat ((Metric.ball a δ).indicator fun _ => (1 : ℂ)) :=
  IsSchwartzBruhat.indicator_const (IsUltrametricDist.isClopen_ball a δ)
    ((isCompact_closedBall a δ).of_isClosed_subset (IsUltrametricDist.isClosed_ball a δ) Metric.ball_subset_closedBall) 1

theorem one_var_SB (g : F → ℂ) (hg : IsSchwartzBruhat g) :
    letI := localBorel ℚ p
    IsSchwartzBruhat (tateFourier (psiLocal ℚ p) (selfDualHaarAt ℚ p) g) := by
  letI := localBorel ℚ p
  haveI : BorelSpace F := borelSpace_localBorel ℚ p
  haveI := E3ReduceSupplyF.isAddHaarMeasure_selfDualHaarAt p
  obtain ⟨h1, h2⟩ := E3ReduceSupplyF.level_zero p
  exact LanglandsTunnell.TateLocal.isSchwartzBruhat_tateFourier ℚ p (selfDualHaarAt ℚ p) (psiLocal ℚ p) 0 h1 h2 g hg

theorem one_var_inv (g : F → ℂ) (hg : IsSchwartzBruhat g) (x : F) :
    letI := localBorel ℚ p
    tateFourier (psiLocal ℚ p) (selfDualHaarAt ℚ p) (tateFourier (psiLocal ℚ p) (selfDualHaarAt ℚ p) g) x = g (-x) :=
  LanglandsTunnell.TateLocal.tateFourier_tateFourier_selfDualHaarAt_of_isSchwartzBruhat ℚ p g hg x

theorem transform_tensor (g₁ g₂ : F → ℂ) (y : F × F) :
    letI := localBorel ℚ p
    (∫ x : F × F, (g₁ x.1 * g₂ x.2) * psiLocal ℚ p (x.1 * y.1 + x.2 * y.2)
        ∂((selfDualHaarAt ℚ p).prod (selfDualHaarAt ℚ p))) =
      tateFourier (psiLocal ℚ p) (selfDualHaarAt ℚ p) g₁ y.1 *
        tateFourier (psiLocal ℚ p) (selfDualHaarAt ℚ p) g₂ y.2 := by
  letI := localBorel ℚ p
  haveI : BorelSpace F := borelSpace_localBorel ℚ p
  haveI := E3ReduceSupplyF.isAddHaarMeasure_selfDualHaarAt p
  simp only [tateFourier]
  rw [← integral_prod_mul]
  congr 1
  funext x
  rw [AddChar.map_add_eq_mul]
  push_cast
  ring

theorem isSchwartzBruhat_tensor {X₁ X₂ : Type*} [TopologicalSpace X₁] [TopologicalSpace X₂]
    (g₁ : X₁ → ℂ) (g₂ : X₂ → ℂ) (h₁ : IsSchwartzBruhat g₁) (h₂ : IsSchwartzBruhat g₂) :
    IsSchwartzBruhat (fun y : X₁ × X₂ => g₁ y.1 * g₂ y.2) := by
  refine ⟨(h₁.1.comp_continuous continuous_fst).mul (h₂.1.comp_continuous continuous_snd), ?_⟩
  refine HasCompactSupport.intro' (h₁.2.prod h₂.2) ((isClosed_tsupport _).prod (isClosed_tsupport _)) ?_
  intro y hy
  rw [Set.mem_prod, not_and_or] at hy
  rcases hy with hy | hy
  · rw [image_eq_zero_of_notMem_tsupport hy, zero_mul]
  · rw [image_eq_zero_of_notMem_tsupport hy, mul_zero]

theorem isSchwartzBruhat_const_mul {Y : Type*} [TopologicalSpace Y] (c : ℂ) (g : Y → ℂ) (hg : IsSchwartzBruhat g) :
    IsSchwartzBruhat (fun y => c * g y) :=
  ⟨(IsLocallyConstant.const c).mul hg.1, hg.2.mul_left⟩

theorem isSchwartzBruhat_zero' {Y : Type*} [TopologicalSpace Y] : IsSchwartzBruhat (fun _ : Y => (0 : ℂ)) :=
  IsSchwartzBruhat.zero

theorem isSchwartzBruhat_add {Y : Type*} [TopologicalSpace Y] (g h : Y → ℂ) (hg : IsSchwartzBruhat g)
    (hh : IsSchwartzBruhat h) : IsSchwartzBruhat (fun y => g y + h y) :=
  ⟨hg.1.add hh.1, hg.2.add hh.2⟩

theorem isSchwartzBruhat_finset_sum {Y : Type*} [TopologicalSpace Y] {ι : Type*} (s : Finset ι) (g : ι → Y → ℂ)
    (hg : ∀ i ∈ s, IsSchwartzBruhat (g i)) : IsSchwartzBruhat (fun y => ∑ i ∈ s, g i y) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using (isSchwartzBruhat_zero' (Y := Y))
  | insert a s ha ih =>
    have : (fun y => ∑ i ∈ insert a s, g i y) = fun y => g a y + ∑ i ∈ s, g i y := by
      funext y; rw [Finset.sum_insert ha]
    rw [this]
    exact isSchwartzBruhat_add _ _ (hg a (Finset.mem_insert_self a s))
      (ih fun i hi => hg i (Finset.mem_insert_of_mem hi))

theorem integrable_tensor_kernel (g₁ g₂ : F → ℂ) (h₁ : IsSchwartzBruhat g₁) (h₂ : IsSchwartzBruhat g₂) (y : F × F) :
    letI := localBorel ℚ p
    Integrable (fun x : F × F => (g₁ x.1 * g₂ x.2) * psiLocal ℚ p (x.1 * y.1 + x.2 * y.2))
      ((selfDualHaarAt ℚ p).prod (selfDualHaarAt ℚ p)) := by
  letI := localBorel ℚ p
  haveI : BorelSpace F := borelSpace_localBorel ℚ p
  haveI := E3ReduceSupplyF.isAddHaarMeasure_selfDualHaarAt p
  have hψc : Continuous (fun t : F => (psiLocal ℚ p t : ℂ)) := continuous_psiLocal p
  have hint : ∀ (g : F → ℂ), IsSchwartzBruhat g → ∀ c : F,
      Integrable (fun t : F => g t * psiLocal ℚ p (t * c)) (selfDualHaarAt ℚ p) := by
    intro g hg c
    refine Continuous.integrable_of_hasCompactSupport ?_ ?_
    · exact hg.1.continuous.mul (hψc.comp (continuous_id.mul continuous_const))
    · exact hg.2.mul_right
  have h := (hint g₁ h₁ y.1).mul_prod (hint g₂ h₂ y.2)
  refine h.congr (Filter.Eventually.of_forall fun x => ?_)
  simp only
  rw [AddChar.map_add_eq_mul]; push_cast; ring

theorem jacquetHaar3_eq :
    letI := localBorel ℚ p
    jacquetHaar3 p = (selfDualHaarAt ℚ p).prod ((selfDualHaarAt ℚ p).prod (selfDualHaarAt ℚ p)) := rfl

theorem transform_tensor3 (g₁ g₂ g₃ : F → ℂ) (h₂ : IsSchwartzBruhat g₂) (h₃ : IsSchwartzBruhat g₃) (y : F × F × F) :
    letI := localBorel ℚ p
    (∫ x : F × F × F, (g₁ x.1 * (g₂ x.2.1 * g₃ x.2.2)) * psiLocal ℚ p (x.1 * y.1 + x.2.1 * y.2.1 + x.2.2 * y.2.2)
        ∂(jacquetHaar3 p)) =
      tateFourier (psiLocal ℚ p) (selfDualHaarAt ℚ p) g₁ y.1 *
        (tateFourier (psiLocal ℚ p) (selfDualHaarAt ℚ p) g₂ y.2.1 *
          tateFourier (psiLocal ℚ p) (selfDualHaarAt ℚ p) g₃ y.2.2) := by
  letI := localBorel ℚ p
  haveI : BorelSpace F := borelSpace_localBorel ℚ p
  haveI := E3ReduceSupplyF.isAddHaarMeasure_selfDualHaarAt p
  rw [jacquetHaar3_eq, ← transform_tensor p g₂ g₃ (y.2.1, y.2.2)]
  simp only [tateFourier]
  rw [← integral_prod_mul]
  congr 1
  funext x
  rw [show x.1 * y.1 + x.2.1 * y.2.1 + x.2.2 * y.2.2 = x.1 * y.1 + (x.2.1 * y.2.1 + x.2.2 * y.2.2) by ring,
    AddChar.map_add_eq_mul]
  push_cast
  ring

theorem integrable_tensor_kernel3 (g₁ g₂ g₃ : F → ℂ) (h₁ : IsSchwartzBruhat g₁) (h₂ : IsSchwartzBruhat g₂)
    (h₃ : IsSchwartzBruhat g₃) (y : F × F × F) :
    letI := localBorel ℚ p
    Integrable (fun x : F × F × F => (g₁ x.1 * (g₂ x.2.1 * g₃ x.2.2)) *
        psiLocal ℚ p (x.1 * y.1 + x.2.1 * y.2.1 + x.2.2 * y.2.2)) (jacquetHaar3 p) := by
  letI := localBorel ℚ p
  haveI : BorelSpace F := borelSpace_localBorel ℚ p
  haveI := E3ReduceSupplyF.isAddHaarMeasure_selfDualHaarAt p
  have hψc : Continuous (fun t : F => (psiLocal ℚ p t : ℂ)) := continuous_psiLocal p
  have hint1 : Integrable (fun t : F => g₁ t * psiLocal ℚ p (t * y.1)) (selfDualHaarAt ℚ p) := by
    refine Continuous.integrable_of_hasCompactSupport ?_ ?_
    · exact h₁.1.continuous.mul (hψc.comp (continuous_id.mul continuous_const))
    · exact h₁.2.mul_right
  have h := hint1.mul_prod (integrable_tensor_kernel p g₂ g₃ h₂ h₃ (y.2.1, y.2.2))
  rw [jacquetHaar3_eq]
  refine h.congr (Filter.Eventually.of_forall fun x => ?_)
  dsimp only
  simp only [AddChar.map_add_eq_mul]
  push_cast
  ring

end ProdFourierInv
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_integral_frame23_mul_eq_integral_matFourier23_dualFrame23_mul.ProdFourierInv"

namespace AffF

variable (p : HeightOneSpectrum (𝓞 ℚ))

local notation "F" => p.adicCompletion ℚ

scoped instance instIsUltrametricDistPi {ι : Type*} [Fintype ι] {Y : ι → Type*} [∀ i, PseudoMetricSpace (Y i)]
    [∀ i, IsUltrametricDist (Y i)] : IsUltrametricDist (∀ i, Y i) := by
  constructor
  intro x y z
  refine (dist_pi_le_iff (le_max_of_le_left dist_nonneg)).2 fun i => ?_
  exact (IsUltrametricDist.dist_triangle_max (x i) (y i) (z i)).trans
    (max_le_max (dist_le_pi_dist x y i) (dist_le_pi_dist y z i))

theorem isNegInvariant_selfDualHaarAt :
    letI := localBorel ℚ p
    (selfDualHaarAt ℚ p).IsNegInvariant := by
  letI := localBorel ℚ p
  haveI : BorelSpace F := borelSpace_localBorel ℚ p
  rw [E3ReduceSupplyF.selfDualHaarAt_eq p]
  exact Measure.IsAddHaarMeasure.isNegInvariant_of_regular _

theorem tateFourier_eq_of_apply_eq (χ : AddChar F ℂ) (c : F) (hχ : ∀ w, χ w = psiLocal ℚ p (c * w))
    (g : F → ℂ) (y : F) :
    letI := localBorel ℚ p
    tateFourier χ (selfDualHaarAt ℚ p) g y = tateFourier (psiLocal ℚ p) (selfDualHaarAt ℚ p) g (c * y) := by
  letI := localBorel ℚ p
  simp only [tateFourier, hχ]
  congr 1; funext x; congr 1; congr 1; ring

theorem isSchwartzBruhat_comp_mul (g : F → ℂ) (hg : IsSchwartzBruhat g) (c : F) (hc : c ≠ 0) :
    IsSchwartzBruhat (fun x => g (c * x)) := by
  have h : (fun x => g (c * x)) = g ∘ (Homeomorph.mulLeft₀ c hc) := by
    funext x; rfl
  rw [h]
  exact ⟨hg.1.comp_continuous (Homeomorph.mulLeft₀ c hc).continuous, hg.2.comp_homeomorph _⟩

theorem inv_twist (ε : F) (hε : ε = 1 ∨ ε = -1) (g : F → ℂ) (hg : IsSchwartzBruhat g) (y : F) :
    letI := localBorel ℚ p
    tateFourier (psiLocal ℚ p) (selfDualHaarAt ℚ p)
        (fun x => tateFourier (psiLocal ℚ p) (selfDualHaarAt ℚ p) g (-ε * x)) (ε * y) = g y := by
  letI := localBorel ℚ p
  haveI : BorelSpace F := borelSpace_localBorel ℚ p
  haveI := E3ReduceSupplyF.isAddHaarMeasure_selfDualHaarAt p
  haveI := isNegInvariant_selfDualHaarAt p
  rcases hε with rfl | rfl
  ·
    have h1 : (fun x : F => tateFourier (psiLocal ℚ p) (selfDualHaarAt ℚ p) g (-1 * x)) =
        fun x => tateFourier (psiLocal ℚ p) (selfDualHaarAt ℚ p) g (-x) := by
      funext x; rw [neg_one_mul]
    rw [h1, one_mul]
    simp only [tateFourier]
    have : (∫ x : F, (∫ t : F, g t * psiLocal ℚ p (t * -x) ∂selfDualHaarAt ℚ p) * psiLocal ℚ p (x * y)
        ∂selfDualHaarAt ℚ p) =
        ∫ x : F, (fun z : F => (∫ t : F, g t * psiLocal ℚ p (t * z) ∂selfDualHaarAt ℚ p) *
          psiLocal ℚ p (z * -y)) (-x) ∂selfDualHaarAt ℚ p := by
      congr 1; funext x; simp only [mul_neg, neg_mul, neg_neg]
    have h2 := integral_neg_eq_self
      (fun z : F => (∫ t : F, g t * psiLocal ℚ p (t * z) ∂selfDualHaarAt ℚ p) * psiLocal ℚ p (z * -y))
      (selfDualHaarAt ℚ p)
    rw [this, h2]
    have := ProdFourierInv.one_var_inv p g hg (-y)
    simp only [tateFourier, neg_neg] at this
    exact this
  ·
    have h1 : (fun x : F => tateFourier (psiLocal ℚ p) (selfDualHaarAt ℚ p) g (-(-1 : F) * x)) =
        tateFourier (psiLocal ℚ p) (selfDualHaarAt ℚ p) g := by
      funext x; rw [neg_neg, one_mul]
    rw [h1, ProdFourierInv.one_var_inv p g hg, neg_mul, one_mul, neg_neg]

end AffF
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_integral_frame23_mul_eq_integral_matFourier23_dualFrame23_mul.ProdFourierInv P2MW.S_LanglandsTunnell_CubicInduction_integral_frame23_mul_eq_integral_matFourier23_dualFrame23_mul.AffF"

namespace AffF

variable (p : HeightOneSpectrum (𝓞 ℚ))

local notation "F" => p.adicCompletion ℚ

def box6 (a00 a10 a01 a11 a02 a12 : F → ℂ) : Matrix (Fin 2) (Fin 3) F → ℂ :=
  fun Y => (a00 (Y 0 0) * a10 (Y 1 0)) * (a01 (Y 0 1) * a11 (Y 1 1)) * (a02 (Y 0 2) * a12 (Y 1 2))

theorem box6_apply (a00 a10 a01 a11 a02 a12 : F → ℂ) (Y : Matrix (Fin 2) (Fin 3) F) :
    box6 p a00 a10 a01 a11 a02 a12 Y = (a00 (Y 0 0) * a10 (Y 1 0)) * (a01 (Y 0 1) * a11 (Y 1 1)) * (a02 (Y 0 2) * a12 (Y 1 2)) :=
  rfl

@[scoped simp] theorem setCol23_e000 (X : Matrix (Fin 2) (Fin 3) F) (u : F × F) :
    setCol23 p X 0 u 0 0 = u.1 := by
  simp [setCol23]
@[scoped simp] theorem setCol23_e001 (X : Matrix (Fin 2) (Fin 3) F) (u : F × F) :
    setCol23 p X 0 u 0 1 = X 0 1 := by
  simp [setCol23]
@[scoped simp] theorem setCol23_e002 (X : Matrix (Fin 2) (Fin 3) F) (u : F × F) :
    setCol23 p X 0 u 0 2 = X 0 2 := by
  simp [setCol23]
@[scoped simp] theorem setCol23_e010 (X : Matrix (Fin 2) (Fin 3) F) (u : F × F) :
    setCol23 p X 0 u 1 0 = u.2 := by
  simp [setCol23]
@[scoped simp] theorem setCol23_e011 (X : Matrix (Fin 2) (Fin 3) F) (u : F × F) :
    setCol23 p X 0 u 1 1 = X 1 1 := by
  simp [setCol23]
@[scoped simp] theorem setCol23_e012 (X : Matrix (Fin 2) (Fin 3) F) (u : F × F) :
    setCol23 p X 0 u 1 2 = X 1 2 := by
  simp [setCol23]
@[scoped simp] theorem setCol23_e100 (X : Matrix (Fin 2) (Fin 3) F) (u : F × F) :
    setCol23 p X 1 u 0 0 = X 0 0 := by
  simp [setCol23]
@[scoped simp] theorem setCol23_e101 (X : Matrix (Fin 2) (Fin 3) F) (u : F × F) :
    setCol23 p X 1 u 0 1 = u.1 := by
  simp [setCol23]
@[scoped simp] theorem setCol23_e102 (X : Matrix (Fin 2) (Fin 3) F) (u : F × F) :
    setCol23 p X 1 u 0 2 = X 0 2 := by
  simp [setCol23]
@[scoped simp] theorem setCol23_e110 (X : Matrix (Fin 2) (Fin 3) F) (u : F × F) :
    setCol23 p X 1 u 1 0 = X 1 0 := by
  simp [setCol23]
@[scoped simp] theorem setCol23_e111 (X : Matrix (Fin 2) (Fin 3) F) (u : F × F) :
    setCol23 p X 1 u 1 1 = u.2 := by
  simp [setCol23]
@[scoped simp] theorem setCol23_e112 (X : Matrix (Fin 2) (Fin 3) F) (u : F × F) :
    setCol23 p X 1 u 1 2 = X 1 2 := by
  simp [setCol23]
@[scoped simp] theorem setCol23_e200 (X : Matrix (Fin 2) (Fin 3) F) (u : F × F) :
    setCol23 p X 2 u 0 0 = X 0 0 := by
  simp [setCol23]
@[scoped simp] theorem setCol23_e201 (X : Matrix (Fin 2) (Fin 3) F) (u : F × F) :
    setCol23 p X 2 u 0 1 = X 0 1 := by
  simp [setCol23]
@[scoped simp] theorem setCol23_e202 (X : Matrix (Fin 2) (Fin 3) F) (u : F × F) :
    setCol23 p X 2 u 0 2 = u.1 := by
  simp [setCol23]
@[scoped simp] theorem setCol23_e210 (X : Matrix (Fin 2) (Fin 3) F) (u : F × F) :
    setCol23 p X 2 u 1 0 = X 1 0 := by
  simp [setCol23]
@[scoped simp] theorem setCol23_e211 (X : Matrix (Fin 2) (Fin 3) F) (u : F × F) :
    setCol23 p X 2 u 1 1 = X 1 1 := by
  simp [setCol23]
@[scoped simp] theorem setCol23_e212 (X : Matrix (Fin 2) (Fin 3) F) (u : F × F) :
    setCol23 p X 2 u 1 2 = u.2 := by
  simp [setCol23]

theorem colFourier23_sum {ι : Type*} (χ : AddChar F ℂ) (j : Fin 3) (B : Finset ι) (c : ι → ℂ)
    (f : ι → Matrix (Fin 2) (Fin 3) F → ℂ) (X : Matrix (Fin 2) (Fin 3) F)
    (hint : letI := localBorel ℚ p; ∀ U ∈ B, Integrable (fun u : F × F => f U (setCol23 p X j u) * χ (u.1 * X 0 j + u.2 * X 1 j))
      ((selfDualHaarAt ℚ p).prod (selfDualHaarAt ℚ p))) :
    colFourier23 p χ j (fun Y => ∑ U ∈ B, c U * f U Y) X = ∑ U ∈ B, c U * colFourier23 p χ j (f U) X := by
  letI := localBorel ℚ p
  simp only [colFourier23_apply]
  have hfun : (fun u : F × F => (∑ U ∈ B, c U * f U (setCol23 p X j u)) * χ (u.1 * X 0 j + u.2 * X 1 j)) =
      fun u => ∑ U ∈ B, c U * (f U (setCol23 p X j u) * χ (u.1 * X 0 j + u.2 * X 1 j)) := by
    funext u; rw [Finset.sum_mul]; refine Finset.sum_congr rfl fun U _ => ?_; ring
  rw [hfun, integral_finsetSum]
  · refine Finset.sum_congr rfl fun U _ => ?_
    rw [integral_const_mul]
  · intro U hU; exact (hint U hU).const_mul _

theorem hfun0_box (χ : AddChar F ℂ) (d : F) (hχ : ∀ w, χ w = psiLocal ℚ p (d * w))
    (a00 a10 a01 a11 a02 a12 : F → ℂ) (X : Matrix (Fin 2) (Fin 3) F) :
    (fun u : F × F => box6 p a00 a10 a01 a11 a02 a12 (setCol23 p X 0 u) * χ (u.1 * X 0 0 + u.2 * X 1 0)) =
      fun u : F × F => (1 * (a01 (X 0 1) * a11 (X 1 1)) * (a02 (X 0 2) * a12 (X 1 2))) *
        ((a00 u.1 * a10 u.2) * psiLocal ℚ p (u.1 * (d * X 0 0) + u.2 * (d * X 1 0))) := by
  funext u
  simp only [box6, setCol23_e000, setCol23_e001, setCol23_e002, setCol23_e010, setCol23_e011, setCol23_e012, hχ]
  rw [show d * (u.1 * X 0 0 + u.2 * X 1 0) = u.1 * (d * X 0 0) + u.2 * (d * X 1 0) by ring]
  ring

theorem col0_box (χ : AddChar F ℂ) (d : F) (hχ : ∀ w, χ w = psiLocal ℚ p (d * w))
    (a00 a10 a01 a11 a02 a12 : F → ℂ) (h0 : IsSchwartzBruhat a00) (h1 : IsSchwartzBruhat a10) :
    letI := localBorel ℚ p
    colFourier23 p χ 0 (box6 p a00 a10 a01 a11 a02 a12) = box6 p (fun x => tateFourier (psiLocal ℚ p) (selfDualHaarAt ℚ p) a00 (d * x)) (fun x => tateFourier (psiLocal ℚ p) (selfDualHaarAt ℚ p) a10 (d * x)) a01 a11 a02 a12 := by
  letI := localBorel ℚ p
  haveI : BorelSpace F := borelSpace_localBorel ℚ p
  haveI := E3ReduceSupplyF.isAddHaarMeasure_selfDualHaarAt p
  funext X
  rw [colFourier23_apply, hfun0_box p χ d hχ, integral_const_mul,
    ProdFourierInv.transform_tensor p a00 a10 (d * X 0 0, d * X 1 0)]
  simp only [box6]
  ring

theorem int0_box (χ : AddChar F ℂ) (d : F) (hχ : ∀ w, χ w = psiLocal ℚ p (d * w))
    (a00 a10 a01 a11 a02 a12 : F → ℂ) (h0 : IsSchwartzBruhat a00) (h1 : IsSchwartzBruhat a10)
    (X : Matrix (Fin 2) (Fin 3) F) :
    letI := localBorel ℚ p
    Integrable (fun u : F × F => box6 p a00 a10 a01 a11 a02 a12 (setCol23 p X 0 u) * χ (u.1 * X 0 0 + u.2 * X 1 0))
      ((selfDualHaarAt ℚ p).prod (selfDualHaarAt ℚ p)) := by
  letI := localBorel ℚ p
  haveI : BorelSpace F := borelSpace_localBorel ℚ p
  haveI := E3ReduceSupplyF.isAddHaarMeasure_selfDualHaarAt p
  rw [hfun0_box p χ d hχ]
  exact (ProdFourierInv.integrable_tensor_kernel p a00 a10 h0 h1 (d * X 0 0, d * X 1 0)).const_mul _

theorem hfun1_box (χ : AddChar F ℂ) (d : F) (hχ : ∀ w, χ w = psiLocal ℚ p (d * w))
    (a00 a10 a01 a11 a02 a12 : F → ℂ) (X : Matrix (Fin 2) (Fin 3) F) :
    (fun u : F × F => box6 p a00 a10 a01 a11 a02 a12 (setCol23 p X 1 u) * χ (u.1 * X 0 1 + u.2 * X 1 1)) =
      fun u : F × F => ((a00 (X 0 0) * a10 (X 1 0)) * 1 * (a02 (X 0 2) * a12 (X 1 2))) *
        ((a01 u.1 * a11 u.2) * psiLocal ℚ p (u.1 * (d * X 0 1) + u.2 * (d * X 1 1))) := by
  funext u
  simp only [box6, setCol23_e100, setCol23_e101, setCol23_e102, setCol23_e110, setCol23_e111, setCol23_e112, hχ]
  rw [show d * (u.1 * X 0 1 + u.2 * X 1 1) = u.1 * (d * X 0 1) + u.2 * (d * X 1 1) by ring]
  ring

theorem col1_box (χ : AddChar F ℂ) (d : F) (hχ : ∀ w, χ w = psiLocal ℚ p (d * w))
    (a00 a10 a01 a11 a02 a12 : F → ℂ) (h0 : IsSchwartzBruhat a01) (h1 : IsSchwartzBruhat a11) :
    letI := localBorel ℚ p
    colFourier23 p χ 1 (box6 p a00 a10 a01 a11 a02 a12) = box6 p a00 a10 (fun x => tateFourier (psiLocal ℚ p) (selfDualHaarAt ℚ p) a01 (d * x)) (fun x => tateFourier (psiLocal ℚ p) (selfDualHaarAt ℚ p) a11 (d * x)) a02 a12 := by
  letI := localBorel ℚ p
  haveI : BorelSpace F := borelSpace_localBorel ℚ p
  haveI := E3ReduceSupplyF.isAddHaarMeasure_selfDualHaarAt p
  funext X
  rw [colFourier23_apply, hfun1_box p χ d hχ, integral_const_mul,
    ProdFourierInv.transform_tensor p a01 a11 (d * X 0 1, d * X 1 1)]
  simp only [box6]
  ring

theorem int1_box (χ : AddChar F ℂ) (d : F) (hχ : ∀ w, χ w = psiLocal ℚ p (d * w))
    (a00 a10 a01 a11 a02 a12 : F → ℂ) (h0 : IsSchwartzBruhat a01) (h1 : IsSchwartzBruhat a11)
    (X : Matrix (Fin 2) (Fin 3) F) :
    letI := localBorel ℚ p
    Integrable (fun u : F × F => box6 p a00 a10 a01 a11 a02 a12 (setCol23 p X 1 u) * χ (u.1 * X 0 1 + u.2 * X 1 1))
      ((selfDualHaarAt ℚ p).prod (selfDualHaarAt ℚ p)) := by
  letI := localBorel ℚ p
  haveI : BorelSpace F := borelSpace_localBorel ℚ p
  haveI := E3ReduceSupplyF.isAddHaarMeasure_selfDualHaarAt p
  rw [hfun1_box p χ d hχ]
  exact (ProdFourierInv.integrable_tensor_kernel p a01 a11 h0 h1 (d * X 0 1, d * X 1 1)).const_mul _

theorem hfun2_box (χ : AddChar F ℂ) (d : F) (hχ : ∀ w, χ w = psiLocal ℚ p (d * w))
    (a00 a10 a01 a11 a02 a12 : F → ℂ) (X : Matrix (Fin 2) (Fin 3) F) :
    (fun u : F × F => box6 p a00 a10 a01 a11 a02 a12 (setCol23 p X 2 u) * χ (u.1 * X 0 2 + u.2 * X 1 2)) =
      fun u : F × F => ((a00 (X 0 0) * a10 (X 1 0)) * (a01 (X 0 1) * a11 (X 1 1)) * 1) *
        ((a02 u.1 * a12 u.2) * psiLocal ℚ p (u.1 * (d * X 0 2) + u.2 * (d * X 1 2))) := by
  funext u
  simp only [box6, setCol23_e200, setCol23_e201, setCol23_e202, setCol23_e210, setCol23_e211, setCol23_e212, hχ]
  rw [show d * (u.1 * X 0 2 + u.2 * X 1 2) = u.1 * (d * X 0 2) + u.2 * (d * X 1 2) by ring]
  ring

theorem col2_box (χ : AddChar F ℂ) (d : F) (hχ : ∀ w, χ w = psiLocal ℚ p (d * w))
    (a00 a10 a01 a11 a02 a12 : F → ℂ) (h0 : IsSchwartzBruhat a02) (h1 : IsSchwartzBruhat a12) :
    letI := localBorel ℚ p
    colFourier23 p χ 2 (box6 p a00 a10 a01 a11 a02 a12) = box6 p a00 a10 a01 a11 (fun x => tateFourier (psiLocal ℚ p) (selfDualHaarAt ℚ p) a02 (d * x)) (fun x => tateFourier (psiLocal ℚ p) (selfDualHaarAt ℚ p) a12 (d * x)) := by
  letI := localBorel ℚ p
  haveI : BorelSpace F := borelSpace_localBorel ℚ p
  haveI := E3ReduceSupplyF.isAddHaarMeasure_selfDualHaarAt p
  funext X
  rw [colFourier23_apply, hfun2_box p χ d hχ, integral_const_mul,
    ProdFourierInv.transform_tensor p a02 a12 (d * X 0 2, d * X 1 2)]
  simp only [box6]
  ring

theorem int2_box (χ : AddChar F ℂ) (d : F) (hχ : ∀ w, χ w = psiLocal ℚ p (d * w))
    (a00 a10 a01 a11 a02 a12 : F → ℂ) (h0 : IsSchwartzBruhat a02) (h1 : IsSchwartzBruhat a12)
    (X : Matrix (Fin 2) (Fin 3) F) :
    letI := localBorel ℚ p
    Integrable (fun u : F × F => box6 p a00 a10 a01 a11 a02 a12 (setCol23 p X 2 u) * χ (u.1 * X 0 2 + u.2 * X 1 2))
      ((selfDualHaarAt ℚ p).prod (selfDualHaarAt ℚ p)) := by
  letI := localBorel ℚ p
  haveI : BorelSpace F := borelSpace_localBorel ℚ p
  haveI := E3ReduceSupplyF.isAddHaarMeasure_selfDualHaarAt p
  rw [hfun2_box p χ d hχ]
  exact (ProdFourierInv.integrable_tensor_kernel p a02 a12 h0 h1 (d * X 0 2, d * X 1 2)).const_mul _

end AffF
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_integral_frame23_mul_eq_integral_matFourier23_dualFrame23_mul.ProdFourierInv P2MW.S_LanglandsTunnell_CubicInduction_integral_frame23_mul_eq_integral_matFourier23_dualFrame23_mul.AffF"

namespace AffF

variable (p : HeightOneSpectrum (𝓞 ℚ))

local notation "F" => p.adicCompletion ℚ

theorem isSchwartzBruhat_T (a : F → ℂ) (ha : IsSchwartzBruhat a) (d : F) (hd : d ≠ 0) :
    letI := localBorel ℚ p
    IsSchwartzBruhat (fun x => tateFourier (psiLocal ℚ p) (selfDualHaarAt ℚ p) a (d * x)) := by
  letI := localBorel ℚ p
  exact isSchwartzBruhat_comp_mul p _ (ProdFourierInv.one_var_SB p a ha) d hd

theorem matFourier23_sum_box6 {ι : Type*} (χ : AddChar F ℂ) (d : F) (hχ : ∀ w, χ w = psiLocal ℚ p (d * w))
    (hd : d ≠ 0) (B : Finset ι) (c : ι → ℂ) (b : ι → Fin 2 → Fin 3 → F → ℂ)
    (hb : ∀ U i j, IsSchwartzBruhat (b U i j)) (X : Matrix (Fin 2) (Fin 3) F) :
    letI := localBorel ℚ p
    matFourier23 p χ (fun Y => ∑ U ∈ B, c U * box6 p (b U 0 0) (b U 1 0) (b U 0 1) (b U 1 1) (b U 0 2) (b U 1 2) Y) X =
      ∑ U ∈ B, c U * box6 p
        (fun x => tateFourier (psiLocal ℚ p) (selfDualHaarAt ℚ p) (b U 0 0) (d * x))
        (fun x => tateFourier (psiLocal ℚ p) (selfDualHaarAt ℚ p) (b U 1 0) (d * x))
        (fun x => tateFourier (psiLocal ℚ p) (selfDualHaarAt ℚ p) (b U 0 1) (d * x))
        (fun x => tateFourier (psiLocal ℚ p) (selfDualHaarAt ℚ p) (b U 1 1) (d * x))
        (fun x => tateFourier (psiLocal ℚ p) (selfDualHaarAt ℚ p) (b U 0 2) (d * x))
        (fun x => tateFourier (psiLocal ℚ p) (selfDualHaarAt ℚ p) (b U 1 2) (d * x)) X := by
  letI := localBorel ℚ p
  have hT : ∀ U i j, IsSchwartzBruhat (fun x => tateFourier (psiLocal ℚ p) (selfDualHaarAt ℚ p) (b U i j) (d * x)) :=
    fun U i j => isSchwartzBruhat_T p _ (hb U i j) d hd
  rw [matFourier23_eq]
  have h2 : colFourier23 p χ 2 (fun Y => ∑ U ∈ B, c U * box6 p (b U 0 0) (b U 1 0) (b U 0 1) (b U 1 1) (b U 0 2) (b U 1 2) Y) =
      fun Y => ∑ U ∈ B, c U * box6 p (b U 0 0) (b U 1 0) (b U 0 1) (b U 1 1)
        (fun x => tateFourier (psiLocal ℚ p) (selfDualHaarAt ℚ p) (b U 0 2) (d * x))
        (fun x => tateFourier (psiLocal ℚ p) (selfDualHaarAt ℚ p) (b U 1 2) (d * x)) Y := by
    funext Y
    rw [colFourier23_sum p χ 2 B c _ Y (fun U _ => int2_box p χ d hχ _ _ _ _ _ _ (hb U 0 2) (hb U 1 2) Y)]
    refine Finset.sum_congr rfl fun U _ => ?_
    rw [col2_box p χ d hχ _ _ _ _ _ _ (hb U 0 2) (hb U 1 2)]
  rw [h2]
  have h1 : colFourier23 p χ 1 (fun Y => ∑ U ∈ B, c U * box6 p (b U 0 0) (b U 1 0) (b U 0 1) (b U 1 1)
        (fun x => tateFourier (psiLocal ℚ p) (selfDualHaarAt ℚ p) (b U 0 2) (d * x))
        (fun x => tateFourier (psiLocal ℚ p) (selfDualHaarAt ℚ p) (b U 1 2) (d * x)) Y) =
      fun Y => ∑ U ∈ B, c U * box6 p (b U 0 0) (b U 1 0)
        (fun x => tateFourier (psiLocal ℚ p) (selfDualHaarAt ℚ p) (b U 0 1) (d * x))
        (fun x => tateFourier (psiLocal ℚ p) (selfDualHaarAt ℚ p) (b U 1 1) (d * x))
        (fun x => tateFourier (psiLocal ℚ p) (selfDualHaarAt ℚ p) (b U 0 2) (d * x))
        (fun x => tateFourier (psiLocal ℚ p) (selfDualHaarAt ℚ p) (b U 1 2) (d * x)) Y := by
    funext Y
    rw [colFourier23_sum p χ 1 B c _ Y (fun U _ => int1_box p χ d hχ _ _ _ _ _ _ (hb U 0 1) (hb U 1 1) Y)]
    refine Finset.sum_congr rfl fun U _ => ?_
    rw [col1_box p χ d hχ _ _ _ _ _ _ (hb U 0 1) (hb U 1 1)]
  rw [h1]
  rw [colFourier23_sum p χ 0 B c _ X (fun U _ => int0_box p χ d hχ _ _ _ _ _ _ (hb U 0 0) (hb U 1 0) X)]
  refine Finset.sum_congr rfl fun U _ => ?_
  rw [col0_box p χ d hχ _ _ _ _ _ _ (hb U 0 0) (hb U 1 0)]

theorem inv_twist_one (ε : F) (hε : ε = 1 ∨ ε = -1) (g : F → ℂ) (hg : IsSchwartzBruhat g) :
    letI := localBorel ℚ p
    tateFourier (psiLocal ℚ p) (selfDualHaarAt ℚ p)
        (fun x => tateFourier (psiLocal ℚ p) (selfDualHaarAt ℚ p) g (-ε * x)) ε = g 1 := by
  have h := inv_twist p ε hε g hg 1
  rwa [mul_one] at h

theorem inv_twist_zero (ε : F) (hε : ε = 1 ∨ ε = -1) (g : F → ℂ) (hg : IsSchwartzBruhat g) :
    letI := localBorel ℚ p
    tateFourier (psiLocal ℚ p) (selfDualHaarAt ℚ p)
        (fun x => tateFourier (psiLocal ℚ p) (selfDualHaarAt ℚ p) g (-ε * x)) 0 = g 0 := by
  have h := inv_twist p ε hε g hg 0
  rwa [mul_zero] at h

theorem frameL00 (a v1 v2 : F) : (!![v1, a, 1; v2, 1, 0] : Matrix (Fin 2) (Fin 3) F) 0 0 = v1 := rfl
theorem frameL10 (a v1 v2 : F) : (!![v1, a, 1; v2, 1, 0] : Matrix (Fin 2) (Fin 3) F) 1 0 = v2 := rfl
theorem frameL01 (a v1 v2 : F) : (!![v1, a, 1; v2, 1, 0] : Matrix (Fin 2) (Fin 3) F) 0 1 = a := rfl
theorem frameL11 (a v1 v2 : F) : (!![v1, a, 1; v2, 1, 0] : Matrix (Fin 2) (Fin 3) F) 1 1 = 1 := rfl
theorem frameL02 (a v1 v2 : F) : (!![v1, a, 1; v2, 1, 0] : Matrix (Fin 2) (Fin 3) F) 0 2 = 1 := rfl
theorem frameL12 (a v1 v2 : F) : (!![v1, a, 1; v2, 1, 0] : Matrix (Fin 2) (Fin 3) F) 1 2 = 0 := rfl
theorem frameR00 (m1 m2 m3 : F) : (!![0, 1, m2; 1, m1, m3] : Matrix (Fin 2) (Fin 3) F) 0 0 = 0 := rfl
theorem frameR10 (m1 m2 m3 : F) : (!![0, 1, m2; 1, m1, m3] : Matrix (Fin 2) (Fin 3) F) 1 0 = 1 := rfl
theorem frameR01 (m1 m2 m3 : F) : (!![0, 1, m2; 1, m1, m3] : Matrix (Fin 2) (Fin 3) F) 0 1 = 1 := rfl
theorem frameR11 (m1 m2 m3 : F) : (!![0, 1, m2; 1, m1, m3] : Matrix (Fin 2) (Fin 3) F) 1 1 = m1 := rfl
theorem frameR02 (m1 m2 m3 : F) : (!![0, 1, m2; 1, m1, m3] : Matrix (Fin 2) (Fin 3) F) 0 2 = m2 := rfl
theorem frameR12 (m1 m2 m3 : F) : (!![0, 1, m2; 1, m1, m3] : Matrix (Fin 2) (Fin 3) F) 1 2 = m3 := rfl

end AffF
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_integral_frame23_mul_eq_integral_matFourier23_dualFrame23_mul.ProdFourierInv P2MW.S_LanglandsTunnell_CubicInduction_integral_frame23_mul_eq_integral_matFourier23_dualFrame23_mul.AffF"

end
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_integral_frame23_mul_eq_integral_matFourier23_dualFrame23_mul.ProdFourierInv P2MW.S_LanglandsTunnell_CubicInduction_integral_frame23_mul_eq_integral_matFourier23_dualFrame23_mul.AffF"

open AffF ProdFourierInv in

theorem solution
    (v : HeightOneSpectrum (𝓞 ℚ)) (η : AddChar (v.adicCompletion ℚ) ℂ)
    (hη : η = psiLocal ℚ v ∨ η = (psiLocal ℚ v)⁻¹)
    (φ : Matrix (Fin 2) (Fin 3) (v.adicCompletion ℚ) → ℂ) (hφ : IsSchwartzBruhat φ) :
    letI := localBorel ℚ v
    ∫ t : v.adicCompletion ℚ × v.adicCompletion ℚ × v.adicCompletion ℚ,
        φ !![t.2.1, t.1, 1; t.2.2, 1, 0] * η (-(t.1 + t.2.2)) ∂(jacquetHaar3 v) =
      ∫ m : v.adicCompletion ℚ × v.adicCompletion ℚ × v.adicCompletion ℚ,
        matFourier23 v η⁻¹ φ !![0, 1, m.2.1; 1, m.1, m.2.2] * η (m.1 + m.2.1) ∂(jacquetHaar3 v) := by
  letI : MeasurableSpace (v.adicCompletion ℚ) := localBorel ℚ v
  haveI : BorelSpace (v.adicCompletion ℚ) := borelSpace_localBorel ℚ v
  haveI := E3ReduceSupplyF.isAddHaarMeasure_selfDualHaarAt v
  classical

  obtain ⟨ε, hε, hηε⟩ : ∃ ε : v.adicCompletion ℚ, (ε = 1 ∨ ε = -1) ∧ ∀ w, η w = psiLocal ℚ v (ε * w) := by
    rcases hη with h | h
    · exact ⟨1, Or.inl rfl, fun w => by rw [h, one_mul]⟩
    · exact ⟨-1, Or.inr rfl, fun w => by rw [h, AddChar.inv_apply, neg_one_mul]⟩
  have hηi : ∀ w, η⁻¹ w = psiLocal ℚ v (-ε * w) := fun w => by
    rw [AddChar.inv_apply, hηε]; congr 1; ring
  have hεne : (-ε : v.adicCompletion ℚ) ≠ 0 := by
    rcases hε with rfl | rfl
    · exact neg_ne_zero.2 one_ne_zero
    · rw [neg_neg]; exact one_ne_zero

  obtain ⟨δ, hδ, B, hB, hsum⟩ :=
    exists_finset_ball_eq_sum_indicator (X := Fin 2 → Fin 3 → v.adicCompletion ℚ) (fun X => φ X) hφ.1 hφ.2
  set aU : Set (Fin 2 → Fin 3 → v.adicCompletion ℚ) → (Fin 2 → Fin 3 → v.adicCompletion ℚ) :=
    fun U => if h : U ∈ B then (hB U h).choose else 0 with haU
  have haU_spec : ∀ U ∈ B, U = Metric.ball (aU U) δ ∧ ∀ x ∈ U, φ x = φ (aU U) := by
    intro U hU
    have : aU U = (hB U hU).choose := by rw [haU]; exact dif_pos hU
    rw [this]
    exact (hB U hU).choose_spec
  set b : Set (Fin 2 → Fin 3 → v.adicCompletion ℚ) → Fin 2 → Fin 3 → v.adicCompletion ℚ → ℂ :=
    fun U i j => (Metric.ball (aU U i j) δ).indicator fun _ => (1 : ℂ) with hb
  have hbSB : ∀ U i j, IsSchwartzBruhat (b U i j) := fun U i j => by
    rw [hb]; exact isSchwartzBruhat_indicator_ball v _ _
  have hpiece : ∀ U ∈ B, ∀ X : Fin 2 → Fin 3 → v.adicCompletion ℚ,
      U.indicator (fun Y => φ Y) X =
        φ (aU U) * box6 v (b U 0 0) (b U 1 0) (b U 0 1) (b U 1 1) (b U 0 2) (b U 1 2) X := by
    intro U hU X
    obtain ⟨hUeq, hconst⟩ := haU_spec U hU
    have hU' : X ∈ U ↔ X ∈ Metric.ball (aU U) δ :=
      ⟨fun h => by rw [← hUeq]; exact h, fun h => by rw [← hUeq] at h; exact h⟩
    have hmem : X ∈ U ↔ ∀ i j, X i j ∈ Metric.ball (aU U i j) δ := by
      rw [hU', Metric.mem_ball, dist_pi_lt_iff hδ]
      refine forall_congr' fun i => ?_
      rw [dist_pi_lt_iff hδ]
      refine forall_congr' fun j => ?_
      rw [Metric.mem_ball]
    simp only [box6_apply, hb]
    by_cases hX : X ∈ U
    · have hall := hmem.1 hX
      rw [Set.indicator_of_mem hX, hconst X hX, Set.indicator_of_mem (hall 0 0), Set.indicator_of_mem (hall 1 0),
        Set.indicator_of_mem (hall 0 1), Set.indicator_of_mem (hall 1 1), Set.indicator_of_mem (hall 0 2),
        Set.indicator_of_mem (hall 1 2)]
      ring
    · rw [Set.indicator_of_notMem hX]
      have hex : ∃ i j, X i j ∉ Metric.ball (aU U i j) δ := by
        by_contra hcon
        push Not at hcon
        exact hX (hmem.2 hcon)
      obtain ⟨i, j, hij⟩ := hex
      fin_cases i <;> fin_cases j <;> (simp at hij; simp [hij])
  have hφeq : φ = fun X => ∑ U ∈ B, φ (aU U) * box6 v (b U 0 0) (b U 1 0) (b U 0 1) (b U 1 1) (b U 0 2) (b U 1 2) X := by
    funext X
    rw [show φ X = ∑ U ∈ B, U.indicator (fun Y => φ Y) X from hsum X]
    exact Finset.sum_congr rfl fun U hU => hpiece U hU X

  set T : (v.adicCompletion ℚ → ℂ) → v.adicCompletion ℚ → ℂ :=
    fun g x => tateFourier (psiLocal ℚ v) (selfDualHaarAt ℚ v) g (-ε * x) with hT
  have hTSB : ∀ U i j, IsSchwartzBruhat (T (b U i j)) := fun U i j => by
    rw [hT]; exact isSchwartzBruhat_T v _ (hbSB U i j) (-ε) hεne

  have hL : ∀ U ∈ B,
      (∫ t : v.adicCompletion ℚ × v.adicCompletion ℚ × v.adicCompletion ℚ,
          box6 v (b U 0 0) (b U 1 0) (b U 0 1) (b U 1 1) (b U 0 2) (b U 1 2) !![t.2.1, t.1, 1; t.2.2, 1, 0] *
            η (-(t.1 + t.2.2)) ∂(jacquetHaar3 v)) =
        (b U 1 1 1 * (b U 0 2 1 * b U 1 2 0)) *
          (tateFourier (psiLocal ℚ v) (selfDualHaarAt ℚ v) (b U 0 1) (-ε) *
            (tateFourier (psiLocal ℚ v) (selfDualHaarAt ℚ v) (b U 0 0) 0 *
              tateFourier (psiLocal ℚ v) (selfDualHaarAt ℚ v) (b U 1 0) (-ε))) := by
    intro U hU
    have hfun : (fun t : v.adicCompletion ℚ × v.adicCompletion ℚ × v.adicCompletion ℚ =>
        box6 v (b U 0 0) (b U 1 0) (b U 0 1) (b U 1 1) (b U 0 2) (b U 1 2) !![t.2.1, t.1, 1; t.2.2, 1, 0] *
          η (-(t.1 + t.2.2))) =
        fun t => (b U 1 1 1 * (b U 0 2 1 * b U 1 2 0)) *
          ((b U 0 1 t.1 * (b U 0 0 t.2.1 * b U 1 0 t.2.2)) *
            psiLocal ℚ v (t.1 * -ε + t.2.1 * 0 + t.2.2 * -ε)) := by
      funext t
      rw [box6_apply, frameL00, frameL10, frameL01, frameL11, frameL02, frameL12, hηε,
        show ε * -(t.1 + t.2.2) = t.1 * -ε + t.2.1 * 0 + t.2.2 * -ε by ring]
      ring
    rw [hfun, integral_const_mul, transform_tensor3 v _ _ _ (hbSB U 0 0) (hbSB U 1 0) (-ε, ((0 : v.adicCompletion ℚ), -ε))]
  have hLint : ∀ U ∈ B, Integrable (fun t : v.adicCompletion ℚ × v.adicCompletion ℚ × v.adicCompletion ℚ =>
        box6 v (b U 0 0) (b U 1 0) (b U 0 1) (b U 1 1) (b U 0 2) (b U 1 2) !![t.2.1, t.1, 1; t.2.2, 1, 0] *
          η (-(t.1 + t.2.2))) (jacquetHaar3 v) := by
    intro U hU
    have hfun : (fun t : v.adicCompletion ℚ × v.adicCompletion ℚ × v.adicCompletion ℚ =>
        box6 v (b U 0 0) (b U 1 0) (b U 0 1) (b U 1 1) (b U 0 2) (b U 1 2) !![t.2.1, t.1, 1; t.2.2, 1, 0] *
          η (-(t.1 + t.2.2))) =
        fun t => (b U 1 1 1 * (b U 0 2 1 * b U 1 2 0)) *
          ((b U 0 1 t.1 * (b U 0 0 t.2.1 * b U 1 0 t.2.2)) *
            psiLocal ℚ v (t.1 * -ε + t.2.1 * 0 + t.2.2 * -ε)) := by
      funext t
      rw [box6_apply, frameL00, frameL10, frameL01, frameL11, frameL02, frameL12, hηε,
        show ε * -(t.1 + t.2.2) = t.1 * -ε + t.2.1 * 0 + t.2.2 * -ε by ring]
      ring
    rw [hfun]
    exact (integrable_tensor_kernel3 v _ _ _ (hbSB U 0 1) (hbSB U 0 0) (hbSB U 1 0) (-ε, ((0 : v.adicCompletion ℚ), -ε))).const_mul _

  have hR : ∀ U ∈ B,
      (∫ m : v.adicCompletion ℚ × v.adicCompletion ℚ × v.adicCompletion ℚ,
          box6 v (T (b U 0 0)) (T (b U 1 0)) (T (b U 0 1)) (T (b U 1 1)) (T (b U 0 2)) (T (b U 1 2))
              !![0, 1, m.2.1; 1, m.1, m.2.2] * η (m.1 + m.2.1) ∂(jacquetHaar3 v)) =
        (T (b U 0 0) 0 * T (b U 1 0) 1 * T (b U 0 1) 1) * (b U 1 1 1 * (b U 0 2 1 * b U 1 2 0)) := by
    intro U hU
    have hfun : (fun m : v.adicCompletion ℚ × v.adicCompletion ℚ × v.adicCompletion ℚ =>
        box6 v (T (b U 0 0)) (T (b U 1 0)) (T (b U 0 1)) (T (b U 1 1)) (T (b U 0 2)) (T (b U 1 2))
            !![0, 1, m.2.1; 1, m.1, m.2.2] * η (m.1 + m.2.1)) =
        fun m => (T (b U 0 0) 0 * T (b U 1 0) 1 * T (b U 0 1) 1) *
          ((T (b U 1 1) m.1 * (T (b U 0 2) m.2.1 * T (b U 1 2) m.2.2)) *
            psiLocal ℚ v (m.1 * ε + m.2.1 * ε + m.2.2 * 0)) := by
      funext m
      rw [box6_apply, frameR00, frameR10, frameR01, frameR11, frameR02, frameR12, hηε,
        show ε * (m.1 + m.2.1) = m.1 * ε + m.2.1 * ε + m.2.2 * 0 by ring]
      ring
    rw [hfun, integral_const_mul, transform_tensor3 v _ _ _ (hTSB U 0 2) (hTSB U 1 2) (ε, (ε, (0 : v.adicCompletion ℚ)))]
    simp only [hT]
    rw [inv_twist_one v ε hε _ (hbSB U 1 1), inv_twist_one v ε hε _ (hbSB U 0 2),
      inv_twist_zero v ε hε _ (hbSB U 1 2)]
  have hRint : ∀ U ∈ B, Integrable (fun m : v.adicCompletion ℚ × v.adicCompletion ℚ × v.adicCompletion ℚ =>
        box6 v (T (b U 0 0)) (T (b U 1 0)) (T (b U 0 1)) (T (b U 1 1)) (T (b U 0 2)) (T (b U 1 2))
            !![0, 1, m.2.1; 1, m.1, m.2.2] * η (m.1 + m.2.1)) (jacquetHaar3 v) := by
    intro U hU
    have hfun : (fun m : v.adicCompletion ℚ × v.adicCompletion ℚ × v.adicCompletion ℚ =>
        box6 v (T (b U 0 0)) (T (b U 1 0)) (T (b U 0 1)) (T (b U 1 1)) (T (b U 0 2)) (T (b U 1 2))
            !![0, 1, m.2.1; 1, m.1, m.2.2] * η (m.1 + m.2.1)) =
        fun m => (T (b U 0 0) 0 * T (b U 1 0) 1 * T (b U 0 1) 1) *
          ((T (b U 1 1) m.1 * (T (b U 0 2) m.2.1 * T (b U 1 2) m.2.2)) *
            psiLocal ℚ v (m.1 * ε + m.2.1 * ε + m.2.2 * 0)) := by
      funext m
      rw [box6_apply, frameR00, frameR10, frameR01, frameR11, frameR02, frameR12, hηε,
        show ε * (m.1 + m.2.1) = m.1 * ε + m.2.1 * ε + m.2.2 * 0 by ring]
      ring
    rw [hfun]
    exact (integrable_tensor_kernel3 v _ _ _ (hTSB U 1 1) (hTSB U 0 2) (hTSB U 1 2) (ε, (ε, (0 : v.adicCompletion ℚ)))).const_mul _

  have hMF : ∀ m : v.adicCompletion ℚ × v.adicCompletion ℚ × v.adicCompletion ℚ,
      matFourier23 v η⁻¹ φ !![0, 1, m.2.1; 1, m.1, m.2.2] =
        ∑ U ∈ B, φ (aU U) * box6 v (T (b U 0 0)) (T (b U 1 0)) (T (b U 0 1)) (T (b U 1 1)) (T (b U 0 2)) (T (b U 1 2))
          !![0, 1, m.2.1; 1, m.1, m.2.2] := by
    intro m
    conv_lhs => rw [hφeq]
    exact matFourier23_sum_box6 v η⁻¹ (-ε) hηi hεne B (fun U => φ (aU U)) b hbSB _

  have hLHS : (∫ t : v.adicCompletion ℚ × v.adicCompletion ℚ × v.adicCompletion ℚ,
        φ !![t.2.1, t.1, 1; t.2.2, 1, 0] * η (-(t.1 + t.2.2)) ∂(jacquetHaar3 v)) =
      ∑ U ∈ B, φ (aU U) * ((b U 1 1 1 * (b U 0 2 1 * b U 1 2 0)) *
          (tateFourier (psiLocal ℚ v) (selfDualHaarAt ℚ v) (b U 0 1) (-ε) *
            (tateFourier (psiLocal ℚ v) (selfDualHaarAt ℚ v) (b U 0 0) 0 *
              tateFourier (psiLocal ℚ v) (selfDualHaarAt ℚ v) (b U 1 0) (-ε)))) := by
    have hfun : (fun t : v.adicCompletion ℚ × v.adicCompletion ℚ × v.adicCompletion ℚ =>
        φ !![t.2.1, t.1, 1; t.2.2, 1, 0] * η (-(t.1 + t.2.2))) =
        fun t => ∑ U ∈ B, φ (aU U) *
          (box6 v (b U 0 0) (b U 1 0) (b U 0 1) (b U 1 1) (b U 0 2) (b U 1 2) !![t.2.1, t.1, 1; t.2.2, 1, 0] *
            η (-(t.1 + t.2.2))) := by
      funext t
      rw [show φ !![t.2.1, t.1, 1; t.2.2, 1, 0] = _ from congrFun hφeq !![t.2.1, t.1, 1; t.2.2, 1, 0],
        Finset.sum_mul]
      refine Finset.sum_congr rfl fun U _ => ?_
      ring
    rw [hfun, integral_finsetSum]
    · refine Finset.sum_congr rfl fun U hU => ?_
      rw [integral_const_mul, hL U hU]
    · intro U hU; exact (hLint U hU).const_mul _
  have hRHS : (∫ m : v.adicCompletion ℚ × v.adicCompletion ℚ × v.adicCompletion ℚ,
        matFourier23 v η⁻¹ φ !![0, 1, m.2.1; 1, m.1, m.2.2] * η (m.1 + m.2.1) ∂(jacquetHaar3 v)) =
      ∑ U ∈ B, φ (aU U) * ((T (b U 0 0) 0 * T (b U 1 0) 1 * T (b U 0 1) 1) * (b U 1 1 1 * (b U 0 2 1 * b U 1 2 0))) := by
    have hfun : (fun m : v.adicCompletion ℚ × v.adicCompletion ℚ × v.adicCompletion ℚ =>
        matFourier23 v η⁻¹ φ !![0, 1, m.2.1; 1, m.1, m.2.2] * η (m.1 + m.2.1)) =
        fun m => ∑ U ∈ B, φ (aU U) *
          (box6 v (T (b U 0 0)) (T (b U 1 0)) (T (b U 0 1)) (T (b U 1 1)) (T (b U 0 2)) (T (b U 1 2))
              !![0, 1, m.2.1; 1, m.1, m.2.2] * η (m.1 + m.2.1)) := by
      funext m
      rw [hMF m, Finset.sum_mul]
      refine Finset.sum_congr rfl fun U _ => ?_
      ring
    rw [hfun, integral_finsetSum]
    · refine Finset.sum_congr rfl fun U hU => ?_
      rw [integral_const_mul, hR U hU]
    · intro U hU; exact (hRint U hU).const_mul _
  rw [hLHS, hRHS]
  refine Finset.sum_congr rfl fun U _ => ?_
  simp only [hT, mul_zero, mul_one]
  ring

end S_LanglandsTunnell_CubicInduction_integral_frame23_mul_eq_integral_matFourier23_dualFrame23_mul
end P2MW
export P2MW.S_LanglandsTunnell_CubicInduction_integral_frame23_mul_eq_integral_matFourier23_dualFrame23_mul (solution)
