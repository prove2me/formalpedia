-- Prove2me | solution 1 for LanglandsTunnell.TateLocal.isSchwartzBruhat_prodFourier_and_prodFourier_prodFourier_selfDualHaarAt_eq
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:08.670037+00:00
-- url     : https://prove2.me/submissions/9357b984-05b0-5e79-86bf-650f5065e4be

import Mathlib
import Definitions.Def_LanglandsTunnell_StandardLocalConstantsAt
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

namespace P2MW.S_LanglandsTunnell_TateLocal_isSchwartzBruhat_prodFourier_and_prodFourier_prodFourier_selfDualHaarAt_eq
p2m_attr_erase "instance" "instFiniteResidueFieldAdicCompletionRingOfIntegersWithZeroMultiplicativeInt_definitions NumberField.instCompactSpaceAdicCompletionIntegers Rat.adicCompletion.locallyCompactSpace NumberField.instFiniteResidueFieldAdicCompletionIntegers instWeaklyLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions instCountableOfNumberField_definitions IsDedekindDomain.HeightOneSpectrum.Extension.instAlgebraSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersValEqUnder IsDedekindDomain.HeightOneSpectrum.Extension.instAlgebraSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersValEqUnder_1 IsDedekindDomain.HeightOneSpectrum.instMulActionHomClassAlgHomTensorProductAdicCompletionForallValEqUnder_definitions IsDedekindDomain.HeightOneSpectrum.Extension.instAlgebraAdicCompletionValEqUnder IsDedekindDomain.HeightOneSpectrum.adicCompletion.instFiniteForallValEqUnderOfFiniteDimensional_definitions IsDedekindDomain.HeightOneSpectrum.instIsBiscalarSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersTensorProductCoeAlgHomTensorAdicCompletionIntegersTo IsDedekindDomain.HeightOneSpectrum.Extension.instContinuousSMulAdicCompletionValEqUnder IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsModuleTopology IsDedekindDomain.HeightOneSpectrum.Extension.instFiniteSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersValEqUnderOfFiniteDimensional IsDedekindDomain.HeightOneSpectrum.adicCompletion.instFiniteValEqUnderOfFiniteDimensional_definitions instIsBiscalarTensorProductCoeAlgHomBaseChange_of_algebraMap IsDedekindDomain.HeightOneSpectrum.instIsScalarTowerSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersValEqUnder_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsModuleTopologyPi Submodule.instIsTopologicalModuleSubtypeMem Pi.instTopologicalModule IsTopologicalModule.toContinuousSMul IsTopologicalModule.toContinuousAdd instFunLike SemialgHomClass.toSemilinearMapClass instCoeTCSemialgHom SemialgHomClass.toRingHomClass SemialgHomClass.instSemialgHom"
p2m_attr_erase "simp" "SemialgHom.baseChange_of_algebraMap_tmul_left SemialgHom.baseChangeRightOfAlgebraMap_apply Pi.semialgHomPi_apply Pi.semialgHom_apply Module.Basis.rightBaseChange_apply LinearEquiv.coe_mulLeft LinearEquiv.coe_mulRight WithVal.semialgebraMap_toFun_ofVal Module.Basis.rightBaseChange_repr IsDedekindDomain.HeightOneSpectrum.adicCompletionIntegers.tensorCoe_tmul IsDedekindDomain.HeightOneSpectrum.tensorAdicCompletionIntegersTo_tmul SemialgHom.baseChangeRightOfAlgebraMap_coe IsDedekindDomain.HeightOneSpectrum.adicCompletion.integerBaseChangeLinearEquiv_tmul_apply SemialgHom.baseChange_of_algebraMap_tmul_right IsLocalization.map_moduleTensorEquiv_symm_tmul IsLocalization.leftModuleTensorEquiv_apply IsLocalization.moduleLid_symm_apply IsLocalization.leftModuleTensorEquiv_symm_apply IsLocalization.map_moduleTensorEquiv_tmul IsModuleTopology.continuousLinearEquiv_apply AlgEquiv.extendScalars_symm_apply IsModuleTopology.Module.Basis.equivFun_homeo_symm_apply IsModuleTopology.Module.Basis.equivFun_homeo_apply IsModuleTopology.continuousAlgEquivOfIsBiscalar_apply AlgEquiv.extendScalars_apply IsModuleTopology.continuousLinearEquiv_symm_apply SemialgHom.restrictScalars_toFun SemialgHom.mk.sizeOf_spec SemialgHom.mk.injEq SemialgHom.coe_coe coe_mk TensorProduct.RightActions.smul_def TensorProduct.RightActions.Module.TensorProduct.comm_symm_apply_tmul TensorProduct.RightActions.LinearMap.baseChange_id TensorProduct.RightActions.algebraMap_eval TensorProduct.RightActions.Module.TensorProduct.comm_apply_tmul TensorProduct.RightActions.Algebra.TensorProduct.comm_symm_apply_tmul TensorProduct.RightActions.Algebra.TensorProduct.comm_apply_tmul"

set_option autoImplicit false

open MeasureTheory IsDedekindDomain NumberField NumberField.StandardAddChar LanglandsTunnell.TateLocal
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

theorem isSchwartzBruhat_tensor (g₁ g₂ : F → ℂ) (h₁ : IsSchwartzBruhat g₁) (h₂ : IsSchwartzBruhat g₂) :
    IsSchwartzBruhat (fun y : F × F => g₁ y.1 * g₂ y.2) := by
  refine ⟨(h₁.1.comp_continuous continuous_fst).mul (h₂.1.comp_continuous continuous_snd), ?_⟩
  refine HasCompactSupport.intro (h₁.2.prod h₂.2) ?_
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

end ProdFourierInv
p2m_reactivate "P2MW.S_LanglandsTunnell_TateLocal_isSchwartzBruhat_prodFourier_and_prodFourier_prodFourier_selfDualHaarAt_eq.ProdFourierInv"

end
p2m_reactivate "P2MW.S_LanglandsTunnell_TateLocal_isSchwartzBruhat_prodFourier_and_prodFourier_prodFourier_selfDualHaarAt_eq.ProdFourierInv"

open ProdFourierInv in

theorem solution
    (p : HeightOneSpectrum (𝓞 ℚ))
    (f : p.adicCompletion ℚ × p.adicCompletion ℚ → ℂ) (hf : IsSchwartzBruhat f) :
    letI := localBorel ℚ p
    IsSchwartzBruhat (fun y : p.adicCompletion ℚ × p.adicCompletion ℚ =>
        ∫ x : p.adicCompletion ℚ × p.adicCompletion ℚ,
          f x * psiLocal ℚ p (x.1 * y.1 + x.2 * y.2) ∂((selfDualHaarAt ℚ p).prod (selfDualHaarAt ℚ p))) ∧
      ∀ x : p.adicCompletion ℚ × p.adicCompletion ℚ,
        (∫ y : p.adicCompletion ℚ × p.adicCompletion ℚ,
            (∫ z : p.adicCompletion ℚ × p.adicCompletion ℚ,
                f z * psiLocal ℚ p (z.1 * y.1 + z.2 * y.2) ∂((selfDualHaarAt ℚ p).prod (selfDualHaarAt ℚ p))) *
              psiLocal ℚ p (y.1 * x.1 + y.2 * x.2) ∂((selfDualHaarAt ℚ p).prod (selfDualHaarAt ℚ p))) =
          f (-x) := by
  letI : MeasurableSpace (p.adicCompletion ℚ) := localBorel ℚ p
  classical

  set ν := selfDualHaarAt ℚ p with hν
  set ψ : AddChar (p.adicCompletion ℚ) ℂ := psiLocal ℚ p with hψ

  obtain ⟨δ, hδ, B, hB, hsum⟩ := exists_finset_ball_eq_sum_indicator f hf.1 hf.2

  set aU : Set (p.adicCompletion ℚ × p.adicCompletion ℚ) → p.adicCompletion ℚ × p.adicCompletion ℚ :=
    fun U => if h : U ∈ B then (hB U h).choose else 0 with haU
  have haU_spec : ∀ U ∈ B, U = Metric.ball (aU U) δ ∧ ∀ x ∈ U, f x = f (aU U) := by
    intro U hU
    have : aU U = (hB U hU).choose := by rw [haU]; exact dif_pos hU
    rw [this]
    exact (hB U hU).choose_spec

  set χ₁ : Set (p.adicCompletion ℚ × p.adicCompletion ℚ) → p.adicCompletion ℚ → ℂ :=
    fun U => (Metric.ball (aU U).1 δ).indicator fun _ => (1 : ℂ) with hχ₁
  set χ₂ : Set (p.adicCompletion ℚ × p.adicCompletion ℚ) → p.adicCompletion ℚ → ℂ :=
    fun U => (Metric.ball (aU U).2 δ).indicator fun _ => (1 : ℂ) with hχ₂
  have hχ₁SB : ∀ U, IsSchwartzBruhat (χ₁ U) := fun U => by rw [hχ₁]; exact isSchwartzBruhat_indicator_ball p _ _
  have hχ₂SB : ∀ U, IsSchwartzBruhat (χ₂ U) := fun U => by rw [hχ₂]; exact isSchwartzBruhat_indicator_ball p _ _

  have hpiece : ∀ U ∈ B, ∀ x : p.adicCompletion ℚ × p.adicCompletion ℚ,
      U.indicator f x = f (aU U) * (χ₁ U x.1 * χ₂ U x.2) := by
    intro U hU x
    obtain ⟨hUeq, hconst⟩ := haU_spec U hU
    have hU' : x ∈ U ↔ x ∈ Metric.ball (aU U) δ :=
      ⟨fun h => by rw [← hUeq]; exact h, fun h => by rw [← hUeq] at h; exact h⟩
    have hmem : x ∈ U ↔ x.1 ∈ Metric.ball (aU U).1 δ ∧ x.2 ∈ Metric.ball (aU U).2 δ := by
      refine hU'.trans ?_
      change x ∈ Metric.ball ((aU U).1, (aU U).2) δ ↔ _
      rw [← ball_prod_same, Set.mem_prod]
    rw [hχ₁, hχ₂]
    simp only
    by_cases hx : x ∈ U
    · obtain ⟨h1, h2⟩ := hmem.1 hx
      rw [Set.indicator_of_mem hx, Set.indicator_of_mem h1, Set.indicator_of_mem h2, hconst x hx, mul_one, mul_one]
    · rw [Set.indicator_of_notMem hx]
      by_cases h1 : x.1 ∈ Metric.ball (aU U).1 δ
      · have h2 : x.2 ∉ Metric.ball (aU U).2 δ := fun h2 => hx (hmem.2 ⟨h1, h2⟩)
        rw [Set.indicator_of_notMem h2, mul_zero, mul_zero]
      · rw [Set.indicator_of_notMem h1, zero_mul, mul_zero]

  set Φ : p.adicCompletion ℚ × p.adicCompletion ℚ → ℂ := fun y =>
    ∑ U ∈ B, f (aU U) * (tateFourier ψ ν (χ₁ U) y.1 * tateFourier ψ ν (χ₂ U) y.2) with hΦ
  have htrans : ∀ y : p.adicCompletion ℚ × p.adicCompletion ℚ,
      (∫ x : p.adicCompletion ℚ × p.adicCompletion ℚ, f x * ψ (x.1 * y.1 + x.2 * y.2) ∂(ν.prod ν)) = Φ y := by
    intro y
    have hfun : (fun x : p.adicCompletion ℚ × p.adicCompletion ℚ => f x * ψ (x.1 * y.1 + x.2 * y.2)) =
        fun x => ∑ U ∈ B, f (aU U) * ((χ₁ U x.1 * χ₂ U x.2) * ψ (x.1 * y.1 + x.2 * y.2)) := by
      funext x
      rw [hsum x, Finset.sum_mul]
      refine Finset.sum_congr rfl fun U hU => ?_
      rw [hpiece U hU x]; ring
    rw [hfun, integral_finsetSum]
    · rw [hΦ]
      refine Finset.sum_congr rfl fun U hU => ?_
      rw [integral_const_mul, hψ, hν, transform_tensor p]
    · intro U hU
      exact (by rw [hψ, hν]; exact integrable_tensor_kernel p (χ₁ U) (χ₂ U) (hχ₁SB U) (hχ₂SB U) y :
        Integrable (fun x : p.adicCompletion ℚ × p.adicCompletion ℚ =>
          (χ₁ U x.1 * χ₂ U x.2) * ψ (x.1 * y.1 + x.2 * y.2)) (ν.prod ν)).const_mul _
  have hΦSB : IsSchwartzBruhat Φ := by
    rw [hΦ]
    refine isSchwartzBruhat_finset_sum B _ fun U _ => isSchwartzBruhat_const_mul _ _ ?_
    exact isSchwartzBruhat_tensor p _ _ (by rw [hψ, hν]; exact one_var_SB p _ (hχ₁SB U))
      (by rw [hψ, hν]; exact one_var_SB p _ (hχ₂SB U))
  refine ⟨?_, ?_⟩
  ·
    have : (fun y : p.adicCompletion ℚ × p.adicCompletion ℚ =>
        ∫ x : p.adicCompletion ℚ × p.adicCompletion ℚ, f x * ψ (x.1 * y.1 + x.2 * y.2) ∂(ν.prod ν)) = Φ :=
      funext htrans
    rw [this]; exact hΦSB
  · intro x
    simp_rw [htrans]

    have hfun : (fun y : p.adicCompletion ℚ × p.adicCompletion ℚ => Φ y * ψ (y.1 * x.1 + y.2 * x.2)) =
        fun y => ∑ U ∈ B, f (aU U) *
          ((tateFourier ψ ν (χ₁ U) y.1 * tateFourier ψ ν (χ₂ U) y.2) * ψ (y.1 * x.1 + y.2 * x.2)) := by
      funext y
      rw [hΦ, Finset.sum_mul]
      refine Finset.sum_congr rfl fun U _ => ?_
      ring
    rw [hfun, integral_finsetSum]
    · rw [hsum (-x)]
      refine Finset.sum_congr rfl fun U hU => ?_
      rw [integral_const_mul, hψ, hν, transform_tensor p, one_var_inv p _ (hχ₁SB U), one_var_inv p _ (hχ₂SB U),
        hpiece U hU (-x)]
      rfl
    · intro U _
      exact (by rw [hψ, hν]; exact integrable_tensor_kernel p _ _ (one_var_SB p _ (hχ₁SB U)) (one_var_SB p _ (hχ₂SB U)) x :
        Integrable (fun y : p.adicCompletion ℚ × p.adicCompletion ℚ =>
          (tateFourier ψ ν (χ₁ U) y.1 * tateFourier ψ ν (χ₂ U) y.2) * ψ (y.1 * x.1 + y.2 * x.2)) (ν.prod ν)).const_mul _

end S_LanglandsTunnell_TateLocal_isSchwartzBruhat_prodFourier_and_prodFourier_prodFourier_selfDualHaarAt_eq
end P2MW
export P2MW.S_LanglandsTunnell_TateLocal_isSchwartzBruhat_prodFourier_and_prodFourier_prodFourier_selfDualHaarAt_eq (solution)
