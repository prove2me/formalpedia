-- Prove2me | solution 1 for OAI.PrimeDegreePackets.ThetaConstruction.normalizedTheta_hasMellin
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-13T06:45:45.65786+00:00
-- url     : https://prove2.me/submissions/f9cdce91-2699-4b1f-9fc1-84cb41ac024c

import Mathlib
import Definitions.Def_OAIQ244Duke023

section
-- module Solutions.OAIQ244_DUKE.PrimePackets_XiBoundary
attribute [-instance] _root_.OAI.DukePrimeDegree.specialLinear_secondCountable _root_.OAI.DukePrimeDegree.upperRootTransverse_secondCountable _root_.OAI.PrimeDegreePackets.instSecondCountableTopologyLeafTestSpace _root_.OAI.PrimeDegreePackets.rootSliceSecondCountable _root_.ValuationTheory.DiscreteValuationField.DVF.residueField.field _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.commRing _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open scoped Matrix Topology BigOperators Classical TensorProduct ENNReal
open MeasureTheory Filter Set Module
universe u
open scoped TensorProduct
open Set Module
open MeasureTheory Set
open scoped ENNReal
open IsDiscreteValuationRing IsLocalRing
open scoped ENNReal BigOperators
open MeasureTheory Set IsDiscreteValuationRing
open Filter
open scoped BigOperators Topology
open NumberField
open scoped NumberField nonZeroDivisors
open scoped BigOperators ArithmeticFunction.zeta
open Finset
open scoped BigOperators Classical
open Finset Nat ArithmeticFunction BoundingSieve
open scoped BigOperators Classical
open Finset Nat
open scoped BigOperators
open Filter Topology
open scoped nonZeroDivisors
open Ideal NumberField Finset UniqueFactorizationMonoid
open Filter Set Topology NumberField
open scoped Matrix Topology BigOperators Classical TensorProduct ENNReal NumberField Pointwise nonZeroDivisors
open MeasureTheory Filter Set Module NumberField FractionalIdeal Topology TopologicalSpace
open Filter Set Topology
open scoped Matrix Topology BigOperators Classical TensorProduct ENNReal NumberField Pointwise nonZeroDivisors RealInnerProductSpace
open MeasureTheory Filter Set Module NumberField FractionalIdeal Topology TopologicalSpace Matrix
open MeasureTheory Filter Set Module TopologicalSpace
open MeasureTheory Filter Set
open scoped BigOperators Topology ENNReal
open scoped BigOperators Topology ENNReal Classical
open scoped BigOperators Topology ENNReal Classical Matrix Matrix.Norms.Elementwise
open scoped BigOperators Topology ENNReal Classical Matrix Matrix.Norms.Elementwise Pointwise
open scoped BigOperators Topology ENNReal Classical Matrix Pointwise
open scoped BigOperators Topology ENNReal Classical Matrix
open MeasureTheory ProbabilityTheory Filter Set
open Set Filter
open scoped Topology
open scoped Classical
open scoped Topology ENNReal Classical
open scoped ENNReal Classical
open MeasureTheory Set Topology UniformSpace TopologicalSpace
open scoped ENNReal Topology
open MeasureTheory Filter Set Matrix
open scoped Topology Classical
open scoped Matrix Classical
open scoped Topology Classical Matrix
open scoped Classical Pointwise
open scoped Topology Classical ENNReal
open scoped Matrix Topology Classical
open MeasureTheory ProbabilityTheory Set Filter
open scoped Matrix Topology Classical ENNReal ProbabilityTheory
open scoped ENNReal ProbabilityTheory
open Set Filter Topology
open Set Filter Topology MeasureTheory
open MeasureTheory Set Filter Topology
open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped Matrix ENNReal NNReal ProbabilityTheory
open MeasureTheory
open scoped BigOperators ENNReal
open NumberField Finset
open NumberField Filter Set Topology

open MeasureTheory ProbabilityTheory Matrix
open scoped Classical BigOperators ENNReal


namespace PrimeDegreePackets.ThetaConstruction
variable {d : Type*} [Fintype d]

lemma periodizedTorus_apply (f : C(d → ℝ,ℂ))
    (hf : LocallyNormal f) (x : d → ℝ) :
    periodizedTorus f hf (torusProjection x) = ∑' z : d → ℤ, f (x + integerVector z) := by
  rw [periodizedTorus]
  change periodizedReal f (torusRepresentative (torusProjection x)) = _
  rw [periodizedReal_representative f hf,periodizedReal_apply f hf]

lemma unitCube_fundamental : IsAddFundamentalDomain (d → ℤ) (unitCube (d := d)) volume := by
  apply IsAddFundamentalDomain.mk' (MeasurableSet.univ_pi' (fun _ => measurableSet_Ioc)).nullMeasurableSet
  intro x
  refine ⟨fun i => 1 - Int.ceil (x i),?_,?_⟩
  · intro i
    change 0 < ((1-Int.ceil (x i):ℤ):ℝ) + x i ∧
      ((1-Int.ceil (x i):ℤ):ℝ) + x i ≤ 1
    push_cast
    constructor <;> linarith [Int.ceil_lt_add_one (x i),Int.le_ceil (x i)]
  · intro z hz
    ext i
    have H := hz i
    change 0 < (z i:ℝ) + x i ∧ (z i:ℝ) + x i ≤ 1 at H
    have hc : Int.ceil (x i) = 1-z i := Int.ceil_eq_iff.mpr (by push_cast; constructor <;> linarith)
    omega

lemma integral_periodization (f : C(d → ℝ,ℂ)) (hf : Integrable f) :
    (∫ x in unitCube, ∑' z : d → ℤ, f (x + integerVector z)) = ∫ x, f x := by
  have hfd := unitCube_fundamental (d := d)
  have hn : (∑' z : d → ℤ, ∫⁻ x in unitCube, ‖f (z +ᵥ x)‖ₑ) ≠ ⊤ := by
    rw [←hfd.lintegral_eq_tsum'' (fun x => ‖f x‖ₑ)]
    exact hf.hasFiniteIntegral.ne
  have H := integral_tsum
    (fun z : d → ℤ => ((f.continuous.comp (continuous_const.add continuous_id)).aestronglyMeasurable.restrict)) hn
  calc
    _ = ∫ x in unitCube, ∑' z : d → ℤ, f (z +ᵥ x) := by
      apply integral_congr_ae
      filter_upwards [] with x
      apply tsum_congr
      intro z
      change f (x + integerVector z) = f (integerVector z + x)
      rw [add_comm]
    _ = _ := H.trans (hfd.integral_eq_tsum'' f hf).symm

omit [Fintype d] in
lemma torusProjection_add_integer (x : d → ℝ) (z : d → ℤ) :
    torusProjection (x + integerVector z) = torusProjection x :=
  ((torusProjection_eq_iff x (x + integerVector z)).mpr ⟨z,rfl⟩).symm

lemma fourierCharacter_norm (m : d → ℤ) (x : d → ℝ) : ‖fourierCharacter m x‖ = 1 := by
  simp only [fourierCharacter,ContinuousMap.comp_apply,ContinuousMap.coe_mk,
    UnitAddTorus.mFourier,norm_prod]
  simp only [fourier_apply,Circle.norm_coe,Finset.prod_const_one]

lemma fourierCharacter_periodic (m z : d → ℤ) (x : d → ℝ) :
    fourierCharacter m (x + integerVector z) = fourierCharacter m x := by
  change UnitAddTorus.mFourier (-m) (torusProjection (x + integerVector z)) = _
  rw [torusProjection_add_integer]
  rfl

lemma integrable_character_mul (m : d → ℤ) (f : C(d → ℝ,ℂ))
    (hf : Integrable f) : Integrable (fourierCharacter m * f) := by
  apply hf.norm.mono' (fourierCharacter m * f).continuous.aestronglyMeasurable
  filter_upwards [] with x
  simp only [ContinuousMap.mul_apply,norm_mul,fourierCharacter_norm,one_mul]
  exact le_rfl

lemma fourierCoeff_periodizedTorus (f : C(d → ℝ,ℂ))
    (hf : LocallyNormal f)
    (hfInt : Integrable f) (m : d → ℤ) :
    UnitAddTorus.mFourierCoeff (periodizedTorus f hf) m = ∫ x, fourierCharacter m x * f x := by
  rw [UnitAddTorus.mFourierCoeff_eq_integral _ _ (fun _ => 0)]
  simp only [smul_eq_mul,zero_add]
  change (∫ x in unitCube, fourierCharacter m x * periodizedTorus f hf (torusProjection x)) = _
  calc
    _ = ∫ x in unitCube, ∑' z : d → ℤ, (fourierCharacter m * f) (x + integerVector z) := by
      apply integral_congr_ae
      filter_upwards [] with x
      rw [periodizedTorus_apply,←tsum_mul_left]
      apply tsum_congr
      intro z
      rw [ContinuousMap.mul_apply,fourierCharacter_periodic]
    _ = _ := integral_periodization _ (integrable_character_mul m f hfInt)

 

theorem multivariate_poisson (f : C(d → ℝ,ℂ))
    (hf : LocallyNormal f)
    (hfInt : Integrable f)
    (hFourier : Summable (fun m : d → ℤ => ∫ x, fourierCharacter m x * f x))
    (x : d → ℝ) :
    (∑' z : d → ℤ, f (x + integerVector z)) =
      ∑' m : d → ℤ, (∫ y, fourierCharacter m y * f y) *
        UnitAddTorus.mFourier m (torusProjection x) := by
  have hs : Summable (UnitAddTorus.mFourierCoeff (periodizedTorus f hf)) := by
    exact hFourier.congr (fun m => (fourierCoeff_periodizedTorus f hf hfInt m).symm)
  have H := UnitAddTorus.hasSum_mFourier_series_apply_of_summable hs (torusProjection x)
  simpa only [fourierCoeff_periodizedTorus f hf hfInt,smul_eq_mul,periodizedTorus_apply] using H.tsum_eq.symm

end PrimeDegreePackets.ThetaConstruction
end
end

end OAI
end

section
-- module Solutions.OAIQ244_DUKE.PrimePackets_CoordinateLattices
attribute [-instance] _root_.CyclicCohomology.permutationSublattice_discreteTopology _root_.OAI.DukePrimeDegree.latticeSubgroupInverseAction _root_.OAI.DukePrimeDegree.specialLinear_secondCountable _root_.OAI.DukePrimeDegree.upperRootTransverse_secondCountable _root_.OAI.PrimeDegreePackets.instSecondCountableTopologyLeafTestSpace _root_.OAI.PrimeDegreePackets.rootSliceSecondCountable _root_.ValuationTheory.DiscreteValuationField.DVF.maximalIdealPowSuccQuotModule _root_.ValuationTheory.DiscreteValuationField.DVF.residueField.field _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.commRing _root_.CyclicCohomology.binaryCoefficientFamilyCommGroup _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic
attribute [-simp] _root_.ClassFormation.chosenOrbitClassEquiv_symm_apply _root_.CyclicCohomology.additive_toMul_finset_sum_units _root_.LocalFieldTheory.powMonoidHom_range_one_mem
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open scoped Matrix Topology BigOperators Classical TensorProduct ENNReal
open MeasureTheory Filter Set Module
universe u
open scoped TensorProduct
open Set Module
open MeasureTheory Set
open scoped ENNReal
open IsDiscreteValuationRing IsLocalRing
open scoped ENNReal BigOperators
open MeasureTheory Set IsDiscreteValuationRing
open Filter
open scoped BigOperators Topology
open NumberField
open scoped NumberField nonZeroDivisors
open scoped BigOperators ArithmeticFunction.zeta
open Finset
open scoped BigOperators Classical
open Finset Nat ArithmeticFunction BoundingSieve
open scoped BigOperators Classical
open Finset Nat
open scoped BigOperators
open Filter Topology
open scoped nonZeroDivisors
open Ideal NumberField Finset UniqueFactorizationMonoid
open Filter Set Topology NumberField
open scoped Matrix Topology BigOperators Classical TensorProduct ENNReal NumberField Pointwise nonZeroDivisors
open MeasureTheory Filter Set Module NumberField FractionalIdeal Topology TopologicalSpace
open Filter Set Topology
open scoped Matrix Topology BigOperators Classical TensorProduct ENNReal NumberField Pointwise nonZeroDivisors RealInnerProductSpace
open MeasureTheory Filter Set Module NumberField FractionalIdeal Topology TopologicalSpace Matrix
open MeasureTheory Filter Set Module TopologicalSpace
open MeasureTheory Filter Set
open scoped BigOperators Topology ENNReal
open scoped BigOperators Topology ENNReal Classical
open scoped BigOperators Topology ENNReal Classical Matrix Matrix.Norms.Elementwise
open scoped BigOperators Topology ENNReal Classical Matrix Matrix.Norms.Elementwise Pointwise
open scoped BigOperators Topology ENNReal Classical Matrix Pointwise
open scoped BigOperators Topology ENNReal Classical Matrix
open MeasureTheory ProbabilityTheory Filter Set
open Set Filter
open scoped Topology
open scoped Classical
open scoped Topology ENNReal Classical
open scoped ENNReal Classical
open MeasureTheory Set Topology UniformSpace TopologicalSpace
open scoped ENNReal Topology
open MeasureTheory Filter Set Matrix
open scoped Topology Classical
open scoped Matrix Classical
open scoped Topology Classical Matrix
open scoped Classical Pointwise
open scoped Topology Classical ENNReal
open scoped Matrix Topology Classical
open MeasureTheory ProbabilityTheory Set Filter
open scoped Matrix Topology Classical ENNReal ProbabilityTheory
open scoped ENNReal ProbabilityTheory
open Set Filter Topology
open Set Filter Topology MeasureTheory
open MeasureTheory Set Filter Topology
open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped Matrix ENNReal NNReal ProbabilityTheory
open MeasureTheory
open scoped BigOperators ENNReal
open NumberField Finset
open NumberField Filter Set Topology
open MeasureTheory ProbabilityTheory Matrix
open scoped Classical BigOperators ENNReal
open MeasureTheory Set Filter Topology Module
open scoped BigOperators SchwartzMap
namespace PrimeDegreePackets.ThetaConstruction
variable {d : Type*} [Fintype d]

omit [Fintype d] in
lemma integerVector_closedEmbedding : IsClosedEmbedding (integerVector (d := d)) := by
  exact IsClosedEmbedding.piMap (fun _ => Int.isClosedEmbedding_coe_real)

lemma integerVector_tendsto : Tendsto (integerVector (d := d)) cofinite (cocompact _) := by
  simpa only [cocompact_eq_cofinite] using (integerVector_closedEmbedding (d := d)).tendsto_cocompact

lemma integerVectorInLattice_injective : Function.Injective (integerVectorInLattice (d := d)) := by
  intro z w h
  have hv := congrArg Subtype.val h
  ext i
  exact Int.cast_injective (congrFun hv i)

lemma coordinateLattice_rank : Module.finrank ℤ (coordinateLattice (d := d)) = Fintype.card d := by
  rw [ZLattice.rank ℝ (coordinateLattice (d := d))]
  simp

lemma summable_integerVector_rpow {r : ℝ} (hr : r < -(Fintype.card d : ℝ)) :
    Summable (fun z : d → ℤ => ‖integerVector z‖ ^ r) := by
  have hr' : r < -(Module.finrank ℤ (coordinateLattice (d := d)) : ℝ) := by
    simpa only [coordinateLattice_rank] using hr
  have H := ZLattice.summable_norm_rpow (coordinateLattice (d := d)) r hr'
  exact H.comp_injective (i := integerVectorInLattice (d := d))
    (integerVectorInLattice_injective (d := d))

end PrimeDegreePackets.ThetaConstruction

open MeasureTheory Set Filter Topology Module WithLp
open scoped BigOperators SchwartzMap ZeroAtInfty
namespace PrimeDegreePackets.ThetaConstruction
variable {d : Type*} [Fintype d]

 

lemma locallyNormal_of_polynomial_decay (f : C(d → ℝ,ℂ)) (p : ℕ)
    (hp : Fintype.card d < p) (C : ℝ) (hC : 0 < C)
    (hdecay : ∀ x, ‖x‖^p * ‖f x‖ ≤ C) : LocallyNormal f := by
  intro K
  obtain ⟨R,hR⟩ := K.isCompact.isBounded.subset_closedBall 0
  have hsum : Summable (fun z : d → ℤ => C * 2^p * ‖integerVector z‖ ^ (-(p:ℝ))) :=
    (summable_integerVector_rpow (by apply neg_lt_neg; exact_mod_cast hp)).mul_left _
  apply Summable.of_norm_bounded_eventually hsum
  have hz : ∀ᶠ z : d → ℤ in cofinite, 2*|R|+1 < ‖integerVector z‖ := by
    exact ((tendsto_norm_cocompact_atTop (E := d → ℝ)).comp
      (integerVector_tendsto (d := d))).eventually (eventually_gt_atTop (2*|R|+1))
  filter_upwards [hz] with z hz
  rw [norm_norm]
  apply (ContinuousMap.norm_le _ (by positivity)).mpr
  rintro ⟨x,hx⟩
  change ‖f (x + integerVector z)‖ ≤ C * 2^p * ‖integerVector z‖ ^ (-(p:ℝ))
  have hxR : ‖x‖ ≤ R := by simpa using hR hx
  have hzpos : 0 < ‖integerVector z‖ := by linarith [abs_nonneg R]
  have htri := norm_sub_le (x + integerVector z) x
  have hzle : ‖integerVector z‖/2 ≤ ‖x + integerVector z‖ := by
    simp only [add_sub_cancel_left] at htri
    linarith [le_abs_self R]
  have hwpos : 0 < ‖x + integerVector z‖ := lt_of_lt_of_le (by positivity) hzle
  have hbound : (‖integerVector z‖/2)^p * ‖f (x+integerVector z)‖ ≤ C :=
    (mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (by positivity) hzle _) (norm_nonneg _)).trans
      (hdecay _)
  rw [Real.rpow_neg (norm_nonneg _),Real.rpow_natCast]
  apply (le_mul_inv_iff₀ (pow_pos hzpos p)).mpr
  rw [div_pow] at hbound
  have H := (div_le_iff₀ (by positivity : 0 < (2:ℝ)^p)).mp
    (show ‖f (x+integerVector z)‖ * ‖integerVector z‖^p / 2^p ≤ C by
      simpa only [div_mul_eq_mul_div,mul_comm] using hbound)
  exact H

lemma gaussian_polynomial_bound (b : ℝ) (hb : 0 < b) (p : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ t : ℝ, |t|^p * Real.exp (-b*t^2) ≤ C := by
  let h : C₀(ℝ,ℝ) := {
    toFun t := |t|^p * Real.exp (-b*t^2)
    continuous_toFun := by fun_prop
    zero_at_infty' := by
      simpa only [Real.rpow_natCast] using
        tendsto_rpow_abs_mul_exp_neg_mul_sq_cocompact hb (p:ℝ) }
  refine ⟨‖h.toBCF‖+1,by positivity,fun t => ?_⟩
  have H := BoundedContinuousFunction.norm_coe_le_norm h.toBCF t
  exact (le_abs_self (h t)).trans (H.trans (by linarith))

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

lemma coordinateGaussian_decay (A : (d → ℝ) ≃L[ℝ] E) (b : ℝ) (hb : 0 < b) (p : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ x, ‖x‖^p * ‖coordinateGaussian A b x‖ ≤ C := by
  obtain ⟨C,hC,hbound⟩ := gaussian_polynomial_bound b hb p
  let B := ‖A.symm.toContinuousLinearMap‖ + 1
  have hB : 0 < B := by dsimp [B] <;> positivity
  refine ⟨B^p*C,by positivity,fun x => ?_⟩
  have hx : ‖x‖ ≤ B * ‖A x‖ := by
    have H := A.symm.toContinuousLinearMap.le_opNorm (A x)
    simp only [ContinuousLinearEquiv.coe_coe,ContinuousLinearEquiv.symm_apply_apply] at H
    exact H.trans (by dsimp [B] <;> nlinarith [norm_nonneg (A x)])
  have hnorm : ‖coordinateGaussian A b x‖ = Real.exp (-b*‖A x‖^2) := by
    simp [coordinateGaussian,Complex.norm_exp,pow_two]
  rw [hnorm]
  calc
    _ ≤ (B*‖A x‖)^p * Real.exp (-b*‖A x‖^2) :=
      mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (norm_nonneg _) hx _) (Real.exp_nonneg _)
    _ = B^p * (‖A x‖^p * Real.exp (-b*‖A x‖^2)) := by rw [mul_pow,mul_assoc]
    _ ≤ B^p*C := mul_le_mul_of_nonneg_left (by simpa only [abs_norm] using hbound ‖A x‖)
      (pow_nonneg hB.le _)

lemma coordinateGaussian_locallyNormal (A : (d → ℝ) ≃L[ℝ] E) (b : ℝ) (hb : 0 < b) :
    LocallyNormal (coordinateGaussian A b) := by
  obtain ⟨C,hC,hdecay⟩ := coordinateGaussian_decay A b hb (Fintype.card d + 1)
  exact locallyNormal_of_polynomial_decay _ _ (Nat.lt_succ_self _) C hC hdecay

end PrimeDegreePackets.ThetaConstruction

open scoped FourierTransform
namespace PrimeDegreePackets.ThetaConstruction
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

lemma integral_comp_linearEquiv (A : E ≃L[ℝ] E) (f : E → ℂ) :
    (∫ x, f (A x)) = |(LinearMap.det A.toLinearMap)⁻¹| • ∫ x, f x := by
  have H := A.toHomeomorph.measurableEmbedding.integral_map f (μ := (volume : Measure E))
  have hd : LinearMap.det A.toLinearMap ≠ 0 := A.toLinearEquiv.isUnit_det'.ne_zero
  have hm : Measure.map A.toHomeomorph volume = ENNReal.ofReal |(LinearMap.det A.toLinearMap)⁻¹| • volume :=
    Measure.map_linearMap_addHaar_eq_smul_addHaar volume hd
  rw [hm,integral_smul_measure,ENNReal.toReal_ofReal (abs_nonneg _)] at H
  exact H.symm

lemma integrable_comp_linearEquiv_iff (A : E ≃L[ℝ] E) (f : E → ℂ) :
    Integrable (fun x => f (A x)) ↔ Integrable f := by
  have hd : LinearMap.det A.toLinearMap ≠ 0 := A.toLinearEquiv.isUnit_det'.ne_zero
  have hm : Measure.map A.toHomeomorph volume = ENNReal.ofReal |(LinearMap.det A.toLinearMap)⁻¹| • volume :=
    Measure.map_linearMap_addHaar_eq_smul_addHaar volume hd
  change Integrable (f ∘ A.toHomeomorph) volume ↔ Integrable f volume
  rw [←A.toHomeomorph.measurableEmbedding.integrable_map_iff,hm]
  exact integrable_smul_measure (by simp [hd]) (by simp)

lemma fourier_comp_linearEquiv (A : E ≃L[ℝ] E) (f : E → ℂ) (w : E) :
    𝓕 (fun x => f (A x)) w = |(LinearMap.det A.toLinearMap)⁻¹| •
      𝓕 f (A.symm.toContinuousLinearMap.adjoint w) := by
  rw [Real.fourier_eq,Real.fourier_eq]
  have H := integral_comp_linearEquiv A
    (fun x => Real.fourierChar (-inner ℝ x (A.symm.toContinuousLinearMap.adjoint w)) • f x)
  convert H using 1
  all_goals try with_reducible_and_instances rfl
  apply integral_congr_ae
  filter_upwards [] with x
  rw [ContinuousLinearMap.adjoint_inner_right]
  simp

end PrimeDegreePackets.ThetaConstruction

open scoped BigOperators SchwartzMap FourierTransform
namespace PrimeDegreePackets.ThetaConstruction
variable {d : Type*} [Fintype d]

lemma fourierCharacter_eq (m : d → ℤ) (x : d → ℝ) :
    fourierCharacter m x = Real.fourierChar (-(∑ i, x i * (m i:ℝ))) := by
  classical
  simp only [fourierCharacter,ContinuousMap.comp_apply,ContinuousMap.coe_mk,
    UnitAddTorus.mFourier,torusProjection,Pi.neg_apply,
    fourier_coe_apply,Int.cast_neg,Real.fourierChar_apply]
  rw [←Complex.exp_sum]
  congr 1
  push_cast
  simp only [←Finset.sum_neg_distrib,Finset.mul_sum,Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro i _
  ring

end PrimeDegreePackets.ThetaConstruction

open scoped BigOperators FourierTransform
namespace PrimeDegreePackets.ThetaConstruction
variable {d : Type*} [Fintype d]



lemma summable_of_locallyNormal (f : C(d → ℝ,ℂ)) (hf : LocallyNormal f) :
    Summable (fun z : d → ℤ => f (integerVector z)) := by
  have H := ContinuousMap.summable_of_locally_summable_norm hf
  have H' := (ContinuousMap.evalCLM ℂ (x := (0:d→ℝ))).summable H
  simpa [translate] using H'

lemma latticeTheta_summable (B : EuclideanSpace ℝ d ≃L[ℝ] EuclideanSpace ℝ d)
    (b : ℝ) (hb : 0 < b) :
    Summable (fun z : d → ℤ => Complex.exp (-(b:ℂ) * ‖B (euclideanInteger z)‖^2)) := by
  exact summable_of_locallyNormal (coordinateGaussian (coordinateBasis B) b)
    (coordinateGaussian_locallyNormal _ b hb)

lemma coordinate_fourierIntegral (f : (d → ℝ) → ℂ) (m : d → ℤ) :
    𝓕 (fun x : EuclideanSpace ℝ d => f x.ofLp) (euclideanInteger m) =
      ∫ x, fourierCharacter m x * f x := by
  rw [Real.fourier_eq]
  have H := (EuclideanSpace.volume_preserving_symm_measurableEquiv_toLp d).integral_comp
    (MeasurableEquiv.toLp 2 (d → ℝ)).symm.measurableEmbedding
    (fun x => fourierCharacter m x * f x)
  rw [←H]
  apply integral_congr_ae
  filter_upwards [] with x
  rw [Circle.smul_def,smul_eq_mul,fourierCharacter_eq,PiLp.inner_apply]
  congr 1
  congr 1
  apply congrArg Real.fourierChar
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  simp [euclideanInteger,integerVector,mul_comm]

lemma coordinateGaussian_integrable (B : EuclideanSpace ℝ d ≃L[ℝ] EuclideanSpace ℝ d)
    (b : ℝ) (hb : 0 < b) : Integrable (coordinateGaussian (coordinateBasis B) b) := by
  have hI : Integrable (fun x : EuclideanSpace ℝ d => Complex.exp (-(b:ℂ)*‖x‖^2)) := by
    simpa using GaussianFourier.integrable_cexp_neg_mul_sq_norm_add
      (V := EuclideanSpace ℝ d) (b := (b:ℂ)) hb 0 0
  have H := (integrable_comp_linearEquiv_iff B _).mpr hI
  have J := (PiLp.volume_preserving_toLp d).integrable_comp_emb
    (MeasurableEquiv.toLp 2 (d → ℝ)).measurableEmbedding
    (g := fun x : EuclideanSpace ℝ d => Complex.exp (-(b:ℂ) * ‖B x‖^2))
  exact J.mpr H

lemma coordinateGaussian_fourier (B : EuclideanSpace ℝ d ≃L[ℝ] EuclideanSpace ℝ d)
    (b : ℝ) (hb : 0 < b) (m : d → ℤ) :
    (∫ x, fourierCharacter m x * coordinateGaussian (coordinateBasis B) b x) =
      ((|(LinearMap.det B.toLinearMap)⁻¹|:ℝ):ℂ) *
        (Real.pi / (b:ℂ)) ^ ((Fintype.card d:ℂ)/2) *
        Complex.exp (-((Real.pi^2/b:ℝ):ℂ) *
          ‖adjointEquiv B.symm (euclideanInteger m)‖^2) := by
  rw [←coordinate_fourierIntegral]
  change 𝓕 (fun x => Complex.exp (-(b:ℂ) * ‖B x‖^2)) (euclideanInteger m) = _
  rw [fourier_comp_linearEquiv B (fun x => Complex.exp (-(b:ℂ) * ‖x‖^2)),
    fourier_gaussian_innerProductSpace (by exact hb)]
  simp only [Complex.real_smul,finrank_euclideanSpace]
  rw [mul_assoc]
  congr 2
  congr 1
  change -((Real.pi:ℂ)^2) * (‖B.symm.toContinuousLinearMap.adjoint (euclideanInteger m)‖:ℂ)^2 / (b:ℂ) =
    -((Real.pi^2/b:ℝ):ℂ) * (‖B.symm.toContinuousLinearMap.adjoint (euclideanInteger m)‖:ℂ)^2
  push_cast
  ring

 

theorem latticeTheta_inversion (B : EuclideanSpace ℝ d ≃L[ℝ] EuclideanSpace ℝ d)
    (b : ℝ) (hb : 0 < b) :
    latticeTheta B b = ((|(LinearMap.det B.toLinearMap)⁻¹|:ℝ):ℂ) *
      (Real.pi / (b:ℂ)) ^ ((Fintype.card d:ℂ)/2) *
        latticeTheta (adjointEquiv B.symm) (Real.pi^2/b) := by
  have hb' : 0 < Real.pi^2/b := div_pos (sq_pos_of_pos Real.pi_pos) hb
  have hsum : Summable (fun m : d → ℤ =>
      ∫ x, fourierCharacter m x * coordinateGaussian (coordinateBasis B) b x) := by
    simp_rw [coordinateGaussian_fourier B b hb]
    exact (latticeTheta_summable (adjointEquiv B.symm) _ hb').mul_left _
  have H := multivariate_poisson (coordinateGaussian (coordinateBasis B) b)
    (coordinateGaussian_locallyNormal _ b hb) (coordinateGaussian_integrable B b hb) hsum 0
  have hm (m : d → ℤ) : UnitAddTorus.mFourier m (torusProjection (0:d→ℝ)) = 1 := by
    simp [UnitAddTorus.mFourier,torusProjection]
  simp only [zero_add,coordinateGaussian_fourier B b hb,hm,mul_one,tsum_mul_left] at H
  exact H

end PrimeDegreePackets.ThetaConstruction

open MeasureTheory Set Filter Topology Module WithLp Asymptotics
namespace PrimeDegreePackets.ThetaConstruction
variable {d : Type*} [Fintype d]

lemma thetaRemainder_summable (B : EuclideanSpace ℝ d ≃L[ℝ] EuclideanSpace ℝ d)
    {t : ℝ} (ht : 0 < t) : Summable (fun z : NonzeroIntegerVector d =>
      Complex.exp (-(t:ℂ) * ‖B (euclideanInteger z.1)‖^2)) :=
  (latticeTheta_summable B t ht).subtype _

lemma gaussianTerm_norm (t r : ℝ) :
    ‖Complex.exp (-(t:ℂ) * (r:ℂ)^2)‖ = Real.exp (-t*r^2) := by
  simp [Complex.norm_exp,pow_two]

lemma thetaRemainder_eq (B : EuclideanSpace ℝ d ≃L[ℝ] EuclideanSpace ℝ d)
    {t : ℝ} (ht : 0 < t) : thetaRemainder B t = latticeTheta B t - 1 := by
  classical
  let f := fun z : d → ℤ => Complex.exp (-(t:ℂ)*‖B (euclideanInteger z)‖^2)
  have H := (latticeTheta_summable B t ht).tsum_eq_add_tsum_ite 0
  have Hz : euclideanInteger (0 : d → ℤ) = 0 := by ext i; simp [euclideanInteger,integerVector]
  have H0 : f 0 = 1 := by simp [f,Hz]
  change latticeTheta B t = f 0 + ∑' z, if z = 0 then 0 else f z at H
  rw [H0] at H
  have HE : thetaRemainder B t = ∑' z, if z = 0 then 0 else f z := by
    change (∑' z : {z : d → ℤ | z ≠ 0}, f z.1) = _
    rw [tsum_subtype {z : d → ℤ | z ≠ 0} f]
    apply tsum_congr
    intro z
    by_cases hz : z = 0 <;> simp [hz,f]
  rw [HE]
  exact eq_sub_iff_add_eq.mpr ((add_comm _ _).trans H.symm)

lemma thetaRemainder_continuousOn (B : EuclideanSpace ℝ d ≃L[ℝ] EuclideanSpace ℝ d) :
    ContinuousOn (thetaRemainder B) (Set.Ioi 0) := by
  intro t ht
  change 0 < t at ht
  have hc : ContinuousOn (thetaRemainder B) (Set.Ioi (t/2)) := by
    apply continuousOn_tsum (u := fun z : NonzeroIntegerVector d =>
      ‖Complex.exp (-((t/2:ℝ):ℂ)*‖B (euclideanInteger z.1)‖^2)‖)
    · intro z; fun_prop
    · exact (thetaRemainder_summable B (by linarith)).norm
    · intro z x hx
      change t/2 < x at hx
      rw [gaussianTerm_norm,gaussianTerm_norm]
      apply Real.exp_le_exp.mpr
      nlinarith [sq_nonneg ‖B (euclideanInteger z.1)‖]
  exact (hc.continuousAt (Ioi_mem_nhds (by linarith))).continuousWithinAt

lemma euclideanInteger_norm_one_le (z : NonzeroIntegerVector d) :
    1 ≤ ‖euclideanInteger z.1‖ := by
  obtain ⟨i,hi⟩ : ∃ i, z.1 i ≠ 0 := by
    by_contra! H
    exact z.2 (funext H)
  have H : (1:ℝ) ≤ |(z.1 i:ℝ)| := by exact_mod_cast Int.one_le_abs hi
  exact H.trans (by simpa [euclideanInteger,integerVector,Real.norm_eq_abs] using
    PiLp.norm_apply_le (euclideanInteger z.1) i)

lemma theta_lattice_lower_bound (B : EuclideanSpace ℝ d ≃L[ℝ] EuclideanSpace ℝ d) :
    ∃ c : ℝ, 0 < c ∧ ∀ z : NonzeroIntegerVector d, c ≤ ‖B (euclideanInteger z.1)‖ := by
  let R := ‖B.symm.toContinuousLinearMap‖ + 1
  have hR : 0 < R := by dsimp [R] <;> positivity
  refine ⟨R⁻¹,inv_pos.mpr hR,fun z => ?_⟩
  have H := B.symm.toContinuousLinearMap.le_opNorm (B (euclideanInteger z.1))
  simp only [ContinuousLinearEquiv.coe_coe,ContinuousLinearEquiv.symm_apply_apply] at H
  rw [inv_eq_one_div]
  apply (div_le_iff₀ hR).mpr
  rw [mul_comm]
  calc
    1 ≤ ‖euclideanInteger z.1‖ := euclideanInteger_norm_one_le z
    _ ≤ ‖B.symm.toContinuousLinearMap‖ * ‖B (euclideanInteger z.1)‖ := H
    _ ≤ R * ‖B (euclideanInteger z.1)‖ := by dsimp [R] <;> nlinarith [norm_nonneg (B (euclideanInteger z.1))]

lemma thetaRemainder_exponential_bound (B : EuclideanSpace ℝ d ≃L[ℝ] EuclideanSpace ℝ d) :
    ∃ a C : ℝ, 0 < a ∧ 0 ≤ C ∧ ∀ t : ℝ, 1 ≤ t →
      ‖thetaRemainder B t‖ ≤ C * Real.exp (-a*t) := by
  obtain ⟨c,hc,hbound⟩ := theta_lattice_lower_bound B
  let v := fun z : NonzeroIntegerVector d =>
    ‖Complex.exp (-((1/2:ℝ):ℂ) * ‖B (euclideanInteger z.1)‖^2)‖
  have hv : Summable v := (thetaRemainder_summable B (by norm_num : (0:ℝ)<1/2)).norm
  refine ⟨c^2/2,∑' z, v z,by positivity,tsum_nonneg (fun z => norm_nonneg _),fun t ht => ?_⟩
  have ht' : 0 < t := by linarith
  calc
    ‖thetaRemainder B t‖ ≤ ∑' z : NonzeroIntegerVector d,
        ‖Complex.exp (-(t:ℂ)*‖B (euclideanInteger z.1)‖^2)‖ :=
      norm_tsum_le_tsum_norm (thetaRemainder_summable B ht').norm
    _ ≤ ∑' z, v z * Real.exp (-(c^2/2)*t) := by
      apply (thetaRemainder_summable B ht').norm.tsum_le_tsum _ (hv.mul_right _)
      intro z
      dsimp [v]
      rw [gaussianTerm_norm,gaussianTerm_norm,←Real.exp_add]
      have hz := hbound z
      have hz2 : c^2 ≤ ‖B (euclideanInteger z.1)‖^2 := sq_le_sq₀ hc.le (norm_nonneg _) |>.mpr hz
      apply Real.exp_le_exp.mpr
      nlinarith [mul_nonneg (sub_nonneg.mpr ht) (sq_nonneg ‖B (euclideanInteger z.1)‖),
        mul_nonneg ht'.le (sub_nonneg.mpr hz2)]
    _ = _ := tsum_mul_right



end PrimeDegreePackets.ThetaConstruction
end
end

end OAI
end

section
-- module Solutions.OAIQ244_DUKE.PrimePackets_LatticeTheta
attribute [-instance] _root_.OAI.DukePrimeDegree.specialLinear_secondCountable _root_.OAI.DukePrimeDegree.upperRootTransverse_secondCountable _root_.OAI.PrimeDegreePackets.instSecondCountableTopologyLeafTestSpace _root_.OAI.PrimeDegreePackets.rootSliceSecondCountable _root_.ValuationTheory.DiscreteValuationField.DVF.maximalIdealPowSuccQuotModule _root_.ValuationTheory.DiscreteValuationField.DVF.residueField.field _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.commRing _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic
attribute [-simp] _root_.ClassFormation.chosenOrbitClassEquiv_symm_apply _root_.CyclicCohomology.additive_toMul_finset_sum_units _root_.LocalFieldTheory.powMonoidHom_range_one_mem
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open scoped Matrix Topology BigOperators Classical TensorProduct ENNReal
open MeasureTheory Filter Set Module
universe u
open scoped TensorProduct
open Set Module
open MeasureTheory Set
open scoped ENNReal
open IsDiscreteValuationRing IsLocalRing
open scoped ENNReal BigOperators
open MeasureTheory Set IsDiscreteValuationRing
open Filter
open scoped BigOperators Topology
open NumberField
open scoped NumberField nonZeroDivisors
open scoped BigOperators ArithmeticFunction.zeta
open Finset
open scoped BigOperators Classical
open Finset Nat ArithmeticFunction BoundingSieve
open scoped BigOperators Classical
open Finset Nat
open scoped BigOperators
open Filter Topology
open scoped nonZeroDivisors
open Ideal NumberField Finset UniqueFactorizationMonoid
open Filter Set Topology NumberField
open scoped Matrix Topology BigOperators Classical TensorProduct ENNReal NumberField Pointwise nonZeroDivisors
open MeasureTheory Filter Set Module NumberField FractionalIdeal Topology TopologicalSpace
open Filter Set Topology
open scoped Matrix Topology BigOperators Classical TensorProduct ENNReal NumberField Pointwise nonZeroDivisors RealInnerProductSpace
open MeasureTheory Filter Set Module NumberField FractionalIdeal Topology TopologicalSpace Matrix
open MeasureTheory Filter Set Module TopologicalSpace
open MeasureTheory Filter Set
open scoped BigOperators Topology ENNReal
open scoped BigOperators Topology ENNReal Classical
open scoped BigOperators Topology ENNReal Classical Matrix Matrix.Norms.Elementwise
open scoped BigOperators Topology ENNReal Classical Matrix Matrix.Norms.Elementwise Pointwise
open scoped BigOperators Topology ENNReal Classical Matrix Pointwise
open scoped BigOperators Topology ENNReal Classical Matrix
open MeasureTheory ProbabilityTheory Filter Set
open Set Filter
open scoped Topology
open scoped Classical
open scoped Topology ENNReal Classical
open scoped ENNReal Classical
open MeasureTheory Set Topology UniformSpace TopologicalSpace
open scoped ENNReal Topology
open MeasureTheory Filter Set Matrix
open scoped Topology Classical
open scoped Matrix Classical
open scoped Topology Classical Matrix
open scoped Classical Pointwise
open scoped Topology Classical ENNReal
open scoped Matrix Topology Classical
open MeasureTheory ProbabilityTheory Set Filter
open scoped Matrix Topology Classical ENNReal ProbabilityTheory
open scoped ENNReal ProbabilityTheory
open Set Filter Topology
open Set Filter Topology MeasureTheory
open MeasureTheory Set Filter Topology
open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped Matrix ENNReal NNReal ProbabilityTheory
open MeasureTheory
open scoped BigOperators ENNReal
open NumberField Finset
open NumberField Filter Set Topology
open MeasureTheory ProbabilityTheory Matrix
open scoped Classical BigOperators ENNReal
open MeasureTheory Set Filter Topology Module
open scoped BigOperators SchwartzMap
open MeasureTheory Set Filter Topology Module WithLp
open scoped BigOperators SchwartzMap ZeroAtInfty
open scoped FourierTransform
open scoped BigOperators SchwartzMap FourierTransform
open scoped BigOperators FourierTransform
open MeasureTheory Set Filter Topology Module WithLp Asymptotics
open Module WithLp MeasureTheory
open scoped BigOperators Matrix


namespace PrimeDegreePackets.ThetaConstruction
variable {d : Type*} [Fintype d]

lemma normalizedTheta_inversion (B : EuclideanSpace ℝ d ≃L[ℝ] EuclideanSpace ℝ d)
    (t : ℝ) (ht : 0 < t) :
    normalizedTheta B t = ((|(LinearMap.det B.toLinearMap)⁻¹|:ℝ):ℂ) *
      (t:ℂ)^(-((Fintype.card d:ℂ)/2)) * normalizedTheta (adjointEquiv B.symm) t⁻¹ := by
  unfold normalizedTheta
  rw [latticeTheta_inversion B (Real.pi*t) (mul_pos Real.pi_pos ht)]
  have hπ : (Real.pi:ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
  have ht' : (t:ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr ht.ne'
  have h1 : (Real.pi:ℂ) / ((Real.pi*t:ℝ):ℂ) = (t:ℂ)⁻¹ := by
    rw [Complex.ofReal_mul]; field_simp
  have h2 : Real.pi^2/(Real.pi*t) = Real.pi*t⁻¹ := by field_simp
  rw [h1,h2,Complex.inv_cpow_ofReal_nonneg ht.le,←Complex.cpow_neg]

lemma normalizedThetaTail_locallyIntegrable (B : EuclideanSpace ℝ d ≃L[ℝ] EuclideanSpace ℝ d) :
    LocallyIntegrable (normalizedThetaTail B) := by
  have hc : Continuous (fun t : ℝ => thetaRemainder B (Real.pi*max t 1)) :=
    (thetaRemainder_continuousOn B).comp_continuous
      (continuous_const.mul (continuous_id.max continuous_const))
      (fun t => mul_pos Real.pi_pos (lt_of_lt_of_le zero_lt_one (le_max_right t 1)))
  exact hc.locallyIntegrable.indicator measurableSet_Ioi

lemma normalizedThetaTail_bigO_exp (B : EuclideanSpace ℝ d ≃L[ℝ] EuclideanSpace ℝ d) :
    ∃ a : ℝ, 0 < a ∧ normalizedThetaTail B =O[atTop] (fun t => Real.exp (-a*t)) := by
  obtain ⟨a,C,ha,_,hbound⟩ := thetaRemainder_exponential_bound B
  refine ⟨a*Real.pi,mul_pos ha Real.pi_pos,IsBigO.of_bound C ?_⟩
  filter_upwards [eventually_gt_atTop (1:ℝ)] with t ht
  have hpt : 1 ≤ Real.pi*t := by nlinarith [Real.pi_gt_three]
  simpa [normalizedThetaTail,ht,max_eq_left ht.le,Real.norm_eq_abs,
    abs_of_pos (Real.exp_pos _),mul_assoc] using hbound (Real.pi*t) hpt

lemma normalizedThetaTail_bigO_zero (B : EuclideanSpace ℝ d ≃L[ℝ] EuclideanSpace ℝ d)
    (b : ℝ) : normalizedThetaTail B =O[𝓝[>] 0] (fun t : ℝ => t^(-b)) := by
  apply IsBigO.of_bound 0
  have H : ∀ᶠ t : ℝ in 𝓝[>] 0, t < 1 :=
    eventually_nhdsWithin_of_eventually_nhds (eventually_lt_nhds zero_lt_one)
  filter_upwards [H] with t ht
  simp [normalizedThetaTail,not_lt.mpr ht.le]

lemma normalizedThetaTail_mellin_convergent (B : EuclideanSpace ℝ d ≃L[ℝ] EuclideanSpace ℝ d)
    (s : ℂ) : MellinConvergent (normalizedThetaTail B) s := by
  obtain ⟨a,ha,hbound⟩ := normalizedThetaTail_bigO_exp B
  exact mellinConvergent_of_isBigO_rpow_exp ha
    ((normalizedThetaTail_locallyIntegrable B).locallyIntegrableOn (Set.Ioi 0)) hbound
    (normalizedThetaTail_bigO_zero B (s.re-1)) (by linarith)

@[fun_prop] lemma normalizedThetaTail_mellin_differentiable (B : EuclideanSpace ℝ d ≃L[ℝ] EuclideanSpace ℝ d) :
    Differentiable ℂ (mellin (normalizedThetaTail B)) := by
  obtain ⟨a,ha,hbound⟩ := normalizedThetaTail_bigO_exp B
  intro s
  exact mellin_differentiableAt_of_isBigO_rpow_exp ha
    ((normalizedThetaTail_locallyIntegrable B).locallyIntegrableOn (Set.Ioi 0)) hbound
    (normalizedThetaTail_bigO_zero B (s.re-1)) (by linarith)

lemma normalizedThetaTail_eq (B : EuclideanSpace ℝ d ≃L[ℝ] EuclideanSpace ℝ d)
    {t : ℝ} (ht : 1 < t) : normalizedThetaTail B t = normalizedTheta B t - 1 := by
  rw [normalizedThetaTail,indicator_of_mem (show t ∈ Set.Ioi 1 from ht),max_eq_left ht.le]
  exact thetaRemainder_eq B (mul_pos Real.pi_pos (zero_lt_one.trans ht))

lemma normalizedTheta_decomposition (B : EuclideanSpace ℝ d ≃L[ℝ] EuclideanSpace ℝ d)
    {t : ℝ} (ht : 0 < t) (hne : t ≠ 1) :
    normalizedTheta B t - 1 =
      normalizedThetaTail B t +
        ((|(LinearMap.det B.toLinearMap)⁻¹|:ℝ):ℂ) * (t:ℂ)^(-((Fintype.card d:ℂ)/2)) *
          normalizedThetaTail (adjointEquiv B.symm) t⁻¹ +
        ((|(LinearMap.det B.toLinearMap)⁻¹|:ℝ):ℂ) *
          (Set.Ioc 0 1).indicator (fun x : ℝ => (x:ℂ)^(-((Fintype.card d:ℂ)/2))) t -
        (Set.Ioc 0 1).indicator (fun _ : ℝ => (1:ℂ)) t := by
  rcases lt_or_gt_of_ne hne with hlt | hgt
  · have hinv : 1 < t⁻¹ := (one_lt_inv₀ ht).mpr hlt
    rw [normalizedThetaTail_eq _ hinv,
      show normalizedThetaTail B t = 0 by simp [normalizedThetaTail,not_lt.mpr hlt.le],
      indicator_of_mem (show t ∈ Set.Ioc 0 1 from ⟨ht,hlt.le⟩),
      indicator_of_mem (show t ∈ Set.Ioc 0 1 from ⟨ht,hlt.le⟩),normalizedTheta_inversion B t ht]
    ring
  · have hinv : t⁻¹ < 1 := (inv_lt_one₀ (zero_lt_one.trans hgt)).mpr hgt
    rw [normalizedThetaTail_eq _ hgt,
      show normalizedThetaTail (adjointEquiv B.symm) t⁻¹ = 0 by
        simp [normalizedThetaTail,not_lt.mpr hinv.le],
      indicator_of_notMem (show t ∉ Set.Ioc 0 1 from fun h => (not_le_of_gt hgt) h.2),
      indicator_of_notMem (show t ∉ Set.Ioc 0 1 from fun h => (not_le_of_gt hgt) h.2)]
    ring

lemma mellinConvergent_inv {f : ℝ → ℂ} {s : ℂ} :
    MellinConvergent (fun t => f t⁻¹) s ↔ MellinConvergent f (-s) := by
  simpa only [Real.rpow_neg_one,Complex.ofReal_neg,Complex.ofReal_one,div_neg,_root_.div_one] using (MellinConvergent.comp_rpow (f := f) (s := s) (a := -1) (by norm_num))

 

theorem normalizedTheta_hasMellin_oai (B : EuclideanSpace ℝ d ≃L[ℝ] EuclideanSpace ℝ d)
    {s : ℂ} (hs : (Fintype.card d:ℝ)/2 < s.re) :
    HasMellin (fun t => normalizedTheta B t - 1) s (thetaMellinContinuation B s) := by
  let a : ℂ := (Fintype.card d:ℂ)/2
  let c : ℂ := ((|(LinearMap.det B.toLinearMap)⁻¹|:ℝ):ℂ)
  let P := normalizedThetaTail B
  let Q := normalizedThetaTail (adjointEquiv B.symm)
  let R := (Set.Ioc 0 1).indicator (fun t : ℝ => (t:ℂ)^(-a))
  let J := (Set.Ioc 0 1).indicator (fun _ : ℝ => (1:ℂ))
  let q := fun t : ℝ => c • ((t:ℂ)^(-a) • Q t⁻¹)
  have ha : a.re = (Fintype.card d:ℝ)/2 := by simp [a]
  have has : 0 < s.re + (-a).re := by rw [Complex.neg_re,ha]; linarith
  have hs0 : 0 < s.re := lt_of_le_of_lt (by positivity) hs
  have hP : MellinConvergent P s := normalizedThetaTail_mellin_convergent B s
  have hQ : MellinConvergent (fun t => (t:ℂ)^(-a) • Q t⁻¹) s := by
    apply MellinConvergent.cpow_smul.mpr
    apply mellinConvergent_inv.mpr
    exact normalizedThetaTail_mellin_convergent _ _
  have hq : MellinConvergent q s := hQ.const_smul c
  have hR : HasMellin R s (1/(s-a)) := by
    simpa only [sub_eq_add_neg] using hasMellin_cpow_Ioc (-a) has
  have hJ : HasMellin J s (1/s) := hasMellin_one_Ioc hs0
  have hPR := hasMellin_add hP hq
  have hPRR := hasMellin_add hPR.1 (hR.1.const_smul c)
  have HF := hasMellin_sub hPRR.1 hJ.1
  have hqeq : mellin q s = c * mellin Q (a-s) := by
    calc
      mellin q s = c • mellin (fun t => (t:ℂ)^(-a) • Q t⁻¹) s :=
        mellin_const_smul _ s c
      _ = c * mellin Q (a-s) := by
        rw [mellin_cpow_smul,mellin_comp_inv,smul_eq_mul]
        congr 2
        ring
  have HFval : mellin (fun t => (P t + q t) + c • R t - J t) s =
      thetaMellinContinuation B s := by
    rw [HF.2,hPRR.2,hPR.2,hqeq,mellin_const_smul,hR.2,hJ.2,smul_eq_mul]
    simp only [thetaMellinContinuation,P,Q,c,a,mul_one_div]
  have Hne : ∀ᵐ t : ℝ ∂(volume.restrict (Set.Ioi 0)), t ≠ 1 := by
    apply ae_restrict_of_ae
    rw [ae_iff]
    simp
  have HE : (fun t => normalizedTheta B t - 1) =ᵐ[volume.restrict (Set.Ioi 0)]
      (fun t => (P t + q t) + c • R t - J t) := by
    filter_upwards [Hne,ae_restrict_mem measurableSet_Ioi] with t hne ht
    simpa only [P,q,c,a,R,J,smul_eq_mul,mul_assoc] using
      normalizedTheta_decomposition B ht hne
  have HI : (fun t : ℝ => (t:ℂ)^(s-1) • (normalizedTheta B t-1))
      =ᵐ[volume.restrict (Set.Ioi 0)]
      (fun t : ℝ => (t:ℂ)^(s-1) • ((P t+q t)+c • R t-J t)) := by
    filter_upwards [HE] with t ht
    rw [ht]
  refine ⟨HF.1.congr HI.symm, ?_⟩
  exact (integral_congr_ae HI).trans HFval

end PrimeDegreePackets.ThetaConstruction

open Module MeasureTheory
end
end

end OAI
end

theorem solution.{u_1} : type_of% @OAI.PrimeDegreePackets.ThetaConstruction.normalizedTheta_hasMellin_oai.{u_1} := @OAI.PrimeDegreePackets.ThetaConstruction.normalizedTheta_hasMellin_oai.{u_1}
