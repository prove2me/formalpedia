-- Prove2me | solution 1 for OAI.PrimeDegreePackets.ThetaConstruction.normalizedPeriodicTheta_decomposition
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-13T06:43:42.970322+00:00
-- url     : https://prove2.me/submissions/9cbd7a4d-4e01-413d-ac34-753a40984491

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



end PrimeDegreePackets.ThetaConstruction

open MeasureTheory Set Filter Topology Module WithLp Asymptotics
end
end

end OAI
end

section
-- module Solutions.OAIQ244_DUKE.PrimePackets_IdealClasses
attribute [-instance] _root_.ValuationTheory.DiscreteValuationField.DVF.maximalIdealPowSuccQuotModule _root_.ValuationTheory.DiscreteValuationField.DVF.residueField.field _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.commRing _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic
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
open scoped BigOperators Classical ArithmeticFunction.Moebius
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
open Module MeasureTheory
open MeasureTheory Module WithLp
open scoped BigOperators NumberField nonZeroDivisors ENNReal
open Complex Set Metric Filter
open Complex Set Metric Filter MeromorphicOn
open scoped Topology ComplexConjugate
open MeasureTheory Set Filter
open scoped ENNReal BigOperators Topology
open MeasureTheory Set Module
open scoped BigOperators ENNReal NumberField nonZeroDivisors
open scoped BigOperators ENNReal NumberField nonZeroDivisors Topology
open Set
open Filter Set Module MeasureTheory
open scoped Topology NumberField
open Filter Set Module MeasureTheory WithLp
open scoped Topology NumberField BigOperators nonZeroDivisors
open scoped Topology NumberField BigOperators nonZeroDivisors ComplexConjugate
open MeasureTheory Set Filter Module WithLp
open scoped Topology BigOperators NumberField nonZeroDivisors
open Complex Set Filter Module
open Complex
open Complex Set Filter
open scoped Topology NumberField ComplexConjugate
open scoped Topology NumberField ComplexConjugate Classical
open Filter Set Topology Module
open MeasureTheory ProbabilityTheory Set Filter TopologicalSpace
open MeasureTheory MeasureTheory.Measure ProbabilityTheory Set Filter
open scoped Matrix Topology Classical ENNReal NNReal ProbabilityTheory
open scoped Matrix Topology Classical ENNReal
open scoped Topology ENNReal
open scoped Matrix Topology ENNReal ProbabilityTheory
open scoped Topology ENNReal CompactlySupported
open MeasureTheory Set Filter TopologicalSpace
open Module Set Matrix MeasureTheory Filter
open scoped NumberField
open CategoryTheory Module
open MeasureTheory Module Set Filter
open scoped BigOperators ENNReal RealInnerProductSpace
open Module Matrix
open scoped NumberField BigOperators
open Module MeasureTheory Set WithLp
open scoped NumberField BigOperators ENNReal
open IntermediateField Module
open Module IntermediateField
open scoped BigOperators NumberField Pointwise
open Module IntermediateField Set
open MeasureTheory Set Module Filter

open scoped BigOperators ENNReal NumberField nonZeroDivisors Topology ComplexConjugate

open Module


namespace PrimeDegreePackets.ThetaConstruction
variable {d : Type*} [Fintype d]


lemma cosetLatticeTheta_summable
    (B : EuclideanSpace ℝ d ≃L[ℝ] EuclideanSpace ℝ d)
    (x : d → ℝ) (b : ℝ) (hb : 0 < b) :
    Summable (fun z : d → ℤ => Complex.exp (-(b:ℂ) *
      ‖B (toLp 2 x + euclideanInteger z)‖^2)) := by
  have H := ContinuousMap.summable_of_locally_summable_norm
    (coordinateGaussian_locallyNormal (coordinateBasis B) b hb)
  have H' := (ContinuousMap.evalCLM ℂ (x := x)).summable H
  simpa [translate, coordinateGaussian, coordinateBasis, euclideanInteger, toLp_add] using H'

lemma cosetPhase_norm (m : d → ℤ) (x : d → ℝ) :
    ‖UnitAddTorus.mFourier m (torusProjection x)‖ = 1 := by
  simp only [UnitAddTorus.mFourier, ContinuousMap.coe_mk, norm_prod,
    fourier_apply, Circle.norm_coe, Finset.prod_const_one]

lemma twistedDualGaussian_summable
    (B : EuclideanSpace ℝ d ≃L[ℝ] EuclideanSpace ℝ d)
    (x : d → ℝ) (b : ℝ) (hb : 0 < b) :
    Summable (fun m : d → ℤ => Complex.exp (-(b:ℂ) *
      ‖B (euclideanInteger m)‖^2) * UnitAddTorus.mFourier m (torusProjection x)) := by
  apply Summable.of_norm_bounded (latticeTheta_summable B b hb).norm
  intro m
  simp [cosetPhase_norm]

 

theorem cosetLatticeTheta_poisson
    (B : EuclideanSpace ℝ d ≃L[ℝ] EuclideanSpace ℝ d)
    (x : d → ℝ) (b : ℝ) (hb : 0 < b) :
    cosetLatticeTheta B x b = ((|(LinearMap.det B.toLinearMap)⁻¹|:ℝ):ℂ) *
      (Real.pi / (b:ℂ)) ^ ((Fintype.card d:ℂ)/2) *
        ∑' m : d → ℤ, Complex.exp (-((Real.pi^2/b:ℝ):ℂ) *
          ‖adjointEquiv B.symm (euclideanInteger m)‖^2) *
          UnitAddTorus.mFourier m (torusProjection x) := by
  have hb' : 0 < Real.pi^2/b := div_pos (sq_pos_of_pos Real.pi_pos) hb
  have hsum : Summable (fun m : d → ℤ =>
      ∫ y, fourierCharacter m y * coordinateGaussian (coordinateBasis B) b y) := by
    simp_rw [coordinateGaussian_fourier B b hb]
    exact (latticeTheta_summable (adjointEquiv B.symm) _ hb').mul_left _
  have H := multivariate_poisson (coordinateGaussian (coordinateBasis B) b)
    (coordinateGaussian_locallyNormal _ b hb) (coordinateGaussian_integrable B b hb) hsum x
  simp only [coordinateGaussian_fourier B b hb, mul_assoc, tsum_mul_left] at H
  simpa [cosetLatticeTheta, coordinateGaussian, coordinateBasis, euclideanInteger, toLp_add,
    mul_assoc] using H



theorem congruenceTheta_poisson {I : Type*} [Fintype I]
    (B : EuclideanSpace ℝ d ≃L[ℝ] EuclideanSpace ℝ d)
    (x : I → d → ℝ) (w : I → ℂ) (b : ℝ) (hb : 0 < b) :
    congruenceTheta B x w b = ((|(LinearMap.det B.toLinearMap)⁻¹|:ℝ):ℂ) *
      (Real.pi / (b:ℂ)) ^ ((Fintype.card d:ℂ)/2) *
        ∑' m : d → ℤ, Complex.exp (-((Real.pi^2/b:ℝ):ℂ) *
          ‖adjointEquiv B.symm (euclideanInteger m)‖^2) *
          congruenceThetaFourierWeight x w m := by
  classical
  let A : ℂ := ((|(LinearMap.det B.toLinearMap)⁻¹|:ℝ):ℂ) *
    (Real.pi / (b:ℂ)) ^ ((Fintype.card d:ℂ)/2)
  let F (m : d → ℤ) := Complex.exp (-((Real.pi^2/b:ℝ):ℂ) *
    ‖adjointEquiv B.symm (euclideanInteger m)‖^2)
  have hb' : 0 < Real.pi^2/b := div_pos (sq_pos_of_pos Real.pi_pos) hb
  have hs (i : I) : Summable (fun m : d → ℤ =>
      w i * (F m * UnitAddTorus.mFourier m (torusProjection (x i)))) :=
    (twistedDualGaussian_summable (adjointEquiv B.symm) (x i) _ hb').mul_left _
  unfold congruenceTheta
  simp_rw [cosetLatticeTheta_poisson B _ b hb]
  change (∑ i, w i * (A * ∑' m, F m *
    UnitAddTorus.mFourier m (torusProjection (x i)))) = _
  calc
    _ = A * ∑ i, ∑' m, w i * (F m *
        UnitAddTorus.mFourier m (torusProjection (x i))) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      rw [tsum_mul_left]
      ring
    _ = A * ∑' m, ∑ i, w i * (F m *
        UnitAddTorus.mFourier m (torusProjection (x i))) := by
      rw [Summable.tsum_finsetSum (fun i _ => hs i)]
    _ = _ := by
      congr 1
      apply tsum_congr
      intro m
      simp only [congruenceThetaFourierWeight, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      ring

end PrimeDegreePackets.ThetaConstruction
end
end

end OAI
end

section
-- module Solutions.OAIQ244_DUKE.PrimePackets_CongruenceLattices
attribute [-instance] _root_.OAI.DukePrimeDegree.instFintypeCyclicSubgroups _root_.ValuationTheory.DiscreteValuationField.DVF.maximalIdealPowSuccQuotModule _root_.ValuationTheory.DiscreteValuationField.DVF.residueField.field _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.commRing _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic
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
open scoped BigOperators Classical ArithmeticFunction.Moebius
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
open Module MeasureTheory
open MeasureTheory Module WithLp
open scoped BigOperators NumberField nonZeroDivisors ENNReal
open Complex Set Metric Filter
open Complex Set Metric Filter MeromorphicOn
open scoped Topology ComplexConjugate
open MeasureTheory Set Filter
open scoped ENNReal BigOperators Topology
open MeasureTheory Set Module
open scoped BigOperators ENNReal NumberField nonZeroDivisors
open scoped BigOperators ENNReal NumberField nonZeroDivisors Topology
open Set
open Filter Set Module MeasureTheory
open scoped Topology NumberField
open Filter Set Module MeasureTheory WithLp
open scoped Topology NumberField BigOperators nonZeroDivisors
open scoped Topology NumberField BigOperators nonZeroDivisors ComplexConjugate
open MeasureTheory Set Filter Module WithLp
open scoped Topology BigOperators NumberField nonZeroDivisors
open Complex Set Filter Module
open Complex
open Complex Set Filter
open scoped Topology NumberField ComplexConjugate
open scoped Topology NumberField ComplexConjugate Classical
open Filter Set Topology Module
open MeasureTheory ProbabilityTheory Set Filter TopologicalSpace
open MeasureTheory MeasureTheory.Measure ProbabilityTheory Set Filter
open scoped Matrix Topology Classical ENNReal NNReal ProbabilityTheory
open scoped Matrix Topology Classical ENNReal
open scoped Topology ENNReal
open scoped Matrix Topology ENNReal ProbabilityTheory
open scoped Topology ENNReal CompactlySupported
open MeasureTheory Set Filter TopologicalSpace
open Module Set Matrix MeasureTheory Filter
open scoped NumberField
open CategoryTheory Module
open MeasureTheory Module Set Filter
open scoped BigOperators ENNReal RealInnerProductSpace
open Module Matrix
open scoped NumberField BigOperators
open Module MeasureTheory Set WithLp
open scoped NumberField BigOperators ENNReal
open IntermediateField Module
open Module IntermediateField
open scoped BigOperators NumberField Pointwise
open Module IntermediateField Set
open MeasureTheory Set Module Filter
open scoped BigOperators ENNReal NumberField nonZeroDivisors Topology ComplexConjugate
open Module
namespace PrimeDegreePackets.ThetaConstruction
variable {d : Type*} [Fintype d]

attribute [local instance] OAI.PrimeDegreePackets.ThetaConstruction.congruenceLatticesDecidableEq
omit [Fintype d] in
lemma scaledInteger_congruence (N : ℕ) [NeZero N]
    (r : d → Fin N) (q : d → ℤ) :
    (N : ℝ)⁻¹ • euclideanInteger ((integerCongruenceEquiv N).symm (r,q)) =
      toLp 2 (congruencePoint N r) + euclideanInteger q := by
  ext i
  simp only [integerCongruenceEquiv, Equiv.coe_fn_symm_mk, Int.divModEquiv_symm_apply,
    euclideanInteger, integerVector, congruencePoint, PiLp.smul_apply, PiLp.add_apply,
    Int.cast_add, Int.cast_mul, Int.cast_natCast, smul_eq_mul]
  have hN : (N : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne N)
  field_simp
  ring

omit [Fintype d] in
lemma scaledInteger_congruence_pair (N : ℕ) [NeZero N]
    (rq : (d → Fin N) × (d → ℤ)) :
    (N : ℝ)⁻¹ • euclideanInteger ((integerCongruenceEquiv N).symm rq) =
      toLp 2 (congruencePoint N rq.1) + euclideanInteger rq.2 :=
  scaledInteger_congruence N rq.1 rq.2



lemma congruenceProduct_summable
    (B : EuclideanSpace ℝ d ≃L[ℝ] EuclideanSpace ℝ d)
    (N : ℕ) [NeZero N] (w : (d → Fin N) → ℂ) (b : ℝ) (hb : 0 < b) :
    Summable (fun rq : (d → Fin N) × (d → ℤ) => w rq.1 *
      Complex.exp (-(b:ℂ) * ‖B (toLp 2 (congruencePoint N rq.1) +
        euclideanInteger rq.2)‖^2)) := by
  classical
  apply Summable.of_norm
  apply (summable_prod_of_nonneg (fun _ => norm_nonneg _)).2
  exact ⟨fun r => ((cosetLatticeTheta_summable B (congruencePoint N r) b hb).mul_left
    (w r)).norm, Summable.of_finite⟩


theorem periodicLatticeTheta_eq_congruenceTheta
    (B : EuclideanSpace ℝ d ≃L[ℝ] EuclideanSpace ℝ d)
    (N : ℕ) [NeZero N] (w : (d → Fin N) → ℂ) (b : ℝ) (hb : 0 < b) :
    periodicLatticeTheta B N w b = congruenceTheta B (congruencePoint N) w b := by
  classical
  unfold periodicLatticeTheta
  rw [← (integerCongruenceEquiv N).symm.tsum_eq]
  simp only [Equiv.apply_symm_apply, scaledInteger_congruence_pair]
  rw [(congruenceProduct_summable B N w b hb).tsum_prod, tsum_fintype]
  simp only [congruenceTheta, cosetLatticeTheta, tsum_mul_left]



end PrimeDegreePackets.ThetaConstruction


namespace PrimeDegreePackets.ThetaConstruction
variable {d : Type*} [Fintype d]

lemma congruenceThetaFourierWeight_bound {I : Type*} [Fintype I]
    (x : I → d → ℝ) (w : I → ℂ) (m : d → ℤ) :
    ‖congruenceThetaFourierWeight x w m‖ ≤ ∑ i, ‖w i‖ := by
  calc
    _ ≤ ∑ i, ‖w i * UnitAddTorus.mFourier m (torusProjection (x i))‖ := norm_sum_le _ _
    _ = _ := by simp only [norm_mul, cosetPhase_norm, mul_one]



end PrimeDegreePackets.ThetaConstruction


namespace PrimeDegreePackets.ThetaConstruction
variable {d : Type*} [Fintype d]

attribute [local instance] OAI.PrimeDegreePackets.ThetaConstruction.congruenceLatticesGaussianDecidableEq
lemma weightedLatticeGaussian_summable
    (B : EuclideanSpace ℝ d ≃L[ℝ] EuclideanSpace ℝ d)
    (a : (d → ℤ) → ℂ) (M : ℝ) (ha : ∀ z, ‖a z‖ ≤ M)
    {t : ℝ} (ht : 0 < t) : Summable (fun z : d → ℤ =>
      a z * Complex.exp (-(t:ℂ) * ‖B (euclideanInteger z)‖^2)) := by
  apply Summable.of_norm_bounded ((latticeTheta_summable B t ht).norm.mul_left M)
  intro z
  rw [norm_mul]
  exact mul_le_mul_of_nonneg_right (ha z) (norm_nonneg _)

lemma weightedLatticeGaussian_decomposition
    (B : EuclideanSpace ℝ d ≃L[ℝ] EuclideanSpace ℝ d)
    (a : (d → ℤ) → ℂ) (M : ℝ) (ha : ∀ z, ‖a z‖ ≤ M)
    {t : ℝ} (ht : 0 < t) :
    (∑' z : d → ℤ, a z * Complex.exp (-(t:ℂ) * ‖B (euclideanInteger z)‖^2)) =
      a 0 + weightedThetaRemainder B a t := by
  classical
  let f := fun z : d → ℤ => a z * Complex.exp (-(t:ℂ) * ‖B (euclideanInteger z)‖^2)
  have H := (weightedLatticeGaussian_summable B a M ha ht).tsum_eq_add_tsum_ite 0
  have Hz : euclideanInteger (0 : d → ℤ) = 0 := by ext i; simp [euclideanInteger,integerVector]
  have H0 : f 0 = a 0 := by simp [f, Hz]
  change (∑' z, f z) = f 0 + ∑' z, if z = 0 then 0 else f z at H
  rw [H0] at H
  have HE : weightedThetaRemainder B a t = ∑' z, if z = 0 then 0 else f z := by
    change (∑' z : {z : d → ℤ | z ≠ 0}, f z.1) = _
    rw [tsum_subtype {z : d → ℤ | z ≠ 0} f]
    apply tsum_congr
    intro z
    by_cases hz : z = 0 <;> simp [hz,f]
  rw [HE]
  exact H

 

theorem congruenceTheta_poisson_zero_mode {I : Type*} [Fintype I]
    (B : EuclideanSpace ℝ d ≃L[ℝ] EuclideanSpace ℝ d)
    (x : I → d → ℝ) (w : I → ℂ) (b : ℝ) (hb : 0 < b) :
    congruenceTheta B x w b = ((|(LinearMap.det B.toLinearMap)⁻¹|:ℝ):ℂ) *
      (Real.pi / (b:ℂ)) ^ ((Fintype.card d:ℂ)/2) *
        ((∑ i, w i) + weightedThetaRemainder (adjointEquiv B.symm)
          (congruenceThetaFourierWeight x w) (Real.pi^2/b)) := by
  rw [congruenceTheta_poisson B x w b hb]
  have ht : 0 < Real.pi^2/b := div_pos (sq_pos_of_pos Real.pi_pos) hb
  congr 1
  rw [← congruenceThetaFourierWeight_zero x w,
    ← weightedLatticeGaussian_decomposition _ _ (∑ i, ‖w i‖)
      (congruenceThetaFourierWeight_bound x w) ht]
  apply tsum_congr
  intro z
  exact mul_comm _ _



lemma congruenceWeight_bound (N : ℕ) (w : (d → Fin N) → ℂ) (r : d → Fin N) :
    ‖w r‖ ≤ ∑ j, ‖w j‖ :=
  Finset.single_le_sum (fun _ _ => norm_nonneg _) (Finset.mem_univ r)

lemma scaledInteger_gaussian_exponent
    (B : EuclideanSpace ℝ d ≃L[ℝ] EuclideanSpace ℝ d)
    (N : ℕ) [NeZero N] (b : ℝ) (z : d → ℤ) :
    -(b:ℂ) * ‖B ((N:ℝ)⁻¹ • euclideanInteger z)‖^2 =
      -((b/(N:ℝ)^2:ℝ):ℂ) * ‖B (euclideanInteger z)‖^2 := by
  have hN : 0 < (N:ℝ) := Nat.cast_pos.mpr (Nat.pos_of_ne_zero (NeZero.ne N))
  rw [map_smul, norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hN)]
  push_cast
  ring

 

theorem periodicLatticeTheta_zero_mode
    (B : EuclideanSpace ℝ d ≃L[ℝ] EuclideanSpace ℝ d)
    (N : ℕ) [NeZero N] (w : (d → Fin N) → ℂ) (b : ℝ) (hb : 0 < b) :
    periodicLatticeTheta B N w b =
      w ((integerCongruenceEquiv N (0 : d → ℤ)).1) +
        weightedThetaRemainder B (fun z => w ((integerCongruenceEquiv N z).1))
          (b / (N:ℝ)^2) := by
  unfold periodicLatticeTheta
  simp_rw [scaledInteger_gaussian_exponent]
  apply weightedLatticeGaussian_decomposition B _ (∑ i, ‖w i‖)
    (fun z => congruenceWeight_bound N w _)
  exact div_pos hb (sq_pos_of_pos (Nat.cast_pos.mpr (Nat.pos_of_ne_zero (NeZero.ne N))))

end PrimeDegreePackets.ThetaConstruction


end
end

end OAI
end

section
-- module Solutions.OAIQ244_DUKE.PrimePackets_PeriodicTheta
attribute [-instance] _root_.OAI.DukePrimeDegree.instFintypeCyclicSubgroups _root_.ValuationTheory.DiscreteValuationField.DVF.maximalIdealPowSuccQuotModule _root_.ValuationTheory.DiscreteValuationField.DVF.residueField.field _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.commRing _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic
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
open scoped BigOperators Classical ArithmeticFunction.Moebius
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
open Module MeasureTheory
open MeasureTheory Module WithLp
open scoped BigOperators NumberField nonZeroDivisors ENNReal
open Complex Set Metric Filter
open Complex Set Metric Filter MeromorphicOn
open scoped Topology ComplexConjugate
open MeasureTheory Set Filter
open scoped ENNReal BigOperators Topology
open MeasureTheory Set Module
open scoped BigOperators ENNReal NumberField nonZeroDivisors
open scoped BigOperators ENNReal NumberField nonZeroDivisors Topology
open Set
open Filter Set Module MeasureTheory
open scoped Topology NumberField
open Filter Set Module MeasureTheory WithLp
open scoped Topology NumberField BigOperators nonZeroDivisors
open scoped Topology NumberField BigOperators nonZeroDivisors ComplexConjugate
open MeasureTheory Set Filter Module WithLp
open scoped Topology BigOperators NumberField nonZeroDivisors
open Complex Set Filter Module
open Complex
open Complex Set Filter
open scoped Topology NumberField ComplexConjugate
open scoped Topology NumberField ComplexConjugate Classical
open Filter Set Topology Module
open MeasureTheory ProbabilityTheory Set Filter TopologicalSpace
open MeasureTheory MeasureTheory.Measure ProbabilityTheory Set Filter
open scoped Matrix Topology Classical ENNReal NNReal ProbabilityTheory
open scoped Matrix Topology Classical ENNReal
open scoped Topology ENNReal
open scoped Matrix Topology ENNReal ProbabilityTheory
open scoped Topology ENNReal CompactlySupported
open MeasureTheory Set Filter TopologicalSpace
open Module Set Matrix MeasureTheory Filter
open scoped NumberField
open CategoryTheory Module
open MeasureTheory Module Set Filter
open scoped BigOperators ENNReal RealInnerProductSpace
open Module Matrix
open scoped NumberField BigOperators
open Module MeasureTheory Set WithLp
open scoped NumberField BigOperators ENNReal
open IntermediateField Module
open Module IntermediateField
open scoped BigOperators NumberField Pointwise
open Module IntermediateField Set
open MeasureTheory Set Module Filter
open scoped BigOperators ENNReal NumberField nonZeroDivisors Topology ComplexConjugate
open Module
namespace PrimeDegreePackets.ThetaConstruction
variable {d : Type*} [Fintype d]

attribute [local instance] OAI.PrimeDegreePackets.ThetaConstruction.periodicThetaDecidableEq
lemma normalizedPeriodicTheta_primal
    (B : EuclideanSpace ℝ d ≃L[ℝ] EuclideanSpace ℝ d)
    (N : ℕ) [NeZero N] (w : (d → Fin N) → ℂ) (t : ℝ) (ht : 0 < t) :
    normalizedPeriodicTheta B N w t = periodicPrimalWeight N w 0 +
      weightedThetaRemainder B (periodicPrimalWeight N w) ((Real.pi/(N:ℝ)^2)*t) := by
  rw [normalizedPeriodicTheta, periodicLatticeTheta_zero_mode B N w _ (mul_pos Real.pi_pos ht)]
  congr 1
  congr 1
  ring

lemma normalizedPeriodicTheta_dual
    (B : EuclideanSpace ℝ d ≃L[ℝ] EuclideanSpace ℝ d)
    (N : ℕ) [NeZero N] (w : (d → Fin N) → ℂ) (t : ℝ) (ht : 0 < t) :
    normalizedPeriodicTheta B N w t = ((|(LinearMap.det B.toLinearMap)⁻¹|:ℝ):ℂ) *
      (t:ℂ)^(-((Fintype.card d:ℂ)/2)) * ((∑ i, w i) +
        weightedThetaRemainder (adjointEquiv B.symm) (periodicDualWeight N w) (Real.pi*t⁻¹)) := by
  rw [normalizedPeriodicTheta, periodicLatticeTheta_eq_congruenceTheta B N w _
    (mul_pos Real.pi_pos ht), congruenceTheta_poisson_zero_mode B _ w _ (mul_pos Real.pi_pos ht)]
  have hπ : (Real.pi:ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
  have ht' : (t:ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr ht.ne'
  have h1 : (Real.pi:ℂ) / ((Real.pi*t:ℝ):ℂ) = (t:ℂ)⁻¹ := by
    rw [Complex.ofReal_mul]; field_simp
  have h2 : Real.pi^2/(Real.pi*t) = Real.pi*t⁻¹ := by field_simp
  rw [h1,h2,Complex.inv_cpow_ofReal_nonneg ht.le,←Complex.cpow_neg]
  rfl

 

lemma normalizedPeriodicTheta_decomposition_oai
    (B : EuclideanSpace ℝ d ≃L[ℝ] EuclideanSpace ℝ d)
    (N : ℕ) [NeZero N] (w : (d → Fin N) → ℂ)
    (hzero : periodicPrimalWeight N w 0 = 0) (hsum : ∑ i, w i = 0)
    {t : ℝ} (ht : 0 < t) (hne : t ≠ 1) :
    normalizedPeriodicTheta B N w t = periodicPrimalTail B N w t +
      ((|(LinearMap.det B.toLinearMap)⁻¹|:ℝ):ℂ) *
        (t:ℂ)^(-((Fintype.card d:ℂ)/2)) * periodicDualTail B N w t⁻¹ := by
  rcases lt_or_gt_of_ne hne with hlt | hgt
  · have hinv : 1 < t⁻¹ := (one_lt_inv₀ ht).mpr hlt
    rw [normalizedPeriodicTheta_dual B N w t ht, hsum, zero_add]
    simp [periodicPrimalTail, periodicDualTail, scaledWeightedThetaTail,
      not_lt.mpr hlt.le, hinv, max_eq_left hinv.le]
  · have hinv : t⁻¹ < 1 := (inv_lt_one₀ (zero_lt_one.trans hgt)).mpr hgt
    rw [normalizedPeriodicTheta_primal B N w t ht, hzero, zero_add]
    simp [periodicPrimalTail, periodicDualTail, scaledWeightedThetaTail,
      not_lt.mpr hinv.le, hgt, max_eq_left hgt.le]



end PrimeDegreePackets.ThetaConstruction


open MeasureTheory Module
end
end

end OAI
end

theorem solution.{u_1} : type_of% @OAI.PrimeDegreePackets.ThetaConstruction.normalizedPeriodicTheta_decomposition_oai.{u_1} := @OAI.PrimeDegreePackets.ThetaConstruction.normalizedPeriodicTheta_decomposition_oai.{u_1}
