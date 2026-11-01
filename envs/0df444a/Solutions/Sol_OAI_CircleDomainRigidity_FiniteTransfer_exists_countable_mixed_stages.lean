-- Prove2me | solution 1 for OAI.CircleDomainRigidity.FiniteTransfer.exists_countable_mixed_stages
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-01T05:46:06.092912+00:00
-- url     : https://prove2.me/submissions/d43c8362-50da-45c2-acfa-18a0f2055195

import Mathlib
import Definitions.Def_KoebeCircleDomains
import Definitions.Def_Q146C010

section
-- module Solutions.Q146_CD.CircleDomains_LengthArea
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Circle domains, conformal removability, and conditional analytic rigidity from length and area estimates. -/

noncomputable section
open Set Classical
open scoped OnePoint

open MeasureTheory Filter Bornology
open scoped Topology
namespace CircleDomainRigidity.LengthArea

theorem summable_mul_of_squares {ι : Type*} {r s : ι → ℝ}
    (hr : Summable (fun j ↦ r j ^ 2)) (hs : Summable (fun j ↦ s j ^ 2)) :
    Summable (fun j ↦ r j * s j) := by
  apply (hr.add hs).of_norm_bounded
  intro j
  rw [Real.norm_eq_abs, abs_mul]
  nlinarith [sq_nonneg (|r j| - |s j|), sq_abs (r j), sq_abs (s j),
    sq_nonneg (r j), sq_nonneg (s j)]

end CircleDomainRigidity.LengthArea

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Modulus_BandIncidence
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Weighted dust incidence

This is the dust part of `eq:weighted-level-bound` in Section 1 of
`047-02`. A point contributes its weight on a measurable set of levels.
Tonelli converts the expected total incidence to the sum of weights
times level probabilities; the band-incidence estimate bounds these
probabilities, and square summability makes the result finite.
-/

open Set MeasureTheory Filter
open scoped ENNReal

namespace CircleDomainRigidity

theorem measurable_weightedBandIncidence {T ι : Type*} [MeasurableSpace T] [Countable ι]
    (E : ι → Set T) (m : ι → ℝ) (hE : ∀ s, MeasurableSet (E s)) :
    Measurable (weightedBandIncidence E m) :=
  Measurable.tsum (fun s => measurable_const.indicator (hE s))

theorem weightedBandIncidence_toReal_eq {T ι : Type*}
    (E : ι → Set T) (m : ι → ℝ) (hm : ∀ s, 0 ≤ m s) (t : T) :
    (weightedBandIncidence E m t).toReal = ∑' s, (E s).indicator (fun _ => m s) t := by
  classical
  rw [weightedBandIncidence, ENNReal.tsum_toReal_eq]
  · apply tsum_congr
    intro s
    by_cases ht : t ∈ E s
    · simp only [indicator_of_mem ht, ENNReal.toReal_ofReal (hm s)]
    · simp only [indicator_of_notMem ht, ENNReal.toReal_zero]
  · intro s
    by_cases ht : t ∈ E s
    · simpa only [indicator_of_mem ht] using ENNReal.ofReal_ne_top
    · simp only [indicator_of_notMem ht, ne_eq, ENNReal.zero_ne_top, not_false_eq_true]

/-- Tonelli's exact incidence identity. -/
theorem lintegral_weightedBandIncidence {T ι : Type*} [MeasurableSpace T] [Countable ι]
    (ν : Measure T) (E : ι → Set T) (m : ι → ℝ) (hE : ∀ s, MeasurableSet (E s)) :
    ∫⁻ t, weightedBandIncidence E m t ∂ν = ∑' s, ENNReal.ofReal (m s) * ν (E s) := by
  unfold weightedBandIncidence
  rw [lintegral_tsum]
  · apply tsum_congr
    intro s
    exact lintegral_indicator_const (hE s) _
  · intro s
    exact (measurable_const.indicator (hE s)).aemeasurable

end CircleDomainRigidity

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Sobolev_MetricEnergy
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# The regularized metric energy in finite transfer

For the two eigenvalues of the positive semidefinite tensor formed by the
coordinate differentials, this is the energy density for the regularized
metric `A + τ g₀`. These estimates are the scalar analytic step in
the finite-transfer construction. In particular, rank-one fillings have
vanishing limiting energy.
-/

open Filter
open scoped Topology

namespace CircleDomainRigidity.FiniteTransfer

noncomputable section

/-- This is the density formula written in the manuscript. -/
theorem metricEnergy_eq_density {a b τ : ℝ}
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hτ : 0 < τ) :
    metricEnergy a b τ =
      (2 * a * b + τ * (a + b)) / Real.sqrt ((a + τ) * (b + τ)) := by
  have haτ : 0 < a + τ := add_pos_of_nonneg_of_pos ha hτ
  have hbτ : 0 < b + τ := add_pos_of_nonneg_of_pos hb hτ
  have hsa : Real.sqrt (a + τ) ≠ 0 := ne_of_gt (Real.sqrt_pos.2 haτ)
  have hsb : Real.sqrt (b + τ) ≠ 0 := ne_of_gt (Real.sqrt_pos.2 hbτ)
  have hsa2 := Real.sq_sqrt haτ.le
  have hsb2 := Real.sq_sqrt hbτ.le
  rw [Real.sqrt_mul haτ.le]
  unfold metricEnergy
  field_simp
  nlinarith

/-- The regularized density has the original trace as a uniform bound.
This bound is independent of the positive regularization parameter. -/
theorem metricEnergy_le_trace {a b τ : ℝ}
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hτ : 0 < τ) :
    metricEnergy a b τ ≤ a + b := by
  rw [metricEnergy_eq_density ha hb hτ]
  have hp : 0 < (a + τ) * (b + τ) :=
    mul_pos (add_pos_of_nonneg_of_pos ha hτ) (add_pos_of_nonneg_of_pos hb hτ)
  have hd : 0 < Real.sqrt ((a + τ) * (b + τ)) := Real.sqrt_pos.2 hp
  apply (div_le_iff₀ hd).2
  have hn : 0 ≤ 2 * a * b + τ * (a + b) := by positivity
  apply (sq_le_sq₀ hn (mul_nonneg (add_nonneg ha hb) hd.le)).mp
  rw [mul_pow, Real.sq_sqrt hp.le]
  have hgap : 0 ≤ (a - b) ^ 2 * (a * b + τ * (a + b)) := by positivity
  nlinarith

private theorem tendsto_energy_term {a b : ℝ} (ha : 0 ≤ a) :
    Tendsto (fun τ : ℝ => a * Real.sqrt (b + τ) / Real.sqrt (a + τ)) (𝓝 0)
      (𝓝 (Real.sqrt a * Real.sqrt b)) := by
  by_cases ha0 : a = 0
  · subst a
    simp
  have hsa : Real.sqrt a ≠ 0 := Real.sqrt_ne_zero'.mpr (lt_of_le_of_ne ha (Ne.symm ha0))
  have hsqrt (c : ℝ) : Tendsto (fun τ : ℝ => Real.sqrt (c + τ)) (𝓝 0)
      (𝓝 (Real.sqrt c)) := by
    have hadd : Tendsto (fun τ : ℝ => c + τ) (𝓝 0) (𝓝 (c + 0)) :=
      tendsto_const_nhds.add tendsto_id
    simpa only [Function.comp_def, add_zero] using
      (Real.continuous_sqrt.tendsto (c + 0)).comp hadd
  have h : Tendsto (fun τ : ℝ => a * Real.sqrt (b + τ) / Real.sqrt (a + τ)) (𝓝 0)
      (𝓝 (a * Real.sqrt b / Real.sqrt a)) :=
    (tendsto_const_nhds.mul (hsqrt b)).div (hsqrt a) hsa
  have heq : a * Real.sqrt b / Real.sqrt a = Real.sqrt a * Real.sqrt b := by
    apply (div_eq_iff hsa).2
    have hsq := Real.sq_sqrt ha
    calc
      a * Real.sqrt b = Real.sqrt a ^ 2 * Real.sqrt b := by rw [hsq]
      _ = Real.sqrt a * Real.sqrt b * Real.sqrt a := by ring
  rwa [heq] at h

/-- The limiting energy is twice the square root of the determinant. -/
theorem tendsto_metricEnergy {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) :
    Tendsto (metricEnergy a b) (𝓝[>] 0) (𝓝 (2 * Real.sqrt (a * b))) := by
  have h := (tendsto_energy_term (b := b) ha).add (tendsto_energy_term (b := a) hb)
  have heq : Real.sqrt a * Real.sqrt b + Real.sqrt b * Real.sqrt a =
      2 * Real.sqrt (a * b) := by rw [Real.sqrt_mul ha]; ring
  rw [heq] at h
  exact h.mono_left nhdsWithin_le_nhds

end

end CircleDomainRigidity.FiniteTransfer

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Sobolev_WedgeEnergy
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Wedge products control the optimized metric energy

The two-dimensional Cauchy–Binet identity is proved directly for finite
lists of coordinate differentials. No rank or determinant identity is
assumed. The resulting bound is the pointwise algebra behind the
finite-transfer energy estimate.
-/

open Finset

namespace CircleDomainRigidity.FiniteTransfer

/-- Cauchy–Binet for the Gram matrix of a finite family of two-dimensional
covectors, with each unordered pair counted once. -/
theorem gramDet_eq_wedgeSquares (x y : ℕ → ℝ) (n : ℕ) :
    (∑ i ∈ range n, x i ^ 2) * (∑ i ∈ range n, y i ^ 2) -
      (∑ i ∈ range n, x i * y i) ^ 2 =
    ∑ j ∈ range n, ∑ i ∈ range j, (x i * y j - x j * y i) ^ 2 := by
  induction n with
  | zero => simp
  | succ n ih =>
    have hsum : (∑ i ∈ range n, (x i * y n - x n * y i) ^ 2) =
        y n ^ 2 * (∑ i ∈ range n, x i ^ 2) +
        x n ^ 2 * (∑ i ∈ range n, y i ^ 2) -
        (2 * x n * y n) * (∑ i ∈ range n, x i * y i) := by
      calc
        _ = ∑ i ∈ range n, (y n ^ 2 * x i ^ 2 + x n ^ 2 * y i ^ 2 -
            (2 * x n * y n) * (x i * y i)) := by
          apply sum_congr rfl
          intro i _
          ring
        _ = _ := by
          rw [sum_sub_distrib, sum_add_distrib, ← mul_sum, ← mul_sum, ← mul_sum]
    simp only [sum_range_succ]
    rw [← ih, hsum]
    ring

/-- The square root of the Gram determinant is bounded by the sum of the
absolute wedge products. This uses the full finite list without a
pairwise-independence assumption. -/
theorem sqrt_gramDet_le_wedges (x y : ℕ → ℝ) (n : ℕ) :
    Real.sqrt ((∑ i ∈ range n, x i ^ 2) * (∑ i ∈ range n, y i ^ 2) -
      (∑ i ∈ range n, x i * y i) ^ 2) ≤
    ∑ j ∈ range n, ∑ i ∈ range j, |x i * y j - x j * y i| := by
  rw [gramDet_eq_wedgeSquares]
  have hinner (j : ℕ) :
      (∑ i ∈ range j, (x i * y j - x j * y i) ^ 2) ≤
        (∑ i ∈ range j, |x i * y j - x j * y i|) ^ 2 := by
    simpa only [sq_abs] using sum_sq_le_sq_sum_of_nonneg
      (s := range j) (f := fun i => |x i * y j - x j * y i|)
      (fun i _ => abs_nonneg _)
  have hnonneg (j : ℕ) : 0 ≤ ∑ i ∈ range j, |x i * y j - x j * y i| :=
    sum_nonneg fun _ _ => abs_nonneg _
  have hsum := sum_le_sum (s := range n) (fun j _ => hinner j)
  have houter := sum_sq_le_sq_sum_of_nonneg (s := range n)
    (f := fun j => ∑ i ∈ range j, |x i * y j - x j * y i|) (fun j _ => hnonneg j)
  exact Real.sqrt_le_iff.mpr ⟨sum_nonneg (fun j _ => hnonneg j), hsum.trans houter⟩

end CircleDomainRigidity.FiniteTransfer

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Sobolev_TensorEnergy
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonMobius.sphereMetric _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# From a positive two-dimensional tensor to optimized energy

The trace and determinant determine the energy of `A + τ I`. The scalar
roots used below are the two nonnegative eigenvalues, constructed directly
from the characteristic polynomial. This connects the metric limit to
the Gram determinant of the actual finite list of coordinate differentials.
-/

open Filter MeasureTheory
open scoped Topology

noncomputable section

namespace CircleDomainRigidity.FiniteTransfer

theorem roots_nonneg {T D : ℝ} (hT : 0 ≤ T) (hD : 0 ≤ D) :
    0 ≤ upperRoot T D ∧ 0 ≤ lowerRoot T D := by
  have hs : Real.sqrt (T ^ 2 - 4 * D) ≤ T :=
    Real.sqrt_le_iff.mpr ⟨hT, by nlinarith⟩
  constructor
  · unfold upperRoot
    positivity
  · unfold lowerRoot
    linarith

theorem roots_sum (T D : ℝ) : upperRoot T D + lowerRoot T D = T := by
  unfold upperRoot lowerRoot
  ring

theorem roots_product {T D : ℝ} (hdisc : 0 ≤ T ^ 2 - 4 * D) :
    upperRoot T D * lowerRoot T D = D := by
  have hs := Real.sq_sqrt hdisc
  unfold upperRoot lowerRoot
  nlinarith

theorem tensorEnergy_eq_metricEnergy {T D τ : ℝ}
    (hT : 0 ≤ T) (hD : 0 ≤ D) (hdisc : 0 ≤ T ^ 2 - 4 * D) (hτ : 0 < τ) :
    tensorEnergy T D τ = metricEnergy (upperRoot T D) (lowerRoot T D) τ := by
  obtain ⟨hhi, hlo⟩ := roots_nonneg hT hD
  have hp := roots_product hdisc
  have hs := roots_sum T D
  rw [metricEnergy_eq_density hhi hlo hτ]
  have hn : 2 * upperRoot T D * lowerRoot T D +
      τ * (upperRoot T D + lowerRoot T D) = 2 * D + τ * T := by
    rw [hs]
    nlinarith [hp]
  have hd : (upperRoot T D + τ) * (lowerRoot T D + τ) = D + τ * T + τ ^ 2 := by
    nlinarith [hp, hs]
  rw [hn, hd]
  rfl

theorem tensorEnergy_le_trace {T D τ : ℝ}
    (hT : 0 ≤ T) (hD : 0 ≤ D) (hdisc : 0 ≤ T ^ 2 - 4 * D) (hτ : 0 < τ) :
    tensorEnergy T D τ ≤ T := by
  rw [tensorEnergy_eq_metricEnergy hT hD hdisc hτ]
  exact (metricEnergy_le_trace (roots_nonneg hT hD).1 (roots_nonneg hT hD).2 hτ).trans_eq
    (roots_sum T D)

theorem tendsto_tensorEnergy {T D : ℝ}
    (hT : 0 ≤ T) (hD : 0 ≤ D) (hdisc : 0 ≤ T ^ 2 - 4 * D) :
    Tendsto (tensorEnergy T D) (𝓝[>] 0) (𝓝 (2 * Real.sqrt D)) := by
  have h := tendsto_metricEnergy (roots_nonneg hT hD).1 (roots_nonneg hT hD).2
  rw [roots_product hdisc] at h
  apply h.congr'
  filter_upwards [show ∀ᶠ τ : ℝ in 𝓝[>] 0, 0 < τ from self_mem_nhdsWithin] with τ hτ
  exact (tensorEnergy_eq_metricEnergy hT hD hdisc hτ).symm

/-- Dominated convergence in terms of the tensor invariants. -/
theorem tendsto_integral_tensorEnergy {X : Type*} [MeasurableSpace X]
    {μ : Measure X} {T D : X → ℝ} (hT : Measurable T) (hD : Measurable D)
    (hT0 : ∀ x, 0 ≤ T x) (hD0 : ∀ x, 0 ≤ D x)
    (hdisc : ∀ x, 0 ≤ T x ^ 2 - 4 * D x) (htrace : Integrable T μ) :
    Tendsto (fun τ : ℝ => ∫ x, tensorEnergy (T x) (D x) τ ∂μ) (𝓝[>] 0)
      (𝓝 (∫ x, 2 * Real.sqrt (D x) ∂μ)) := by
  have hmeas (τ : ℝ) : Measurable (fun x => tensorEnergy (T x) (D x) τ) := by
    unfold tensorEnergy
    fun_prop
  apply tendsto_integral_filter_of_dominated_convergence T
  · exact Filter.Eventually.of_forall fun τ => (hmeas τ).aestronglyMeasurable
  · filter_upwards [show ∀ᶠ τ : ℝ in 𝓝[>] 0, 0 < τ from self_mem_nhdsWithin] with τ hτ
    apply Filter.Eventually.of_forall
    intro x
    have hn : 0 ≤ tensorEnergy (T x) (D x) τ := by
      have ht := hT0 x
      have hd := hD0 x
      unfold tensorEnergy
      positivity
    rw [Real.norm_eq_abs, abs_of_nonneg hn]
    exact tensorEnergy_le_trace (hT0 x) (hD0 x) (hdisc x) hτ
  · exact htrace
  · exact Filter.Eventually.of_forall fun x => tendsto_tensorEnergy (hT0 x) (hD0 x) (hdisc x)

theorem covectorTrace_nonneg (x y : ℕ → ℝ) (n : ℕ) : 0 ≤ covectorTrace x y n := by
  unfold covectorTrace
  positivity

theorem covectorDet_nonneg (x y : ℕ → ℝ) (n : ℕ) : 0 ≤ covectorDet x y n := by
  unfold covectorDet
  rw [gramDet_eq_wedgeSquares]
  exact Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => sq_nonneg _

theorem covector_discriminant_nonneg (x y : ℕ → ℝ) (n : ℕ) :
    0 ≤ covectorTrace x y n ^ 2 - 4 * covectorDet x y n := by
  unfold covectorTrace covectorDet
  nlinarith [sq_nonneg ((∑ i ∈ Finset.range n, x i ^ 2) -
    (∑ i ∈ Finset.range n, y i ^ 2)), sq_nonneg (∑ i ∈ Finset.range n, x i * y i)]

end CircleDomainRigidity.FiniteTransfer

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Sobolev_FiniteEnergy
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonMobius.sphereMetric _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Selecting the finite-transfer regularization

For a finite list of planar differentials, a small integral of absolute
pairwise wedges produces a regularized metric with small total energy.
This proves the energy optimization step of finite transfer, after the
geometric filling and staircase construction have supplied the differentials.
-/

open Filter MeasureTheory Finset
open scoped Topology

noncomputable section

namespace CircleDomainRigidity.FiniteTransfer

/-- The exact finite-transfer energy choice, using the actually constructed
finite family of coordinate differentials. -/
theorem exists_regularization_energy_lt
    {X : Type*} [MeasurableSpace X] {μ : Measure X}
    (x y : ℕ → X → ℝ) (n : ℕ)
    (hx : ∀ i, Measurable (x i)) (hy : ∀ i, Measurable (y i))
    (htrace : Integrable (fun z => covectorTrace (fun i => x i z) (fun i => y i z) n) μ)
    (hwedge : Integrable (fun z => covectorWedges (fun i => x i z) (fun i => y i z) n) μ)
    {ε : ℝ} (hε : (∫ z, 2 * covectorWedges (fun i => x i z) (fun i => y i z) n ∂μ) < ε) :
    ∃ τ : ℝ, 0 < τ ∧
      (∫ z, tensorEnergy
        (covectorTrace (fun i => x i z) (fun i => y i z) n)
        (covectorDet (fun i => x i z) (fun i => y i z) n) τ ∂μ) < ε := by
  let T : X → ℝ := fun z => covectorTrace (fun i => x i z) (fun i => y i z) n
  let D : X → ℝ := fun z => covectorDet (fun i => x i z) (fun i => y i z) n
  let W : X → ℝ := fun z => covectorWedges (fun i => x i z) (fun i => y i z) n
  have hT : Measurable T := by
    dsimp [T, covectorTrace]
    fun_prop
  have hD : Measurable D := by
    dsimp [D, covectorDet]
    fun_prop
  have hpoint (z : X) : 2 * Real.sqrt (D z) ≤ 2 * W z := by
    apply mul_le_mul_of_nonneg_left _ (by norm_num)
    exact sqrt_gramDet_le_wedges (fun i => x i z) (fun i => y i z) n
  have hi : Integrable (fun z => 2 * Real.sqrt (D z)) μ := by
    apply (hwedge.const_mul 2).mono'
      ((hD.sqrt.const_mul 2).aestronglyMeasurable)
    apply Filter.Eventually.of_forall
    intro z
    have hnonneg : 0 ≤ 2 * Real.sqrt (D z) := by positivity
    simpa only [Real.norm_eq_abs, abs_of_nonneg hnonneg] using hpoint z
  have hlimlt : (∫ z, 2 * Real.sqrt (D z) ∂μ) < ε :=
    (integral_mono hi (hwedge.const_mul 2) hpoint).trans_lt hε
  have hlim := tendsto_integral_tensorEnergy hT hD
    (fun z => covectorTrace_nonneg (fun i => x i z) (fun i => y i z) n)
    (fun z => covectorDet_nonneg (fun i => x i z) (fun i => y i z) n)
    (fun z => covector_discriminant_nonneg (fun i => x i z) (fun i => y i z) n) htrace
  have hpos : ∀ᶠ τ : ℝ in 𝓝[>] 0, 0 < τ := self_mem_nhdsWithin
  exact (hpos.and (hlim.eventually (gt_mem_nhds hlimlt))).exists

end CircleDomainRigidity.FiniteTransfer

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Sobolev_MetricTensor
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# The regularized metric as a matrix

This identifies the scalar energy expression with
`trace ((A + τ I)⁻¹ A) sqrt (det (A + τ I))`, and proves that
regularizing a positive semidefinite tensor gives a positive definite
metric. Thus the energy optimization applies to the actual metric tensor.
-/

open Matrix

noncomputable section

namespace CircleDomainRigidity.FiniteTransfer

theorem det_regularizedTensor (a b c τ : ℝ) :
    (regularizedTensor a b c τ).det = (a * c - b ^ 2) + τ * (a + c) + τ ^ 2 := by
  simp [regularizedTensor, symmetricTensor, Matrix.det_fin_two]
  ring

theorem det_regularizedTensor_pos {a b c τ : ℝ}
    (ha : 0 ≤ a) (hc : 0 ≤ c) (hD : 0 ≤ a * c - b ^ 2) (hτ : 0 < τ) :
    0 < (regularizedTensor a b c τ).det := by
  rw [det_regularizedTensor]
  exact add_pos_of_nonneg_of_pos (add_nonneg hD (mul_nonneg hτ.le (add_nonneg ha hc)))
    (sq_pos_of_pos hτ)

/-- The actual inverse-matrix energy density equals the scalar invariant
expression used in the dominated-convergence argument. -/
theorem trace_inverse_energy_eq_tensorEnergy {a b c τ : ℝ}
    (ha : 0 ≤ a) (hc : 0 ≤ c) (hD : 0 ≤ a * c - b ^ 2) (hτ : 0 < τ) :
    Matrix.trace ((regularizedTensor a b c τ)⁻¹ * symmetricTensor a b c) *
      Real.sqrt (regularizedTensor a b c τ).det =
      tensorEnergy (a + c) (a * c - b ^ 2) τ := by
  have hpos := det_regularizedTensor_pos ha hc hD hτ
  have hne := ne_of_gt hpos
  have hspos : 0 < Real.sqrt (regularizedTensor a b c τ).det := Real.sqrt_pos.mpr hpos
  have hsq := Real.sq_sqrt hpos.le
  have htrace : Matrix.trace ((regularizedTensor a b c τ)⁻¹ * symmetricTensor a b c) =
      (2 * (a * c - b ^ 2) + τ * (a + c)) / (regularizedTensor a b c τ).det := by
    rw [Matrix.inv_def, Ring.inverse_eq_inv, Matrix.adjugate_fin_two]
    simp [regularizedTensor, symmetricTensor, Matrix.trace_fin_two, div_eq_mul_inv]
    ring
  rw [htrace, tensorEnergy, ← det_regularizedTensor]
  have hmul := congrArg (fun t : ℝ => (2 * (a * c - b ^ 2) + τ * (a + c)) * t) hsq
  field_simp [hne, hspos.ne']
  nlinarith only [hmul]

end CircleDomainRigidity.FiniteTransfer

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Sobolev_GramMetric
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonEmbeddedArc.Arc.graphVertices_finite _root_.OAI.CannonMobius.sphereMetric _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Choosing the actual metric from the coordinate differentials

The Gram tensor is the sum of the rank-one coordinate tensors.
Regularization makes it a positive definite metric, and the integral
bound is for its actual inverse-matrix energy density.
-/

open Matrix MeasureTheory Finset
open scoped ContDiff Matrix.Norms.Elementwise

noncomputable section

namespace CircleDomainRigidity.FiniteTransfer

theorem gramTensor_eq_sum (x y : ℕ → ℝ) (n : ℕ) :
    gramTensor x y n = ∑ i ∈ range n, Matrix.vecMulVec ![x i, y i] ![x i, y i] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [gramTensor, symmetricTensor, Matrix.vecMulVec, Matrix.sum_apply, pow_two, mul_comm]

theorem gramTensor_posSemidef (x y : ℕ → ℝ) (n : ℕ) : (gramTensor x y n).PosSemidef := by
  rw [gramTensor_eq_sum]
  apply Matrix.posSemidef_sum
  intro i _
  simpa only [star_trivial] using Matrix.posSemidef_vecMulVec_self_star ![x i, y i]

theorem gramTensor_energy {τ : ℝ} (hτ : 0 < τ) (x y : ℕ → ℝ) (n : ℕ) :
    Matrix.trace ((gramTensor x y n + τ • 1)⁻¹ * gramTensor x y n) *
      Real.sqrt (gramTensor x y n + τ • 1).det =
      tensorEnergy (covectorTrace x y n) (covectorDet x y n) τ := by
  exact trace_inverse_energy_eq_tensorEnergy
    (sum_nonneg (fun _ _ => sq_nonneg _)) (sum_nonneg (fun _ _ => sq_nonneg _))
    (covectorDet_nonneg x y n) hτ

/-- Small pairwise wedge integrals give one positive definite metric with
small total coordinate energy. All tensor and inverse formulas are derived. -/
theorem exists_gramMetric_energy_lt
    {X : Type*} [MeasurableSpace X] {μ : Measure X}
    (x y : ℕ → X → ℝ) (n : ℕ)
    (hx : ∀ i, Measurable (x i)) (hy : ∀ i, Measurable (y i))
    (htrace : Integrable (fun z => covectorTrace (fun i => x i z) (fun i => y i z) n) μ)
    (hwedge : Integrable (fun z => covectorWedges (fun i => x i z) (fun i => y i z) n) μ)
    {ε : ℝ} (hε : (∫ z, 2 * covectorWedges (fun i => x i z) (fun i => y i z) n ∂μ) < ε) :
    ∃ τ : ℝ, 0 < τ ∧
      (∀ z, (gramTensor (fun i => x i z) (fun i => y i z) n + τ • 1).PosDef) ∧
      (∫ z, Matrix.trace
        ((gramTensor (fun i => x i z) (fun i => y i z) n + τ • 1)⁻¹ *
          gramTensor (fun i => x i z) (fun i => y i z) n) *
        Real.sqrt (gramTensor (fun i => x i z) (fun i => y i z) n + τ • 1).det ∂μ) < ε := by
  obtain ⟨τ, hτ, henergy⟩ := exists_regularization_energy_lt x y n hx hy htrace hwedge hε
  refine ⟨τ, hτ, fun z => ?_, ?_⟩
  · exact Matrix.PosDef.posSemidef_add (gramTensor_posSemidef _ _ _)
      (Matrix.PosDef.one.smul hτ)
  · simpa only [gramTensor_energy hτ] using henergy

/-- For smooth coordinate differentials on a bounded planar region,
integrability is automatic and the chosen positive definite metric is
itself smooth. -/
theorem exists_smooth_gramMetric_on_bounded
    (x y : ℕ → (ℝ × ℝ) → ℝ) (n : ℕ)
    (hx : ∀ i, ContDiff ℝ ∞ (x i)) (hy : ∀ i, ContDiff ℝ ∞ (y i))
    {S : Set (ℝ × ℝ)} (hS : Bornology.IsBounded S) {ε : ℝ}
    (hε : (∫ z in S, 2 * covectorWedges (fun i => x i z) (fun i => y i z) n) < ε) :
    ∃ τ : ℝ, 0 < τ ∧
      ContDiff ℝ ∞ (fun z => gramTensor (fun i => x i z) (fun i => y i z) n + τ • 1) ∧
      (∀ z, (gramTensor (fun i => x i z) (fun i => y i z) n + τ • 1).PosDef) ∧
      (∫ z in S, Matrix.trace
        ((gramTensor (fun i => x i z) (fun i => y i z) n + τ • 1)⁻¹ *
          gramTensor (fun i => x i z) (fun i => y i z) n) *
        Real.sqrt (gramTensor (fun i => x i z) (fun i => y i z) n + τ • 1).det) < ε := by
  have hT : Continuous (fun z => covectorTrace (fun i => x i z) (fun i => y i z) n) := by
    unfold covectorTrace
    fun_prop
  have hW : Continuous (fun z => covectorWedges (fun i => x i z) (fun i => y i z) n) := by
    unfold covectorWedges
    fun_prop
  have hTi : IntegrableOn (fun z => covectorTrace (fun i => x i z) (fun i => y i z) n) S :=
    (hT.continuousOn.integrableOn_compact hS.isCompact_closure).mono_set subset_closure
  have hWi : IntegrableOn (fun z => covectorWedges (fun i => x i z) (fun i => y i z) n) S :=
    (hW.continuousOn.integrableOn_compact hS.isCompact_closure).mono_set subset_closure
  obtain ⟨τ, hτ, hPD, hE⟩ := exists_gramMetric_energy_lt x y n
    (fun i => (hx i).continuous.measurable) (fun i => (hy i).continuous.measurable) hTi hWi hε
  refine ⟨τ, hτ, ?_, hPD, hE⟩
  apply contDiff_pi.mpr
  intro i
  apply contDiff_pi.mpr
  intro j
  fin_cases i <;> fin_cases j <;>
    simp [gramTensor, symmetricTensor]
    <;> fun_prop

end CircleDomainRigidity.FiniteTransfer

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Topology_CutoffStaircase
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Joining a coordinate to a staircase outside a core

These are the differential and periodicity calculations for the actual
cutoff modification `u + χ (P ∘ u - u)` in finite transfer. They apply to
ordinary real branches and hence also to compatible periodic branches.
-/

open Filter

noncomputable section

namespace CircleDomainRigidity.FiniteTransfer

/-- The modified differential has the original gradient multiplier and
one error term supported on the cutoff transition. -/
theorem hasFDerivAt_cutoffStaircase {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {u χ : E → ℝ} {P : ℝ → ℝ} {x : E} {du dχ : E →L[ℝ] ℝ} {p : ℝ}
    (hu : HasFDerivAt u du x) (hχ : HasFDerivAt χ dχ x) (hP : HasDerivAt P p (u x)) :
    HasFDerivAt (cutoffStaircase u χ P)
      ((1 - χ x + χ x * p) • du + (P (u x) - u x) • dχ) x := by
  have hd := hu.add (hχ.mul ((hP.comp_hasFDerivAt x hu).sub hu))
  refine hd.congr_fderiv (Eq.symm ?_)
  · ext v
    simp only [add_apply, sub_apply, smul_apply, smul_eq_mul, Pi.sub_apply,
      Function.comp_apply]
    ring

/-- The original coordinate is retained exactly where the cutoff is zero. -/
theorem cutoffStaircase_of_zero {X : Type*} {u χ : X → ℝ} {P : ℝ → ℝ} {x : X}
    (hχ : χ x = 0) : cutoffStaircase u χ P x = u x := by
  simp [cutoffStaircase, hχ]

/-- The staircase is used exactly where the cutoff is one. -/
theorem cutoffStaircase_of_one {X : Type*} {u χ : X → ℝ} {P : ℝ → ℝ} {x : X}
    (hχ : χ x = 1) : cutoffStaircase u χ P x = P (u x) := by
  simp [cutoffStaircase, hχ]

end CircleDomainRigidity.FiniteTransfer

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Topology_CollarExtension
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonMobius.sphereMetric _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Smooth extension of the active filling coordinate

A real branch smooth on a collar can be retained on a smaller closed
collar and extended to be constant away from it. In a filling disk all
other branches are constant, so this is the only extension needed there.
-/

open Set Filter
open scoped Topology Manifold ContDiff

noncomputable section

namespace CircleDomainRigidity.FiniteTransfer

/-- Multiplication by a smooth cutoff which vanishes near the complement
of `U` makes a branch smooth globally. No regularity of the branch is
required outside its original open domain. -/
theorem contDiff_collar_cutoff {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {U : Set E} {f χ : E → ℝ} {n : ℕ∞} (hU : IsOpen U)
    (hf : ContDiffOn ℝ n f U) (hχ : ContDiff ℝ n χ)
    (hzero : ∀ᶠ x in 𝓝ˢ Uᶜ, χ x = 0) (c : ℝ) :
    ContDiff ℝ n (fun x => c + χ x * (f x - c)) := by
  apply contDiff_iff_contDiffAt.mpr
  intro x
  by_cases hx : x ∈ U
  · exact contDiffAt_const.add
      (hχ.contDiffAt.mul ((hf.contDiffAt (hU.mem_nhds hx)).sub contDiffAt_const))
  · have heq : (fun y => c + χ y * (f y - c)) =ᶠ[𝓝 x] (fun _ => c) := by
      filter_upwards [hzero.filter_mono (nhds_le_nhdsSet hx)] with y hy
      simp [hy]
    exact contDiffAt_const.congr_of_eventuallyEq heq

/-- Retain an arbitrary smooth real branch near a closed collar inside
its domain, and make it constant off that domain. -/
theorem exists_smooth_collar_extension {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {U A : Set E} (hU : IsOpen U) (hA : IsClosed A) (hAU : A ⊆ U)
    {f : E → ℝ} (hf : ContDiffOn ℝ ∞ f U) (c : ℝ) :
    ∃ F : E → ℝ, ContDiff ℝ ∞ F ∧ F =ᶠ[𝓝ˢ A] f ∧ ∀ x ∉ U, F x = c := by
  have hd : Disjoint Uᶜ A := Set.disjoint_left.mpr (fun x hx hxa => hx (hAU hxa))
  obtain ⟨χ, hzero, hone, _⟩ := exists_contMDiffMap_zero_one_nhds_of_isClosed
    (𝓘(ℝ, E)) hU.isClosed_compl hA hd (n := (⊤ : ℕ∞))
  have hχ : ContDiff ℝ ∞ (χ : E → ℝ) := contMDiff_iff_contDiff.mp χ.contMDiff
  refine ⟨fun x => c + χ x * (f x - c), contDiff_collar_cutoff hU hf hχ hzero c, ?_, ?_⟩
  · filter_upwards [hone] with x hx
    simp [hx]
  · intro x hx
    change c + χ x * (f x - c) = c
    rw [hzero.self_of_nhdsSet x hx]
    ring

end CircleDomainRigidity.FiniteTransfer

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Selection_Staircase
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Smooth periodic staircases

An explicit degree-one smooth staircase with spacing `h` and transition
half-width `δ`. The transition in the cell `[nh,(n+1)h]` is centered at
`(n+1/2)h`. The floor jumps cancel because the transition is flat near
the cell endpoints.
-/

open Set Filter
open scoped Topology ContDiff

noncomputable section

namespace CircleDomainRigidity.FiniteTransfer

private theorem cell_lower {h : ℝ} (hh : 0 < h) (x : ℝ) :
    h * (⌊x / h⌋ : ℝ) ≤ x := by
  have hx := (le_div_iff₀ hh).mp (Int.floor_le (x / h))
  simpa only [mul_comm] using hx

private theorem cell_upper {h : ℝ} (hh : 0 < h) (x : ℝ) :
    x < h * ((⌊x / h⌋ : ℝ) + 1) := by
  have hx := (div_lt_iff₀ hh).mp (Int.lt_floor_add_one (x / h))
  simpa only [mul_comm] using hx

theorem smoothStaircase_lower {h : ℝ} (hh : 0 ≤ h) (δ x : ℝ) :
    h * (⌊x / h⌋ : ℝ) ≤ smoothStaircase h δ x := by
  unfold smoothStaircase
  exact mul_le_mul_of_nonneg_left (le_add_of_nonneg_right
    (Real.smoothTransition.nonneg _)) hh

theorem smoothStaircase_upper {h : ℝ} (hh : 0 ≤ h) (δ x : ℝ) :
    smoothStaircase h δ x ≤ h * ((⌊x / h⌋ : ℝ) + 1) := by
  unfold smoothStaircase
  exact mul_le_mul_of_nonneg_left (add_le_add (le_refl _)
    (Real.smoothTransition.le_one _)) hh

/-- The staircase is a degree-one lift with period increment `h`. -/
theorem smoothStaircase_add_period {h : ℝ} (hh : 0 < h) (δ x : ℝ) :
    smoothStaircase h δ (x + h) = smoothStaircase h δ x + h := by
  have hfloor : ⌊(x + h) / h⌋ = ⌊x / h⌋ + 1 := by
    rw [add_div, div_self hh.ne', Int.floor_add_one]
  have hresid : x + h - h * ((⌊x / h⌋ : ℝ) + 1) = x - h * (⌊x / h⌋ : ℝ) := by
    ring
  simp only [smoothStaircase, hfloor, Int.cast_add, Int.cast_one, hresid]
  ring

/-- Uniform displacement is bounded by one grid spacing. -/
theorem abs_smoothStaircase_sub_le {h : ℝ} (hh : 0 < h) (δ x : ℝ) :
    |smoothStaircase h δ x - x| ≤ h := by
  have hl := smoothStaircase_lower hh.le δ x
  have hu := smoothStaircase_upper hh.le δ x
  have hcl := cell_lower hh x
  have hcu := cell_upper hh x
  apply abs_le.mpr
  constructor <;> nlinarith

/-- Positive transition width gives a monotone staircase. -/
theorem monotone_smoothStaircase {h δ : ℝ} (hh : 0 < h) (hδ : 0 < δ) :
    Monotone (smoothStaircase h δ) := by
  intro x y hxy
  have hfloor := Int.floor_mono ((div_le_div_iff_of_pos_right hh).mpr hxy)
  rcases lt_or_eq_of_le hfloor with hlt | heq
  · have hi : ⌊x / h⌋ + 1 ≤ ⌊y / h⌋ := Int.add_one_le_iff.mpr hlt
    have hir : (⌊x / h⌋ : ℝ) + 1 ≤ (⌊y / h⌋ : ℝ) := by exact_mod_cast hi
    exact (smoothStaircase_upper hh.le δ x).trans
      ((mul_le_mul_of_nonneg_left hir hh.le).trans (smoothStaircase_lower hh.le δ y))
  · simp only [smoothStaircase, heq]
    apply mul_le_mul_of_nonneg_left _ hh.le
    apply add_le_add (le_refl _)
    apply Real.smoothTransition.monotone
    apply (div_le_div_iff_of_pos_right (by positivity : 0 < 2 * δ)).mpr
    linarith

/-- Around a cell boundary the floor jump cancels the completed transition,
so the staircase is identically the lattice value. -/
private theorem smoothStaircase_eq_near_lattice {h δ x : ℝ}
    (hh : 0 < h) (hδ : 0 < δ) (hδh : δ < h / 4) (n : ℤ)
    (hl : h * n - h / 4 < x) (hu : x < h * n + h / 4) :
    smoothStaircase h δ x = h * n := by
  have hlow : n - 1 ≤ ⌊x / h⌋ := by
    apply Int.le_floor.mpr
    apply (le_div_iff₀ hh).mpr
    simp only [Int.cast_sub, Int.cast_one]
    nlinarith
  have hupp : ⌊x / h⌋ ≤ n := by
    apply Int.floor_le_iff.mpr
    apply (div_lt_iff₀ hh).mpr
    nlinarith
  have hcases : ⌊x / h⌋ = n - 1 ∨ ⌊x / h⌋ = n := by omega
  rcases hcases with hleft | hright
  · have harg : 1 ≤ (x - h * ((n - 1 : ℤ) : ℝ) - (h / 2 - δ)) / (2 * δ) := by
      apply (le_div_iff₀ (by positivity : 0 < 2 * δ)).mpr
      simp only [Int.cast_sub, Int.cast_one]
      nlinarith
    simp only [smoothStaircase, hleft]
    rw [Real.smoothTransition.one_of_one_le harg]
    push_cast
    ring
  · have harg : (x - h * (n : ℝ) - (h / 2 - δ)) / (2 * δ) ≤ 0 := by
      apply (div_le_iff₀ (by positivity : 0 < 2 * δ)).mpr
      nlinarith
    simp only [smoothStaircase, hright, Real.smoothTransition.zero_of_nonpos harg, add_zero]

private theorem smoothStaircase_eventually_eq_lattice {h δ : ℝ}
    (hh : 0 < h) (hδ : 0 < δ) (hδh : δ < h / 4) (n : ℤ) :
    smoothStaircase h δ =ᶠ[𝓝 (h * n)] (fun _ => h * n) := by
  filter_upwards [Ioo_mem_nhds (by linarith : h * (n : ℝ) - h / 4 < h * n)
    (by linarith : h * (n : ℝ) < h * n + h / 4)] with y hy
  exact smoothStaircase_eq_near_lattice hh hδ hδh n hy.1 hy.2

private theorem smoothStaircase_eventually_eq_cell {h δ x : ℝ}
    (hh : 0 < h) (n : ℤ) (hl : h * n < x) (hu : x < h * (n + 1)) :
    smoothStaircase h δ =ᶠ[𝓝 x] (fun y => h * ((n : ℝ) +
      Real.smoothTransition ((y - h * n - (h / 2 - δ)) / (2 * δ)))) := by
  filter_upwards [Ioo_mem_nhds hl hu] with y hy
  have hfloor : ⌊y / h⌋ = n := by
    apply Int.floor_eq_iff.mpr
    constructor
    · apply (le_div_iff₀ hh).mpr
      nlinarith [hy.1]
    · apply (div_lt_iff₀ hh).mpr
      nlinarith [hy.2]
  simp only [smoothStaircase, hfloor]

/-- The apparent jumps of the floor formula cancel; the staircase is smooth
at lattice points as well as inside every cell. -/
theorem contDiff_smoothStaircase {h δ : ℝ}
    (hh : 0 < h) (hδ : 0 < δ) (hδh : δ < h / 4) :
    ContDiff ℝ ∞ (smoothStaircase h δ) := by
  apply contDiff_iff_contDiffAt.mpr
  intro x
  let n : ℤ := ⌊x / h⌋
  by_cases hx : x = h * n
  · have heq : smoothStaircase h δ =ᶠ[𝓝 x] (fun _ => h * n) := by
      simpa only [hx] using smoothStaircase_eventually_eq_lattice hh hδ hδh n
    exact contDiffAt_const.congr_of_eventuallyEq heq
  · have hl : h * n < x := lt_of_le_of_ne (cell_lower hh x) (Ne.symm hx)
    have hu : x < h * (n + 1) := cell_upper hh x
    have hc : ContDiff ℝ ∞ (fun y : ℝ => h * ((n : ℝ) +
        Real.smoothTransition ((y - h * n - (h / 2 - δ)) / (2 * δ)))) := by
      fun_prop
    exact hc.contDiffAt.congr_of_eventuallyEq (smoothStaircase_eventually_eq_cell hh n hl hu)

private theorem transition_hasDerivAt_zero_of_nonpos {t : ℝ} (ht : t ≤ 0) :
    HasDerivAt Real.smoothTransition 0 t := by
  have hd : HasDerivWithinAt Real.smoothTransition 0 (Iic t) t :=
    (hasDerivWithinAt_const t (Iic t) (0 : ℝ)).congr
      (fun y hy => Real.smoothTransition.zero_of_nonpos (hy.trans ht))
      (Real.smoothTransition.zero_of_nonpos ht)
  have hzero := hd.deriv_eq_zero (uniqueDiffWithinAt_Iic t)
  simpa only [hzero] using
    ((Real.smoothTransition.contDiff (n := 1)).differentiable_one t).hasDerivAt

private theorem transition_hasDerivAt_zero_of_one_le {t : ℝ} (ht : 1 ≤ t) :
    HasDerivAt Real.smoothTransition 0 t := by
  have hd : HasDerivWithinAt Real.smoothTransition 0 (Ici t) t :=
    (hasDerivWithinAt_const t (Ici t) (1 : ℝ)).congr
      (fun y hy => Real.smoothTransition.one_of_one_le (ht.trans hy))
      (Real.smoothTransition.one_of_one_le ht)
  have hzero := hd.deriv_eq_zero (uniqueDiffWithinAt_Ici t)
  simpa only [hzero] using
    ((Real.smoothTransition.contDiff (n := 1)).differentiable_one t).hasDerivAt

/-- The derivative is supported in the open `δ`-bands about the half-shifted
lattice. The assertion includes the endpoints of each band. -/
theorem deriv_smoothStaircase_eq_zero {h δ x : ℝ}
    (hh : 0 < h) (hδ : 0 < δ) (hδh : δ < h / 4)
    (hfar : ∀ n : ℤ, δ ≤ |x - h * ((n : ℝ) + 1 / 2)|) :
    deriv (smoothStaircase h δ) x = 0 := by
  let n : ℤ := ⌊x / h⌋
  by_cases hx : x = h * n
  · have heq : smoothStaircase h δ =ᶠ[𝓝 x] (fun _ => h * n) := by
      simpa only [hx] using smoothStaircase_eventually_eq_lattice hh hδ hδh n
    exact ((hasDerivAt_const x (h * (n : ℝ))).congr_of_eventuallyEq heq).deriv
  · have hl : h * n < x := lt_of_le_of_ne (cell_lower hh x) (Ne.symm hx)
    have hu : x < h * (n + 1) := cell_upper hh x
    have htrans : HasDerivAt Real.smoothTransition 0
        ((x - h * n - (h / 2 - δ)) / (2 * δ)) := by
      rcases le_abs.mp (hfar n) with hr | hl
      · apply transition_hasDerivAt_zero_of_one_le
        apply (le_div_iff₀ (by positivity : 0 < 2 * δ)).mpr
        nlinarith
      · apply transition_hasDerivAt_zero_of_nonpos
        apply (div_le_iff₀ (by positivity : 0 < 2 * δ)).mpr
        nlinarith
    have harg : HasDerivAt
        (fun y : ℝ => (y - h * n - (h / 2 - δ)) / (2 * δ)) (1 / (2 * δ)) x :=
      (((hasDerivAt_id x).sub_const (h * n)).sub_const (h / 2 - δ)).div_const (2 * δ)
    have hcell : HasDerivAt (fun y : ℝ => h * ((n : ℝ) +
        Real.smoothTransition ((y - h * n - (h / 2 - δ)) / (2 * δ)))) 0 x := by
      convert! ((htrans.comp x harg).const_add (n : ℝ)).const_mul h using 1
      all_goals try with_reducible_and_instances rfl
      simp
    exact (hcell.congr_of_eventuallyEq (smoothStaircase_eventually_eq_cell hh n hl hu)).deriv

end CircleDomainRigidity.FiniteTransfer

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Selection_StaircaseMean
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Mean derivative of a randomly shifted staircase

A smooth degree-one lift has average derivative one over a full period.
For a uniform shift of the level grid this gives the derivative expectation.
Iterated integration gives the corresponding product identity for two
independent shifts.
-/

open MeasureTheory

namespace CircleDomainRigidity.FiniteTransfer

/-- FTC computes the integral of the shifted derivative over one period. -/
theorem integral_shifted_deriv_eq_period {P : ℝ → ℝ} {h : ℝ}
    (hP : ContDiff ℝ 1 P) (hperiod : ∀ x, P (x + h) = P x + h) (x : ℝ) :
    (∫ θ in (0 : ℝ)..h, deriv P (x - θ)) = h := by
  rw [intervalIntegral.integral_comp_sub_left, sub_zero,
    intervalIntegral.integral_deriv_of_contDiffOn_uIcc hP.contDiffOn]
  have heq := hperiod (x - h)
  have hx : x - h + h = x := by ring
  rw [hx] at heq
  linarith

/-- Joining the original coordinate to a shifted staircase by a cutoff
preserves the mean derivative multiplier. -/
theorem integral_cutoff_multiplier {P : ℝ → ℝ} {h : ℝ}
    (hP : ContDiff ℝ 1 P) (hperiod : ∀ x, P (x + h) = P x + h)
    (x χ : ℝ) :
    (∫ θ in (0 : ℝ)..h, (1 - χ) + χ * deriv P (x - θ)) = h := by
  have hi : IntervalIntegrable (fun θ => deriv P (x - θ)) volume 0 h :=
    (hP.continuous_deriv_one.comp (continuous_const.sub continuous_id)).intervalIntegrable 0 h
  rw [intervalIntegral.integral_add intervalIntegrable_const (hi.const_mul χ),
    intervalIntegral.integral_const, intervalIntegral.integral_const_mul,
    integral_shifted_deriv_eq_period hP hperiod]
  simp only [sub_zero, smul_eq_mul]
  ring

end CircleDomainRigidity.FiniteTransfer

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Selection_ShiftedStaircase
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# The randomly shifted smooth staircase family

Translating the explicit staircase places its transition bands at
`θ + hℤ`. The resulting family has the exact derivative mean required
for uniform random shifts, and retains the displacement and period
properties needed for periodic coordinate branches.
-/

open MeasureTheory
open scoped Topology ContDiff

noncomputable section

namespace CircleDomainRigidity.FiniteTransfer

theorem contDiff_shiftedStaircase {h δ : ℝ}
    (hh : 0 < h) (hδ : 0 < δ) (hδh : δ < h / 4) (θ : ℝ) :
    ContDiff ℝ ∞ (shiftedStaircase h δ θ) := by
  have hP := contDiff_smoothStaircase hh hδ hδh
  unfold shiftedStaircase
  exact ((hP.comp ((contDiff_id.add contDiff_const).sub contDiff_const)).add
    contDiff_const).sub contDiff_const

theorem monotone_shiftedStaircase {h δ : ℝ} (hh : 0 < h) (hδ : 0 < δ) (θ : ℝ) :
    Monotone (shiftedStaircase h δ θ) := by
  intro x y hxy
  unfold shiftedStaircase
  exact sub_le_sub_right (add_le_add
    (monotone_smoothStaircase hh hδ (by linarith)) (le_refl θ)) (h / 2)

theorem abs_shiftedStaircase_sub_le {h : ℝ} (hh : 0 < h) (δ θ x : ℝ) :
    |shiftedStaircase h δ θ x - x| ≤ h := by
  have heq : shiftedStaircase h δ θ x - x =
      smoothStaircase h δ ((x + h / 2) - θ) - ((x + h / 2) - θ) := by
    unfold shiftedStaircase
    ring
  rw [heq]
  exact abs_smoothStaircase_sub_le hh δ _

theorem shiftedStaircase_add_period {h : ℝ} (hh : 0 < h) (δ θ x : ℝ) :
    shiftedStaircase h δ θ (x + h) = shiftedStaircase h δ θ x + h := by
  have heq : (x + h + h / 2) - θ = ((x + h / 2) - θ) + h := by ring
  simp only [shiftedStaircase, heq, smoothStaircase_add_period hh]
  ring

theorem shiftedStaircase_add_nat_mul_period {h : ℝ} (hh : 0 < h)
    (δ θ x : ℝ) (N : ℕ) :
    shiftedStaircase h δ θ (x + N * h) = shiftedStaircase h δ θ x + N * h := by
  induction N with
  | zero => simp
  | succ N ih =>
    have heq : x + (↑(N + 1) : ℝ) * h = (x + N * h) + h := by push_cast <;> ring
    rw [heq, shiftedStaircase_add_period hh, ih]
    push_cast
    ring

/-- Choosing reciprocal-integer spacing preserves additive period one. -/
theorem shiftedStaircase_add_one {N : ℕ} (hN : 0 < N) (δ θ x : ℝ) :
    shiftedStaircase (1 / (N : ℝ)) δ θ (x + 1) =
      shiftedStaircase (1 / (N : ℝ)) δ θ x + 1 := by
  have hNr : 0 < (N : ℝ) := by exact_mod_cast hN
  have hmul : (N : ℝ) * (1 / (N : ℝ)) = 1 := by field_simp [ne_of_gt hNr]
  simpa only [hmul] using shiftedStaircase_add_nat_mul_period
    (div_pos zero_lt_one hNr) δ θ x N

/-- Translation does not change the derivative multiplier. -/
theorem deriv_shiftedStaircase {h δ : ℝ}
    (hh : 0 < h) (hδ : 0 < δ) (hδh : δ < h / 4) (θ x : ℝ) :
    deriv (shiftedStaircase h δ θ) x =
      deriv (smoothStaircase h δ) ((x + h / 2) - θ) := by
  have hP := (contDiff_smoothStaircase hh hδ hδh).differentiable (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)
  have harg : HasDerivAt (fun t : ℝ => (t + h / 2) - θ) 1 x :=
    ((hasDerivAt_id x).add_const (h / 2)).sub_const θ
  have hd := (((hP ((x + h / 2) - θ)).hasDerivAt.comp x harg).add_const θ).sub_const (h / 2)
  convert! hd.deriv using 1
  all_goals try with_reducible_and_instances rfl
  simp

theorem deriv_shiftedStaircase_nonneg {h δ : ℝ}
    (hh : 0 < h) (hδ : 0 < δ) (θ x : ℝ) :
    0 ≤ deriv (shiftedStaircase h δ θ) x :=
  (monotone_shiftedStaircase hh hδ θ).deriv_nonneg

/-- Only the open `δ`-neighborhoods of the shifted lattice can support
nonzero derivative, with zero derivative also at their endpoints. -/
theorem deriv_shiftedStaircase_eq_zero {h δ θ x : ℝ}
    (hh : 0 < h) (hδ : 0 < δ) (hδh : δ < h / 4)
    (hfar : ∀ n : ℤ, δ ≤ |x - (θ + h * n)|) :
    deriv (shiftedStaircase h δ θ) x = 0 := by
  rw [deriv_shiftedStaircase hh hδ hδh]
  apply deriv_smoothStaircase_eq_zero hh hδ hδh
  intro n
  convert hfar n using 1
  all_goals try with_reducible_and_instances rfl
  congr 1
  ring

theorem continuous_shiftedStaircase_deriv {h δ : ℝ}
    (hh : 0 < h) (hδ : 0 < δ) (hδh : δ < h / 4) (x : ℝ) :
    Continuous (fun θ => deriv (shiftedStaircase h δ θ) x) := by
  simp_rw [deriv_shiftedStaircase hh hδ hδh]
  have hP : ContDiff ℝ 1 (smoothStaircase h δ) :=
    (contDiff_smoothStaircase hh hδ hδh).of_le (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)
  exact hP.continuous_deriv_one.comp (continuous_const.sub continuous_id)

/-- A cutoff between the original coordinate and the actual shifted
staircase preserves mean multiplier one. -/
theorem integral_shiftedStaircase_cutoff_multiplier {h δ : ℝ}
    (hh : 0 < h) (hδ : 0 < δ) (hδh : δ < h / 4) (x χ : ℝ) :
    (∫ θ in (0 : ℝ)..h, (1 - χ) + χ * deriv (shiftedStaircase h δ θ) x) = h := by
  simp_rw [deriv_shiftedStaircase hh hδ hδh]
  exact integral_cutoff_multiplier
    ((contDiff_smoothStaircase hh hδ hδh).of_le (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top))
    (smoothStaircase_add_period hh δ) (x + h / 2) χ

end CircleDomainRigidity.FiniteTransfer

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Selection_WedgeEstimate
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Wedge estimate for cutoff staircase coordinates

The common cutoff differential makes the quadratic error term vanish.
The remaining terms have exactly the bounds used before taking independent
shift expectations in the finite-transfer construction.
-/

namespace CircleDomainRigidity.FiniteTransfer

/-- The two error covectors have the same direction, so their wedge is zero. -/
theorem planarWedge_cutoff_expansion (u v c : ℝ × ℝ) (q p r s : ℝ) :
    planarWedge (q • u + r • c) (p • v + s • c) =
      q * p * planarWedge u v + q * s * planarWedge u c + r * p * planarWedge c v := by
  simp only [planarWedge, Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd, smul_eq_mul]
  ring

/-- Pointwise bound for the wedge of two modified coordinate gradients. -/
theorem abs_planarWedge_cutoff_le (u v c : ℝ × ℝ) {q p r s h : ℝ}
    (hq : 0 ≤ q) (hp : 0 ≤ p) (hr : |r| ≤ h) (hs : |s| ≤ h) :
    |planarWedge (q • u + r • c) (p • v + s • c)| ≤
      q * p * |planarWedge u v| + h * q * |planarWedge u c| +
        h * p * |planarWedge c v| := by
  rw [planarWedge_cutoff_expansion]
  calc
    |q * p * planarWedge u v + q * s * planarWedge u c + r * p * planarWedge c v| ≤
        |q * p * planarWedge u v| + |q * s * planarWedge u c| +
          |r * p * planarWedge c v| :=
      (abs_add_le _ _).trans (add_le_add (abs_add_le _ _) le_rfl)
    _ = q * p * |planarWedge u v| + |s| * q * |planarWedge u c| +
          |r| * p * |planarWedge c v| := by
      simp only [abs_mul, abs_of_nonneg hq, abs_of_nonneg hp]
      ring
    _ ≤ _ := by
      gcongr

end CircleDomainRigidity.FiniteTransfer

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Selection_WedgeMean
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonMobius.sphereMetric _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Averaging the cutoff wedge estimate

Independent shifts reduce the leading wedge term to its original size.
The error from the common cutoff is linear in the grid spacing. Integrals
here use the square of shifts before normalization by its area `h²`.
-/

open MeasureTheory Set

namespace CircleDomainRigidity.FiniteTransfer

theorem integral_cutoff_wedge_le
    (u v c : ℝ × ℝ) {q p r s : ℝ → ℝ} {h : ℝ} (hh : 0 ≤ h)
    (hq : Continuous q) (hp : Continuous p) (hr : Continuous r) (hs : Continuous s)
    (hq0 : ∀ t ∈ Icc 0 h, 0 ≤ q t) (hp0 : ∀ t ∈ Icc 0 h, 0 ≤ p t)
    (hrh : ∀ t ∈ Icc 0 h, |r t| ≤ h) (hsh : ∀ t ∈ Icc 0 h, |s t| ≤ h)
    (hqmean : (∫ t in Icc 0 h, q t) = h)
    (hpmean : (∫ t in Icc 0 h, p t) = h) :
    (∫ z in Icc 0 h ×ˢ Icc 0 h,
      |planarWedge (q z.1 • u + r z.1 • c) (p z.2 • v + s z.2 • c)|
      ∂volume.prod volume) ≤
      h ^ 2 * |planarWedge u v| + h ^ 3 *
        (|planarWedge u c| + |planarWedge c v|) := by
  let A := |planarWedge u v|
  let B := |planarWedge u c|
  let C := |planarWedge c v|
  let D := Icc (0 : ℝ) h ×ˢ Icc (0 : ℝ) h
  have hcompact : IsCompact D := isCompact_Icc.prod isCompact_Icc
  have hf : IntegrableOn (fun z : ℝ × ℝ =>
      |planarWedge (q z.1 • u + r z.1 • c) (p z.2 • v + s z.2 • c)|)
      D (volume.prod volume) := by
    apply ContinuousOn.integrableOn_compact hcompact
    unfold planarWedge
    fun_prop
  have hqp : IntegrableOn (fun z : ℝ × ℝ => (q z.1 * p z.2) * A)
      D (volume.prod volume) := by
    apply ContinuousOn.integrableOn_compact hcompact
    fun_prop
  have hq1 : IntegrableOn (fun z : ℝ × ℝ => (q z.1 * 1) * (h * B))
      D (volume.prod volume) := by
    apply ContinuousOn.integrableOn_compact hcompact
    fun_prop
  have h1p : IntegrableOn (fun z : ℝ × ℝ => (1 * p z.2) * (h * C))
      D (volume.prod volume) := by
    apply ContinuousOn.integrableOn_compact hcompact
    fun_prop
  have hbound := setIntegral_mono_on hf ((hqp.add hq1).add h1p) hcompact.measurableSet
    (fun z hz => (abs_planarWedge_cutoff_le u v c (hq0 _ hz.1)
      (hp0 _ hz.2) (hrh _ hz.1) (hsh _ hz.2)).trans_eq (by dsimp [A, B, C] <;> ring))
  have hone : (∫ t in Icc (0 : ℝ) h, (1 : ℝ)) = h := by
    simp [hh]
  have hqint : (∫ z in Icc 0 h ×ˢ Icc 0 h, q z.1 ∂volume.prod volume) = h * h := by
    simpa only [mul_one, hqmean, hone] using
      (setIntegral_prod_mul (μ := volume) (ν := volume)
        q (fun _ : ℝ => (1 : ℝ)) (Icc 0 h) (Icc 0 h))
  have hpint : (∫ z in Icc 0 h ×ˢ Icc 0 h, p z.2 ∂volume.prod volume) = h * h := by
    simpa only [one_mul, hpmean, hone] using
      (setIntegral_prod_mul (μ := volume) (ν := volume)
        (fun _ : ℝ => (1 : ℝ)) p (Icc 0 h) (Icc 0 h))
  calc
    _ ≤ (∫ z in D, (q z.1 * p z.2) * A + (q z.1 * 1) * (h * B) +
        (1 * p z.2) * (h * C) ∂volume.prod volume) := hbound
    _ = h ^ 2 * A + h ^ 3 * (B + C) := by
      have hadd := integral_add (hqp.add hq1) h1p
      have hadd' := integral_add hqp hq1
      simp only [Pi.add_apply] at hadd hadd'
      rw [hadd, hadd']
      simp only [D, integral_mul_const, setIntegral_prod_mul, hqmean, hpmean, hqint,
        one_mul, hpint]
      ring

end CircleDomainRigidity.FiniteTransfer

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Selection_StaircaseWedge
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Expected wedge of actual staircase coordinates

This instantiates the averaging bound with the constructed smooth
staircase family. After division by `h²`, the error is proportional to
`h`, uniformly in the transition width.
-/

open MeasureTheory Set
open scoped Topology

noncomputable section

namespace CircleDomainRigidity.FiniteTransfer

theorem continuous_shiftedStaircase_value {h δ : ℝ}
    (hh : 0 < h) (hδ : 0 < δ) (hδh : δ < h / 4) (x : ℝ) :
    Continuous (fun θ => shiftedStaircase h δ θ x) := by
  unfold shiftedStaircase
  exact (((contDiff_smoothStaircase hh hδ hδh).continuous.comp
    (continuous_const.sub continuous_id)).add continuous_id).sub continuous_const

/-- The finite-transfer wedge bound for two independently shifted actual
staircases, prior to summing over coordinate pairs and domain points. -/
theorem average_staircase_wedge_le (u v c : ℝ × ℝ) (x y : ℝ)
    {h δ χ : ℝ} (hh : 0 < h) (hδ : 0 < δ) (hδh : δ < h / 4)
    (hχ0 : 0 ≤ χ) (hχ1 : χ ≤ 1) :
    (∫ z in Icc 0 h ×ˢ Icc 0 h,
      |planarWedge
        (((1 - χ) + χ * deriv (shiftedStaircase h δ z.1) x) • u +
          (shiftedStaircase h δ z.1 x - x) • c)
        (((1 - χ) + χ * deriv (shiftedStaircase h δ z.2) y) • v +
          (shiftedStaircase h δ z.2 y - y) • c)| ∂volume.prod volume) / h ^ 2 ≤
      |planarWedge u v| + h * (|planarWedge u c| + |planarWedge c v|) := by
  let q := fun θ => (1 - χ) + χ * deriv (shiftedStaircase h δ θ) x
  let p := fun θ => (1 - χ) + χ * deriv (shiftedStaircase h δ θ) y
  let r := fun θ => shiftedStaircase h δ θ x - x
  let s := fun θ => shiftedStaircase h δ θ y - y
  have hq : Continuous q := continuous_const.add
    (continuous_const.mul (continuous_shiftedStaircase_deriv hh hδ hδh x))
  have hp : Continuous p := continuous_const.add
    (continuous_const.mul (continuous_shiftedStaircase_deriv hh hδ hδh y))
  have hr : Continuous r := (continuous_shiftedStaircase_value hh hδ hδh x).sub continuous_const
  have hs : Continuous s := (continuous_shiftedStaircase_value hh hδ hδh y).sub continuous_const
  have hq0 (θ : ℝ) : 0 ≤ q θ :=
    add_nonneg (sub_nonneg.mpr hχ1)
      (mul_nonneg hχ0 (deriv_shiftedStaircase_nonneg hh hδ θ x))
  have hp0 (θ : ℝ) : 0 ≤ p θ :=
    add_nonneg (sub_nonneg.mpr hχ1)
      (mul_nonneg hχ0 (deriv_shiftedStaircase_nonneg hh hδ θ y))
  have hqm : (∫ θ in Icc 0 h, q θ) = h := by
    rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le hh.le]
    exact integral_shiftedStaircase_cutoff_multiplier hh hδ hδh x χ
  have hpm : (∫ θ in Icc 0 h, p θ) = h := by
    rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le hh.le]
    exact integral_shiftedStaircase_cutoff_multiplier hh hδ hδh y χ
  have hbound := integral_cutoff_wedge_le u v c hh.le hq hp hr hs
    (fun θ _ => hq0 θ) (fun θ _ => hp0 θ)
    (fun θ _ => abs_shiftedStaircase_sub_le hh δ θ x)
    (fun θ _ => abs_shiftedStaircase_sub_le hh δ θ y) hqm hpm
  apply (div_le_iff₀ (sq_pos_of_pos hh)).mpr
  exact hbound.trans_eq (by ring)

end CircleDomainRigidity.FiniteTransfer

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Probability_RandomShifts
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Independent uniform grid shifts

The shifts have normalized interval distribution. Any two distinct labels
have product law, so the two-shift integral equals their expected wedge cost.
-/

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal

noncomputable section

namespace CircleDomainRigidity.FiniteTransfer

theorem shiftLaw_eq (h : ℝ) :
    shiftLaw h = (ENNReal.ofReal h)⁻¹ • volume.restrict (Icc 0 h) := by
  simp only [shiftLaw, ProbabilityTheory.cond, Real.volume_Icc, sub_zero]

theorem shiftLaw_isProbabilityMeasure {h : ℝ} (hh : 0 < h) :
    IsProbabilityMeasure (shiftLaw h) := by
  apply cond_isProbabilityMeasure_of_finite
  · simp [Real.volume_Icc, hh]
  · simp [Real.volume_Icc]

theorem integral_shiftLaw_pair (h : ℝ) (f : ℝ × ℝ → ℝ) :
    (∫ z, f z ∂(shiftLaw h).prod (shiftLaw h)) =
      (∫ z in Icc 0 h ×ˢ Icc 0 h, f z ∂volume.prod volume) / h ^ 2 := by
  rw [shiftLaw_eq, Measure.prod_smul_left, Measure.prod_smul_right,
    smul_smul, ← Measure.prod_restrict, integral_smul_measure]
  simp only [ENNReal.toReal_mul, ENNReal.toReal_inv, smul_eq_mul]
  by_cases hh : 0 ≤ h
  · rw [ENNReal.toReal_ofReal hh]
    ring
  · have he : Icc 0 h = ∅ := Icc_eq_empty_of_lt (lt_of_not_ge hh)
    simp [he]

theorem measurePreserving_grid_pair (μ : Measure ℝ) [IsProbabilityMeasure μ]
    {n : ℕ} {i j : Fin n} (hij : i ≠ j) :
    MeasurePreserving (fun θ : Fin n → ℝ => (θ i, θ j))
      (Measure.pi (fun _ => μ)) (μ.prod μ) := by
  refine ⟨(measurable_pi_apply i).prodMk (measurable_pi_apply j), ?_⟩
  have hind := (iIndepFun_pi (μ := fun _ : Fin n => μ)
    (X := fun _ => id) (fun _ => aemeasurable_id)).indepFun hij
  have hmap := hind.map_prod_eq_prod_map_map
    (measurable_pi_apply i).aemeasurable (measurable_pi_apply j).aemeasurable
  simpa only [(measurePreserving_eval (fun _ : Fin n => μ) i).map_eq,
    (measurePreserving_eval (fun _ : Fin n => μ) j).map_eq] using hmap

theorem integral_grid_pair (μ : Measure ℝ) [IsProbabilityMeasure μ]
    {n : ℕ} {i j : Fin n} (hij : i ≠ j) (f : ℝ × ℝ → ℝ)
    (hf : AEStronglyMeasurable f (μ.prod μ)) :
    (∫ θ, f (θ i, θ j) ∂Measure.pi (fun _ : Fin n => μ)) =
      ∫ z, f z ∂μ.prod μ := by
  have hp := measurePreserving_grid_pair μ hij
  rw [← hp.map_eq]
  exact (integral_map hp.measurable.aemeasurable (hp.map_eq.symm ▸ hf)).symm

end CircleDomainRigidity.FiniteTransfer

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Transfer_ReciprocalGridSelection
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Selecting an actual reciprocal-integer grid

The grid spacing must be `1/N` so that the staircases respect period one.
The laws of the uniform shifts change with the spacing. This selection
uses those actual product laws, keeps any prescribed conull compatibility
event, and makes both the wedge cost and scaled terminal count small.
-/

open Set MeasureTheory Filter
open scoped Topology

namespace CircleDomainRigidity.FiniteTransfer

theorem reciprocalGridStep_pos (N : ℕ) : 0 < reciprocalGridStep N := by
  unfold reciprocalGridStep
  positivity

theorem reciprocalGridStep_le_one (N : ℕ) : reciprocalGridStep N ≤ 1 := by
  unfold reciprocalGridStep
  apply (div_le_one (by positivity : 0 < (N : ℝ) + 1)).mpr
  exact le_add_of_nonneg_left (Nat.cast_nonneg N)

theorem reciprocalGridStep_mul_denominator (N : ℕ) :
    reciprocalGridStep N * ((N : ℝ) + 1) = 1 := by
  unfold reciprocalGridStep
  exact div_mul_cancel₀ 1 (by positivity)

theorem reciprocalGridStep_tendsto_zero :
    Tendsto reciprocalGridStep atTop (𝓝 0) :=
  tendsto_one_div_add_atTop_nhds_zero_nat

theorem reciprocalGridLaw_isProbabilityMeasure (n N : ℕ) :
    IsProbabilityMeasure (reciprocalGridLaw n N) := by
  let := shiftLaw_isProbabilityMeasure (reciprocalGridStep_pos N)
  unfold reciprocalGridLaw
  first | (set_option synthInstance.maxHeartbeats 20000 in infer_instance) | exact Measure.isProbabilityMeasure_map (by first | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability)

end CircleDomainRigidity.FiniteTransfer

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Topology_ThinCollar
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonMobius.sphereMetric _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Interpolation in a thin exterior neighborhood

For a compact retained core, integrals over shrinking exterior neighborhoods
tend to zero. A continuous family of energy densities can consequently be
interpolated smoothly to its original value near the core with arbitrarily
small added energy. No measure-zero assumption on the core boundary is used.
-/

open Set Filter Metric MeasureTheory
open scoped Topology ContDiff Manifold

noncomputable section

namespace CircleDomainRigidity.FiniteTransfer

theorem reciprocalGridStep_antitone : Antitone reciprocalGridStep := by
  intro m n hmn
  unfold reciprocalGridStep
  apply one_div_le_one_div_of_le (by positivity)
  exact_mod_cast Nat.add_le_add_right hmn 1

theorem iInter_outer_thickenings_eq_empty
    {E : Type*} [MetricSpace E] {K : Set E} (hK : IsClosed K) :
    (⋂ n : ℕ, thickening (reciprocalGridStep n) K \ K) = ∅ := by
  apply eq_empty_iff_forall_notMem.mpr
  intro x hx
  have hx' := mem_iInter.mp hx
  have hxK : x ∈ closure K := by
    rw [closure_eq_iInter_thickening]
    apply mem_iInter₂.mpr
    intro ε hε
    obtain ⟨n, hn⟩ := (reciprocalGridStep_tendsto_zero.eventually
      (gt_mem_nhds hε)).exists
    exact thickening_mono hn.le K (hx' n).1
  exact (hx' 0).2 (hK.closure_eq ▸ hxK)

theorem tendsto_integral_outer_thickenings
    {E : Type*} [MetricSpace E] [MeasurableSpace E] [BorelSpace E]
    {μ : Measure E} {K : Set E} (hK : IsClosed K)
    {f : E → ℝ} (hf : IntegrableOn f (thickening 1 K) μ) :
    Tendsto (fun n => ∫ x in thickening (reciprocalGridStep n) K \ K, f x ∂μ)
      atTop (𝓝 0) := by
  have ht := tendsto_setIntegral_of_antitone
    (fun n : ℕ => isOpen_thickening.measurableSet.diff hK.measurableSet)
    (fun m n hmn => sdiff_subset_sdiff_left (thickening_mono
      (reciprocalGridStep_antitone hmn) K))
    (f := f) (μ := μ) ⟨0, by
      simpa only [reciprocalGridStep, Nat.cast_zero, zero_add, div_one]
        using hf.mono_set sdiff_subset⟩
  simpa only [iInter_outer_thickenings_eq_empty hK, setIntegral_empty] using ht

/-- Smoothly select the original member `H (x,0)` near the retained core,
and the new member `H (x,1)` away from a small neighborhood. The absolute
change of its integral outside the core is arbitrarily small. -/
theorem exists_smooth_interpolation_small_change
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    {μ : Measure E} [IsFiniteMeasureOnCompacts μ]
    {K S U : Set E} (hK : IsCompact K) (hS : Bornology.IsBounded S)
    (hSm : MeasurableSet S) (hU : IsOpen U) (hKU : K ⊆ U)
    (H : E × ℝ → ℝ) (hH : ContinuousOn H (univ ×ˢ Icc 0 1))
    {ε : ℝ} (hε : 0 < ε) :
    ∃ (N : Set E) (χ : E → ℝ), IsOpen N ∧ K ⊆ N ∧ N ⊆ U ∧
      ContDiff ℝ ∞ χ ∧ (∀ x, χ x ∈ Icc 0 1) ∧
      (∀ᶠ x in 𝓝ˢ K, χ x = 0) ∧ (∀ x ∉ N, χ x = 1) ∧
      (∫ x in S \ K, |H (x, χ x) - H (x, 1)| ∂μ) < ε := by
  have hbox := hK.cthickening (r := 1)
  have hprod : IsCompact (cthickening 1 K ×ˢ Icc (0 : ℝ) 1) := hbox.prod isCompact_Icc
  obtain ⟨B, hB⟩ := hprod.exists_bound_of_continuousOn
    (hH.mono (prod_mono (subset_univ _) Subset.rfl))
  let C : ℝ := 2 * max B 0
  have hC : 0 ≤ C := mul_nonneg (by norm_num) (le_max_right _ _)
  have hbound {x : E} (hx : x ∈ cthickening 1 K) {t : ℝ} (ht : t ∈ Icc 0 1) :
      |H (x,t) - H (x,1)| ≤ C := by
    calc
      |H (x,t) - H (x,1)| ≤ |H (x,t)| + |H (x,1)| := abs_sub _ _
      _ ≤ B + B := add_le_add (hB _ ⟨hx, ht⟩) (hB _ ⟨hx, by norm_num⟩)
      _ ≤ C := by dsimp [C] <;> linarith [le_max_left B 0]
  have hCi : IntegrableOn (fun _ : E => C) (thickening 1 K) μ :=
    (continuous_const.continuousOn.integrableOn_compact hbox).mono_set
      (thickening_subset_cthickening 1 K)
  have hsmall := (tendsto_integral_outer_thickenings hK.isClosed hCi).eventually
    (gt_mem_nhds hε)
  obtain ⟨r, hr, hrU⟩ := hK.exists_cthickening_subset_open hU hKU
  have hthin := reciprocalGridStep_tendsto_zero.eventually (gt_mem_nhds hr)
  obtain ⟨n, hnsmall, hnthin⟩ := (hsmall.and hthin).exists
  let N := thickening (reciprocalGridStep n) K
  have hN : IsOpen N := isOpen_thickening
  have hKN : K ⊆ N := self_subset_thickening (reciprocalGridStep_pos n) K
  have hNU : N ⊆ U := (thickening_subset_cthickening _ K).trans
    ((cthickening_mono hnthin.le K).trans hrU)
  obtain ⟨χ, hzero, hone, hχrange⟩ := exists_contMDiffMap_zero_one_nhds_of_isClosed
    (𝓘(ℝ, E)) hK.isClosed hN.isClosed_compl
    (disjoint_compl_right_iff_subset.mpr hKN) (n := (⊤ : ℕ∞))
  have hχ : ContDiff ℝ ∞ (χ : E → ℝ) := contMDiff_iff_contDiff.mp χ.contMDiff
  have hχone : ∀ x ∉ N, χ x = 1 := fun x hx => hone.self_of_nhdsSet x hx
  have h1 : Continuous (fun x : E => H (x,1)) :=
    hH.comp_continuous (by fun_prop) (by intro x; exact ⟨mem_univ x, by norm_num⟩)
  have hc : Continuous (fun x : E => H (x,χ x)) :=
    hH.comp_continuous (continuous_id.prodMk hχ.continuous)
      (fun x => ⟨mem_univ x, hχrange x⟩)
  let g : E → ℝ := fun x => |H (x,χ x) - H (x,1)|
  have hgi : IntegrableOn g (S \ K) μ :=
    ((hc.sub h1).abs.continuousOn.integrableOn_compact hS.isCompact_closure).mono_set
      (sdiff_subset.trans subset_closure)
  have hT : MeasurableSet (S \ K) := hSm.diff hK.isClosed.measurableSet
  have heq : (∫ x in S \ K, g x ∂μ) = ∫ x in (S \ K) ∩ N, g x ∂μ := by
    have hz : (∫ x in (S \ K) \ N, g x ∂μ) = 0 := by
      apply setIntegral_eq_zero_of_forall_eq_zero
      intro x hx
      simp only [g, hχone x hx.2, sub_self, abs_zero]
    have hadd := integral_inter_add_sdiff hN.measurableSet hgi
    rw [hz, add_zero] at hadd
    exact hadd.symm
  have hCNi : IntegrableOn (fun _ : E => C) (N \ K) μ :=
    hCi.mono_set (sdiff_subset.trans (thickening_mono (reciprocalGridStep_le_one n) K))
  refine ⟨N, χ, hN, hKN, hNU, hχ, hχrange, hzero, hχone, ?_⟩
  change (∫ x in S \ K, g x ∂μ) < ε
  rw [heq]
  calc
    (∫ x in (S \ K) ∩ N, g x ∂μ) ≤ ∫ x in (S \ K) ∩ N, C ∂μ := by
      apply setIntegral_mono_on (hgi.mono_set inter_subset_left)
        (hCNi.mono_set (by intro x hx; exact ⟨hx.2, hx.1.2⟩))
        (hT.inter hN.measurableSet)
      intro x hx
      exact hbound ((thickening_subset_cthickening _ K
        ((thickening_mono (reciprocalGridStep_le_one n) K) hx.2))) (hχrange x)
    _ ≤ ∫ x in N \ K, C ∂μ :=
      setIntegral_mono_set hCNi (Eventually.of_forall (fun _ => hC))
        (Eventually.of_forall (fun _ hx => ⟨hx.2, hx.1.2⟩))
    _ < ε := hnsmall

end CircleDomainRigidity.FiniteTransfer

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Sobolev_MetricInterpolation
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonMobius.sphereMetric _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
attribute [-simp] _root_.OAI.CircleDomainRigidity.FiniteTransfer.blendMetric_identity _root_.OAI.CircleDomainRigidity.FiniteTransfer.covectorEnergy_identity _root_.OAI.CircleDomainRigidity.metricBeltramiCoefficient_scalar
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Keeping the original metric near the retained core

The interpolated metric is an actual positive definite matrix field.
Its coordinate energy is the inverse-matrix energy density, rather than
an independently supplied scalar surrogate.
-/

open Matrix Set Filter MeasureTheory
open scoped Topology ContDiff Matrix.Norms.Elementwise

noncomputable section

namespace CircleDomainRigidity.FiniteTransfer

theorem blendMetric_posDef {g : PlanarMetric} (hg : g.PosDef)
    {t : ℝ} (ht : t ∈ Icc 0 1) : (blendMetric g t).PosDef := by
  by_cases hz : t = 0
  · simpa only [hz, blendMetric_zero] using (Matrix.PosDef.one : (1 : PlanarMetric).PosDef)
  · exact Matrix.PosDef.posSemidef_add
      (Matrix.PosSemidef.one.smul (sub_nonneg.mpr ht.2))
      (hg.smul (lt_of_le_of_ne ht.1 (Ne.symm hz)))

theorem continuousOn_matrixEnergy
    {X : Type*} [TopologicalSpace X] {D : Set X}
    {A g : X → PlanarMetric} (hA : Continuous A) (hg : Continuous g)
    (hPD : ∀ x ∈ D, (g x).PosDef) :
    ContinuousOn (fun x => matrixEnergy (A x) (g x)) D := by
  have hi : ContinuousOn (fun x => (g x).det⁻¹) D :=
    hg.matrix_det.continuousOn.inv₀ (fun x hx => (hPD x hx).det_pos.ne')
  have hiMat : ContinuousOn (fun x => (g x).det⁻¹ • (g x).adjugate) D :=
    hi.smul hg.matrix_adjugate.continuousOn
  have hm : ContinuousOn (fun x => ((g x).det⁻¹ • (g x).adjugate) * A x) D :=
    hiMat.mul hA.continuousOn
  have ht : ContinuousOn (fun x => Matrix.trace (((g x).det⁻¹ • (g x).adjugate) * A x)) D :=
    (continuous_id.matrix_trace : Continuous (Matrix.trace : PlanarMetric → ℝ)).comp_continuousOn hm
  simpa only [matrixEnergy, Matrix.inv_def, Ring.inverse_eq_inv, Pi.mul_def] using
    ht.mul hg.matrix_det.sqrt.continuousOn

/-- Replace a smooth positive definite metric by the identity near a compact
core. The change of the actual coordinate energy outside that core is small.
The transition can be confined to any prescribed open neighborhood. -/
theorem exists_core_preserving_metric
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    {μ : Measure E} [IsFiniteMeasureOnCompacts μ]
    {K S U : Set E} (hK : IsCompact K) (hS : Bornology.IsBounded S)
    (hSm : MeasurableSet S) (hU : IsOpen U) (hKU : K ⊆ U)
    (A g : E → PlanarMetric) (hA : Continuous A) (hg : ContDiff ℝ ∞ g)
    (hPD : ∀ x, (g x).PosDef) {ε : ℝ} (hε : 0 < ε) :
    ∃ (N : Set E) (g' : E → PlanarMetric), IsOpen N ∧ K ⊆ N ∧ N ⊆ U ∧
      ContDiff ℝ ∞ g' ∧ (∀ x, (g' x).PosDef) ∧
      (∀ᶠ x in 𝓝ˢ K, g' x = 1) ∧ (∀ x ∉ N, g' x = g x) ∧
      (∫ x in S \ K, |matrixEnergy (A x) (g' x) - matrixEnergy (A x) (g x)| ∂μ) < ε := by
  let H : E × ℝ → ℝ := fun p => matrixEnergy (A p.1) (blendMetric (g p.1) p.2)
  have hblend : Continuous (fun p : E × ℝ => blendMetric (g p.1) p.2) := by
    unfold blendMetric
    fun_prop
  have hH : ContinuousOn H (univ ×ˢ Icc 0 1) :=
    continuousOn_matrixEnergy (hA.comp continuous_fst) hblend
      (fun p hp => blendMetric_posDef (hPD p.1) hp.2)
  obtain ⟨N, χ, hN, hKN, hNU, hχ, hrange, hzero, hone, hchange⟩ :=
    exists_smooth_interpolation_small_change (μ := μ) hK hS hSm hU hKU H hH hε
  let g' : E → PlanarMetric := fun x => blendMetric (g x) (χ x)
  refine ⟨N, g', hN, hKN, hNU, ?_, ?_, ?_, ?_, ?_⟩
  · dsimp [g', blendMetric]
    exact (contDiff_const.sub hχ).smul contDiff_const |>.add (hχ.smul hg)
  · exact fun x => blendMetric_posDef (hPD x) (hrange x)
  · filter_upwards [hzero] with x hx
    simp only [g', hx, blendMetric_zero]
  · intro x hx
    simp only [g', hone x hx, blendMetric_one]
  · simpa only [H, g', blendMetric_one] using hchange

theorem continuous_matrixEnergy
    {X : Type*} [TopologicalSpace X] {A g : X → PlanarMetric}
    (hA : Continuous A) (hg : Continuous g) (hPD : ∀ x, (g x).PosDef) :
    Continuous (fun x => matrixEnergy (A x) (g x)) :=
  continuousOn_univ.mp (continuousOn_matrixEnergy hA hg (fun x _ => hPD x))

/-- The complete local metric step: small pairwise wedges give one smooth
positive definite metric with the prescribed total energy bound, equal to
the original identity metric on a full neighborhood of the retained core.
The constant regularization and the transition region are both constructed.
-/
theorem exists_smooth_core_gramMetric
    (x y : ℕ → (ℝ × ℝ) → ℝ) (n : ℕ)
    (hx : ∀ i, ContDiff ℝ ∞ (x i)) (hy : ∀ i, ContDiff ℝ ∞ (y i))
    {K S U : Set (ℝ × ℝ)} (hK : IsCompact K) (hS : Bornology.IsBounded S)
    (hSm : MeasurableSet S) (hU : IsOpen U) (hKU : K ⊆ U) {ε : ℝ}
    (hε : (∫ z in S \ K, 2 * covectorWedges (fun i => x i z) (fun i => y i z) n) < ε) :
    ∃ (τ : ℝ) (N : Set (ℝ × ℝ)) (g : (ℝ × ℝ) → PlanarMetric),
      0 < τ ∧ IsOpen N ∧ K ⊆ N ∧ N ⊆ U ∧ ContDiff ℝ ∞ g ∧
      (∀ z, (g z).PosDef) ∧ (∀ᶠ z in 𝓝ˢ K, g z = 1) ∧
      (∀ z ∉ N, g z = gramTensor (fun i => x i z) (fun i => y i z) n + τ • 1) ∧
      (∫ z in S \ K, matrixEnergy (gramTensor (fun i => x i z) (fun i => y i z) n) (g z)) < ε := by
  let A := fun z => gramTensor (fun i => x i z) (fun i => y i z) n
  obtain ⟨τ, hτ, hreg, hPD, henergy⟩ := exists_smooth_gramMetric_on_bounded x y n hx hy
    (hS.subset sdiff_subset) hε
  let g₀ := fun z => A z + τ • 1
  change ContDiff ℝ ∞ g₀ at hreg
  change (∫ z in S \ K, matrixEnergy (A z) (g₀ z)) < ε at henergy
  have hAc : Continuous A := by
    have h := hreg.continuous.sub (continuous_const (y := τ • (1 : PlanarMetric)))
    change Continuous (fun z => A z + τ • 1 - τ • 1) at h
    simpa only [add_sub_cancel_right] using h
  have hci := continuous_matrixEnergy hAc hreg.continuous hPD
  let I := ∫ z in S \ K, matrixEnergy (A z) (g₀ z)
  obtain ⟨N, g, hN, hKN, hNU, hg, hgPD, hcore, hout, hchange⟩ :=
    exists_core_preserving_metric (μ := volume) hK hS hSm hU hKU A g₀ hAc hreg hPD
      (sub_pos.mpr henergy)
  have hgi := continuous_matrixEnergy hAc hg.continuous hgPD
  have hbasei : IntegrableOn (fun z => matrixEnergy (A z) (g₀ z)) (S \ K) :=
    (hci.continuousOn.integrableOn_compact hS.isCompact_closure).mono_set
      (sdiff_subset.trans subset_closure)
  have hnewi : IntegrableOn (fun z => matrixEnergy (A z) (g z)) (S \ K) :=
    (hgi.continuousOn.integrableOn_compact hS.isCompact_closure).mono_set
      (sdiff_subset.trans subset_closure)
  refine ⟨τ, N, g, hτ, hN, hKN, hNU, hg, hgPD, hcore, hout, ?_⟩
  have hle : (∫ z in S \ K, matrixEnergy (A z) (g z)) - I ≤
      ∫ z in S \ K, |matrixEnergy (A z) (g z) - matrixEnergy (A z) (g₀ z)| := by
    dsimp only [I]
    rw [← integral_sub hnewi hbasei]
    exact integral_mono (hnewi.sub hbasei) (hnewi.sub hbasei).abs
      (fun _ => le_abs_self _)
  change (∫ z in S \ K, |matrixEnergy (A z) (g z) - matrixEnergy (A z) (g₀ z)|) < ε - I
    at hchange
  linarith

end CircleDomainRigidity.FiniteTransfer

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Sobolev_CoordinateEnergy
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# The separate coordinate energies in the chosen metric

The inverse-matrix trace density is exactly the sum of the nonnegative
squared covector norms. Thus control of the Gram energy controls every
coordinate, and in the identity metric these are the usual squared
Euclidean differential norms.
-/

open Matrix Finset
open scoped Matrix.Norms.Elementwise

noncomputable section

namespace CircleDomainRigidity.FiniteTransfer

theorem gramEnergy_eq_sum_covectorEnergy (x y : ℕ → ℝ) (n : ℕ) (g : PlanarMetric) :
    matrixEnergy (gramTensor x y n) g =
      ∑ i ∈ range n, covectorEnergy ![x i,y i] g := by
  rw [gramTensor_eq_sum]
  simp only [covectorEnergy_eq_matrixEnergy, matrixEnergy, Finset.mul_sum,
    Matrix.trace_sum, Finset.sum_mul]

end CircleDomainRigidity.FiniteTransfer

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Transfer_RankOneFilling
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Rank-one smooth filling of a collar

If at most one coordinate varies on a collar, extend that coordinate by
a smooth cutoff and all the others constantly. Every pairwise wedge of
the resulting coordinate gradients vanishes throughout the filling.
-/

open Set Filter
open scoped Topology ContDiff

noncomputable section

namespace CircleDomainRigidity.FiniteTransfer

/-- The scalar collar extension gives a simultaneous smooth extension
with zero pairwise wedges when only one boundary coordinate is active. -/
theorem exists_rank_one_collar_extension {ι : Type*} (k : ι)
    {U A : Set (ℝ × ℝ)} (hU : IsOpen U) (hA : IsClosed A) (hAU : A ⊆ U)
    (f : ι → (ℝ × ℝ) → ℝ) (c : ι → ℝ)
    (hfk : ContDiffOn ℝ ∞ (f k) U)
    (hinactive : ∀ i, i ≠ k → EqOn (f i) (fun _ => c i) U) :
    ∃ F : ι → (ℝ × ℝ) → ℝ,
      (∀ i, ContDiff ℝ ∞ (F i)) ∧
      (∀ᶠ x in 𝓝ˢ A, ∀ i, F i x = f i x) ∧
      (∀ i x, x ∉ U → F i x = c i) ∧
      (∀ i j, i ≠ j → ∀ x, planarWedge (planarGradient (F i) x)
        (planarGradient (F j) x) = 0) := by
  classical
  obtain ⟨g, hg, hag, hgc⟩ := exists_smooth_collar_extension hU hA hAU hfk (c k)
  let F : ι → (ℝ × ℝ) → ℝ := fun i => if i = k then g else fun _ => c i
  refine ⟨F, ?_, ?_, ?_, ?_⟩
  · intro i
    by_cases hi : i = k
    · simpa [F, hi] using hg
    · simpa [F, hi] using (contDiff_const : ContDiff ℝ ∞ (fun _ : ℝ × ℝ => c i))
  · have hUnhds : U ∈ 𝓝ˢ A := hU.mem_nhdsSet.mpr hAU
    filter_upwards [hag, hUnhds] with x hx hxU i
    by_cases hi : i = k
    · simpa [F, hi] using hx
    · simpa [F, hi] using (hinactive i hi hxU).symm
  · intro i x hx
    by_cases hi : i = k
    · simpa [F, hi] using hgc x hx
    · simp [F, hi]
  · intro i j hij x
    by_cases hi : i = k
    · have hj : j ≠ k := fun hj => hij (hi.trans hj.symm)
      simp [F, hj, planarWedge]
    · simp [F, hi, planarWedge]

end CircleDomainRigidity.FiniteTransfer

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Modulus_GridIncidence
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonMobius.sphereMetric _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Actual probabilities that a shifted lattice meets a band

A grid of spacing `h` meets `[a,b]` exactly when the shift modulo `h`
lies in the projection of this interval. Haar measure of that projection
is at most `min h (b-a)`. Under the actual normalized interval law for
the shift, the probability is at most `min 1 ((b-a)/h)`.
-/

open Set MeasureTheory Metric

namespace CircleDomainRigidity.FiniteTransfer

theorem latticeBandIncidence_eq_preimage (h a b : ℝ) :
    latticeBandIncidence h a b =
      ((↑) : ℝ → AddCircle h) ⁻¹' (((↑) : ℝ → AddCircle h) '' Icc a b) := by
  ext θ
  constructor
  · rintro ⟨k, hk⟩
    refine ⟨θ + (k : ℝ) * h, hk, ?_⟩
    exact (addCircle_eq_iff_exists_int h _ _).mpr ⟨k, rfl⟩
  · rintro ⟨x, hx, heq⟩
    obtain ⟨k, hk⟩ := (addCircle_eq_iff_exists_int h x θ).mp heq
    exact ⟨k, hk ▸ hx⟩

theorem measurableSet_latticeBandIncidence {h : ℝ} (hh : 0 < h) (a b : ℝ) :
    MeasurableSet (latticeBandIncidence h a b) := by
  let : Fact (0 < h) := ⟨hh⟩
  rw [latticeBandIncidence_eq_preimage]
  exact ((isCompact_Icc.image (AddCircle.continuous_mk' h)).isClosed.measurableSet).preimage
    (AddCircle.continuous_mk' h).measurable

theorem volume_addCircle_interval_le {h : ℝ} [Fact (0 < h)] (a b : ℝ) :
    volume (((↑) : ℝ → AddCircle h) '' Icc a b) ≤
      ENNReal.ofReal (min h (b - a)) := by
  have hsub : ((↑) : ℝ → AddCircle h) '' Icc a b ⊆
      closedBall (((a + b) / 2 : ℝ) : AddCircle h) ((b - a) / 2) := by
    rintro _ ⟨x, hx, rfl⟩
    rw [mem_closedBall, dist_eq_norm, ← QuotientAddGroup.mk_sub]
    apply QuotientAddGroup.norm_mk_le_norm.trans
    rw [Real.norm_eq_abs, abs_le]
    constructor <;> linarith [hx.1, hx.2]
  calc
    _ ≤ volume (closedBall (((a + b) / 2 : ℝ) : AddCircle h) ((b - a) / 2)) :=
      measure_mono hsub
    _ = _ := by rw [AddCircle.volume_closedBall]; congr 2; ring

/-- The normalized interval shift law gives the exact quotient measure
of the event, divided by the grid spacing. -/
theorem shiftLaw_latticeBandIncidence_eq {h : ℝ} [Fact (0 < h)] (a b : ℝ) :
    shiftLaw h (latticeBandIncidence h a b) =
      volume (((↑) : ℝ → AddCircle h) '' Icc a b) / ENNReal.ofReal h := by
  have hmeas : MeasurableSet (((↑) : ℝ → AddCircle h) '' Icc a b) :=
    (isCompact_Icc.image (AddCircle.continuous_mk' h)).isClosed.measurableSet
  have hpush := (AddCircle.measurePreserving_mk (T := h) 0).measure_preimage
    hmeas.nullMeasurableSet
  change (volume.restrict (Ioc 0 (0 + h)))
    (((↑) : ℝ → AddCircle h) ⁻¹' (((↑) : ℝ → AddCircle h) '' Icc a b)) = _ at hpush
  rw [shiftLaw_eq, Measure.smul_apply, smul_eq_mul,
    ← restrict_Ioc_eq_restrict_Icc, latticeBandIncidence_eq_preimage]
  rw [zero_add] at hpush
  rw [hpush, div_eq_mul_inv, mul_comm]

/-- The quantitative band-hit estimate used in the terminal-count
expectation. It is proved for the actual normalized shift measure. -/
theorem shiftLaw_latticeBandIncidence_le {h : ℝ} (hh : 0 < h) (a b : ℝ) :
    shiftLaw h (latticeBandIncidence h a b) ≤
      ENNReal.ofReal (min 1 ((b - a) / h)) := by
  let : Fact (0 < h) := ⟨hh⟩
  rw [shiftLaw_latticeBandIncidence_eq]
  calc
    _ ≤ ENNReal.ofReal (min h (b - a)) / ENNReal.ofReal h :=
      ENNReal.div_le_div_right (volume_addCircle_interval_le a b) _
    _ = ENNReal.ofReal (min h (b - a) / h) := (ENNReal.ofReal_div_of_pos hh).symm
    _ = _ := by rw [← min_div_div_right hh.le, div_self hh.ne']

end CircleDomainRigidity.FiniteTransfer

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Transfer_GridSummability
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Vanishing terminal-count bounds for finite transfer

In the Koebe manuscript's finite-transfer estimate `eq:transfer-terminal-mean`,
the scaled expected terminal count is bounded by a finite-cardinality
term and finitely many series of clipped oscillation products.
Square-summability of the oscillations makes these products summable,
and dominated convergence makes the bound tend to zero as the grid
spacing tends to zero through positive values.
-/

open Filter
open scoped Topology

namespace CircleDomainRigidity.FiniteTransfer

/-- Clipping two nonnegative oscillations at a nonnegative grid spacing
preserves the summable mixed-product majorant. -/
theorem min_mul_min_norm_le {ι : Type*} {a b : ι → ℝ} {h : ℝ}
    (ha : ∀ s, 0 ≤ a s) (hb : ∀ s, 0 ≤ b s) (hh : 0 ≤ h) (s : ι) :
    ‖min h (a s) * min h (b s)‖ ≤ a s * b s := by
  rw [Real.norm_eq_abs, abs_of_nonneg
    (mul_nonneg (le_min hh (ha s)) (le_min hh (hb s)))]
  exact mul_le_mul (min_le_right _ _) (min_le_right _ _)
    (le_min hh (hb s)) (ha s)

/-- Each clipped-product series is summable at every nonnegative spacing. -/
theorem summable_min_mul_min {ι : Type*} {a b : ι → ℝ} {h : ℝ}
    (ha : ∀ s, 0 ≤ a s) (hb : ∀ s, 0 ≤ b s)
    (ha2 : Summable (fun s => a s ^ 2)) (hb2 : Summable (fun s => b s ^ 2))
    (hh : 0 ≤ h) : Summable (fun s => min h (a s) * min h (b s)) :=
  (LengthArea.summable_mul_of_squares ha2 hb2).of_norm_bounded
    (min_mul_min_norm_le ha hb hh)

/-- Dominated convergence for the clipped oscillation products in the
terminal-count estimate. -/
theorem tendsto_tsum_min_mul_min_zero {ι : Type*} {a b : ι → ℝ}
    (ha : ∀ s, 0 ≤ a s) (hb : ∀ s, 0 ≤ b s)
    (ha2 : Summable (fun s => a s ^ 2)) (hb2 : Summable (fun s => b s ^ 2)) :
    Tendsto (fun h : ℝ => ∑' s, min h (a s) * min h (b s))
      (𝓝[>] 0) (𝓝 0) := by
  have hid : Tendsto (fun h : ℝ => h) (𝓝[>] 0) (𝓝 0) :=
    tendsto_id.mono_left nhdsWithin_le_nhds
  have hpoint : ∀ s, Tendsto (fun h : ℝ => min h (a s) * min h (b s))
      (𝓝[>] 0) (𝓝 (0 : ℝ)) := by
    intro s
    have hmina : Tendsto (fun h : ℝ => min h (a s)) (𝓝[>] 0) (𝓝 (min 0 (a s))) :=
      hid.min tendsto_const_nhds
    have hminb : Tendsto (fun h : ℝ => min h (b s)) (𝓝[>] 0) (𝓝 (min 0 (b s))) :=
      hid.min tendsto_const_nhds
    simpa only [min_eq_left (ha s), min_eq_left (hb s), zero_mul] using
      hmina.mul hminb
  have hpos : ∀ᶠ h : ℝ in 𝓝[>] 0, 0 < h := self_mem_nhdsWithin
  have hbound : ∀ᶠ h : ℝ in 𝓝[>] 0, ∀ s,
      ‖min h (a s) * min h (b s)‖ ≤ a s * b s := by
    filter_upwards [hpos] with h hh
    exact min_mul_min_norm_le ha hb hh.le
  simpa only [tsum_zero] using tendsto_tsum_of_dominated_convergence
    (LengthArea.summable_mul_of_squares ha2 hb2) hpoint hbound

end CircleDomainRigidity.FiniteTransfer

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Transfer_GridCollisions
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonEmbeddedArc.Arc.graphVertices_finite _root_.OAI.CannonMobius.sphereMetric _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Finite terminal flags from actual independent grid shifts

For two different coordinate labels, their lattice-hit events have
product probability. Countably many flagged points and finitely many
label pairs can therefore be counted by Tonelli. Square-summable band
widths imply a finite expected collision count, hence only finitely many
flagged collisions for almost every choice of the grids.
-/

open Set MeasureTheory Function
open scoped ENNReal

namespace CircleDomainRigidity.FiniteTransfer

theorem measurableSet_pairedLatticeIncidence {n : ℕ} {h : ℝ} (hh : 0 < h)
    (a b c d : ℝ) (i j : Fin n) :
    MeasurableSet (pairedLatticeIncidence h a b c d i j) :=
  ((measurableSet_latticeBandIncidence hh a b).preimage (measurable_pi_apply i)).inter
    ((measurableSet_latticeBandIncidence hh c d).preimage (measurable_pi_apply j))

theorem measure_pairedLatticeIncidence_le {n : ℕ} {h : ℝ} (hh : 0 < h)
    (a b c d : ℝ) {i j : Fin n} (hij : i ≠ j) :
    (Measure.pi (fun _ : Fin n => shiftLaw h)) (pairedLatticeIncidence h a b c d i j) ≤
      ENNReal.ofReal (min 1 ((b - a) / h)) * ENNReal.ofReal (min 1 ((d - c) / h)) := by
  let := shiftLaw_isProbabilityMeasure hh
  have hprod := (measurePreserving_grid_pair (shiftLaw h) hij).measure_preimage
    (((measurableSet_latticeBandIncidence hh a b).prod
      (measurableSet_latticeBandIncidence hh c d)).nullMeasurableSet)
  change (Measure.pi (fun _ : Fin n => shiftLaw h))
    (pairedLatticeIncidence h a b c d i j) = _ at hprod
  rw [hprod, Measure.prod_prod]
  exact mul_le_mul' (shiftLaw_latticeBandIncidence_le hh a b)
    (shiftLaw_latticeBandIncidence_le hh c d)

/-- Exact pair laws and Tonelli yield the expected collision bound. -/
theorem lintegral_gridCollisionCount_le {n : ℕ} {P S : Type*}
    [Fintype P] [Countable S] {h : ℝ} (hh : 0 < h)
    (pairs : P → Fin n × Fin n) (hpairs : ∀ p, (pairs p).1 ≠ (pairs p).2)
    (a b : Fin n → S → ℝ) :
    (∫⁻ θ, gridCollisionCount h pairs a b θ
      ∂Measure.pi (fun _ : Fin n => shiftLaw h)) ≤
      ∑ p, ∑' s, ENNReal.ofReal (min 1 ((b (pairs p).1 s - a (pairs p).1 s) / h)) *
        ENNReal.ofReal (min 1 ((b (pairs p).2 s - a (pairs p).2 s) / h)) := by
  unfold gridCollisionCount
  rw [lintegral_weightedBandIncidence]
  · simp only [ENNReal.ofReal_one, one_mul]
    rw [ENNReal.tsum_prod', tsum_fintype]
    exact Finset.sum_le_sum (fun p _ => ENNReal.tsum_le_tsum fun s =>
      measure_pairedLatticeIncidence_le hh _ _ _ _ (hpairs p))
  · intro ps
    exact measurableSet_pairedLatticeIncidence hh _ _ _ _ _ _

/-- The product majorant for two square-summable band widths is
summable at every positive grid spacing. -/
theorem summable_grid_pair_probabilities {S : Type*} {h : ℝ} (hh : 0 < h)
    (a b : S → ℝ) (ha : ∀ s, 0 ≤ a s) (hb : ∀ s, 0 ≤ b s)
    (ha2 : Summable (fun s => a s ^ 2)) (hb2 : Summable (fun s => b s ^ 2)) :
    Summable (fun s => min 1 (a s / h) * min 1 (b s / h)) := by
  have hs := (LengthArea.summable_mul_of_squares ha2 hb2).div_const (h * h)
  apply hs.of_norm_bounded
  intro s
  have hma : 0 ≤ min 1 (a s / h) := le_min zero_le_one (div_nonneg (ha s) hh.le)
  have hmb : 0 ≤ min 1 (b s / h) := le_min zero_le_one (div_nonneg (hb s) hh.le)
  rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg hma hmb)]
  calc
    _ ≤ (a s / h) * (b s / h) :=
      mul_le_mul (min_le_right _ _) (min_le_right _ _) hmb (div_nonneg (ha s) hh.le)
    _ = (a s * b s) / (h * h) := by ring

theorem tsum_grid_pair_probabilities_lt_top {S : Type*} {h : ℝ} (hh : 0 < h)
    (a b : S → ℝ) (ha : ∀ s, 0 ≤ a s) (hb : ∀ s, 0 ≤ b s)
    (ha2 : Summable (fun s => a s ^ 2)) (hb2 : Summable (fun s => b s ^ 2)) :
    (∑' s, ENNReal.ofReal (min 1 (a s / h)) * ENNReal.ofReal (min 1 (b s / h))) < ∞ := by
  have hnonneg (s) : 0 ≤ min 1 (a s / h) * min 1 (b s / h) :=
    mul_nonneg (le_min zero_le_one (div_nonneg (ha s) hh.le))
      (le_min zero_le_one (div_nonneg (hb s) hh.le))
  have heq : (∑' s, ENNReal.ofReal (min 1 (a s / h)) *
      ENNReal.ofReal (min 1 (b s / h))) =
      ENNReal.ofReal (∑' s, min 1 (a s / h) * min 1 (b s / h)) := by
    rw [ENNReal.ofReal_tsum_of_nonneg hnonneg
      (summable_grid_pair_probabilities hh a b ha hb ha2 hb2)]
    apply tsum_congr
    intro s
    exact (ENNReal.ofReal_mul (le_min zero_le_one (div_nonneg (ha s) hh.le))).symm
  rw [heq]
  exact ENNReal.ofReal_lt_top

/-- Square-summable band widths make the actual expected collision
count finite, rather than merely a formal upper bound. -/
theorem lintegral_gridCollisionCount_lt_top {n : ℕ} {P S : Type*}
    [Fintype P] [Countable S] {h : ℝ} (hh : 0 < h)
    (pairs : P → Fin n × Fin n) (hpairs : ∀ p, (pairs p).1 ≠ (pairs p).2)
    (a b : Fin n → S → ℝ)
    (hwidth : ∀ i s, 0 ≤ b i s - a i s)
    (hwidth2 : ∀ i, Summable (fun s => (b i s - a i s) ^ 2)) :
    (∫⁻ θ, gridCollisionCount h pairs a b θ
      ∂Measure.pi (fun _ : Fin n => shiftLaw h)) < ∞ := by
  apply (lintegral_gridCollisionCount_le hh pairs hpairs a b).trans_lt
  apply ENNReal.sum_lt_top.mpr
  intro p _
  exact tsum_grid_pair_probabilities_lt_top hh
    (fun s => b (pairs p).1 s - a (pairs p).1 s)
    (fun s => b (pairs p).2 s - a (pairs p).2 s)
    (hwidth (pairs p).1) (hwidth (pairs p).2)
    (hwidth2 (pairs p).1) (hwidth2 (pairs p).2)

end CircleDomainRigidity.FiniteTransfer

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Transfer_GridCollisionEstimate
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonEmbeddedArc.Arc.graphVertices_finite _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Vanishing scaled expectation for the actual collision count

The probability estimates are multiplied by the square of the grid spacing.
This turns the normalized band probabilities into the clipped products
`min h a * min h b`, dominated by summable oscillation products.
Thus the actual random count, with its spacing-dependent law, satisfies the
small-expectation premise of the reciprocal-grid selection theorem.
-/

open Set MeasureTheory Filter
open scoped Topology ENNReal

namespace CircleDomainRigidity.FiniteTransfer

theorem scaled_pair_probability_eq {h a b : ℝ} (hh : 0 < h) :
    h ^ 2 * (min 1 (a / h) * min 1 (b / h)) = min h a * min h b := by
  have ha : min 1 (a / h) = min h a / h := by
    rw [← min_div_div_right hh.le, div_self hh.ne']
  have hb : min 1 (b / h) = min h b / h := by
    rw [← min_div_div_right hh.le, div_self hh.ne']
  rw [ha, hb]
  field_simp

theorem scaled_lintegral_gridCollisionCount_le {n : ℕ} {P S : Type*}
    [Fintype P] [Countable S] {h : ℝ} (hh : 0 < h)
    (pairs : P → Fin n × Fin n) (hpairs : ∀ p, (pairs p).1 ≠ (pairs p).2)
    (a b : Fin n → S → ℝ)
    (hwidth : ∀ i s, 0 ≤ b i s - a i s)
    (hwidth2 : ∀ i, Summable (fun s => (b i s - a i s) ^ 2)) :
    ENNReal.ofReal (h ^ 2) *
      (∫⁻ θ, gridCollisionCount h pairs a b θ
        ∂Measure.pi (fun _ : Fin n => shiftLaw h)) ≤
      ENNReal.ofReal (∑ p, ∑' s,
        min h (b (pairs p).1 s - a (pairs p).1 s) *
          min h (b (pairs p).2 s - a (pairs p).2 s)) := by
  have hterm (p : P) (s : S) :
      ENNReal.ofReal (h ^ 2) *
        (ENNReal.ofReal (min 1 ((b (pairs p).1 s - a (pairs p).1 s) / h)) *
          ENNReal.ofReal (min 1 ((b (pairs p).2 s - a (pairs p).2 s) / h))) =
      ENNReal.ofReal (min h (b (pairs p).1 s - a (pairs p).1 s) *
        min h (b (pairs p).2 s - a (pairs p).2 s)) := by
    rw [← ENNReal.ofReal_mul (le_min zero_le_one
      (div_nonneg (hwidth (pairs p).1 s) hh.le)),
      ← ENNReal.ofReal_mul (sq_nonneg h), scaled_pair_probability_eq hh]
  calc
    _ ≤ ENNReal.ofReal (h ^ 2) *
        (∑ p, ∑' s, ENNReal.ofReal (min 1 ((b (pairs p).1 s - a (pairs p).1 s) / h)) *
          ENNReal.ofReal (min 1 ((b (pairs p).2 s - a (pairs p).2 s) / h))) :=
      mul_le_mul_right (lintegral_gridCollisionCount_le hh pairs hpairs a b) _
    _ = ∑ p, ∑' s, ENNReal.ofReal
        (min h (b (pairs p).1 s - a (pairs p).1 s) *
          min h (b (pairs p).2 s - a (pairs p).2 s)) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro p _
      rw [← ENNReal.tsum_mul_left]
      exact tsum_congr (hterm p)
    _ = _ := by
      rw [ENNReal.ofReal_sum_of_nonneg]
      · apply Finset.sum_congr rfl
        intro p _
        exact (ENNReal.ofReal_tsum_of_nonneg
          (fun s => mul_nonneg (le_min hh.le (hwidth (pairs p).1 s))
            (le_min hh.le (hwidth (pairs p).2 s)))
          (summable_min_mul_min (hwidth (pairs p).1) (hwidth (pairs p).2)
            (hwidth2 (pairs p).1) (hwidth2 (pairs p).2) hh.le)).symm
      · intro p _
        exact tsum_nonneg (fun s => mul_nonneg (le_min hh.le (hwidth (pairs p).1 s))
          (le_min hh.le (hwidth (pairs p).2 s)))

/-- The actual count is integrable, and its ordinary expected value
satisfies the paper's scaled clipped-product estimate. -/
theorem scaled_integral_gridCollisionCount_le {n : ℕ} {P S : Type*}
    [Fintype P] [Countable S] {h : ℝ} (hh : 0 < h)
    (pairs : P → Fin n × Fin n) (hpairs : ∀ p, (pairs p).1 ≠ (pairs p).2)
    (a b : Fin n → S → ℝ)
    (hwidth : ∀ i s, 0 ≤ b i s - a i s)
    (hwidth2 : ∀ i, Summable (fun s => (b i s - a i s) ^ 2)) :
    Integrable (fun θ => (gridCollisionCount h pairs a b θ).toReal)
      (Measure.pi (fun _ : Fin n => shiftLaw h)) ∧
    h ^ 2 * (∫ θ, (gridCollisionCount h pairs a b θ).toReal
      ∂Measure.pi (fun _ : Fin n => shiftLaw h)) ≤
      ∑ p, ∑' s, min h (b (pairs p).1 s - a (pairs p).1 s) *
        min h (b (pairs p).2 s - a (pairs p).2 s) := by
  have hmeas : Measurable (gridCollisionCount h pairs a b) :=
    measurable_weightedBandIncidence _ _ (fun ps =>
      measurableSet_pairedLatticeIncidence hh _ _ _ _ _ _)
  have hfinite := lintegral_gridCollisionCount_lt_top hh pairs hpairs a b hwidth hwidth2
  refine ⟨integrable_toReal_of_lintegral_ne_top hmeas.aemeasurable hfinite.ne, ?_⟩
  rw [integral_toReal hmeas.aemeasurable (ae_lt_top hmeas hfinite.ne)]
  have hb := ENNReal.toReal_mono ENNReal.ofReal_ne_top
    (scaled_lintegral_gridCollisionCount_le hh pairs hpairs a b hwidth hwidth2)
  rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal (sq_nonneg h),
    ENNReal.toReal_ofReal] at hb
  · exact hb
  · exact Finset.sum_nonneg (fun p _ => tsum_nonneg (fun s =>
      mul_nonneg (le_min hh.le (hwidth (pairs p).1 s))
        (le_min hh.le (hwidth (pairs p).2 s))))

/-- The scaled collision expectation tends to zero along the exact
reciprocal-integer grids and their actual independent shift laws. -/
theorem scaled_gridCollisionCount_mean_tendsto_zero {n : ℕ} {P S : Type*}
    [Fintype P] [Countable S]
    (pairs : P → Fin n × Fin n) (hpairs : ∀ p, (pairs p).1 ≠ (pairs p).2)
    (a b : Fin n → S → ℝ)
    (hwidth : ∀ i s, 0 ≤ b i s - a i s)
    (hwidth2 : ∀ i, Summable (fun s => (b i s - a i s) ^ 2)) :
    Tendsto (fun N => reciprocalGridStep N ^ 2 *
      (∫ θ, (gridCollisionCount (reciprocalGridStep N) pairs a b θ).toReal
        ∂reciprocalGridLaw n N)) atTop (𝓝 0) := by
  have hstep : Tendsto reciprocalGridStep atTop (𝓝[>] 0) :=
    tendsto_nhdsWithin_iff.mpr ⟨reciprocalGridStep_tendsto_zero,
      Eventually.of_forall reciprocalGridStep_pos⟩
  have hboundlim : Tendsto (fun N => ∑ p, ∑' s,
      min (reciprocalGridStep N) (b (pairs p).1 s - a (pairs p).1 s) *
        min (reciprocalGridStep N) (b (pairs p).2 s - a (pairs p).2 s))
      atTop (𝓝 0) := by
    simpa only [Finset.sum_const_zero, Function.comp_apply] using
      tendsto_finsetSum Finset.univ (fun p _ =>
        (tendsto_tsum_min_mul_min_zero (hwidth (pairs p).1) (hwidth (pairs p).2)
          (hwidth2 (pairs p).1) (hwidth2 (pairs p).2)).comp hstep)
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hboundlim
  · intro N
    exact mul_nonneg (sq_nonneg _) (integral_nonneg (fun _ => ENNReal.toReal_nonneg))
  · intro N
    exact (scaled_integral_gridCollisionCount_le (reciprocalGridStep_pos N)
      pairs hpairs a b hwidth hwidth2).2

end CircleDomainRigidity.FiniteTransfer

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Probability_FatouSelection
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonMobius.sphereMetric _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# One compatible sample with arbitrarily late good widths

The grid shifts must be fixed before the staircase width is chosen.
Fatou's lemma preserves a strict expected-cost budget along a sequence
of widths, and yields infinitely many good widths for one fixed sample.
-/

open MeasureTheory Filter
open scoped ENNReal

namespace CircleDomainRigidity.FiniteTransfer

theorem exists_compatible_frequently_small_cost
    {X : Type*} [MeasurableSpace X] {μ : Measure X} [IsProbabilityMeasure μ]
    (F : ℕ → X → ℝ≥0∞) (hF : ∀ n, AEMeasurable (F n) μ)
    {P : X → Prop} (hP : ∀ᵐ x ∂μ, P x) {c : ℝ≥0∞} (hc : c < 1)
    (hmean : ∀ n, (∫⁻ x, F n x ∂μ) ≤ c) :
    ∃ x, P x ∧ ∃ᶠ n in atTop, F n x < 1 := by
  have hlim : (∫⁻ x, liminf (fun n => F n x) atTop ∂μ) ≤ c := by
    apply (lintegral_liminf_le' hF).trans
    exact liminf_le_of_frequently_le' (Frequently.of_forall hmean)
  have hgood : ∃ x, P x ∧ liminf (fun n => F n x) atTop < 1 := by
    by_contra hno
    push Not at hno
    have hpoint : ∀ᵐ x ∂μ, (1 : ℝ≥0∞) ≤ liminf (fun n => F n x) atTop :=
      hP.mono (fun x hx => hno x hx)
    have hge := lintegral_mono_ae hpoint
    have hge' : (1 : ℝ≥0∞) ≤ ∫⁻ x, liminf (fun n => F n x) atTop ∂μ := by
      simpa using hge
    exact (not_lt_of_ge (hge'.trans hlim)) hc
  obtain ⟨x, hx, hsmall⟩ := hgood
  exact ⟨x, hx, frequently_lt_of_liminf_lt (by isBoundedDefault) hsmall⟩

/-- The second cost is independent of the width, so the same sample
has a small terminal cost and arbitrarily late small wedge costs. -/
theorem exists_compatible_frequently_small_pair
    {X : Type*} [MeasurableSpace X] {μ : Measure X} [IsProbabilityMeasure μ]
    (W : ℕ → X → ℝ≥0∞) (J : X → ℝ≥0∞)
    (hW : ∀ n, AEMeasurable (W n) μ) (hJ : AEMeasurable J μ)
    {P : X → Prop} (hP : ∀ᵐ x ∂μ, P x) {c : ℝ≥0∞} (hc : c < 1)
    (hmean : ∀ n, (∫⁻ x, W n x + J x ∂μ) ≤ c) :
    ∃ x, P x ∧ J x < 1 ∧ ∃ᶠ n in atTop, W n x < 1 := by
  obtain ⟨x, hx, hgood⟩ := exists_compatible_frequently_small_cost
    (fun n x => W n x + J x) (fun n => (hW n).add hJ) hP hc hmean
  obtain ⟨n, hn⟩ := hgood.exists
  refine ⟨x, hx, (le_add_left le_rfl).trans_lt hn, ?_⟩
  exact hgood.mono (fun n hn => (le_add_right le_rfl).trans_lt hn)

end CircleDomainRigidity.FiniteTransfer

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Transfer_GridWidthSelection
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonMobius.sphereMetric _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Fixing grid shifts before the staircase width

The wedge costs depend on a sequence of widths, whereas the terminal
cost depends only on the grid shifts. Fatou selection provides one
compatible choice of shifts with small terminal cost and arbitrarily
late small wedge costs. Thus subsequent collar conditions may impose
any finite lower bound on the width-sequence index.
-/

open Set MeasureTheory Filter
open scoped Topology ENNReal

namespace CircleDomainRigidity.FiniteTransfer

/-- The real-valued version of the Fatou selection estimate, with the
two costs normalized by their actual thresholds. -/
theorem exists_compatible_frequently_small_real_pair
    {X : Type*} [MeasurableSpace X] {μ : Measure X} [IsProbabilityMeasure μ]
    (W : ℕ → X → ℝ) (J : X → ℝ) {P : X → Prop} {A B : ℝ}
    (hA : 0 < A) (hB : 0 < B)
    (hWi : ∀ k, Integrable (W k) μ) (hJi : Integrable J μ)
    (hW0 : ∀ k, ∀ᵐ x ∂μ, 0 ≤ W k x) (hJ0 : ∀ᵐ x ∂μ, 0 ≤ J x)
    (hP : ∀ᵐ x ∂μ, P x)
    (hWmean : ∀ k, (∫ x, W k x ∂μ) < A / 4)
    (hJmean : (∫ x, J x ∂μ) < B / 4) :
    ∃ x, P x ∧ J x < B ∧ ∃ᶠ k in atTop, W k x < A := by
  let U : ℕ → X → ℝ≥0∞ := fun k x => ENNReal.ofReal (W k x / A)
  let V : X → ℝ≥0∞ := fun x => ENNReal.ofReal (J x / B)
  have hU k : AEMeasurable (U k) μ :=
    ((hWi k).div_const A).aestronglyMeasurable.aemeasurable.ennreal_ofReal
  have hV : AEMeasurable V μ :=
    (hJi.div_const B).aestronglyMeasurable.aemeasurable.ennreal_ofReal
  have hmean k : (∫⁻ x, U k x + V x ∂μ) ≤ ENNReal.ofReal (1 / 2 : ℝ) := by
    rw [lintegral_add_left' (hU k)]
    have hWu : (∫⁻ x, U k x ∂μ) = ENNReal.ofReal ((∫ x, W k x ∂μ) / A) := by
      dsimp [U]
      rw [← ofReal_integral_eq_lintegral_ofReal ((hWi k).div_const A)
        ((hW0 k).mono (fun _ hx => div_nonneg hx hA.le)), integral_div]
    have hJv : (∫⁻ x, V x ∂μ) = ENNReal.ofReal ((∫ x, J x ∂μ) / B) := by
      dsimp [V]
      rw [← ofReal_integral_eq_lintegral_ofReal (hJi.div_const B)
        (hJ0.mono (fun _ hx => div_nonneg hx hB.le)), integral_div]
    rw [hWu, hJv, ← ENNReal.ofReal_add
      (div_nonneg (integral_nonneg_of_ae (hW0 k)) hA.le)
      (div_nonneg (integral_nonneg_of_ae hJ0) hB.le)]
    apply ENNReal.ofReal_le_ofReal
    have hWlt : (∫ x, W k x ∂μ) / A < 1 / 4 :=
      (div_lt_iff₀ hA).mpr (by linarith [hWmean k])
    have hJlt : (∫ x, J x ∂μ) / B < 1 / 4 :=
      (div_lt_iff₀ hB).mpr (by linarith [hJmean])
    linarith
  obtain ⟨x, hxP, hxJ, hxW⟩ := exists_compatible_frequently_small_pair U V hU hV hP
    (ENNReal.ofReal_lt_one.mpr (by norm_num : (1 / 2 : ℝ) < 1)) hmean
  refine ⟨x, hxP, ?_, ?_⟩
  · exact (div_lt_one hB).mp (ENNReal.ofReal_lt_one.mp hxJ)
  · exact hxW.mono (fun k hk => (div_lt_one hA).mp (ENNReal.ofReal_lt_one.mp hk))

/-- Simultaneous choice of reciprocal grid spacing and fixed shifts,
retaining any conull compatibility event and arbitrarily late good
width indices. The terminal cost includes all compulsory indices. -/
theorem exists_reciprocal_grid_with_frequently_small_widths {n : ℕ}
    (W : ℕ → ℕ → (Fin n → ℝ) → ℝ) (J : ℕ → (Fin n → ℝ) → ℝ)
    (P : ℕ → (Fin n → ℝ) → Prop) {η δ : ℝ} (hη : 0 < η) (hδ : 0 < δ)
    (hWi : ∀ N k, Integrable (W N k) (reciprocalGridLaw n N))
    (hJi : ∀ N, Integrable (J N) (reciprocalGridLaw n N))
    (hW0 : ∀ N k, ∀ᵐ θ ∂reciprocalGridLaw n N, 0 ≤ W N k θ)
    (hJ0 : ∀ N, ∀ᵐ θ ∂reciprocalGridLaw n N, 0 ≤ J N θ)
    (hP : ∀ N, ∀ᵐ θ ∂reciprocalGridLaw n N, P N θ)
    (hWmean : ∀ᶠ N in atTop, ∀ k,
      (∫ θ, W N k θ ∂reciprocalGridLaw n N) < η / 4)
    (hJmean : Tendsto
      (fun N => reciprocalGridStep N ^ 2 * (∫ θ, J N θ ∂reciprocalGridLaw n N))
      atTop (𝓝 0)) :
    ∃ (N : ℕ) (θ : Fin n → ℝ), reciprocalGridStep N < δ ∧ P N θ ∧
      reciprocalGridStep N * Real.sqrt (J N θ) < η ∧
      ∃ᶠ k in atTop, W N k θ < η := by
  have hsmall : ∀ᶠ N in atTop,
      reciprocalGridStep N < δ ∧
      (∀ k, (∫ θ, W N k θ ∂reciprocalGridLaw n N) < η / 4) ∧
      reciprocalGridStep N ^ 2 * (∫ θ, J N θ ∂reciprocalGridLaw n N) < η ^ 2 / 4 := by
    filter_upwards [reciprocalGridStep_tendsto_zero.eventually_lt_const hδ, hWmean,
      hJmean.eventually_lt_const (by positivity : 0 < η ^ 2 / 4)] with N hN hW hJ
    exact ⟨hN, hW, hJ⟩
  obtain ⟨N, hN, hW, hJ⟩ := hsmall.exists
  let := reciprocalGridLaw_isProbabilityMeasure n N
  let C : (Fin n → ℝ) → ℝ := fun θ => reciprocalGridStep N ^ 2 * J N θ
  have hCi : Integrable C (reciprocalGridLaw n N) := (hJi N).const_mul _
  have hC0 : ∀ᵐ θ ∂reciprocalGridLaw n N, 0 ≤ C θ :=
    (hJ0 N).mono (fun _ hx => mul_nonneg (sq_nonneg _) hx)
  have hCmean : (∫ θ, C θ ∂reciprocalGridLaw n N) < η ^ 2 / 4 := by
    simpa only [C, integral_const_mul] using hJ
  obtain ⟨θ, hθ, hθC, hθW⟩ := exists_compatible_frequently_small_real_pair
    (W N) C hη (sq_pos_of_pos hη) (hWi N) hCi (hW0 N) hC0
    ((hP N).and (hJ0 N)) hW hCmean
  refine ⟨N, θ, hN, hθ.1, ?_, hθW⟩
  have hsquare : (reciprocalGridStep N * Real.sqrt (J N θ)) ^ 2 < η ^ 2 := by
    rwa [mul_pow, Real.sq_sqrt hθ.2]
  exact (sq_lt_sq₀
    (mul_nonneg (reciprocalGridStep_pos N).le (Real.sqrt_nonneg _)) hη.le).mp hsquare

end CircleDomainRigidity.FiniteTransfer

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Selection_TerminalCounts
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonEmbeddedArc.Arc.graphVertices_finite _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Actual terminal indices and their counting cost

Terminals consist of prescribed points together with points flagged by
two distinct grids. Their cardinality is bounded by the prescribed
cardinality plus the number of pair/flag incidences. This upper counting
cost is integrable and its expectation, scaled by the square of the
spacing, tends to zero for the actual reciprocal-grid laws.
-/

open Set MeasureTheory Filter
open scoped Topology ENNReal

namespace CircleDomainRigidity.FiniteTransfer

theorem finite_active_of_weighted_count_ne_top {T I : Type*}
    (E : I → Set T) (t : T)
    (hfinite : weightedBandIncidence E (fun _ => 1) t ≠ ∞) :
    {i | t ∈ E i}.Finite := by
  have hf := ENNReal.finite_const_le_of_tsum_ne_top hfinite
    (by norm_num : (1 : ℝ≥0∞) ≠ 0)
  apply hf.subset
  intro i hi
  have hi' : t ∈ E i := hi
  change 1 ≤ (E i).indicator (fun _ => ENNReal.ofReal 1) t
  rw [indicator_of_mem hi', ENNReal.ofReal_one]

theorem weighted_count_toReal_eq_ncard {T I : Type*}
    (E : I → Set T) (t : T) (hfinite : {i | t ∈ E i}.Finite) :
    (weightedBandIncidence E (fun _ => 1) t).toReal = ({i | t ∈ E i}.ncard : ℝ) := by
  classical
  rw [weightedBandIncidence_toReal_eq E (fun _ => 1) (fun _ => zero_le_one),
    tsum_eq_sum (s := hfinite.toFinset)]
  · rw [ncard_eq_toFinset_card _ hfinite]
    calc
      _ = ∑ _i ∈ hfinite.toFinset, (1 : ℝ) := by
        apply Finset.sum_congr rfl
        intro i hi
        exact indicator_of_mem (show t ∈ E i from hfinite.mem_toFinset.mp hi) _
      _ = _ := by simp
  · intro i hi
    exact indicator_of_notMem (s := E i)
      (fun h => hi (hfinite.mem_toFinset.mpr h)) _

/-- Counting pair/point incidences only overcounts the actual terminal
indices, including the prescribed finite set. -/
theorem finite_gridTerminalIndices_and_card_le {n : ℕ} {P S : Type*}
    (F : Set S) (hF : F.Finite) (h : ℝ)
    (pairs : P → Fin n × Fin n) (a b : Fin n → S → ℝ) (θ : Fin n → ℝ)
    (hfinite : gridCollisionCount h pairs a b θ ≠ ∞) :
    (gridTerminalIndices F h pairs a b θ).Finite ∧
      ((gridTerminalIndices F h pairs a b θ).ncard : ℝ) ≤
        gridTerminalCost F h pairs a b θ := by
  let E : P × S → Set (Fin n → ℝ) := fun ps => pairedLatticeIncidence h
    (a (pairs ps.1).1 ps.2) (b (pairs ps.1).1 ps.2)
    (a (pairs ps.1).2 ps.2) (b (pairs ps.1).2 ps.2) (pairs ps.1).1 (pairs ps.1).2
  let A : Set (P × S) := {ps | θ ∈ E ps}
  have hA : A.Finite := finite_active_of_weighted_count_ne_top E θ hfinite
  have hset : gridTerminalIndices F h pairs a b θ = F ∪ Prod.snd '' A := by
    ext s
    simp only [gridTerminalIndices, mem_union, mem_ofPred_eq, mem_image, Prod.exists,
      A, E, exists_eq_right]
  refine ⟨hset ▸ hF.union (hA.image _), ?_⟩
  have hcount : (gridCollisionCount h pairs a b θ).toReal = (A.ncard : ℝ) :=
    weighted_count_toReal_eq_ncard E θ hA
  rw [gridTerminalCost, hcount, hset]
  exact_mod_cast (ncard_union_le F (Prod.snd '' A)).trans
    (Nat.add_le_add_left (ncard_image_le hA) F.ncard)

theorem integrable_gridTerminalCost {n : ℕ} {P S : Type*}
    [Fintype P] [Countable S] (F : Set S) {h : ℝ} (hh : 0 < h)
    (pairs : P → Fin n × Fin n) (hpairs : ∀ p, (pairs p).1 ≠ (pairs p).2)
    (a b : Fin n → S → ℝ) (hwidth : ∀ i s, 0 ≤ b i s - a i s)
    (hwidth2 : ∀ i, Summable (fun s => (b i s - a i s) ^ 2)) :
    Integrable (gridTerminalCost F h pairs a b)
      (Measure.pi (fun _ : Fin n => shiftLaw h)) := by
  let := shiftLaw_isProbabilityMeasure hh
  exact (integrable_const _).add
    (scaled_integral_gridCollisionCount_le hh pairs hpairs a b hwidth hwidth2).1

theorem gridTerminalCost_nonneg {n : ℕ} {P S : Type*} (F : Set S) (h : ℝ)
    (pairs : P → Fin n × Fin n) (a b : Fin n → S → ℝ) (θ : Fin n → ℝ) :
    0 ≤ gridTerminalCost F h pairs a b θ :=
  add_nonneg (Nat.cast_nonneg _) ENNReal.toReal_nonneg

/-- The finitely many prescribed terminals also have vanishing scaled
expected cost. The number of pair/flag incidences was handled by the
clipped-product summability estimate. -/
theorem scaled_gridTerminalCost_mean_tendsto_zero {n : ℕ} {P S : Type*}
    [Fintype P] [Countable S] (F : Set S)
    (pairs : P → Fin n × Fin n) (hpairs : ∀ p, (pairs p).1 ≠ (pairs p).2)
    (a b : Fin n → S → ℝ) (hwidth : ∀ i s, 0 ≤ b i s - a i s)
    (hwidth2 : ∀ i, Summable (fun s => (b i s - a i s) ^ 2)) :
    Tendsto (fun N => reciprocalGridStep N ^ 2 *
      (∫ θ, gridTerminalCost F (reciprocalGridStep N) pairs a b θ
        ∂reciprocalGridLaw n N)) atTop (𝓝 0) := by
  have hconst : Tendsto (fun N => reciprocalGridStep N ^ 2 * (F.ncard : ℝ))
      atTop (𝓝 0) := by
    simpa using (reciprocalGridStep_tendsto_zero.pow 2).mul_const (F.ncard : ℝ)
  have hsum := hconst.add
    (scaled_gridCollisionCount_mean_tendsto_zero pairs hpairs a b hwidth hwidth2)
  simp only [zero_add] at hsum
  convert hsum using 1
  all_goals try with_reducible_and_instances rfl
  funext N
  let := reciprocalGridLaw_isProbabilityMeasure n N
  have hi := (scaled_integral_gridCollisionCount_le (reciprocalGridStep_pos N)
    pairs hpairs a b hwidth hwidth2).1
  change Integrable (fun θ => (gridCollisionCount (reciprocalGridStep N) pairs a b θ).toReal)
    (reciprocalGridLaw n N) at hi
  dsimp only [gridTerminalCost]
  rw [integral_add (integrable_const _) hi, integral_const,
    probReal_univ, one_smul, mul_add]

/-- Uniform wedge-mean bounds give spacing and shifts with a small terminal
counting cost for every sufficiently narrow staircase. -/
theorem exists_grid_with_finite_terminals_and_good_widths
    {n : ℕ} {P S : Type*} [Fintype P] [Countable S]
    (F : Set S) (hF : F.Finite)
    (pairs : P → Fin n × Fin n) (hpairs : ∀ p, (pairs p).1 ≠ (pairs p).2)
    (a b : Fin n → S → ℝ) (hwidth : ∀ i s, 0 ≤ b i s - a i s)
    (hwidth2 : ∀ i, Summable (fun s => (b i s - a i s) ^ 2))
    (W : ℕ → ℕ → (Fin n → ℝ) → ℝ) (Q : ℕ → (Fin n → ℝ) → Prop)
    {η δ : ℝ} (hη : 0 < η) (hδ : 0 < δ)
    (hWi : ∀ N k, Integrable (W N k) (reciprocalGridLaw n N))
    (hW0 : ∀ N k, ∀ᵐ θ ∂reciprocalGridLaw n N, 0 ≤ W N k θ)
    (hQ : ∀ N, ∀ᵐ θ ∂reciprocalGridLaw n N, Q N θ)
    (hWmean : ∀ᶠ N in atTop, ∀ k,
      (∫ θ, W N k θ ∂reciprocalGridLaw n N) < η / 4) :
    ∃ (N : ℕ) (θ : Fin n → ℝ), reciprocalGridStep N < δ ∧ Q N θ ∧
      (gridTerminalIndices F (reciprocalGridStep N) pairs a b θ).Finite ∧
      reciprocalGridStep N *
        Real.sqrt ((gridTerminalIndices F (reciprocalGridStep N) pairs a b θ).ncard : ℝ) < η ∧
      ∃ᶠ k in atTop, W N k θ < η := by
  have hfinite N : ∀ᵐ θ ∂reciprocalGridLaw n N,
      gridCollisionCount (reciprocalGridStep N) pairs a b θ ≠ ∞ := by
    have hm : Measurable (gridCollisionCount (reciprocalGridStep N) pairs a b) :=
      measurable_weightedBandIncidence _ _ (fun _ =>
        measurableSet_pairedLatticeIncidence (reciprocalGridStep_pos N) _ _ _ _ _ _)
    exact (ae_lt_top hm (lintegral_gridCollisionCount_lt_top
      (reciprocalGridStep_pos N) pairs hpairs a b hwidth hwidth2).ne).mono
        (fun _ hx => hx.ne)
  obtain ⟨N, θ, hN, hθ, hJ, hW⟩ := exists_reciprocal_grid_with_frequently_small_widths
    W (fun N => gridTerminalCost F (reciprocalGridStep N) pairs a b)
    (fun N θ => Q N θ ∧ gridCollisionCount (reciprocalGridStep N) pairs a b θ ≠ ∞)
    hη hδ hWi
    (fun N => integrable_gridTerminalCost F (reciprocalGridStep_pos N)
      pairs hpairs a b hwidth hwidth2)
    hW0 (fun N => Filter.Eventually.of_forall (gridTerminalCost_nonneg F _ pairs a b))
    (fun N => (hQ N).and (hfinite N)) hWmean
    (scaled_gridTerminalCost_mean_tendsto_zero F pairs hpairs a b hwidth hwidth2)
  obtain ⟨hterm, hcard⟩ := finite_gridTerminalIndices_and_card_le
    F hF _ pairs a b θ hθ.2
  exact ⟨N, θ, hN, hθ.1, hterm,
    (mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt hcard)
      (reciprocalGridStep_pos N).le).trans_lt hJ, hW⟩

end CircleDomainRigidity.FiniteTransfer

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Selection_ExpectedWedges
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonMobius.sphereMetric _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!+# Expected wedges for a finite family of actual random staircases

The product space has one uniform shift per coordinate. Distinct labels
have the two-shift law used in the analytic mean calculation.
-/

open MeasureTheory Set Finset

noncomputable section

namespace CircleDomainRigidity.FiniteTransfer

theorem continuous_staircaseCovector {h δ : ℝ}
    (hh : 0 < h) (hδ : 0 < δ) (hδh : δ < h / 4)
    (χ x : ℝ) (u c : ℝ × ℝ) :
    Continuous (fun θ => staircaseCovector h δ χ θ x u c) := by
  unfold staircaseCovector
  exact ((continuous_const.add
    (continuous_const.mul (continuous_shiftedStaircase_deriv hh hδ hδh x))).smul
    continuous_const).add
    (((continuous_shiftedStaircase_value hh hδ hδh x).sub continuous_const).smul
      continuous_const)

/-- Fubini turns the pointwise mean estimate into the spatial wedge
estimate. Joint integrability is exposed so this can be used both on
compact smooth pieces and on exhausted finite-energy regions. -/
theorem expected_integrated_grid_pair_wedge_le
    {X : Type*} [MeasurableSpace X] {μ : Measure X} [SFinite μ]
    {n : ℕ} {i j : Fin n} (hij : i ≠ j)
    (u v c : X → ℝ × ℝ) (x y χ : X → ℝ) {h δ : ℝ}
    (hh : 0 < h) (hδ : 0 < δ) (hδh : δ < h / 4)
    (hχ0 : ∀ z, 0 ≤ χ z) (hχ1 : ∀ z, χ z ≤ 1)
    (hjoint : Integrable (fun p : (ℝ × ℝ) × X =>
      |planarWedge
        (staircaseCovector h δ (χ p.2) p.1.1 (x p.2) (u p.2) (c p.2))
        (staircaseCovector h δ (χ p.2) p.1.2 (y p.2) (v p.2) (c p.2))|)
      (((shiftLaw h).prod (shiftLaw h)).prod μ))
    (hbound : Integrable (fun z => |planarWedge (u z) (v z)| +
      h * (|planarWedge (u z) (c z)| + |planarWedge (c z) (v z)|)) μ) :
    (∫ θ, (∫ z, |planarWedge
      (staircaseCovector h δ (χ z) (θ i) (x z) (u z) (c z))
      (staircaseCovector h δ (χ z) (θ j) (y z) (v z) (c z))| ∂μ)
        ∂Measure.pi (fun _ : Fin n => shiftLaw h)) ≤
      ∫ z, |planarWedge (u z) (v z)| +
        h * (|planarWedge (u z) (c z)| + |planarWedge (c z) (v z)|) ∂μ := by
  let : IsProbabilityMeasure (shiftLaw h) := shiftLaw_isProbabilityMeasure hh
  let f : (ℝ × ℝ) → X → ℝ := fun θ z => |planarWedge
    (staircaseCovector h δ (χ z) θ.1 (x z) (u z) (c z))
    (staircaseCovector h δ (χ z) θ.2 (y z) (v z) (c z))|
  change (∫ θ, (∫ z, f (θ i, θ j) z ∂μ)
    ∂Measure.pi (fun _ : Fin n => shiftLaw h)) ≤ _
  rw [integral_grid_pair (shiftLaw h) hij (fun θ => ∫ z, f θ z ∂μ)
    hjoint.integral_prod_left.aestronglyMeasurable]
  rw [integral_integral_swap hjoint]
  apply integral_mono hjoint.integral_prod_right hbound
  intro z
  change (∫ θ, f θ z ∂(shiftLaw h).prod (shiftLaw h)) ≤
    |planarWedge (u z) (v z)| +
      h * (|planarWedge (u z) (c z)| + |planarWedge (c z) (v z)|)
  rw [integral_shiftLaw_pair]
  exact average_staircase_wedge_le (u z) (v z) (c z) (x z) (y z)
    hh hδ hδh (hχ0 z) (hχ1 z)

end CircleDomainRigidity.FiniteTransfer

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Sobolev_WedgeIntegrability
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonMobius.sphereMetric _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Joint integrability of the actual random wedge

Tonelli and the pointwise expected-wedge bound prove joint integrability.
Thus applying Fubini to the random staircase construction needs only
measurable input fields and the original integrable wedge majorant.
-/

open Set MeasureTheory
open scoped ENNReal

namespace CircleDomainRigidity.FiniteTransfer

/-- Finite squared norms of the original planar covectors make their
absolute wedge product integrable by Hölder's inequality. -/
theorem integrable_abs_planarWedge_of_memLp
    {X : Type*} [MeasurableSpace X] {μ : Measure X} {u v : X → ℝ × ℝ}
    (hu : MemLp u 2 μ) (hv : MemLp v 2 μ) :
    Integrable (fun z => |planarWedge (u z) (v z)|) μ := by
  have hu1 := (ContinuousLinearMap.fst ℝ ℝ ℝ).comp_memLp' hu
  have hu2 := (ContinuousLinearMap.snd ℝ ℝ ℝ).comp_memLp' hu
  have hv1 := (ContinuousLinearMap.fst ℝ ℝ ℝ).comp_memLp' hv
  have hv2 := (ContinuousLinearMap.snd ℝ ℝ ℝ).comp_memLp' hv
  have h12 : MemLp (fun z => (u z).1 * (v z).2) 1 μ := hv2.mul hu1
  have h21 : MemLp (fun z => (u z).2 * (v z).1) 1 μ := hv1.mul hu2
  exact ((memLp_one_iff_integrable.mp h12).sub (memLp_one_iff_integrable.mp h21)).abs

theorem integrable_nonnegative_prod_of_inner_bound
    {A B : Type*} [MeasurableSpace A] [MeasurableSpace B]
    {μ : Measure A} {ν : Measure B} [SFinite μ] [SFinite ν]
    {f : A × B → ℝ} (hf : AEStronglyMeasurable f (μ.prod ν))
    (h0 : ∀ p, 0 ≤ f p) (hi : ∀ y, Integrable (fun x => f (x, y)) μ)
    {b : B → ℝ} (hb : Integrable b ν)
    (hbound : ∀ y, (∫ x, f (x, y) ∂μ) ≤ b y) : Integrable f (μ.prod ν) := by
  refine ⟨hf, (hasFiniteIntegral_iff_ofReal (Filter.Eventually.of_forall h0)).mpr ?_⟩
  rw [lintegral_prod_symm _ hf.aemeasurable.ennreal_ofReal]
  have hb0 : ∀ y, 0 ≤ b y := fun y =>
    (integral_nonneg (fun x => h0 (x, y))).trans (hbound y)
  calc
    _ = ∫⁻ y, ENNReal.ofReal (∫ x, f (x, y) ∂μ) ∂ν := by
      apply lintegral_congr
      intro y
      exact (ofReal_integral_eq_lintegral_ofReal (hi y)
        (Filter.Eventually.of_forall (fun x => h0 (x, y)))).symm
    _ ≤ ∫⁻ y, ENNReal.ofReal (b y) ∂ν :=
      lintegral_mono (fun y => ENNReal.ofReal_le_ofReal (hbound y))
    _ < ∞ := (hasFiniteIntegral_iff_ofReal (Filter.Eventually.of_forall hb0)).mp hb.2

/-- Every continuous two-shift integrand is integrable for the actual
compactly supported product shift law. -/
theorem integrable_shiftLaw_pair_of_continuous {h : ℝ} (hh : 0 < h)
    {f : ℝ × ℝ → ℝ} (hf : Continuous f) :
    Integrable f ((shiftLaw h).prod (shiftLaw h)) := by
  rw [shiftLaw_eq, Measure.prod_smul_left, Measure.prod_smul_right,
    smul_smul, Measure.prod_restrict]
  exact (hf.continuousOn.integrableOn_compact (isCompact_Icc.prod isCompact_Icc)).smul_measure
    (ENNReal.mul_ne_top (ENNReal.inv_ne_top.mpr (ENNReal.ofReal_ne_zero_iff.mpr hh))
      (ENNReal.inv_ne_top.mpr (ENNReal.ofReal_ne_zero_iff.mpr hh)))

theorem measurable_staircaseCovector
    {Ω : Type*} [MeasurableSpace Ω] {h δ : ℝ}
    (hh : 0 < h) (hδ : 0 < δ) (hδh : δ < h / 4)
    {χ θ x : Ω → ℝ} {u c : Ω → ℝ × ℝ}
    (hχ : Measurable χ) (hθ : Measurable θ) (hx : Measurable x)
    (hu : Measurable u) (hc : Measurable c) :
    Measurable (fun ω => staircaseCovector h δ (χ ω) (θ ω) (x ω) (u ω) (c ω)) := by
  have hP := contDiff_smoothStaircase hh hδ hδh
  have hd : Measurable (deriv (smoothStaircase h δ)) :=
    (hP.continuous_deriv (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)).measurable
  have hv : Measurable (smoothStaircase h δ) := hP.continuous.measurable
  simp only [staircaseCovector, deriv_shiftedStaircase hh hδ hδh, shiftedStaircase]
  fun_prop

/-- Joint integrability follows from the original wedge and cutoff
terms; it is not assumed before interchanging the spatial and shift
integrals. -/
theorem integrable_staircase_pair_density
    {X : Type*} [MeasurableSpace X] {μ : Measure X} [SFinite μ]
    (u v c : X → ℝ × ℝ) (x y χ : X → ℝ)
    (hu : Measurable u) (hv : Measurable v) (hc : Measurable c)
    (hx : Measurable x) (hy : Measurable y) (hχ : Measurable χ)
    {h δ : ℝ} (hh : 0 < h) (hδ : 0 < δ) (hδh : δ < h / 4)
    (hχ0 : ∀ z, 0 ≤ χ z) (hχ1 : ∀ z, χ z ≤ 1)
    (hbound : Integrable (fun z => |planarWedge (u z) (v z)| +
      h * (|planarWedge (u z) (c z)| + |planarWedge (c z) (v z)|)) μ) :
    Integrable (fun p : (ℝ × ℝ) × X => |planarWedge
      (staircaseCovector h δ (χ p.2) p.1.1 (x p.2) (u p.2) (c p.2))
      (staircaseCovector h δ (χ p.2) p.1.2 (y p.2) (v p.2) (c p.2))|)
      (((shiftLaw h).prod (shiftLaw h)).prod μ) := by
  let := shiftLaw_isProbabilityMeasure hh
  let f : (ℝ × ℝ) × X → ℝ := fun p => |planarWedge
    (staircaseCovector h δ (χ p.2) p.1.1 (x p.2) (u p.2) (c p.2))
    (staircaseCovector h δ (χ p.2) p.1.2 (y p.2) (v p.2) (c p.2))|
  have hmu : Measurable (fun p : (ℝ × ℝ) × X =>
      staircaseCovector h δ (χ p.2) p.1.1 (x p.2) (u p.2) (c p.2)) :=
    measurable_staircaseCovector hh hδ hδh
    (hχ.comp measurable_snd) (measurable_fst.fst) (hx.comp measurable_snd)
    (hu.comp measurable_snd) (hc.comp measurable_snd)
  have hmv : Measurable (fun p : (ℝ × ℝ) × X =>
      staircaseCovector h δ (χ p.2) p.1.2 (y p.2) (v p.2) (c p.2)) :=
    measurable_staircaseCovector hh hδ hδh
    (hχ.comp measurable_snd) (measurable_fst.snd) (hy.comp measurable_snd)
    (hv.comp measurable_snd) (hc.comp measurable_snd)
  have hmf : Measurable f := ((hmu.fst.mul hmv.snd).sub (hmu.snd.mul hmv.fst)).abs
  refine integrable_nonnegative_prod_of_inner_bound hmf.aestronglyMeasurable
    (fun _ => abs_nonneg _) ?_ hbound ?_
  · intro z
    apply integrable_shiftLaw_pair_of_continuous hh
    exact (((continuous_staircaseCovector hh hδ hδh (χ z) (x z) (u z) (c z)).comp
      continuous_fst).fst.mul
      (((continuous_staircaseCovector hh hδ hδh (χ z) (y z) (v z) (c z)).comp
        continuous_snd).snd)).sub
        ((((continuous_staircaseCovector hh hδ hδh (χ z) (x z) (u z) (c z)).comp
          continuous_fst).snd).mul
          (((continuous_staircaseCovector hh hδ hδh (χ z) (y z) (v z) (c z)).comp
            continuous_snd).fst)) |>.abs
  · intro z
    rw [integral_shiftLaw_pair]
    simpa only [f, staircaseCovector] using
      average_staircase_wedge_le (u z) (v z) (c z) (x z) (y z)
      hh hδ hδh (hχ0 z) (hχ1 z)

end CircleDomainRigidity.FiniteTransfer

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Modulus_FiniteWedgeCosts
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# The complete finite-list random wedge cost

The actual spatial wedge integrals are integrable random variables.
Summing their independent-pair estimates gives a mean bound uniform in
the staircase width, with an error proportional to the grid spacing.
-/

open Set MeasureTheory Filter
open scoped Topology

namespace CircleDomainRigidity.FiniteTransfer

theorem staircaseWidth_pos {h : ℝ} (hh : 0 < h) (k : ℕ) :
    0 < staircaseWidth h k := mul_pos (by positivity) (reciprocalGridStep_pos k)

theorem staircaseWidth_lt {h : ℝ} (hh : 0 < h) (k : ℕ) :
    staircaseWidth h k < h / 4 := by
  have hle := mul_le_mul_of_nonneg_left (reciprocalGridStep_le_one k)
    (by positivity : 0 ≤ h / 8)
  dsimp only [staircaseWidth]
  nlinarith

theorem staircaseWidth_tendsto_zero (h : ℝ) :
    Tendsto (staircaseWidth h) atTop (𝓝 0) := by
  change Tendsto (fun k => h / 8 * reciprocalGridStep k) atTop (𝓝 0)
  simpa only [mul_zero] using reciprocalGridStep_tendsto_zero.const_mul (h / 8)

theorem integrable_staircasePairCost
    {X : Type*} [MeasurableSpace X] {μ : Measure X} [SFinite μ] {n : ℕ}
    (u : Fin n → X → ℝ × ℝ) (c : X → ℝ × ℝ) (x : Fin n → X → ℝ) (χ : X → ℝ)
    (hu : ∀ i, Measurable (u i)) (hc : Measurable c)
    (hx : ∀ i, Measurable (x i)) (hχ : Measurable χ)
    {h δ : ℝ} (hh : 0 < h) (hδ : 0 < δ) (hδh : δ < h / 4)
    (hχ0 : ∀ z, 0 ≤ χ z) (hχ1 : ∀ z, χ z ≤ 1)
    {i j : Fin n} (hij : i ≠ j)
    (hbound : Integrable (fun z => |planarWedge (u i z) (u j z)| +
      h * (|planarWedge (u i z) (c z)| + |planarWedge (c z) (u j z)|)) μ) :
    Integrable (staircasePairCost μ u c x χ h δ i j)
      (Measure.pi (fun _ : Fin n => shiftLaw h)) := by
  let := shiftLaw_isProbabilityMeasure hh
  have hjoint := integrable_staircase_pair_density (u i) (u j) c (x i) (x j) χ
    (hu i) (hu j) hc (hx i) (hx j) hχ hh hδ hδh hχ0 hχ1 hbound
  exact (measurePreserving_grid_pair (shiftLaw h) hij).integrable_comp_of_integrable
    hjoint.integral_prod_left

end CircleDomainRigidity.FiniteTransfer

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Selection_FinitePatching
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonEmbeddedArc.Arc.graphVertices_finite _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Patching the finite family of filling disks

On pairwise disjoint open disks, replace the old coordinate by its
smooth collar extension. Equality on full boundary neighborhoods gives
smoothness across every boundary, and local equality preserves the
rank-one wedge condition inside each filling disk.
-/

open Set Filter Function
open scoped Topology ContDiff

namespace CircleDomainRigidity.FiniteTransfer

theorem patchOpenRegions_eq_of_mem {X Y I : Type*}
    (D : I → Set X) (g : I → X → Y) (f : X → Y)
    (hd : Pairwise (Disjoint on D)) {i : I} {x : X} (hx : x ∈ D i) :
    patchOpenRegions D g f x = g i x := by
  classical
  have he : ∃ j, x ∈ D j := ⟨i, hx⟩
  have hi : Classical.choose he = i := by
    by_contra hne
    exact Set.disjoint_left.mp (hd hne) (Classical.choose_spec he) hx
  simp only [patchOpenRegions, dite_eq_left he, hi]

theorem patchOpenRegions_eq_of_notMem {X Y I : Type*}
    (D : I → Set X) (g : I → X → Y) (f : X → Y)
    {x : X} (hx : ∀ i, x ∉ D i) : patchOpenRegions D g f x = f x := by
  simp only [patchOpenRegions, dite_eq_right (not_exists.mpr hx)]

theorem patchOpenRegions_eventuallyEq_inside {X Y I : Type*} [TopologicalSpace X]
    (D : I → Set X) (g : I → X → Y) (f : X → Y)
    (hD : ∀ i, IsOpen (D i)) (hd : Pairwise (Disjoint on D))
    {i : I} {x : X} (hx : x ∈ D i) :
    patchOpenRegions D g f =ᶠ[𝓝 x] g i := by
  filter_upwards [(hD i).mem_nhds hx] with y hy
  exact patchOpenRegions_eq_of_mem D g f hd hy

/-- Finiteness permits simultaneous agreement near a point lying
outside all filling interiors, including a point on their boundaries. -/
theorem patchOpenRegions_eventuallyEq_outside
    {X Y I : Type*} [TopologicalSpace X] [Fintype I]
    (D : I → Set X) (g : I → X → Y) (f : X → Y)
    (hD : ∀ i, IsOpen (D i)) {x : X} (hx : ∀ i, x ∉ D i)
    (hagree : ∀ i, x ∈ frontier (D i) → g i =ᶠ[𝓝 x] f) :
    patchOpenRegions D g f =ᶠ[𝓝 x] f := by
  have hlocal i : ∀ᶠ y in 𝓝 x, y ∈ D i → g i y = f y := by
    by_cases hc : x ∈ closure (D i)
    · have hb : x ∈ frontier (D i) := by
        rw [(hD i).frontier_eq]
        exact ⟨hc, hx i⟩
      exact (hagree i hb).mono (fun _ hy _ => hy)
    · filter_upwards [isClosed_closure.isOpen_compl.mem_nhds hc] with y hy hmem
      exact (hy (subset_closure hmem)).elim
  filter_upwards [eventually_all.mpr hlocal] with y hy
  by_cases hm : ∃ i, y ∈ D i
  · simp only [patchOpenRegions, dite_eq_left hm]
    exact hy (Classical.choose hm) (Classical.choose_spec hm)
  · exact patchOpenRegions_eq_of_notMem D g f (not_exists.mp hm)

/-- Smoothness follows from smoothness of the old coordinate off the
filling interiors and of each replacement inside its own disk. -/
theorem contDiffOn_patchOpenRegions
    {E I : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [Fintype I]
    (D : I → Set E) (g : I → E → ℝ) (f : E → ℝ)
    (hD : ∀ i, IsOpen (D i)) (hd : Pairwise (Disjoint on D))
    {U : Set E}
    (hf : ∀ x ∈ U, (∀ i, x ∉ D i) → ContDiffAt ℝ ∞ f x)
    (hg : ∀ i, ∀ x ∈ U ∩ D i, ContDiffAt ℝ ∞ (g i) x)
    (hagree : ∀ i, ∀ x ∈ U ∩ frontier (D i), g i =ᶠ[𝓝 x] f) :
    ContDiffOn ℝ ∞ (patchOpenRegions D g f) U := by
  intro x hx
  by_cases hm : ∃ i, x ∈ D i
  · obtain ⟨i, hi⟩ := hm
    exact ((hg i x ⟨hx, hi⟩).congr_of_eventuallyEq
      (patchOpenRegions_eventuallyEq_inside D g f hD hd hi)).contDiffWithinAt
  · have hn := not_exists.mp hm
    exact ((hf x hx hn).congr_of_eventuallyEq
      (patchOpenRegions_eventuallyEq_outside D g f hD hn
        (fun i hi => hagree i x ⟨hx, hi⟩))).contDiffWithinAt

/-- The patched family inherits each filling's pointwise zero wedges.
The conclusion concerns actual derivatives of the patched functions. -/
theorem patchOpenRegions_wedges_eq_zero_inside
    {I L : Type*} (D : I → Set (ℝ × ℝ)) (g : I → L → (ℝ × ℝ) → ℝ)
    (f : L → (ℝ × ℝ) → ℝ) (hD : ∀ i, IsOpen (D i))
    (hd : Pairwise (Disjoint on D))
    (hzero : ∀ i j k, j ≠ k → ∀ x ∈ D i,
      planarWedge (planarGradient (g i j) x) (planarGradient (g i k) x) = 0)
    {i : I} {x : ℝ × ℝ} (hx : x ∈ D i) (j k : L) (hjk : j ≠ k) :
    planarWedge
      (planarGradient (patchOpenRegions D (fun i => g i j) (f j)) x)
      (planarGradient (patchOpenRegions D (fun i => g i k) (f k)) x) = 0 := by
  have heq l := (patchOpenRegions_eventuallyEq_inside D (fun i => g i l) (f l) hD hd hx).fderiv_eq
    (𝕜 := ℝ)
  simp only [planarGradient, heq]
  exact hzero i j k hjk x hx

end CircleDomainRigidity.FiniteTransfer

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Topology_InactiveCollars
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonMobius.sphereMetric _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Staircases are constant on collars avoiding their grids

A compact connected collar has a compact connected real branch image.
If this image misses the translated lattice, it has positive distance
from that closed lattice. Every sufficiently narrow staircase therefore
has zero derivative on the image and is constant on the collar. The
width bound can be chosen simultaneously for finitely many collars.
-/

open Set Filter Metric
open scoped Topology

namespace CircleDomainRigidity.FiniteTransfer

theorem isClosed_shiftedLattice {h : ℝ} (hh : 0 < h) (θ : ℝ) :
    IsClosed (shiftedLattice h θ) := by
  let : Fact (0 < h) := ⟨hh⟩
  have heq : shiftedLattice h θ =
      ((↑) : ℝ → AddCircle h) ⁻¹' {(θ : AddCircle h)} := by
    ext x
    simp only [shiftedLattice, mem_range, mem_preimage, mem_singleton_iff,
      addCircle_eq_iff_exists_int]
    constructor
    · rintro ⟨k, rfl⟩
      exact ⟨k, by ring⟩
    · rintro ⟨k, hk⟩
      exact ⟨k, by rw [hk]; ring⟩
  rw [heq]
  exact isClosed_singleton.preimage (AddCircle.continuous_mk' h)

theorem exists_uniform_lattice_distance {h θ : ℝ} (hh : 0 < h)
    {E : Set ℝ} (hE : IsCompact E) (havoid : Disjoint E (shiftedLattice h θ)) :
    ∃ ρ : ℝ, 0 < ρ ∧ ∀ x ∈ E, ∀ k : ℤ, ρ ≤ |x - (θ + h * k)| := by
  have hne : (shiftedLattice h θ).Nonempty := ⟨θ + h * (0 : ℤ), ⟨0, rfl⟩⟩
  obtain ⟨ρ, hρ, hdist⟩ := hE.exists_forall_le'
    (continuous_infDist_pt (shiftedLattice h θ)).continuousOn
    (fun x hx => ((isClosed_shiftedLattice hh θ).notMem_iff_infDist_pos hne).mp
      (fun hxL => Set.disjoint_left.mp havoid hx hxL))
  refine ⟨ρ, hρ, fun x hx k => (hdist x hx).trans ?_⟩
  simpa only [Real.dist_eq] using
    infDist_le_dist_of_mem (x := x) (show θ + h * k ∈ shiftedLattice h θ from ⟨k, rfl⟩)

/-- The same positive width bound works for the whole collar, and
the proof yields both derivative vanishing and constancy. -/
theorem eventually_constant_staircase_on_collar
    {X : Type*} [TopologicalSpace X] {C : Set X} (hC : IsCompact C)
    (hconn : IsPreconnected C) (u : X → ℝ) (hu : ContinuousOn u C)
    {h θ : ℝ} (hh : 0 < h) (havoid : Disjoint (u '' C) (shiftedLattice h θ)) :
    ∀ᶠ δ : ℝ in 𝓝[>] 0,
      (∀ x ∈ C, deriv (shiftedStaircase h δ θ) (u x) = 0) ∧
      ∀ x ∈ C, ∀ y ∈ C, shiftedStaircase h δ θ (u x) = shiftedStaircase h δ θ (u y) := by
  obtain ⟨ρ, hρ, hdist⟩ := exists_uniform_lattice_distance hh
    (hC.image_of_continuousOn hu) havoid
  have hδbound : ∀ᶠ δ : ℝ in 𝓝[>] 0, 0 < δ ∧ δ < min ρ (h / 4) := by
    have hp : ∀ᶠ δ : ℝ in 𝓝[>] 0, 0 < δ := self_mem_nhdsWithin
    exact hp.and
      ((eventually_lt_nhds (lt_min hρ (by positivity))).filter_mono nhdsWithin_le_nhds)
  filter_upwards [hδbound] with δ hδ
  have hδh : δ < h / 4 := hδ.2.trans_le (min_le_right _ _)
  have hzero : ∀ z ∈ u '' C, deriv (shiftedStaircase h δ θ) z = 0 := by
    intro z hz
    apply deriv_shiftedStaircase_eq_zero hh hδ.1 hδh
    intro k
    exact (hδ.2.trans_le (min_le_left _ _)).le.trans (hdist z hz k)
  refine ⟨fun x hx => hzero (u x) ⟨x, hx, rfl⟩, ?_⟩
  intro x hx y hy
  have hdiff := (contDiff_shiftedStaircase hh hδ.1 hδh θ).differentiable (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)
  have hbound := Convex.norm_image_sub_le_of_norm_deriv_le (C := 0)
    (fun z (_ : z ∈ u '' C) => hdiff z)
    (fun z hz => by simp only [hzero z hz, norm_zero, le_refl])
    (hconn.image u hu).ordConnected.convex ⟨x, hx, rfl⟩ ⟨y, hy, rfl⟩
  have heq : shiftedStaircase h δ θ (u y) - shiftedStaircase h δ θ (u x) = 0 := by
    apply norm_eq_zero.mp
    exact le_antisymm (by simpa only [zero_mul] using hbound) (norm_nonneg _)
  exact (sub_eq_zero.mp heq).symm

end CircleDomainRigidity.FiniteTransfer

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Topology_ConnectedCollars
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonMobius.sphereMetric _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Connected compact neighborhoods of filling boundaries

Small closed metric thickenings of a compact connected planar curve
are connected and compact. They give connected collars inside any
prescribed open boundary neighborhood, as required for simultaneous
staircase inactivity. No smooth tubular-neighborhood theorem is needed.
-/

open Set Filter Metric
open scoped Topology

namespace CircleDomainRigidity.FiniteTransfer

theorem isConnected_cthickening
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {C : Set E} (hc : IsCompact C) (hconn : IsConnected C) {δ : ℝ} (hδ : 0 ≤ δ) :
    IsConnected (cthickening δ C) := by
  obtain ⟨x, hx⟩ := hconn.nonempty
  have hp : IsPreconnected (⋃ z : C, C ∪ closedBall (z : E) δ) := by
    apply isPreconnected_iUnion
    · exact ⟨x, mem_iInter.mpr (fun _ => Or.inl hx)⟩
    · intro z
      exact hconn.isPreconnected.union (z : E) z.property (mem_closedBall_self hδ)
        isPreconnected_closedBall
  have heq : (⋃ z : C, C ∪ closedBall (z : E) δ) = cthickening δ C := by
    rw [hc.cthickening_eq_biUnion_closedBall hδ]
    ext y
    constructor
    · intro hy
      obtain ⟨z, hy⟩ := mem_iUnion.mp hy
      rcases hy with hy | hy
      · exact mem_iUnion₂.mpr ⟨y, hy, mem_closedBall_self hδ⟩
      · exact mem_iUnion₂.mpr ⟨z, z.property, hy⟩
    · intro hy
      obtain ⟨z, hz, hy⟩ := mem_iUnion₂.mp hy
      exact mem_iUnion.mpr ⟨⟨z, hz⟩, Or.inr hy⟩
  exact ⟨⟨x, self_subset_cthickening C hx⟩, heq ▸ hp⟩

theorem exists_compact_connected_neighborhood
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [ProperSpace E]
    {C U : Set E} (hc : IsCompact C) (hconn : IsConnected C)
    (hU : IsOpen U) (hCU : C ⊆ U) :
    ∃ K : Set E, IsCompact K ∧ IsConnected K ∧ K ∈ 𝓝ˢ C ∧ K ⊆ U := by
  obtain ⟨δ, hδ, hsub⟩ := hc.exists_cthickening_subset_open hU hCU
  exact ⟨cthickening δ C, hc.cthickening, isConnected_cthickening hc hconn hδ.le,
    cthickening_mem_nhdsSet C hδ, hsub⟩

end CircleDomainRigidity.FiniteTransfer

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Transfer_FilledCoordinates
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonEmbeddedArc.Arc.graphVertices_finite _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Simultaneous smooth coordinate fillings

Compact connected collars are chosen inside the supplied real-branch
domains and away from all inactive lattices. A single sufficiently small
width makes every inactive staircase constant there. Rank-one collar
extensions then patch into the retained coordinates across all the
pairwise disjoint filling disks. No lifting theorem is assumed.
-/

open Set Filter Function
open scoped Topology ContDiff

namespace CircleDomainRigidity.FiniteTransfer

theorem IsFilledCoordinateFamily.eventuallyEq_outside
    {I L : Type*} [Fintype I] {D : I → Set (ℝ × ℝ)} {Ω : Set (ℝ × ℝ)}
    {v F : L → (ℝ × ℝ) → ℝ} (hF : IsFilledCoordinateFamily D Ω v F)
    (hD : ∀ i, IsOpen (D i)) {x : ℝ × ℝ} (hx : ∀ i, x ∉ D i) (l : L) :
    F l =ᶠ[𝓝 x] v l := by
  by_cases hb : ∃ i, x ∈ frontier (D i)
  · obtain ⟨i, hi⟩ := hb
    exact ((hF.2.2.1 i).filter_mono (nhds_le_nhdsSet hi)).mono (fun _ h => h l)
  · have hc (i : I) : x ∉ closure (D i) := by
      intro hi
      apply hb
      refine ⟨i, ?_⟩
      rw [(hD i).frontier_eq]
      exact ⟨hi, hx i⟩
    have hn : ∀ᶠ y in 𝓝 x, ∀ i, y ∉ closure (D i) :=
      eventually_all.mpr (fun i => isClosed_closure.isOpen_compl.mem_nhds (hc i))
    filter_upwards [hn] with y hy
    exact hF.2.1 l y (fun i hi => hy i (subset_closure hi))

/-- The open collar can be chosen to avoid every inactive lattice even
when the real branches are smooth only on their supplied open domains. -/
theorem exists_inactive_connected_collar
    {L : Type*} [Fintype L] {A O : Set (ℝ × ℝ)}
    (hAc : IsCompact A) (hAconn : IsConnected A) (hO : IsOpen O) (hAO : A ⊆ O)
    (u : L → (ℝ × ℝ) → ℝ) (hu : ∀ l, ContDiffOn ℝ ∞ (u l) O)
    (active : L) {h : ℝ} (hh : 0 < h) (θ : L → ℝ)
    (havoid : ∀ l, l ≠ active → Disjoint (u l '' A) (shiftedLattice h (θ l))) :
    ∃ C : Set (ℝ × ℝ), IsCompact C ∧ IsConnected C ∧ C ∈ 𝓝ˢ A ∧ C ⊆ O ∧
      ∀ l, l ≠ active → Disjoint (u l '' C) (shiftedLattice h (θ l)) := by
  classical
  let V : Set (ℝ × ℝ) := O ∩ ⋂ l : L,
    if l = active then O else O ∩ (u l) ⁻¹' (shiftedLattice h (θ l))ᶜ
  have hVo : IsOpen V := hO.inter (isOpen_iInter_of_finite fun l => by
    by_cases hl : l = active
    · simpa only [ite_eq_left hl] using hO
    · simpa only [ite_eq_right hl] using (hu l).continuousOn.isOpen_inter_preimage hO
        (isClosed_shiftedLattice hh (θ l)).isOpen_compl)
  have hAV : A ⊆ V := by
    intro x hx
    refine ⟨hAO hx, mem_iInter.mpr fun l => ?_⟩
    by_cases hl : l = active
    · simpa only [ite_eq_left hl] using hAO hx
    · simp only [ite_eq_right hl, mem_inter_iff, mem_preimage, mem_compl_iff]
      exact ⟨hAO hx, fun h => Set.disjoint_left.mp (havoid l hl) ⟨x, hx, rfl⟩ h⟩
  obtain ⟨C, hCc, hCconn, hCA, hCV⟩ :=
    exists_compact_connected_neighborhood hAc hAconn hVo hAV
  refine ⟨C, hCc, hCconn, hCA, (fun x hx => (hCV hx).1), ?_⟩
  intro l hl
  apply Set.disjoint_left.mpr
  rintro y ⟨x, hx, rfl⟩ hy
  have hv := mem_iInter.mp (hCV hx).2 l
  simp only [ite_eq_right hl, mem_inter_iff, mem_preimage, mem_compl_iff] at hv
  exact hv.2 hy

theorem pairwise_disjoint_realJordan_closures
    {I : Type*} (H : I → ℂ ≃ₜ ℂ)
    (hH : Pairwise (Disjoint on fun i => closure (jordanInterior (H i)))) :
    Pairwise (Disjoint on fun i => closure (realJordanInterior (H i))) := by
  let e := Complex.equivRealProdCLM.toHomeomorph
  intro i j hij
  change Disjoint (closure (e '' jordanInterior (H i)))
    (closure (e '' jordanInterior (H j)))
  rw [← e.image_closure, ← e.image_closure]
  exact Set.disjoint_image_of_injective e.injective (hH hij)

end CircleDomainRigidity.FiniteTransfer

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Uniformization_ConformalMetric
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Restoring the spherical metric factor

In two dimensions positive scalar rescaling leaves the full Dirichlet
energy density unchanged. Thus a compactly supported metric modification
in a planar chart can retain the original spherical factor both near
the core and outside a compact set.
-/

open Matrix Set Filter MeasureTheory Metric
open scoped Topology ContDiff Matrix.Norms.Elementwise

noncomputable section

namespace CircleDomainRigidity.FiniteTransfer

theorem contDiff_sphericalMetricFactor : ContDiff ℝ ∞ sphericalMetricFactor := by
  unfold sphericalMetricFactor
  apply ContDiff.div contDiff_const
  · fun_prop
  · intro z
    positivity

end CircleDomainRigidity.FiniteTransfer

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Sobolev_StaircaseGradient
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonMobius.sphereMetric _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# The actual differential of the cutoff staircase

This identifies the random covectors used in the wedge-cost selection
with derivatives of the modified scalar coordinates.
-/

open Set Filter
open scoped Topology ContDiff

noncomputable section

namespace CircleDomainRigidity.FiniteTransfer

theorem planarGradient_cutoffStaircase
    {u χ : (ℝ × ℝ) → ℝ} {z : ℝ × ℝ}
    (hu : DifferentiableAt ℝ u z) (hχ : DifferentiableAt ℝ χ z)
    {h δ : ℝ} (hh : 0 < h) (hδ : 0 < δ) (hδh : δ < h / 4) (θ : ℝ) :
    planarGradient (cutoffStaircase u χ (shiftedStaircase h δ θ)) z =
      staircaseCovector h δ (χ z) θ (u z) (planarGradient u z) (planarGradient χ z) := by
  have hP := ((contDiff_shiftedStaircase hh hδ hδh θ).differentiable (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top) (u z)).hasDerivAt
  have hd := (hasFDerivAt_cutoffStaircase hu.hasFDerivAt hχ.hasFDerivAt hP).fderiv
  ext <;> simp [planarGradient, hd, staircaseCovector, smul_eq_mul]

end CircleDomainRigidity.FiniteTransfer

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Sobolev_CoordinateEstimates
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Actual coordinate energies on the completed surface

The metric trace estimate controls the sum of the actual scalar
coordinate energies. Exact agreement near the retained core then gives
localized estimates against the original domain, even though the original
coordinates need not extend into the filled holes.
-/

open Set Filter MeasureTheory Finset Matrix
open scoped Topology ContDiff Matrix.Norms.Elementwise

noncomputable section

namespace CircleDomainRigidity.FiniteTransfer

/-- Compare localized energy to the original domain, without evaluating
or integrating an original coordinate in the added holes. -/
theorem localized_energy_lt_source
    {X : Type*} [MeasurableSpace X] {μ : Measure X}
    {Q G K E : Set X} (hQ : MeasurableSet Q) (hG : MeasurableSet G)
    (hK : MeasurableSet K) (hE : MeasurableSet E) (hEK : E ⊆ K)
    (hQKG : Q ∩ K ⊆ G) {f u T : X → ℝ}
    (hf : IntegrableOn f Q μ) (hu : IntegrableOn u G μ)
    (hT : IntegrableOn T (Q \ K) μ) (hu0 : ∀ x ∈ G, 0 ≤ u x)
    (hcore : ∀ x ∈ Q ∩ K, f x = u x) (htail : ∀ x ∈ Q \ K, f x ≤ T x)
    {ε : ℝ} (hε : (∫ x in Q \ K, T x ∂μ) < ε) :
    (∫ x in Q \ E, f x ∂μ) < (∫ x in G \ E, u x ∂μ) + ε := by
  have hdiff : (Q \ E) \ K = Q \ K := by
    ext x
    constructor
    · exact fun hx => ⟨hx.1.1, hx.2⟩
    · exact fun hx => ⟨⟨hx.1, fun he => hx.2 (hEK he)⟩, hx.2⟩
  have heq : (∫ x in (Q \ E) ∩ K, f x ∂μ) = ∫ x in (Q \ E) ∩ K, u x ∂μ :=
    setIntegral_congr_fun ((hQ.diff hE).inter hK)
      (fun x hx => hcore x ⟨hx.1.1, hx.2⟩)
  have hsplit := integral_inter_add_sdiff hK (hf.mono_set (s := Q \ E) sdiff_subset)
  rw [hdiff, heq] at hsplit
  have ht : (∫ x in Q \ K, f x ∂μ) < ε :=
    (setIntegral_mono_on (hf.mono_set sdiff_subset) hT (hQ.diff hK) htail).trans_lt hε
  have hc : (∫ x in (Q \ E) ∩ K, u x ∂μ) ≤ ∫ x in G \ E, u x ∂μ :=
    setIntegral_mono_set (hu.mono_set sdiff_subset)
      ((ae_restrict_mem (hG.diff hE)).mono (fun x hx => hu0 x hx.1))
      (Eventually.of_forall (fun x hx => ⟨hQKG ⟨hx.1.1, hx.2⟩, hx.1.2⟩))
  linarith

end CircleDomainRigidity.FiniteTransfer

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Selection_UpperPairs
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# The actual finite wedge sum and its pair indexing

Each unordered coordinate pair occurs exactly once. This identifies the
spatial cost selected by the random-grid argument with the wedge sum of
the actual cutoff staircase differentials.
-/

open Set MeasureTheory Finset Filter

noncomputable section

namespace CircleDomainRigidity.FiniteTransfer

theorem upperPair_ne {n : ℕ} (p : UpperPairs n) : (upperPair p).1 ≠ (upperPair p).2 := by
  intro heq
  have h := congrArg Fin.val heq
  exact (Nat.ne_of_lt p.2.isLt) h

theorem upperPair_covers {n : ℕ} (i j : Fin n) (hij : i ≠ j) :
    ∃ p : UpperPairs n, upperPair p = (i,j) ∨ upperPair p = (j,i) := by
  have hne : i.val ≠ j.val := fun h => hij (Fin.ext h)
  rcases lt_or_gt_of_ne hne with h | h
  · refine ⟨⟨j, ⟨i.val, h⟩⟩, Or.inl ?_⟩
    rfl
  · refine ⟨⟨i, ⟨j.val, h⟩⟩, Or.inr ?_⟩
    rfl

theorem covectorWedges_eq_sum_upperPairs (x y : ℕ → ℝ) (n : ℕ) :
    covectorWedges x y n =
      ∑ p : UpperPairs n, |x p.2.val * y p.1.val - x p.1.val * y p.2.val| := by
  rw [Fintype.sum_sigma]
  unfold covectorWedges
  rw [Finset.sum_range]
  apply sum_congr rfl
  intro j _
  exact Finset.sum_range (fun i : ℕ => |x i * y j.val - x j.val * y i|)

end CircleDomainRigidity.FiniteTransfer

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Sobolev_FixedWidthIntegrability
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonMobius.sphereMetric _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Spatial integrability at every fixed staircase width

The derivative of a smooth staircase is periodic and bounded. Thus each
fixed choice of shifts has integrable spatial wedges whenever the original
three wedge terms are integrable. In particular, the cost identity needs
no separate integrability assumption for the modified coordinates.
-/

open Set Filter MeasureTheory
open scoped Topology

noncomputable section

namespace CircleDomainRigidity.FiniteTransfer

theorem periodic_deriv_shiftedStaircase {h δ : ℝ} (hh : 0 < h) (θ : ℝ) :
    Function.Periodic (deriv (shiftedStaircase h δ θ)) h := by
  intro x
  have heq : (fun t => shiftedStaircase h δ θ (t + h)) =
      (fun t => shiftedStaircase h δ θ t + h) :=
    funext (shiftedStaircase_add_period hh δ θ)
  have hd := congrArg (fun f : ℝ → ℝ => deriv f x) heq
  simpa only [deriv_comp_add_const, deriv_add_const] using hd

theorem bounded_staircase_multiplier {h δ : ℝ}
    (hh : 0 < h) (hδ : 0 < δ) (hδh : δ < h / 4) (θ : ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (χ x : ℝ), χ ∈ Icc 0 1 →
      0 ≤ (1 - χ) + χ * deriv (shiftedStaircase h δ θ) x ∧
      (1 - χ) + χ * deriv (shiftedStaircase h δ θ) x ≤ C := by
  have hc := (contDiff_shiftedStaircase hh hδ hδh θ).continuous_deriv (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)
  obtain ⟨B, hB⟩ := ((periodic_deriv_shiftedStaircase hh θ).compact_of_continuous
    hh.ne' hc).exists_bound_of_continuousOn continuous_id.continuousOn
  let C : ℝ := 1 + max B 0
  refine ⟨C, by dsimp [C] <;> positivity, ?_⟩
  intro χ x hχ
  have hd0 := deriv_shiftedStaircase_nonneg hh hδ θ x
  have hdB : deriv (shiftedStaircase h δ θ) x ≤ max B 0 :=
    (le_abs_self _).trans ((hB _ (mem_range_self x)).trans (le_max_left B 0))
  refine ⟨add_nonneg (sub_nonneg.mpr hχ.2) (mul_nonneg hχ.1 hd0), ?_⟩
  have hmul : χ * deriv (shiftedStaircase h δ θ) x ≤ max B 0 := by
    calc
      _ ≤ χ * max B 0 := mul_le_mul_of_nonneg_left hdB hχ.1
      _ ≤ 1 * max B 0 := mul_le_mul_of_nonneg_right hχ.2 (le_max_right _ _)
      _ = _ := one_mul _
  dsimp [C]
  linarith [hχ.1]

theorem integrable_staircase_pair_at_shifts
    {X : Type*} [MeasurableSpace X] {μ : Measure X}
    (u v c : X → ℝ × ℝ) (x y χ : X → ℝ)
    (hu : Measurable u) (hv : Measurable v) (hc : Measurable c)
    (hx : Measurable x) (hy : Measurable y) (hχ : Measurable χ)
    {h δ : ℝ} (hh : 0 < h) (hδ : 0 < δ) (hδh : δ < h / 4)
    (hχ0 : ∀ z, 0 ≤ χ z) (hχ1 : ∀ z, χ z ≤ 1)
    (huv : Integrable (fun z => |planarWedge (u z) (v z)|) μ)
    (huc : Integrable (fun z => |planarWedge (u z) (c z)|) μ)
    (hcv : Integrable (fun z => |planarWedge (c z) (v z)|) μ)
    (θ φ : ℝ) :
    Integrable (fun z => |planarWedge
      (staircaseCovector h δ (χ z) θ (x z) (u z) (c z))
      (staircaseCovector h δ (χ z) φ (y z) (v z) (c z))|) μ := by
  obtain ⟨A, hA0, hA⟩ := bounded_staircase_multiplier hh hδ hδh θ
  obtain ⟨B, hB0, hB⟩ := bounded_staircase_multiplier hh hδ hδh φ
  have hmajor := ((huv.const_mul (A * B)).add (huc.const_mul (h * A))).add
    (hcv.const_mul (h * B))
  have hmu := measurable_staircaseCovector hh hδ hδh hχ measurable_const hx hu hc
    (θ := fun _ => θ)
  have hmv := measurable_staircaseCovector hh hδ hδh hχ measurable_const hy hv hc
    (θ := fun _ => φ)
  apply hmajor.mono' (((hmu.fst.mul hmv.snd).sub (hmu.snd.mul hmv.fst)).abs.aestronglyMeasurable)
  apply Eventually.of_forall
  intro z
  rw [Real.norm_eq_abs, abs_abs]
  have hAz := hA (χ z) (x z) ⟨hχ0 z, hχ1 z⟩
  have hBz := hB (χ z) (y z) ⟨hχ0 z, hχ1 z⟩
  have he := abs_planarWedge_cutoff_le (u z) (v z) (c z) hAz.1 hBz.1
    (abs_shiftedStaircase_sub_le hh δ θ (x z))
    (abs_shiftedStaircase_sub_le hh δ φ (y z))
  apply he.trans
  dsimp only [Pi.add_apply]
  gcongr <;> first | exact hAz.1 | exact hAz.2 | exact hBz.1 | exact hBz.2

theorem integrable_staircase_pair_at_shifts_of_memLp
    {X : Type*} [MeasurableSpace X] {μ : Measure X}
    (u v c : X → ℝ × ℝ) (x y χ : X → ℝ)
    (hu : Measurable u) (hv : Measurable v) (hc : Measurable c)
    (hx : Measurable x) (hy : Measurable y) (hχ : Measurable χ)
    (hu2 : MemLp u 2 μ) (hv2 : MemLp v 2 μ) (hc2 : MemLp c 2 μ)
    {h δ : ℝ} (hh : 0 < h) (hδ : 0 < δ) (hδh : δ < h / 4)
    (hχ0 : ∀ z, 0 ≤ χ z) (hχ1 : ∀ z, χ z ≤ 1) (θ φ : ℝ) :
    Integrable (fun z => |planarWedge
      (staircaseCovector h δ (χ z) θ (x z) (u z) (c z))
      (staircaseCovector h δ (χ z) φ (y z) (v z) (c z))|) μ :=
  integrable_staircase_pair_at_shifts u v c x y χ hu hv hc hx hy hχ hh hδ hδh hχ0 hχ1
    (integrable_abs_planarWedge_of_memLp hu2 hv2)
    (integrable_abs_planarWedge_of_memLp hu2 hc2)
    (integrable_abs_planarWedge_of_memLp hc2 hv2) θ φ

end CircleDomainRigidity.FiniteTransfer

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Sobolev_LiftDifferentials
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Independence of differentials from the chosen real lift

Two continuous real lifts of one circle map differ locally by a fixed
integer. Their differentials, and those of the actual reciprocal-grid
cutoff modifications, therefore agree. These are local consequences of
the real quotient, with no additional published input.
-/

open Set Filter Function Metric
open scoped Topology

noncomputable section

namespace CircleDomainRigidity.FiniteTransfer

theorem map_add_int_of_add_one {P : ℝ → ℝ} (hP : ∀ x, P (x + 1) = P x + 1)
    (x : ℝ) (m : ℤ) : P (x + (m : ℝ)) = P x + (m : ℝ) := by
  have hp : Periodic (fun x => P x - x) 1 := by
    intro y
    change P (y + 1) - (y + 1) = P y - y
    rw [hP]
    ring
  have hm := hp.int_mul m x
  simp only [mul_one] at hm
  linarith

end CircleDomainRigidity.FiniteTransfer

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Sobolev_CircleDifferential
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Intrinsic differentials and cutoff modifications of circle coordinates

The differential is computed in a genuine real quotient chart. Local
integer transition functions make it independent of the chosen lift.
The cutoff staircase descends to the circle and is smooth in the same
charts; no global real lift or extra topological input is required.
-/

open Set Filter Function
open scoped Topology ContDiff

noncomputable section

namespace CircleDomainRigidity.FiniteTransfer

theorem circleGradient_eq_lift
    {f : (ℝ × ℝ) → UnitAddCircle} {u : (ℝ × ℝ) → ℝ} {x : ℝ × ℝ}
    (hf : ContinuousAt f x) (hu : ContinuousAt u x)
    (heq : (fun y => (u y : UnitAddCircle)) =ᶠ[𝓝 x] f) :
    circleGradient f x = planarGradient u x := by
  simp only [circleGradient, circleFDeriv_eq_lift hf hu heq, planarGradient]

theorem circleCutoff_eq_lift {X : Type*} (f : X → UnitAddCircle) (χ : X → ℝ)
    {P : ℝ → ℝ} (hP : ∀ r, P (r + 1) = P r + 1)
    {u : X → ℝ} {x : X} (hu : (u x : UnitAddCircle) = f x) :
    circleCutoff f χ P x = (cutoffStaircase u χ P x : UnitAddCircle) := by
  obtain ⟨m, hm⟩ := (addCircle_eq_iff_exists_int 1 (circleRepresentative (f x)) (u x)).mp
    ((coe_circleRepresentative (f x)).trans hu.symm)
  have hr : circleRepresentative (f x) = u x + (m : ℝ) := by simpa only [mul_one] using hm
  have hc : cutoffStaircase (fun y => circleRepresentative (f y)) χ P x =
      cutoffStaircase u χ P x + (m : ℝ) := by
    simp only [cutoffStaircase, hr, map_add_int_of_add_one hP]
    ring
  change (cutoffStaircase (fun y => circleRepresentative (f y)) χ P x : UnitAddCircle) = _
  rw [hc]
  apply (addCircle_eq_iff_exists_int 1 _ _).mpr
  exact ⟨m, by simp only [mul_one]⟩

theorem circleCutoff_eq_of_zero {X : Type*} (f : X → UnitAddCircle) (χ : X → ℝ)
    (P : ℝ → ℝ) {x : X} (hx : χ x = 0) : circleCutoff f χ P x = f x := by
  simp only [circleCutoff, cutoffStaircase, hx, zero_mul, add_zero, coe_circleRepresentative]

/-- The actual reciprocal-grid cutoff is smooth on every smooth circle
coordinate's domain, with the original additive transition functions. -/
theorem smoothCircleOn_reciprocal_cutoff
    {f : (ℝ × ℝ) → UnitAddCircle} {U : Set (ℝ × ℝ)}
    (hf : SmoothCircleOn f U) (χ : (ℝ × ℝ) → ℝ) (hχ : ContDiff ℝ ∞ χ)
    (N : ℕ) {δ : ℝ} (hδ : 0 < δ) (hδh : δ < reciprocalGridStep N / 4) (θ : ℝ) :
    SmoothCircleOn (circleCutoff f χ (shiftedStaircase (reciprocalGridStep N) δ θ)) U := by
  have hP (r : ℝ) : shiftedStaircase (reciprocalGridStep N) δ θ (r + 1) =
      shiftedStaircase (reciprocalGridStep N) δ θ r + 1 := by
    simpa only [reciprocalGridStep, Nat.cast_succ] using
      shiftedStaircase_add_one (Nat.succ_pos N) δ θ r
  apply smoothCircleOn_iff_local_lifts.mpr
  intro x hx
  obtain ⟨u, hu, heq⟩ := smoothCircleOn_iff_local_lifts.mp hf x hx
  refine ⟨cutoffStaircase u χ (shiftedStaircase (reciprocalGridStep N) δ θ), ?_, ?_⟩
  · exact hu.add (hχ.contDiffAt.mul
      (((contDiff_shiftedStaircase (reciprocalGridStep_pos N) hδ hδh θ).contDiffAt.comp x hu).sub hu))
  · filter_upwards [heq] with y hy
    exact (circleCutoff_eq_lift f χ hP hy).symm

end CircleDomainRigidity.FiniteTransfer

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Topology_CircleCovectors
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonMobius.sphereMetric _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Smooth covector fields of periodic coordinates

The locally defined circle differential is an ordinary smooth covector
field on its open domain. This supplies the tensor used in the same
metric construction as for single-valued real coordinates.
-/

open Set Filter Function
open scoped Topology ContDiff

noncomputable section

namespace CircleDomainRigidity.FiniteTransfer

theorem contDiffOn_circleFDeriv
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f : E → UnitAddCircle} {U : Set E} (hU : IsOpen U) (hf : SmoothCircleOn f U) :
    ContDiffOn ℝ ∞ (circleFDeriv f) U := by
  intro x hx
  let a := circleCut f x
  let V := U ∩ f ⁻¹' ({(a : UnitAddCircle)} : Set UnitAddCircle)ᶜ
  have hV : IsOpen V := hf.continuousOn.isOpen_inter_preimage hU isClosed_singleton.isOpen_compl
  have hxV : x ∈ V := ⟨hx, circleCut_ne f x⟩
  have hu : ContDiffOn ℝ ∞ (circleBranch f a) V := by
    intro y hy
    exact (hf y hy.1 a hy.2).contDiffWithinAt
  have heq := circleFDeriv_eventuallyEq_lift hV (hf.continuousOn.mono inter_subset_left)
    hu (fun y _ => coe_circleBranch f a y) hxV
  exact (((hu.fderiv_of_isOpen (m := ∞) hV (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)).contDiffAt (hV.mem_nhds hxV)).congr_of_eventuallyEq
    heq).contDiffWithinAt

theorem contDiffOn_circleGradient
    {f : (ℝ × ℝ) → UnitAddCircle} {U : Set (ℝ × ℝ)}
    (hU : IsOpen U) (hf : SmoothCircleOn f U) : ContDiffOn ℝ ∞ (circleGradient f) U := by
  have hd := contDiffOn_circleFDeriv hU hf
  exact (hd.clm_apply contDiffOn_const).prodMk (hd.clm_apply contDiffOn_const)

end CircleDomainRigidity.FiniteTransfer

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Sobolev_CovectorMetric
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonMobius.sphereMetric _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Metric selection for local covectors

Periodic coordinates need not have a global scalar potential. The Gram
argument applies to their smooth covector fields, retaining the spherical
metric near a closed core and near infinity, and realizing masked fields
by smooth extensions.
-/

open Set Filter MeasureTheory Finset Metric
open scoped Topology ContDiff Manifold Matrix.Norms.Elementwise

noncomputable section

namespace CircleDomainRigidity.FiniteTransfer

theorem continuousOn_fieldEnergy
    {Ω : Set (ℝ × ℝ)} {v : (ℝ × ℝ) → ℝ × ℝ} (hv : ContinuousOn v Ω)
    {g : (ℝ × ℝ) → PlanarMetric} (hg : Continuous g) (hPD : ∀ z, (g z).PosDef) :
    ContinuousOn (fieldEnergy v g) Ω := by
  have hw : ContinuousOn (fun z => ![(v z).1, (v z).2]) Ω := by
    apply continuousOn_pi.mpr
    intro i
    fin_cases i
    · exact hv.fst
    · exact hv.snd
  have hA : ContinuousOn (fun z => Matrix.vecMulVec ![(v z).1, (v z).2]
      ![(v z).1, (v z).2]) Ω := by
    apply continuousOn_pi.mpr
    intro i
    apply continuousOn_pi.mpr
    intro j
    exact (continuousOn_pi.mp hw i).mul (continuousOn_pi.mp hw j)
  change ContinuousOn (fun z => covectorEnergy ![(v z).1, (v z).2] (g z)) Ω
  simpa only [covectorEnergy_eq_matrixEnergy] using
    continuousOn_matrixEnergy_local hA hg.continuousOn (fun z _ => hPD z)

theorem integral_fieldGram_eq_sum
    {Q K : Set (ℝ × ℝ)} (hQ : IsCompact Q)
    (v : ℕ → (ℝ × ℝ) → ℝ × ℝ) (hv : ∀ i, Continuous (v i)) (n : ℕ)
    {g : (ℝ × ℝ) → PlanarMetric} (hg : Continuous g) (hPD : ∀ z, (g z).PosDef) :
    (∫ z in Q \ K, matrixEnergy (fieldGram v n z) (g z)) =
      ∑ i ∈ range n, ∫ z in Q \ K, fieldEnergy (v i) g z := by
  simp only [fieldGram, gramEnergy_eq_sum_covectorEnergy]
  exact integral_finsetSum _ (fun i _ =>
    ((continuousOn_fieldEnergy (hv i).continuousOn hg hPD).integrableOn_compact hQ).mono_set sdiff_subset)

/-- The spherical Gram metric construction does not require exactness
of the covectors and therefore applies to periodic differentials. -/
theorem exists_spherical_metric_for_covectors
    (v : ℕ → (ℝ × ℝ) → ℝ × ℝ) (n : ℕ) (hv : ∀ i, ContDiff ℝ ∞ (v i))
    {Q K : Set (ℝ × ℝ)} (hQ : IsCompact Q) (hK : IsClosed K) {ε : ℝ}
    (hε : (∫ z in Q \ K, 2 * fieldWedges v n z) < ε) :
    ∃ (R : ℝ) (g : (ℝ × ℝ) → PlanarMetric), 0 < R ∧ ContDiff ℝ ∞ g ∧
      (∀ z, (g z).PosDef) ∧
      (∀ᶠ z in 𝓝ˢ K, g z = sphericalMetricFactor z • 1) ∧
      (∀ z ∉ closedBall 0 R, g z = sphericalMetricFactor z • 1) ∧
      (∫ z in Q \ K, matrixEnergy (fieldGram v n z) (g z)) < ε := by
  obtain ⟨R, hR, hQR⟩ := hQ.isBounded.exists_pos_norm_lt
  have hQB : Q ⊆ ball 0 R := fun z hz => by
    simpa only [mem_ball, dist_zero_right] using hQR z hz
  let L := K ∩ closedBall 0 R
  have hL : IsCompact L := (isCompact_closedBall (0 : ℝ × ℝ) R).of_isClosed_subset
    (hK.inter isClosed_closedBall) inter_subset_right
  have hdiff : Q \ L = Q \ K := by
    ext z
    constructor
    · intro hz
      exact ⟨hz.1, fun hzK => hz.2 ⟨hzK, ball_subset_closedBall (hQB hz.1)⟩⟩
    · exact fun hz => ⟨hz.1, fun hzL => hz.2 hzL.1⟩
  obtain ⟨τ, N, g₀, _, _, _, _, hg₀, hPD₀, hcore, _, henergy⟩ :=
    exists_smooth_core_gramMetric (fun i z => (v i z).1) (fun i z => (v i z).2) n
      (fun i => (hv i).fst) (fun i => (hv i).snd) hL hQ.isBounded
      hQ.isClosed.measurableSet isOpen_univ (subset_univ _) (hdiff.symm ▸ hε)
  obtain ⟨ψ, hzero, hone, hψrange⟩ := exists_contMDiffMap_zero_one_nhds_of_isClosed
    (𝓘(ℝ, ℝ × ℝ)) isOpen_ball.isClosed_compl hQ.isClosed
      (disjoint_compl_left_iff_subset.mpr hQB) (n := (⊤ : ℕ∞))
  have hψ : ContDiff ℝ ∞ (ψ : (ℝ × ℝ) → ℝ) := contMDiff_iff_contDiff.mp ψ.contMDiff
  let b : (ℝ × ℝ) → PlanarMetric := fun z => blendMetric (g₀ z) (ψ z)
  have hb : ContDiff ℝ ∞ b :=
    ((contDiff_const.sub hψ).smul contDiff_const).add (hψ.smul hg₀)
  have hbPD (z : ℝ × ℝ) : (b z).PosDef := blendMetric_posDef (hPD₀ z) (hψrange z)
  have heqQ {z : ℝ × ℝ} (hz : z ∈ Q) : b z = g₀ z := by
    dsimp only [b]
    rw [hone.self_of_nhdsSet z hz, blendMetric_one]
  have hbcore : ∀ᶠ z in 𝓝ˢ K, b z = 1 := by
    apply eventually_nhdsSet_iff_forall.mpr
    intro z hz
    by_cases hzB : z ∈ closedBall 0 R
    · filter_upwards [hcore.filter_mono (nhds_le_nhdsSet (show z ∈ L from ⟨hz, hzB⟩))]
        with w hw
      simp only [b, hw, blendMetric_identity]
    · have hzout : z ∈ (ball 0 R)ᶜ := fun hh => hzB (ball_subset_closedBall hh)
      filter_upwards [hzero.filter_mono (nhds_le_nhdsSet hzout)] with w hw
      simp only [b, hw, blendMetric_zero]
  refine ⟨R, fun z => sphericalMetricFactor z • b z, hR,
    contDiff_sphericalMetricFactor.smul hb,
    fun z => (hbPD z).smul (sphericalMetricFactor_pos z), ?_, ?_, ?_⟩
  · filter_upwards [hbcore] with z hz
    rw [hz]
  · intro z hz
    have hzout : z ∈ (ball 0 R)ᶜ := fun hh => hz (ball_subset_closedBall hh)
    simp only [b, hzero.self_of_nhdsSet z hzout, blendMetric_zero]
  · rw [hdiff] at henergy
    have heq : (∫ z in Q \ K, matrixEnergy (fieldGram v n z)
        (sphericalMetricFactor z • b z)) =
        ∫ z in Q \ K, matrixEnergy (fieldGram v n z) (g₀ z) := by
      apply setIntegral_congr_fun (hQ.isClosed.measurableSet.diff hK.measurableSet)
      intro z hz
      change matrixEnergy (fieldGram v n z) (sphericalMetricFactor z • b z) =
        matrixEnergy (fieldGram v n z) (g₀ z)
      rw [matrixEnergy_pos_smul _ (hbPD z) (sphericalMetricFactor_pos z), heqQ hz.1]
    exact heq.trans_lt henergy

/-- Extend a local covector field across the inactive side of a mask.
No global scalar primitive is introduced. -/
theorem exists_smooth_masked_covector
    {Ω Q K M : Set (ℝ × ℝ)} (hΩ : IsOpen Ω) (hQ : IsCompact Q) (hQΩ : Q ⊆ Ω)
    (hM : IsClosed M) (hboundary : frontier M ⊆ interior K)
    {v : (ℝ × ℝ) → ℝ × ℝ} (hv : ContDiffOn ℝ ∞ v (Ω ∩ interior M)) :
    ∃ V : (ℝ × ℝ) → ℝ × ℝ, ContDiff ℝ ∞ V ∧
      ∀ z ∈ Q \ K, V z = M.indicator v z := by
  let A := (Q ∩ (interior K)ᶜ) ∩ M
  have hA : IsClosed A := (hQ.isClosed.inter isOpen_interior.isClosed_compl).inter hM
  have hAU : A ⊆ Ω ∩ interior M := by
    intro z hz
    exact ⟨hQΩ hz.1.1, (mem_interior_iff_notMem_frontier hz.2).mpr
      (fun hb => hz.1.2 (hboundary hb))⟩
  obtain ⟨vx, hvx, hex, hzx⟩ := exists_smooth_collar_extension
    (hΩ.inter isOpen_interior) hA hAU hv.fst 0
  obtain ⟨vy, hvy, hey, hzy⟩ := exists_smooth_collar_extension
    (hΩ.inter isOpen_interior) hA hAU hv.snd 0
  refine ⟨fun z => (vx z, vy z), hvx.prodMk hvy, ?_⟩
  intro z hz
  change (vx z, vy z) = M.indicator v z
  by_cases hzM : z ∈ M
  · have hzA : z ∈ A := ⟨⟨hz.1, fun hi => hz.2 (interior_subset hi)⟩, hzM⟩
    rw [indicator_of_mem hzM, hex.self_of_nhdsSet hzA, hey.self_of_nhdsSet hzA]
  · have hzU : z ∉ Ω ∩ interior M := fun h => hzM (interior_subset h.2)
    simp only [indicator_of_notMem hzM, hzx z hzU, hzy z hzU, Prod.mk_zero_zero]

end CircleDomainRigidity.FiniteTransfer

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Rigidity_MaskedCircleMetric
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonMobius.sphereMetric _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
attribute [-simp] _root_.OAI.CircleDomainRigidity.metricBeltramiCoefficient_scalar
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# One metric for masked periodic coordinates

The actual intrinsic differentials of the circle coordinates are used
throughout. Mask boundaries lie inside the retained core, so the masked
covectors extend smoothly across the portion on which the metric changes.
Their pairwise wedge budget controls the sum of energies on the masks.
-/

open Set Filter MeasureTheory Finset
open scoped Topology ContDiff Matrix.Norms.Elementwise

noncomputable section

namespace CircleDomainRigidity.FiniteTransfer

theorem contDiff_natCovectorFamily
    {n : ℕ} {v : Fin n → (ℝ × ℝ) → ℝ × ℝ}
    (hv : ∀ i, ContDiff ℝ ∞ (v i)) (i : ℕ) :
    ContDiff ℝ ∞ (natCovectorFamily v i) := by
  by_cases hi : i < n
  · simpa only [natCovectorFamily, dite_eq_left hi] using hv ⟨i, hi⟩
  · simp only [natCovectorFamily, dite_eq_right hi]
    exact contDiff_const

theorem fieldWedges_eq_sum_upperPairs {n : ℕ}
    (v : Fin n → (ℝ × ℝ) → ℝ × ℝ) (z : ℝ × ℝ) :
    fieldWedges (natCovectorFamily v) n z =
      ∑ p : UpperPairs n, |planarWedge (v (upperPair p).1 z) (v (upperPair p).2 z)| := by
  rw [fieldWedges, covectorWedges_eq_sum_upperPairs]
  apply sum_congr rfl
  intro p _
  have h₁ := p.2.isLt.trans p.1.isLt
  have h₂ := p.1.isLt
  simp only [natCovectorFamily, dite_eq_left h₁, dite_eq_left h₂, upperPair,
    planarWedge, mul_comm]

theorem fieldEnergy_indicator (M : Set (ℝ × ℝ)) (v : (ℝ × ℝ) → ℝ × ℝ)
    (g : (ℝ × ℝ) → PlanarMetric) (z : ℝ × ℝ) :
    fieldEnergy (M.indicator v) g z = M.indicator (fieldEnergy v g) z := by
  by_cases hz : z ∈ M
  · simp only [fieldEnergy, indicator_of_mem hz]
  · simp [fieldEnergy, indicator_of_notMem hz, covectorEnergy]

/-- This is the masked metric step for genuine circle-valued
coordinates; no globally defined scalar potentials are assumed. -/
theorem exists_spherical_metric_for_masked_circles
    {n : ℕ} {Ω Q K : Set (ℝ × ℝ)} (hΩ : IsOpen Ω) (hQ : IsCompact Q) (hQΩ : Q ⊆ Ω)
    (hK : IsClosed K) (M : Fin n → Set (ℝ × ℝ)) (hM : ∀ i, IsClosed (M i))
    (hboundary : ∀ i, frontier (M i) ⊆ interior K)
    (f : Fin n → (ℝ × ℝ) → UnitAddCircle)
    (hf : ∀ i, SmoothCircleOn (f i) (Ω ∩ interior (M i)))
    {ε : ℝ} (hbudget : (∫ z in Q \ K, 2 * maskedCircleWedges M f z) < ε) :
    ∃ (R : ℝ) (g : (ℝ × ℝ) → PlanarMetric), 0 < R ∧ ContDiff ℝ ∞ g ∧
      (∀ z, (g z).PosDef) ∧
      (∀ᶠ z in 𝓝ˢ K, g z = sphericalMetricFactor z • 1) ∧
      (∀ z ∉ Metric.closedBall 0 R, g z = sphericalMetricFactor z • 1) ∧
      (∑ i : Fin n, ∫ z in (Q \ K) ∩ M i, fieldEnergy (circleGradient (f i)) g z) < ε := by
  choose V hV hgrad using fun i => exists_smooth_masked_covector
    hΩ hQ hQΩ (hM i) (hboundary i)
    (contDiffOn_circleGradient (hΩ.inter isOpen_interior) (hf i))
  have hVn := contDiff_natCovectorFamily hV
  have hW {z : ℝ × ℝ} (hz : z ∈ Q \ K) :
      fieldWedges (natCovectorFamily V) n z = maskedCircleWedges M f z := by
    rw [fieldWedges_eq_sum_upperPairs]
    apply sum_congr rfl
    intro p _
    rw [hgrad _ z hz, hgrad _ z hz]
  have hbudget' : (∫ z in Q \ K, 2 * fieldWedges (natCovectorFamily V) n z) < ε := by
    have heq := setIntegral_congr_fun (μ := volume) (hQ.isClosed.measurableSet.diff hK.measurableSet)
      (fun z hz => congrArg (fun a : ℝ => 2 * a) (hW hz))
    exact heq.trans_lt hbudget
  obtain ⟨R, g, hR, hg, hPD, hcore, hfar, henergy⟩ :=
    exists_spherical_metric_for_covectors _ n hVn hQ hK hbudget'
  refine ⟨R, g, hR, hg, hPD, hcore, hfar, ?_⟩
  have heq : (∫ z in Q \ K, matrixEnergy (fieldGram (natCovectorFamily V) n z) (g z)) =
      ∑ i : Fin n, ∫ z in (Q \ K) ∩ M i, fieldEnergy (circleGradient (f i)) g z := by
    rw [integral_fieldGram_eq_sum hQ _ (fun i => (hVn i).continuous) n hg.continuous hPD,
      Finset.sum_range]
    apply sum_congr rfl
    intro i _
    simp only [natCovectorFamily, dite_eq_left i.isLt]
    calc
      (∫ z in Q \ K, fieldEnergy (V i) g z) =
          ∫ z in Q \ K, (M i).indicator (fieldEnergy (circleGradient (f i)) g) z := by
        apply setIntegral_congr_fun (hQ.isClosed.measurableSet.diff hK.measurableSet)
        intro z hz
        rw [← fieldEnergy_indicator]
        exact congrArg (fun v : ℝ × ℝ => covectorEnergy ![v.1, v.2] (g z)) (hgrad i z hz)
      _ = _ := setIntegral_indicator (hM i).measurableSet
  exact heq.symm.trans_lt henergy

end CircleDomainRigidity.FiniteTransfer

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Sobolev_CircleStaircaseGradient
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Actual cutoff differential of a periodic coordinate

The same covector formula used by the random-grid estimate is the
intrinsic differential of the descended circle cutoff. Its scalar input
can be the bounded canonical representative; integer changes of branch
do not change either the multiplier or the error term.
-/

open Set Filter Function
open scoped Topology ContDiff

noncomputable section

namespace CircleDomainRigidity.FiniteTransfer

theorem deriv_map_add_int_of_add_one {P : ℝ → ℝ}
    (hP : ∀ x, P (x + 1) = P x + 1) (x : ℝ) (m : ℤ) :
    deriv P (x + (m : ℝ)) = deriv P x := by
  have heq : (fun y => P (y + (m : ℝ))) = (fun y => P y + (m : ℝ)) :=
    funext (fun y => map_add_int_of_add_one hP y m)
  have hd := congrArg (fun f : ℝ → ℝ => deriv f x) heq
  simpa only [deriv_comp_add_const, deriv_add_const] using hd

theorem staircaseCovector_reciprocal_add_int
    (N : ℕ) (δ χ θ x : ℝ) (m : ℤ) (u c : ℝ × ℝ) :
    staircaseCovector (reciprocalGridStep N) δ χ θ (x + (m : ℝ)) u c =
      staircaseCovector (reciprocalGridStep N) δ χ θ x u c := by
  have hP (r : ℝ) : shiftedStaircase (reciprocalGridStep N) δ θ (r + 1) =
      shiftedStaircase (reciprocalGridStep N) δ θ r + 1 := by
    simpa only [reciprocalGridStep, Nat.cast_succ] using
      shiftedStaircase_add_one (Nat.succ_pos N) δ θ r
  unfold staircaseCovector
  rw [deriv_map_add_int_of_add_one hP, map_add_int_of_add_one hP]
  congr 2
  ring

theorem circleGradient_reciprocal_cutoff
    {f : (ℝ × ℝ) → UnitAddCircle} {u χ : (ℝ × ℝ) → ℝ} {x : ℝ × ℝ}
    (hf : ContinuousAt f x) (hu : ContDiffAt ℝ ∞ u x) (hχ : ContDiffAt ℝ ∞ χ x)
    (hproj : (fun y => (u y : UnitAddCircle)) =ᶠ[𝓝 x] f)
    (N : ℕ) {δ : ℝ} (hδ : 0 < δ) (hδh : δ < reciprocalGridStep N / 4) (θ : ℝ) :
    circleGradient (circleCutoff f χ (shiftedStaircase (reciprocalGridStep N) δ θ)) x =
      staircaseCovector (reciprocalGridStep N) δ (χ x) θ
        (circleRepresentative (f x)) (circleGradient f x) (planarGradient χ x) := by
  let P := shiftedStaircase (reciprocalGridStep N) δ θ
  have hP (r : ℝ) : P (r + 1) = P r + 1 := by
    simpa only [P, reciprocalGridStep, Nat.cast_succ] using
      shiftedStaircase_add_one (Nat.succ_pos N) δ θ r
  let v := cutoffStaircase u χ P
  have hv : ContDiffAt ℝ ∞ v x := hu.add (hχ.mul
    (((contDiff_shiftedStaircase (reciprocalGridStep_pos N) hδ hδh θ).contDiffAt.comp x hu).sub hu))
  have hnew : (fun y => (v y : UnitAddCircle)) =ᶠ[𝓝 x] circleCutoff f χ P := by
    filter_upwards [hproj] with y hy
    exact (circleCutoff_eq_lift f χ hP hy).symm
  have hfnew : ContinuousAt (circleCutoff f χ P) x :=
    ((AddCircle.continuous_mk' (1 : ℝ)).continuousAt.comp hv.continuousAt).congr hnew
  have hbase := circleGradient_eq_lift hf hu.continuousAt hproj
  have hmod := circleGradient_eq_lift hfnew hv.continuousAt hnew
  have hxproj : (u x : UnitAddCircle) = f x := hproj.self_of_nhds
  obtain ⟨m, hm⟩ := (addCircle_eq_iff_exists_int 1 (circleRepresentative (f x)) (u x)).mp
    ((coe_circleRepresentative (f x)).trans hxproj.symm)
  have hr : circleRepresentative (f x) = u x + (m : ℝ) := by simpa only [mul_one] using hm
  rw [hmod, planarGradient_cutoffStaircase (hu.differentiableAt (by simp))
    (hχ.differentiableAt (by simp)) (reciprocalGridStep_pos N) hδ hδh θ, hbase, hr]
  exact (staircaseCovector_reciprocal_add_int N δ (χ x) θ (u x) m
    (planarGradient u x) (planarGradient χ x)).symm

end CircleDomainRigidity.FiniteTransfer

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Modulus_CircleWedgeCost
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonMobius.sphereMetric _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Actual random wedge cost for circle coordinates

The random covectors are exactly the intrinsic differentials of the
modified circle maps. Fixed-width integrability follows from the
original L² differentials and the cutoff, just as in the real case.
-/

open Set Filter MeasureTheory
open scoped Topology ContDiff

noncomputable section

namespace CircleDomainRigidity.FiniteTransfer

theorem measurable_circleRepresentative : Measurable circleRepresentative := by
  apply measurable_of_continuousOn_compl_singleton (0 : UnitAddCircle)
  intro t ht
  exact (continuous_subtype_val.continuousAt.comp
    (AddCircle.continuousAt_equivIco 1 0 ht)).continuousWithinAt

end CircleDomainRigidity.FiniteTransfer

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Modulus_MobiusNormalization
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonMobius.sphereMetric _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions _root_.OAI.CircleDomainRigidity.finiteSphericalArea _root_.OAI.CircleDomainRigidity.sphereFirstCountableTopology
attribute [-simp] _root_.OAI.CannonMobius.affine_coe _root_.OAI.CannonMobius.affine_infty _root_.OAI.CannonMobius.inv_inv_apply _root_.OAI.CannonMobius.roundChart_coe _root_.OAI.CannonMobius.tripleMap_mul _root_.OAI.CircleDomainRigidity.CompactScalarModel.postcompose_coefficient _root_.OAI.CircleDomainRigidity.FiniteTransfer.coe_mem_sphericalCore _root_.OAI.CircleDomainRigidity.FiniteTransfer.coe_mem_sphericalDiskUnion _root_.OAI.CircleDomainRigidity.FiniteTransfer.infty_mem_cutoffCore _root_.OAI.CircleDomainRigidity.FiniteTransfer.infty_mem_sphericalCore _root_.OAI.CircleDomainRigidity.FiniteTransfer.infty_not_mem_sphericalDiskUnion _root_.OAI.CircleDomainRigidity.FiniteTransfer.realChartDomain_union _root_.OAI.CircleDomainRigidity.affineSphere_coe _root_.OAI.CircleDomainRigidity.affineSphere_infty _root_.OAI.CircleDomainRigidity.centeredJordanCoordinate_self _root_.OAI.CircleDomainRigidity.chartSymm_coe_apply _root_.OAI.CircleDomainRigidity.chart_coe_apply _root_.OAI.CircleDomainRigidity.chart_infty_apply _root_.OAI.CircleDomainRigidity.extendAtInfinity_coe _root_.OAI.CircleDomainRigidity.extendAtInfinity_infty _root_.OAI.CircleDomainRigidity.sphereInv_infty _root_.OAI.CircleDomainRigidity.sphereInv_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Concrete Möbius normalizations

Affine changes and inversion are homeomorphisms of the concrete sphere.
Their matrix actions agree with the projective-line action used in the
definition of round disks.
-/

open Set Filter Function
open scoped Topology OnePoint

noncomputable section

namespace CircleDomainRigidity

theorem inversion_eq_smul (p : Sphere) : CannonMobius.inversion p = inversionMobius • p := by
  change CannonMobius.inv p = inversionMobius • p
  cases p using OnePoint.rec with
  | infty => simp [OnePoint.smul_infty_eq_ite, inversionMobius]
  | coe z =>
    by_cases hz : z = 0
    · simp [hz, OnePoint.smul_some_eq_ite, inversionMobius]
    · simp [hz, OnePoint.smul_some_eq_ite, inversionMobius,
        CannonMobius.inv, div_eq_mul_inv]

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Topology_TerminalDisks
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonEmbeddedArc.Arc.graphVertices_finite _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Selecting finite terminal neighborhoods with simultaneous band control

Section 2, Step 2 of the Koebe manuscript first fixes finitely many
terminal points and then chooses their neighborhoods, before choosing
the staircase width. Here positive-radius metric balls are selected
inside prescribed neighborhoods with pairwise disjoint closed balls.
Their physical coordinate values lie in the boundary bands enlarged
by `h`; hence all shifted staircases have oscillation at most `a + 4h`
there, simultaneously for every staircase width.

For the complex plane these selected balls are actual round disks.
On a general quotient metric sphere they are only metric neighborhoods:
the separate smooth-contour construction is still needed to obtain
physical smooth Jordan boundaries around non-point fibers.
-/

open Set Filter Metric Function
open scoped Topology

namespace CircleDomainRigidity.FiniteTransfer

/-- Finitely many distinct points have disjoint closed-ball
neighborhoods inside arbitrary prescribed neighborhoods, with any
prescribed positive upper bounds for their radii. -/
theorem exists_disjoint_closedBalls_in_neighborhoods
    {X I : Type*} [MetricSpace X] [Fintype I]
    (p : I → X) (hp : Injective p) (O : I → Set X)
    (hO : ∀ i, O i ∈ 𝓝 (p i)) (ρ : I → ℝ) (hρ : ∀ i, 0 < ρ i) :
    ∃ r : I → ℝ, (∀ i, 0 < r i ∧ r i < ρ i) ∧
      (∀ i, closedBall (p i) (r i) ⊆ O i) ∧
      Pairwise (Disjoint on fun i => closedBall (p i) (r i)) := by
  classical
  have hdisj : Pairwise (Disjoint on fun i => ({p i} : Set X)) := by
    intro i j hij
    exact disjoint_singleton.mpr (fun h => hij (hp h))
  have hn : Pairwise (Disjoint on fun i => 𝓝ˢ ({p i} : Set X)) := by
    intro i j hij
    exact disjoint_nhdsSet_nhdsSet isClosed_singleton isClosed_singleton (hdisj hij)
  obtain ⟨V, hV, hVd⟩ := hn.exists_mem_filter_basis_of_disjoint
    (fun i => hasBasis_nhdsSet ({p i} : Set X))
  have hlocal (i : I) : V i ∩ O i ∈ 𝓝 (p i) :=
    inter_mem ((hV i).1.mem_nhds ((hV i).2 (mem_singleton _))) (hO i)
  have hball (i : I) : ∃ R : ℝ, 0 < R ∧ closedBall (p i) R ⊆ V i ∩ O i :=
    nhds_basis_closedBall.mem_iff.mp (hlocal i)
  choose R hR hRV using hball
  let r : I → ℝ := fun i => min (R i / 2) (ρ i / 2)
  have hr (i : I) : 0 < r i ∧ r i < ρ i := by
    dsimp [r]
    exact ⟨lt_min (half_pos (hR i)) (half_pos (hρ i)),
      (min_le_right _ _).trans_lt (by linarith [hρ i])⟩
  have hsub (i : I) : closedBall (p i) (r i) ⊆ V i ∩ O i := by
    apply (closedBall_subset_closedBall ?_).trans (hRV i)
    exact (min_le_left _ _).trans (by linarith [hR i])
  refine ⟨r, hr, fun i x hx => (hsub i hx).2, ?_⟩
  intro i j hij
  exact (hVd hij).mono (fun _ hx => (hsub i hx).1) (fun _ hx => (hsub j hx).1)

/-- The values near a boundary point lie in its actual liminf/limsup
band enlarged by any positive margin. -/
theorem eventually_mem_enlarged_boundary_band
    {X : Type*} [TopologicalSpace X] {G : Set X} {f : X → ℝ} {M : ℝ}
    (hM : ∀ y ∈ G, |f y| ≤ M) (x : X) {h : ℝ} (hh : 0 < h) :
    ∀ᶠ y in 𝓝[G] x,
      liminf f (𝓝[G] x) - h < f y ∧ f y < limsup f (𝓝[G] x) + h := by
  have hb : ∀ᶠ y in 𝓝[G] x, -M ≤ f y ∧ f y ≤ M := by
    filter_upwards [self_mem_nhdsWithin] with y hy
    exact abs_le.mp (hM y hy)
  have hlo : IsBoundedUnder (· ≥ ·) (𝓝[G] x) f :=
    isBoundedUnder_of_eventually_ge (hb.mono (fun _ hy => hy.1))
  have hhi : IsBoundedUnder (· ≤ ·) (𝓝[G] x) f :=
    isBoundedUnder_of_eventually_le (hb.mono (fun _ hy => hy.2))
  exact (eventually_lt_of_lt_liminf (by linarith) hlo).and
    (eventually_lt_of_limsup_lt (by linarith) hhi)

/-- Actual finite-radius selection, with all nonsingular coordinate
band bounds imposed at once. `active i j` specifies which coordinates
need a real branch at terminal point `i`; the physical domain and branch
may depend on that terminal point, as for periodic coordinates. -/
theorem exists_terminal_balls_with_band_control
    {X I J : Type*} [MetricSpace X] [Fintype I] [Fintype J]
    (p : I → X) (hp : Injective p) (O : I → Set X)
    (hO : ∀ i, O i ∈ 𝓝 (p i)) (ρ : I → ℝ) (hρ : ∀ i, 0 < ρ i)
    (G : I → Set X) (f : I → J → X → ℝ) (M : I → J → ℝ)
    (hM : ∀ i j y, y ∈ G i → |f i j y| ≤ M i j)
    (active : I → J → Prop) {h : ℝ} (hh : 0 < h) :
    ∃ r : I → ℝ, (∀ i, 0 < r i ∧ r i < ρ i) ∧
      (∀ i, closedBall (p i) (r i) ⊆ O i) ∧
      Pairwise (Disjoint on fun i => closedBall (p i) (r i)) ∧
      ∀ i j, active i j → ∀ y ∈ closedBall (p i) (r i) ∩ G i,
        liminf (f i j) (𝓝[G i] (p i)) - h < f i j y ∧
          f i j y < limsup (f i j) (𝓝[G i] (p i)) + h := by
  let Q : I → Set X := fun i => {y | y ∈ G i → ∀ j, active i j →
    liminf (f i j) (𝓝[G i] (p i)) - h < f i j y ∧
      f i j y < limsup (f i j) (𝓝[G i] (p i)) + h}
  have hQ (i : I) : Q i ∈ 𝓝 (p i) := by
    apply eventually_nhdsWithin_iff.mp
    apply eventually_all.mpr
    intro j
    exact (eventually_mem_enlarged_boundary_band (hM i j) (p i) hh).mono
      (fun _ hy _ => hy)
  obtain ⟨r, hr, hsub, hdisj⟩ := exists_disjoint_closedBalls_in_neighborhoods
    p hp (fun i => O i ∩ Q i) (fun i => inter_mem (hO i) (hQ i)) ρ hρ
  refine ⟨r, hr, fun i y hy => (hsub i hy).1, hdisj, ?_⟩
  intro i j hj y hy
  exact (hsub i hy.1).2 hy.2 j hj

/-- Enlarging the coordinate band by `h` at each end gives oscillation
at most its band budget plus `2h`. -/
theorem abs_sub_le_of_enlarged_boundary_band
    {X : Type*} [TopologicalSpace X] {G : Set X} {f : X → ℝ}
    {s x y : X} {a h : ℝ}
    (hband : limsup f (𝓝[G] s) - liminf f (𝓝[G] s) ≤ a)
    (hx : liminf f (𝓝[G] s) - h < f x ∧ f x < limsup f (𝓝[G] s) + h)
    (hy : liminf f (𝓝[G] s) - h < f y ∧ f y < limsup f (𝓝[G] s) + h) :
    |f x - f y| ≤ a + 2 * h := by
  rw [abs_le]
  constructor <;> linarith [hx.1, hx.2, hy.1, hy.2]

/-- The terminal oscillation estimate is uniform in the staircase
width. Thus disk neighborhoods can be fixed before taking that width
to zero, exactly as required in Step 2. -/
theorem terminal_staircase_oscillation_le
    {X : Type*} [TopologicalSpace X] {G : Set X} {f : X → ℝ}
    {s x y : X} {a h : ℝ} (hh : 0 < h)
    (hband : limsup f (𝓝[G] s) - liminf f (𝓝[G] s) ≤ a)
    (hx : liminf f (𝓝[G] s) - h < f x ∧ f x < limsup f (𝓝[G] s) + h)
    (hy : liminf f (𝓝[G] s) - h < f y ∧ f y < limsup f (𝓝[G] s) + h)
    (δ θ : ℝ) :
    |shiftedStaircase h δ θ (f x) - shiftedStaircase h δ θ (f y)| ≤ a + 4 * h := by
  have hu := abs_sub_le_of_enlarged_boundary_band hband hx hy
  have hpx := abs_shiftedStaircase_sub_le hh δ θ (f x)
  have hpy := abs_shiftedStaircase_sub_le hh δ θ (f y)
  rw [abs_le] at hu hpx hpy ⊢
  constructor <;> linarith [hu.1, hu.2, hpx.1, hpx.2, hpy.1, hpy.2]

/-- The radii are chosen once for all staircase widths and shifts.
Any subsequently constructed physical terminal contour lying in these
closed balls inherits the paper's `a + 4h` oscillation bound. -/
theorem exists_terminal_balls_with_uniform_staircase_oscillation
    {X I J : Type*} [MetricSpace X] [Fintype I] [Fintype J]
    (p : I → X) (hp : Injective p) (O : I → Set X)
    (hO : ∀ i, O i ∈ 𝓝 (p i)) (ρ : I → ℝ) (hρ : ∀ i, 0 < ρ i)
    (G : I → Set X) (f : I → J → X → ℝ) (M : I → J → ℝ)
    (hM : ∀ i j y, y ∈ G i → |f i j y| ≤ M i j)
    (active : I → J → Prop) (a : I → J → ℝ)
    (hbudget : ∀ i j, active i j →
      limsup (f i j) (𝓝[G i] (p i)) - liminf (f i j) (𝓝[G i] (p i)) ≤ a i j)
    {h : ℝ} (hh : 0 < h) :
    ∃ r : I → ℝ, (∀ i, 0 < r i ∧ r i < ρ i) ∧
      (∀ i, closedBall (p i) (r i) ⊆ O i) ∧
      Pairwise (Disjoint on fun i => closedBall (p i) (r i)) ∧
      ∀ i j, active i j → ∀ δ θ : ℝ,
        ∀ x ∈ closedBall (p i) (r i) ∩ G i,
        ∀ y ∈ closedBall (p i) (r i) ∩ G i,
          |shiftedStaircase h δ θ (f i j x) - shiftedStaircase h δ θ (f i j y)| ≤
            a i j + 4 * h := by
  obtain ⟨r, hr, hsub, hdisj, hcontrol⟩ :=
    exists_terminal_balls_with_band_control p hp O hO ρ hρ G f M hM active hh
  refine ⟨r, hr, hsub, hdisj, ?_⟩
  intro i j hj δ θ x hx y hy
  exact terminal_staircase_oscillation_le hh (hbudget i j hj)
    (hcontrol i j hj x hx) (hcontrol i j hj y hy) δ θ

end CircleDomainRigidity.FiniteTransfer

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Modulus_TerminalOscillation
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Summing the terminal oscillation errors

The simultaneous boundary estimate `A ≤ a + 4h` on finitely many
terminal disks gives the required square-sum error `4h√J`. Singular
indices can be omitted by using any subfamily of the terminal indices.
-/

open Set

namespace CircleDomainRigidity.FiniteTransfer

theorem sqrt_sum_terminal_excess_sq_le {I : Type*} (S : Finset I)
    (A a : I → ℝ) {h : ℝ} (hh : 0 ≤ h)
    (hA : ∀ s ∈ S, A s ≤ a s + 4 * h) :
    Real.sqrt (∑ s ∈ S, max (A s - a s) 0 ^ 2) ≤
      4 * h * Real.sqrt (S.card : ℝ) := by
  have hsum : (∑ s ∈ S, max (A s - a s) 0 ^ 2) ≤ (S.card : ℝ) * (4 * h) ^ 2 := by
    calc
      _ ≤ ∑ _s ∈ S, (4 * h) ^ 2 := by
        apply Finset.sum_le_sum
        intro s hs
        have hb : max (A s - a s) 0 ≤ 4 * h :=
          max_le (by linarith [hA s hs]) (by positivity)
        exact pow_le_pow_left₀ (le_max_right _ _) hb 2
      _ = _ := by simp [nsmul_eq_mul]
  apply (sq_le_sq₀ (Real.sqrt_nonneg _) (by positivity)).mp
  rw [Real.sq_sqrt (Finset.sum_nonneg (fun _ _ => sq_nonneg _))]
  calc
    _ ≤ (S.card : ℝ) * (4 * h) ^ 2 := hsum
    _ = (4 * h * Real.sqrt (S.card : ℝ)) ^ 2 := by
      simp only [mul_pow, Real.sq_sqrt (Nat.cast_nonneg S.card)]
      ring

/-- The terminal-count selection directly gives the finite-transfer
oscillation budget for every nonsingular subfamily. -/
theorem sqrt_sum_terminal_excess_sq_lt {I : Type*} (S T : Finset I)
    (hST : S ⊆ T) (A a : I → ℝ) {h η : ℝ} (hh : 0 ≤ h)
    (hA : ∀ s ∈ S, A s ≤ a s + 4 * h)
    (hsmall : h * Real.sqrt (T.card : ℝ) < η) :
    Real.sqrt (∑ s ∈ S, max (A s - a s) 0 ^ 2) < 4 * η := by
  have hcard : (S.card : ℝ) ≤ T.card := by exact_mod_cast Finset.card_le_card hST
  have hle := (sqrt_sum_terminal_excess_sq_le S A a hh hA).trans
    (mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt hcard) (by positivity))
  have hlt : 4 * h * Real.sqrt (T.card : ℝ) < 4 * η := by nlinarith [hsmall]
  exact hle.trans_lt hlt

end CircleDomainRigidity.FiniteTransfer

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Sobolev_SmallEnergyCore
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonMobius.sphereMetric _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Choosing the retained core from finite energy

Compact exhaustion of the actual open domain makes the original wedge
integral arbitrarily small. An intervening open neighborhood puts every
prescribed compact subset strictly inside the selected compact core.
-/

open Set Filter MeasureTheory
open scoped Topology

noncomputable section

namespace CircleDomainRigidity.FiniteTransfer

theorem exists_compact_core_small_tail
    {G K₀ : Set (ℝ × ℝ)} (hG : IsOpen G) (hK₀ : IsCompact K₀) (hK₀G : K₀ ⊆ G)
    {f : (ℝ × ℝ) → ℝ} (hf : IntegrableOn f G) (hf0 : ∀ z, 0 ≤ f z)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ K : Set (ℝ × ℝ), IsCompact K ∧ K₀ ⊆ interior K ∧ K ⊆ G ∧
      (∫ z in G \ K, f z) < ε := by
  let : LocallyCompactSpace G := hG.locallyCompactSpace
  let C := CompactExhaustion.choice G
  let T : ℕ → Set (ℝ × ℝ) := fun n => Subtype.val '' C n
  have hTc (n : ℕ) : IsCompact (T n) := (C.isCompact n).image continuous_subtype_val
  have hTG (n : ℕ) : T n ⊆ G := by
    rintro z ⟨x, _, rfl⟩
    exact x.property
  have hD : Antitone (fun n => G \ T n) := by
    intro m n hmn z hz
    exact ⟨hz.1, fun hzT => hz.2 (image_mono (C.subset hmn) hzT)⟩
  have hempty : (⋂ n, G \ T n) = ∅ := by
    apply eq_empty_iff_forall_notMem.mpr
    intro z hz
    have hzG := (mem_iInter.mp hz 0).1
    obtain ⟨n, hn⟩ := C.exists_mem ⟨z, hzG⟩
    exact (mem_iInter.mp hz n).2 ⟨⟨z, hzG⟩, hn, rfl⟩
  have ht : Tendsto (fun n => ∫ z in G \ T n, f z) atTop (𝓝 0) := by
    have ht := tendsto_setIntegral_of_antitone
      (fun n => hG.measurableSet.diff (hTc n).isClosed.measurableSet) hD
      ⟨0, hf.mono_set sdiff_subset⟩
    simpa only [hempty, setIntegral_empty] using ht
  obtain ⟨n, hn⟩ := (ht.eventually (eventually_lt_nhds hε)).exists
  have hA : IsCompact (K₀ ∪ T n) := hK₀.union (hTc n)
  obtain ⟨V, hV, hAV, hVG, hVc⟩ := exists_open_between_and_isCompact_closure hA hG
    (union_subset hK₀G (hTG n))
  refine ⟨closure V, hVc, (subset_union_left.trans hAV).trans hV.subset_interior_closure, hVG, ?_⟩
  apply lt_of_le_of_lt _ hn
  apply setIntegral_mono_set (hf.mono_set sdiff_subset) (Eventually.of_forall hf0)
  exact Eventually.of_forall (fun z hz => ⟨hz.1, fun hzT =>
    hz.2 (subset_closure (hAV (Or.inr hzT)))⟩)

end CircleDomainRigidity.FiniteTransfer

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Topology_CoreCutoff
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# The actual cutoff used in grid modification

A compact retained core in the open physical domain admits a globally
smooth cutoff, zero near the core and one off a larger compact subset of
the domain. Its gradient is square-integrable without an extra premise.
-/

open Set Filter Function MeasureTheory
open scoped Topology ContDiff Manifold

noncomputable section

namespace CircleDomainRigidity.FiniteTransfer

theorem continuous_planarGradient
    {f : (ℝ × ℝ) → ℝ} (hf : ContDiff ℝ ∞ f) : Continuous (planarGradient f) := by
  have hd : Continuous (fderiv ℝ f) := (hf.fderiv_right (m := ∞) (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)).continuous
  exact (hd.clm_apply continuous_const).prodMk (hd.clm_apply continuous_const)

theorem hasCompactSupport_planarGradient
    {f : (ℝ × ℝ) → ℝ} (hf : HasCompactSupport f) : HasCompactSupport (planarGradient f) := by
  apply hf.mono'
  intro z hz
  by_contra hzf
  have hd : fderiv ℝ f z = 0 := fderiv_of_notMem_tsupport ℝ hzf
  exact hz (by simp [planarGradient, hd])

end CircleDomainRigidity.FiniteTransfer

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Transfer_GridPreparation
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Preparing the actual random grid from finite-energy coordinates

The retained core, cutoff, cutoff energy and small original wedge sum
are all constructed. The only grid event supplied to the selection is
an explicitly conull event, as in the separate compatibility argument.
-/

open Set Filter MeasureTheory
open scoped Topology ContDiff

noncomputable section

namespace CircleDomainRigidity.FiniteTransfer

theorem measurable_planarGradient (f : (ℝ × ℝ) → ℝ) : Measurable (planarGradient f) :=
  (measurable_fderiv_apply_const ℝ f (1, 0)).prodMk
    (measurable_fderiv_apply_const ℝ f (0, 1))

end CircleDomainRigidity.FiniteTransfer

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Transfer_RegularCore
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonMobius.sphereMetric _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# A regular retained core containing infinity

Only the already stated planar Sard input is used for the regular value.
The core may contain an arbitrary closed subset of the domain. Its
complement has compact closure in the finite chart, so the core retains
an entire neighborhood of infinity.
-/

open Set Filter Function MeasureTheory
open scoped Topology ContDiff Manifold

noncomputable section

namespace CircleDomainRigidity.FiniteTransfer

theorem exists_real_regular_value_in_interval (hsard : SmoothPlanarSard)
    {f : (ℝ × ℝ) → ℝ} (hf : ContDiff ℝ ∞ f) (hcompact : HasCompactSupport f)
    {a b : ℝ} (hab : a < b) :
    ∃ t ∈ Ioo a b, ∀ z, f z = t → fderiv ℝ f z ≠ 0 := by
  let e := Complex.equivRealProdCLM
  let g : ℂ → ℝ := f ∘ e
  have hg : ContDiff ℝ ∞ g := hf.comp e.contDiff
  have hgc : HasCompactSupport g := hcompact.comp_homeomorph e.toHomeomorph
  obtain ⟨t, ht, hregular⟩ := exists_regular_value_in_interval hsard hg hgc hab
  refine ⟨t, ht, ?_⟩
  intro z hz hzero
  apply hregular (e.symm z) (by simpa only [g, Function.comp_apply, e.apply_symm_apply] using hz)
  change fderiv ℝ (f ∘ e) (e.symm z) = 0
  rw [fderiv_comp (e.symm z) (hf.differentiable (by simp) _) e.differentiableAt,
    e.fderiv, e.apply_symm_apply, hzero, ContinuousLinearMap.zero_comp]

theorem exists_smooth_real_cutoff
    {A O : Set (ℝ × ℝ)} (hA : IsCompact A) (hO : IsOpen O) (hAO : A ⊆ O) :
    ∃ f : (ℝ × ℝ) → ℝ, ContDiff ℝ ∞ f ∧ HasCompactSupport f ∧
      tsupport f ⊆ O ∧ (∀ z, f z ∈ Icc 0 1) ∧ (∀ᶠ z in 𝓝ˢ A, f z = 1) := by
  obtain ⟨V, hV, hAV, hVO, hVc⟩ := exists_open_between_and_isCompact_closure hA hO hAO
  obtain ⟨f, hzero, hone, hrange⟩ := exists_contMDiffMap_zero_one_nhds_of_isClosed
    (𝓘(ℝ, ℝ × ℝ)) hV.isClosed_compl hA.isClosed
    (disjoint_compl_left_iff_subset.mpr hAV) (n := (⊤ : ℕ∞))
  have hsupport : support (f : (ℝ × ℝ) → ℝ) ⊆ V := by
    intro z hz
    by_contra hzV
    exact hz (hzero.self_of_nhdsSet z hzV)
  have hts : tsupport (f : (ℝ × ℝ) → ℝ) ⊆ closure V := closure_mono hsupport
  exact ⟨f, contMDiff_iff_contDiff.mp f.contMDiff,
    hVc.of_isClosed_subset isClosed_closure hts, hts.trans hVO, hrange, hone⟩

/-- Sard selects a regular level separating a prescribed closed part of
the physical domain from all its complementary components. Finite
energy makes the remaining tail small. -/
theorem exists_regular_core_small_tail (hsard : SmoothPlanarSard)
    {G K₀ : Set (ℝ × ℝ)} (hG : IsOpen G) (hGc : IsCompact Gᶜ)
    (hK₀ : IsClosed K₀) (hK₀G : K₀ ⊆ G)
    {f : (ℝ × ℝ) → ℝ} (hf : IntegrableOn f G) (hf0 : ∀ z, 0 ≤ f z)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ (ψ : (ℝ × ℝ) → ℝ) (t : ℝ) (K : Set (ℝ × ℝ)),
      ContDiff ℝ ∞ ψ ∧ HasCompactSupport ψ ∧ t ∈ Ioo 0 1 ∧
      (∀ z, ψ z = t → fderiv ℝ ψ z ≠ 0) ∧ K = {z | ψ z ≤ t} ∧
      IsClosed K ∧ K₀ ⊆ interior K ∧ K ⊆ G ∧ IsCompact (closure Kᶜ) ∧
      (∫ z in G \ K, f z) < ε := by
  obtain ⟨A, hAc, _, hAG, htail⟩ := exists_compact_core_small_tail hG isCompact_empty
    (empty_subset G) hf hf0 hε
  have hB : IsClosed (K₀ ∪ A) := hK₀.union hAc.isClosed
  have hBG : K₀ ∪ A ⊆ G := union_subset hK₀G hAG
  obtain ⟨ψ, hψ, hψc, hψsupp, _, hone⟩ := exists_smooth_real_cutoff hGc hB.isOpen_compl
    (fun z hzG hzB => hzG (hBG hzB))
  obtain ⟨t, ht, hreg⟩ := exists_real_regular_value_in_interval hsard hψ hψc zero_lt_one
  let K : Set (ℝ × ℝ) := {z | ψ z ≤ t}
  have hzero (z : ℝ × ℝ) (hz : z ∈ K₀ ∪ A) : ψ z = 0 :=
    image_eq_zero_of_notMem_tsupport (fun hs => hψsupp hs hz)
  have hBK : K₀ ∪ A ⊆ K := fun z hz => by
    change ψ z ≤ t
    rw [hzero z hz]
    exact ht.1.le
  have hclosed : IsClosed K := isClosed_le hψ.continuous continuous_const
  have hcore : K₀ ⊆ interior K := by
    have hsmall : {z | ψ z < t} ⊆ interior K := by
      apply interior_maximal ?_ (isOpen_lt hψ.continuous continuous_const)
      intro z hz
      change ψ z ≤ t
      exact hz.le
    intro z hz
    apply hsmall
    change ψ z < t
    rw [hzero z (Or.inl hz)]
    exact ht.1
  have hKG : K ⊆ G := by
    intro z hz
    by_contra hzG
    have h1 := hone.self_of_nhdsSet z hzG
    have hle : ψ z ≤ t := hz
    rw [h1] at hle
    exact (not_le.mpr ht.2) hle
  have hsupp : Kᶜ ⊆ tsupport ψ := by
    intro z hz
    apply subset_tsupport
    change ψ z ≠ 0
    intro heq
    apply hz
    change ψ z ≤ t
    rw [heq]
    exact ht.1.le
  refine ⟨ψ, t, K, hψ, hψc, ht, hreg, rfl, hclosed, hcore, hKG,
    hψc.of_isClosed_subset isClosed_closure (closure_minimal hsupp (isClosed_tsupport ψ)), ?_⟩
  apply lt_of_le_of_lt _ htail
  apply setIntegral_mono_set (hf.mono_set sdiff_subset) (Eventually.of_forall hf0)
  exact Eventually.of_forall (fun z hz => ⟨hz.1, fun hzA => hz.2 (hBK (Or.inr hzA))⟩)

/-- For a domain containing infinity the cutoff is compactly supported
in the finite chart, vanishes near the entire retained core and equals
one near every missing component. -/
theorem exists_cutoff_near_complement
    {G K : Set (ℝ × ℝ)} (hGc : IsCompact Gᶜ) (hK : IsClosed K) (hKG : K ⊆ G) :
    ∃ χ : (ℝ × ℝ) → ℝ, ContDiff ℝ ∞ χ ∧ HasCompactSupport χ ∧
      (∀ z, χ z ∈ Icc 0 1) ∧ (∀ᶠ z in 𝓝ˢ K, χ z = 0) ∧
      (∀ᶠ z in 𝓝ˢ Gᶜ, χ z = 1) ∧ MemLp (planarGradient χ) 2 volume := by
  obtain ⟨χ, hχ, hχc, hsupport, hrange, hone⟩ := exists_smooth_real_cutoff hGc hK.isOpen_compl
    (fun z hzG hzK => hzG (hKG hzK))
  refine ⟨χ, hχ, hχc, hrange, ?_, hone,
    (continuous_planarGradient hχ).memLp_of_hasCompactSupport (hasCompactSupport_planarGradient hχc)⟩
  apply eventually_nhdsSet_iff_forall.mpr
  intro z hz
  exact notMem_tsupport_iff_eventuallyEq.mp (fun hs => hsupport hs hz)

end CircleDomainRigidity.FiniteTransfer

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Sobolev_SmoothJordanNeighborhoods
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Finite smooth Jordan neighborhoods

The contour construction in Section 1 of the Koebe manuscript is derived
from the smooth cutoff and regular level, scalar Sard, compact
one-manifold classification, and planar Schoenflies. Outer selection and containment
give the finite family of Jordan neighborhoods.
-/

open Set Filter Function
open scoped Topology ContDiff Manifold

namespace CircleDomainRigidity

/-- Actual finite smooth Jordan disks covering a chosen compact part of an
obstacle, with disjoint closures contained in the prescribed physical open
set. Its complement is required connected and unbounded precisely for the
hole-filling containment argument. -/
theorem exists_finite_smooth_jordan_cover
    (hsard : SmoothPlanarSard) (hschoenflies : PlanarSchoenflies)
    {A F V : Set ℂ} (hA : IsCompact A) (hAF : A ⊆ F)
    (hFA : IsClosed (F \ A)) (hV : IsOpen V) (hAV : A ⊆ V)
    (hVconn : IsPreconnected Vᶜ) (hVunbounded : ¬ Bornology.IsBounded Vᶜ) :
    ∃ (f : ℂ → ℝ) (t : ℝ)
      (γ : ConnectedComponents {z // f z = t} → Circle → ℂ)
      (H : ConnectedComponents {z // f z = t} → ℂ ≃ₜ ℂ)
      (s : Set (ConnectedComponents {z // f z = t})),
      s.Finite ∧ A ⊆ ⋃ i ∈ s, jordanInterior (H i) ∧
      s.Pairwise (fun i j => Disjoint (closure (jordanInterior (H i)))
        (closure (jordanInterior (H j)))) ∧
      (∀ i ∈ s, closure (jordanInterior (H i)) ⊆ V) ∧
      ∀ i ∈ s, ContMDiff (𝓡 1) (𝓘(ℝ, ℂ)) ∞ (γ i) ∧
        Topology.IsEmbedding (γ i) ∧
        frontier (jordanInterior (H i)) = range (γ i) ∧
        Disjoint (frontier (jordanInterior (H i))) F := by
  classical
  obtain ⟨f, t, hf, ht, hU, hAU, hUc, hUV, _, hlevel, hregular, havoid, _⟩ :=
    exists_regular_superlevel_isolating_obstacle hsard hA hAF hFA hV hAV
  obtain ⟨hfinite, γ, hγ, hγdisj, hγcover⟩ :=
    compact_regular_level_circle_contours hf hregular hlevel
  let : Finite (ConnectedComponents {z // f z = t}) := hfinite
  choose H hH using fun i => hschoenflies (γ i) (hγ i).2.continuous (hγ i).2.injective
  have hfront (i) : frontier (jordanInterior (H i)) = range (γ i) :=
    frontier_jordanInterior_eq_circle_range (H i) (γ i) (hH i)
  have hUd : frontier {z | t < f z} = {z | f z = t} :=
    frontier_superlevel_eq_regular_level hf.continuous hregular
  have hfrontlevel (i) : frontier (jordanInterior (H i)) ⊆ {z | f z = t} := by
    rw [hfront, ← hγcover]
    exact subset_iUnion (fun i => range (γ i)) i
  have hpair : Pairwise (fun i j => Disjoint (frontier (jordanInterior (H i)))
      (frontier (jordanInterior (H j)))) := by
    intro i j hij
    simpa only [hfront] using hγdisj hij
  obtain ⟨s, hs, hsd, hdom, _⟩ := exists_outer_jordanInteriors H hpair
  let : Finite s := hs.to_subtype
  have hsd' : Pairwise (Disjoint on fun i : s => closure (jordanInterior (H i))) := by
    intro i j hij
    exact hsd i.property j.property (fun h => hij (Subtype.ext h))
  have hcover : frontier {z | t < f z} ⊆ ⋃ i : s, closure (jordanInterior (H i)) := by
    intro z hz
    rw [hUd, ← hγcover] at hz
    obtain ⟨i, hi⟩ := mem_iUnion.mp hz
    have hi' : z ∈ closure (jordanInterior (H i)) := by
      apply frontier_subset_closure
      simpa only [hfront] using hi
    obtain ⟨j, hj, hij⟩ := hdom i
    exact mem_iUnion.mpr ⟨⟨j, hj⟩, hij hi'⟩
  have hUcover : {z | t < f z} ⊆ ⋃ i : s, jordanInterior (H i) :=
    open_subset_finite_jordanInteriors_of_frontier_subset (fun i : s => H i) hsd'
      hU (hUc.isBounded.subset subset_closure) hcover
      (fun i => hUd.symm ▸ hfrontlevel i)
  refine ⟨f, t, γ, H, s, hs, ?_, hsd, ?_, ?_⟩
  · intro z hz
    obtain ⟨i, hi⟩ := mem_iUnion.mp (hUcover (hAU hz))
    exact mem_iUnion₂.mpr ⟨i, i.property, hi⟩
  · intro i _
    apply closed_jordanInterior_subset_of_unbounded_connected_compl (H i) hVconn hVunbounded
    intro z hz
    apply hUV
    apply frontier_subset_closure
    rw [hUd]
    exact hfrontlevel i hz
  · intro i _
    exact ⟨(hγ i).1, (hγ i).2, hfront i, havoid.mono_left (hfrontlevel i)⟩

end CircleDomainRigidity

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Topology_BoundaryBumping
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Boundary bumping for compact continua

This is the compact-space argument used in the small-disk and generic-level
lemmas of the uniformization manuscript. It does not assume local
connectedness of the continuum.
-/

open Set Topology

namespace CircleDomainRigidity

/-- Every component of a proper closed subset of a compact connected space
meets its boundary. -/
theorem component_meets_frontier
    {X : Type*} [TopologicalSpace X] [CompactSpace X] [T2Space X]
    [PreconnectedSpace X] {F : Set X} (hF : IsClosed F) (hproper : F ≠ univ)
    {x : X} (hx : x ∈ F) :
    (connectedComponentIn F x ∩ frontier F).Nonempty := by
  classical
  by_contra hnonempty
  have hdisj : Disjoint (frontier F) (connectedComponentIn F x) :=
    (Set.disjoint_iff_inter_eq_empty.mpr (Set.not_nonempty_iff_eq_empty.mp hnonempty)).symm
  let : CompactSpace F := isCompact_iff_compactSpace.mp hF.isCompact
  let xf : F := ⟨x, hx⟩
  let K : Set F := (Subtype.val : F → X) ⁻¹' frontier F
  have hK : IsClosed K := isClosed_frontier.preimage continuous_subtype_val
  have hd : Disjoint K (connectedComponent xf) := by
    apply Set.disjoint_left.mpr
    intro z hzK hzC
    apply Set.disjoint_left.mp hdisj hzK
    rw [connectedComponentIn_eq_image hx]
    exact ⟨z, hzC, rfl⟩
  rw [connectedComponent_eq_iInter_isClopen xf] at hd
  obtain ⟨s, hs⟩ := hK.isCompact.elim_finite_subfamily_closed
    (fun U : {U : Set F // IsClopen U ∧ xf ∈ U} => U.val)
    (fun U => U.property.1.isClosed) (Set.disjoint_iff_inter_eq_empty.mp hd)
  let U : Set F := ⋂ V ∈ s, (V : Set F)
  have hU : IsClopen U := isClopen_biInter_finset fun V _ => V.property.1
  have hxU : xf ∈ U := mem_iInter₂.mpr fun V _ => V.property.2
  let W : Set X := (Subtype.val : F → X) '' U
  have hWclosed : IsClosed W := hF.isClosedMap_subtype_val U hU.isClosed
  have hWF : W ⊆ F := by
    rintro _ ⟨z, _, rfl⟩
    exact z.property
  have hWint : W ⊆ interior F := by
    rintro _ ⟨z, hz, rfl⟩
    by_contra hzi
    have hzK : z ∈ K := ⟨subset_closure z.property, hzi⟩
    exact Set.disjoint_left.mp (Set.disjoint_iff_inter_eq_empty.mpr hs) hzK hz
  obtain ⟨O, hO, hWO⟩ :=
    Topology.IsInducing.subtypeVal.image_eq_isOpen_inter_range hU.isOpen
  change W = O ∩ range (Subtype.val : F → X) at hWO
  have hWeq : W = O ∩ interior F := by
    apply Subset.antisymm
    · intro z hz
      exact ⟨(hWO ▸ hz).1, hWint hz⟩
    · intro z hz
      rw [hWO]
      exact ⟨hz.1, ⟨⟨z, interior_subset hz.2⟩, rfl⟩⟩
  have hWopen : IsOpen W := hWeq ▸ hO.inter isOpen_interior
  have hWuniv : W = univ := (show IsClopen W from ⟨hWclosed, hWopen⟩).eq_univ
    ⟨x, xf, hxU, rfl⟩
  apply hproper
  apply Set.eq_univ_of_univ_subset
  rw [← hWuniv]
  exact hWF

/-- Adjoining totally disconnected dust to a closed set creates no new
nondegenerate continuum. This is the first small-disk lemma of the paper. -/
theorem continuum_subset_closed_of_totallyDisconnected
    {X : Type*} [TopologicalSpace X] [T2Space X]
    {C F B : Set X} (hC : IsCompact C) (hconn : IsConnected C)
    (hnt : C.Nontrivial) (hF : IsClosed F) (hB : IsTotallyDisconnected B)
    (hsub : C ⊆ F ∪ B) : C ⊆ F := by
  classical
  let : CompactSpace C := isCompact_iff_compactSpace.mp hC
  let : PreconnectedSpace C := Subtype.preconnectedSpace hconn.isPreconnected
  intro x hx
  by_contra hxF
  obtain ⟨y, hy, hyx⟩ := hnt.exists_ne x
  let xc : C := ⟨x, hx⟩
  let yc : C := ⟨y, hy⟩
  let O : Set C := ((Subtype.val : C → X) ⁻¹' F)ᶜ ∩ {yc}ᶜ
  have hO : IsOpen O := (hF.preimage continuous_subtype_val).isOpen_compl.inter
    isClosed_singleton.isOpen_compl
  have hxO : xc ∈ O := ⟨hxF, fun h => hyx (congrArg Subtype.val h).symm⟩
  obtain ⟨N, hNnhds, hNclosed, hNO⟩ := exists_mem_nhds_isClosed_subset (hO.mem_nhds hxO)
  have hxN : xc ∈ N := mem_of_mem_nhds hNnhds
  have hNproper : N ≠ univ := by
    intro h
    have hyN : yc ∈ N := by rw [h]; trivial
    exact (hNO hyN).2 rfl
  obtain ⟨z, hzC, hzfront⟩ := component_meets_frontier hNclosed hNproper hxN
  have hconnN : IsPreconnected (connectedComponentIn N xc) :=
    isPreconnected_connectedComponentIn
  have himageB : (Subtype.val : C → X) '' connectedComponentIn N xc ⊆ B := by
    rintro _ ⟨w, hw, rfl⟩
    have hwN := connectedComponentIn_subset N xc hw
    exact (hsub w.property).resolve_left (hNO hwN).1
  have hsingle := hB _ himageB (hconnN.image _ continuous_subtype_val.continuousOn)
  have hzxeq : z.val = x := hsingle ⟨z, hzC, rfl⟩
    ⟨xc, mem_connectedComponentIn hxN, rfl⟩
  have hzxc : z = xc := Subtype.ext hzxeq
  have hxfront : xc ∈ frontier N := hzxc ▸ hzfront
  exact hxfront.2 (mem_interior_iff_mem_nhds.mpr hNnhds)

end CircleDomainRigidity

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Topology_ClopenNeighborhood
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Isolating a component by a clopen neighborhood

This is the compact-space step before the smooth contour construction:
a neighborhood containing a whole component contains a clopen
neighborhood of that component's base point. Applied in a closed
obstacle set, it isolates a singleton dust component.
-/

open Set

namespace CircleDomainRigidity

theorem exists_clopen_between_component_and_open
    {X : Type*} [TopologicalSpace X] [CompactSpace X] [T2Space X]
    (x : X) {O : Set X} (hO : IsOpen O) (hC : connectedComponent x ⊆ O) :
    ∃ V : Set X, IsClopen V ∧ x ∈ V ∧ V ⊆ O := by
  classical
  have hd : Disjoint Oᶜ (connectedComponent x) :=
    Set.disjoint_left.mpr (fun y hy hyC => hy (hC hyC))
  rw [connectedComponent_eq_iInter_isClopen x] at hd
  obtain ⟨s, hs⟩ := hO.isClosed_compl.isCompact.elim_finite_subfamily_closed
    (fun V : {V : Set X // IsClopen V ∧ x ∈ V} => V.val)
    (fun V => V.property.1.isClosed) (Set.disjoint_iff_inter_eq_empty.mp hd)
  refine ⟨⋂ V ∈ s, (V : Set X), isClopen_biInter_finset (fun V _ => V.property.1),
    mem_iInter₂.mpr (fun V _ => V.property.2), ?_⟩
  intro y hy
  by_contra hyO
  exact Set.disjoint_left.mp (Set.disjoint_iff_inter_eq_empty.mpr hs) hyO hy

/-- In particular, singleton components in a compact closed obstacle
have arbitrarily small relatively clopen neighborhoods. -/
theorem exists_clopen_neighborhood_of_singleton_component
    {X : Type*} [TopologicalSpace X] [CompactSpace X] [T2Space X]
    (x : X) (hC : connectedComponent x = {x}) {O : Set X}
    (hO : IsOpen O) (hx : x ∈ O) :
    ∃ V : Set X, IsClopen V ∧ x ∈ V ∧ V ⊆ O :=
  exists_clopen_between_component_and_open x hO (by simpa only [hC, singleton_subset_iff] using hx)

end CircleDomainRigidity

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Topology_ComponentLocalization
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Localizing nondegenerate components

Boundary bumping turns a nondegenerate continuum through a point into
one in any prescribed neighborhood. This is the localization used in
the lower-grid obstacle argument. Totally disconnected dust cannot
destroy a singleton component of a compact closed obstacle.
-/

open Set Topology

namespace CircleDomainRigidity

theorem exists_nontrivial_subcontinuum_in_open
    {X : Type*} [TopologicalSpace X] [T2Space X]
    {C U : Set X} (hcompact : IsCompact C) (hconn : IsConnected C)
    (hnt : C.Nontrivial) {x : X} (hx : x ∈ C) (hU : IsOpen U) (hxU : x ∈ U) :
    ∃ D : Set X, IsCompact D ∧ IsConnected D ∧ D.Nontrivial ∧ x ∈ D ∧ D ⊆ C ∩ U := by
  classical
  let : CompactSpace C := isCompact_iff_compactSpace.mp hcompact
  let : PreconnectedSpace C := Subtype.preconnectedSpace hconn.isPreconnected
  obtain ⟨y, hy, hyx⟩ := hnt.exists_ne x
  let xc : C := ⟨x, hx⟩
  let yc : C := ⟨y, hy⟩
  let O : Set C := (Subtype.val ⁻¹' U) ∩ {yc}ᶜ
  have hO : IsOpen O := (hU.preimage continuous_subtype_val).inter
    isClosed_singleton.isOpen_compl
  have hxO : xc ∈ O := ⟨hxU, fun heq => hyx (congrArg Subtype.val heq).symm⟩
  obtain ⟨N, hNnhds, hNclosed, hNO⟩ := exists_mem_nhds_isClosed_subset (hO.mem_nhds hxO)
  have hxN : xc ∈ N := mem_of_mem_nhds hNnhds
  have hNproper : N ≠ univ := by
    intro heq
    have hyN : yc ∈ N := by rw [heq]; trivial
    exact (hNO hyN).2 rfl
  obtain ⟨z, hz, hzfront⟩ := component_meets_frontier hNclosed hNproper hxN
  let K := connectedComponentIn N xc
  have hKclosed : IsClosed K := by
    change IsClosed (connectedComponentIn N xc)
    rw [connectedComponentIn_eq_image hxN]
    exact hNclosed.isClosedMap_subtype_val _ isClosed_connectedComponent
  have hKconn : IsConnected K := isConnected_connectedComponentIn_iff.mpr hxN
  let D : Set X := Subtype.val '' K
  have hxD : x ∈ D := ⟨xc, mem_connectedComponentIn hxN, rfl⟩
  have hzD : z.val ∈ D := ⟨z, hz, rfl⟩
  have hzx : z.val ≠ x := by
    intro heq
    have hzc : z = xc := Subtype.ext heq
    have hxfront : xc ∈ frontier N := hzc ▸ hzfront
    exact hxfront.2 (mem_interior_iff_mem_nhds.mpr hNnhds)
  refine ⟨D, hKclosed.isCompact.image continuous_subtype_val,
    hKconn.image _ continuous_subtype_val.continuousOn,
    ⟨x, hxD, z.val, hzD, hzx.symm⟩, hxD, ?_⟩
  rintro _ ⟨w, hw, rfl⟩
  exact ⟨w.property, (hNO (connectedComponentIn_subset N xc hw)).1⟩

/-- To rule out a nondegenerate component, it suffices to rule out small
subcontinua through the point in one open neighborhood. -/
theorem component_eq_singleton_of_local_no_continuum
    {X : Type*} [TopologicalSpace X] [CompactSpace X] [T2Space X]
    {F U : Set X} (hF : IsClosed F) {x : X} (hx : x ∈ F)
    (hU : IsOpen U) (hxU : x ∈ U)
    (hno : ∀ D : Set X, IsCompact D → IsConnected D → x ∈ D →
      D ⊆ F ∩ U → ¬ D.Nontrivial) :
    connectedComponentIn F x = {x} := by
  have hclosed : IsClosed (connectedComponentIn F x) := by
    rw [connectedComponentIn_eq_image hx]
    exact hF.isClosedMap_subtype_val _ isClosed_connectedComponent
  have hconn := isConnected_connectedComponentIn_iff.mpr hx
  have hsub : (connectedComponentIn F x).Subsingleton := by
    by_contra hn
    have hnt : (connectedComponentIn F x).Nontrivial := Set.not_subsingleton_iff.mp hn
    obtain ⟨D, hDcompact, hDconn, hDnt, hxD, hDsub⟩ :=
      exists_nontrivial_subcontinuum_in_open hclosed.isCompact hconn hnt
        (mem_connectedComponentIn hx) hU hxU
    exact hno D hDcompact hDconn hxD
      (fun y hy => ⟨connectedComponentIn_subset F x (hDsub hy).1, (hDsub hy).2⟩) hDnt
  exact hsub.eq_singleton_of_mem (mem_connectedComponentIn hx)

/-- Adding compact totally disconnected dust preserves every singleton
component of a closed obstacle and gives singleton components off it. -/
theorem component_union_dust_eq_singleton
    {X : Type*} [TopologicalSpace X] [CompactSpace X] [T2Space X]
    {F B : Set X} (hF : IsClosed F) (hB : IsClosed B)
    (htd : IsTotallyDisconnected B) {x : X} (hx : x ∈ F ∪ B)
    (hsing : x ∈ F → connectedComponentIn F x = {x}) :
    connectedComponentIn (F ∪ B) x = {x} := by
  let C := connectedComponentIn (F ∪ B) x
  have hclosed : IsClosed C := by
    change IsClosed (connectedComponentIn (F ∪ B) x)
    rw [connectedComponentIn_eq_image hx]
    exact (hF.union hB).isClosedMap_subtype_val _ isClosed_connectedComponent
  have hconn : IsConnected C := isConnected_connectedComponentIn_iff.mpr hx
  have hxC : x ∈ C := mem_connectedComponentIn hx
  have hsub : C.Subsingleton := by
    by_contra hn
    have hnt : C.Nontrivial := Set.not_subsingleton_iff.mp hn
    have hCF : C ⊆ F := continuum_subset_closed_of_totallyDisconnected
      hclosed.isCompact hconn hnt hF htd (connectedComponentIn_subset (F ∪ B) x)
    have hCsing : C ⊆ {x} := by
      rw [← hsing (hCF hxC)]
      exact hconn.isPreconnected.subset_connectedComponentIn hxC hCF
    exact hn (fun _ ha _ hb => (mem_singleton_iff.mp (hCsing ha)).trans
      (mem_singleton_iff.mp (hCsing hb)).symm)
  exact hsub.eq_singleton_of_mem hxC

/-- Near a point, a finite closed level union only uses the levels which
contain that point. A singleton component in this smaller union is
therefore a singleton component in the entire union. -/
theorem component_finite_union_eq_singleton
    {X ι : Type*} [TopologicalSpace X] [CompactSpace X] [T2Space X]
    (s : Finset ι) (H : ι → Set X) (hH : ∀ i ∈ s, IsClosed (H i))
    {x : X} (hx : x ∈ ⋃ i ∈ s, H i)
    (hpresent : connectedComponentIn (⋃ i ∈ s, ⋃ (_ : x ∈ H i), H i) x = {x}) :
    connectedComponentIn (⋃ i ∈ s, H i) x = {x} := by
  classical
  let F := ⋃ i ∈ s, H i
  let B := ⋃ i ∈ s.filter (fun i => x ∉ H i), H i
  have hF : IsClosed F := isClosed_biUnion_finset (fun i hi => hH i hi)
  have hB : IsClosed B := isClosed_biUnion_finset (fun i hi => hH i (Finset.mem_filter.mp hi).1)
  have hxB : x ∉ B := by
    simp only [B, mem_iUnion, exists_prop, Finset.mem_filter]
    rintro ⟨i, ⟨_, hxi⟩, hxi'⟩
    exact hxi hxi'
  apply component_eq_singleton_of_local_no_continuum hF hx hB.isOpen_compl hxB
  intro D hDcompact hDconn hxD hDsub hDnt
  have hsub : D ⊆ ⋃ i ∈ s, ⋃ (_ : x ∈ H i), H i := by
    intro y hy
    obtain ⟨i, hi, hyi⟩ := mem_iUnion₂.mp (hDsub hy).1
    have hxi : x ∈ H i := by
      by_contra hn
      exact (hDsub hy).2 (mem_iUnion₂.mpr ⟨i, Finset.mem_filter.mpr ⟨hi, hn⟩, hyi⟩)
    exact mem_iUnion₂.mpr ⟨i, hi, mem_iUnion.mpr ⟨hxi, hyi⟩⟩
  have hsingle : D ⊆ {x} := by
    rw [← hpresent]
    exact hDconn.isPreconnected.subset_connectedComponentIn hxD hsub
  exact hDnt.not_subsingleton (fun _ ha _ hb => (mem_singleton_iff.mp (hsingle ha)).trans
    (mem_singleton_iff.mp (hsingle hb)).symm)

end CircleDomainRigidity

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Topology_SmallPhysicalDisks
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions _root_.OAI.CircleDomainRigidity.finiteSphericalArea _root_.OAI.CircleDomainRigidity.sphereFirstCountableTopology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Small physical disks at singleton quotient components

A singleton component of a closed quotient obstacle has a compact relatively
clopen neighborhood inside any prescribed open neighborhood. Pulling it back
and applying the proved smooth contour construction gives actual physical
Jordan disks. The boundaries avoid the entire quotient obstacle, and hence
lie in the physical domain whenever that obstacle contains the collapsed
complementary components.
-/

open Set Function
open scoped Topology Manifold ContDiff

namespace CircleDomainRigidity

/-- The compact relatively clopen obstacle piece used before smoothing. -/
theorem exists_compact_piece_of_singleton_component
    {X : Type*} [TopologicalSpace X] [CompactSpace X] [T2Space X]
    {F V : Set X} (hF : IsClosed F) {x : X} (hx : x ∈ F)
    (hcomponent : connectedComponentIn F x = {x})
    (hV : IsOpen V) (hxV : x ∈ V) :
    ∃ A : Set X, IsCompact A ∧ x ∈ A ∧ A ⊆ F ∧ A ⊆ V ∧ IsClosed (F \ A) := by
  let : CompactSpace F := isCompact_iff_compactSpace.mp hF.isCompact
  let xf : F := ⟨x, hx⟩
  have hcomp : connectedComponent xf = {xf} := by
    apply Set.Subset.antisymm
    · intro y hy
      have hy' : y.val ∈ connectedComponentIn F x := by
        rw [connectedComponentIn_eq_image hx]
        exact ⟨y, hy, rfl⟩
      rw [hcomponent] at hy'
      exact mem_singleton_iff.mpr (Subtype.ext (mem_singleton_iff.mp hy'))
    · exact singleton_subset_iff.mpr mem_connectedComponent
  obtain ⟨B, hB, hxB, hBV⟩ := exists_clopen_neighborhood_of_singleton_component xf hcomp
    (hV.preimage continuous_subtype_val) hxV
  let A : Set X := Subtype.val '' B
  have hdiff : F \ A = Subtype.val '' Bᶜ := by
    ext y
    constructor
    · rintro ⟨hyF, hyA⟩
      exact ⟨⟨y, hyF⟩, fun h => hyA ⟨⟨y, hyF⟩, h, rfl⟩, rfl⟩
    · rintro ⟨y, hy, rfl⟩
      refine ⟨y.property, ?_⟩
      rintro ⟨z, hz, hzy⟩
      have hzy' : z = y := Subtype.ext hzy
      exact hy (hzy' ▸ hz)
  refine ⟨A, hB.isClosed.isCompact.image continuous_subtype_val,
    ⟨xf, hxB, rfl⟩, ?_, ?_, ?_⟩
  · rintro _ ⟨y, _, rfl⟩
    exact y.property
  · rintro _ ⟨y, hy, rfl⟩
    exact hBV hy
  · rw [hdiff]
    exact hF.isClosedMap_subtype_val _ hB.isOpen.isClosed_compl

/-- Finite smooth disk cover of the physical fiber at a singleton quotient
component. The connected unbounded complement condition is imposed on the
specified physical preimage, exactly where the filling argument uses it. -/
theorem exists_small_physical_disks_at_singleton_component
    (hsard : SmoothPlanarSard) (hschoenflies : PlanarSchoenflies)
    {X : Type*} [TopologicalSpace X] [CompactSpace X] [T2Space X]
    (π : Sphere → X) (hπ : Continuous π) {F V : Set X}
    (hF : IsClosed F) {x : X} (hx : x ∈ F)
    (hcomponent : connectedComponentIn F x = {x})
    (hV : IsOpen V) (hxV : x ∈ V) (hinfty : π OnePoint.infty ∉ V)
    (hVconn : IsPreconnected ((fun z : ℂ => π (z : Sphere)) ⁻¹' V)ᶜ)
    (hVunbounded : ¬ Bornology.IsBounded ((fun z : ℂ => π (z : Sphere)) ⁻¹' V)ᶜ)
    {G : Set Sphere} (hbad : ∀ p ∈ Gᶜ, π p ∈ F) :
    ∃ (f : ℂ → ℝ) (t : ℝ)
      (γ : ConnectedComponents {z // f z = t} → Circle → ℂ)
      (H : ConnectedComponents {z // f z = t} → ℂ ≃ₜ ℂ)
      (s : Set (ConnectedComponents {z // f z = t})),
      s.Finite ∧
      (∀ z : ℂ, π (z : Sphere) = x → z ∈ ⋃ i ∈ s, jordanInterior (H i)) ∧
      s.Pairwise (fun i j => Disjoint (closure (jordanInterior (H i)))
        (closure (jordanInterior (H j)))) ∧
      (∀ i ∈ s, closure (jordanInterior (H i)) ⊆
        (fun z : ℂ => π (z : Sphere)) ⁻¹' V) ∧
      ∀ i ∈ s, ContMDiff (𝓡 1) (𝓘(ℝ, ℂ)) ∞ (γ i) ∧
        Topology.IsEmbedding (γ i) ∧ frontier (jordanInterior (H i)) = range (γ i) ∧
        (∀ z ∈ frontier (jordanInterior (H i)), (z : Sphere) ∈ G ∧ π (z : Sphere) ∉ F) := by
  obtain ⟨A, hAc, hxA, hAF, hAV, hFA⟩ :=
    exists_compact_piece_of_singleton_component hF hx hcomponent hV hxV
  let q : ℂ → X := fun z => π (z : Sphere)
  have hq : Continuous q := hπ.comp OnePoint.continuous_coe
  have hAp : IsCompact (q ⁻¹' A) := by
    apply isCompact_finite_preimage (hAc.isClosed.preimage hπ)
    exact fun h => hinfty (hAV h)
  have hFp : IsClosed ((q ⁻¹' F) \ (q ⁻¹' A)) := by
    simpa only [preimage_sdiff] using hFA.preimage hq
  obtain ⟨f, t, γ, H, s, hs, hcov, hd, hinside, hcurves⟩ :=
    exists_finite_smooth_jordan_cover hsard hschoenflies hAp
      (preimage_mono hAF) hFp (hV.preimage hq) (preimage_mono hAV) hVconn hVunbounded
  refine ⟨f, t, γ, H, s, hs, ?_, hd, hinside, ?_⟩
  · intro z hz
    apply hcov
    change π (z : Sphere) ∈ A
    simpa only [hz] using hxA
  · intro i hi
    obtain ⟨hγsmooth, hγemb, hγfront, havoid⟩ := hcurves i hi
    refine ⟨hγsmooth, hγemb, hγfront, ?_⟩
    intro z hz
    have hnotF : π (z : Sphere) ∉ F := fun h => Set.disjoint_left.mp havoid hz h
    refine ⟨?_, hnotF⟩
    by_contra h
    exact hnotF (hbad _ h)

end CircleDomainRigidity

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Topology_SmallQuotientDisks
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions _root_.OAI.CircleDomainRigidity.finiteSphericalArea _root_.OAI.CircleDomainRigidity.sphereFirstCountableTopology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Smooth physical disks from the component quotient

These statements combine compact clopen isolation, actual contour selection,
the component quotient, and the infinity-chart argument. Connectedness and
unboundedness of the physical exterior are conclusions of the preceding
lemmas, not additional disk-selection hypotheses.
-/

open Set Function
open scoped Topology Manifold ContDiff

namespace CircleDomainRigidity

/-- The small physical disk construction for a singleton component of
the actual quotient obstacle. -/
theorem smoothPhysicalDiskCover_of_component_quotient
    (hsard : SmoothPlanarSard) (hschoenflies : PlanarSchoenflies)
    {X : Type*} [TopologicalSpace X] [CompactSpace X] [T2Space X]
    (G : Set Sphere) (π : Sphere → X) (hπ : Continuous π)
    (hclosed : IsClosedMap π) (hsurj : Surjective π)
    (hr : ∀ x y, π x = π y ↔
      x = y ∨ (x ∈ Gᶜ ∧ y ∈ connectedComponentIn Gᶜ x))
    {F V : Set X} (hF : IsClosed F) {x : X} (hx : x ∈ F)
    (hcomponent : connectedComponentIn F x = {x})
    (hV : IsOpen V) (hxV : x ∈ V) (hVconn : IsConnected Vᶜ)
    (hinfty : π OnePoint.infty ∉ closure V)
    (hbad : ∀ p ∈ Gᶜ, π p ∈ F) :
    SmoothPhysicalDiskCover π x V F G := by
  obtain ⟨hphysical, hunbounded⟩ :=
    physical_exterior_connected_unbounded_of_component_collapse G π hπ hclosed hsurj hr
      hV hVconn hinfty
  exact exists_small_physical_disks_at_singleton_component hsard hschoenflies
    π hπ hF hx hcomponent hV hxV (fun h => hinfty (subset_closure h))
      hphysical hunbounded hbad

end CircleDomainRigidity

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Topology_SinglePhysicalDisk
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions _root_.OAI.CircleDomainRigidity.finiteSphericalArea _root_.OAI.CircleDomainRigidity.sphereFirstCountableTopology
attribute [-simp] _root_.OAI.CircleDomainRigidity.CompactScalarModel.postcompose_coefficient _root_.OAI.CircleDomainRigidity.FiniteTransfer.coe_mem_sphericalCore _root_.OAI.CircleDomainRigidity.FiniteTransfer.coe_mem_sphericalDiskUnion _root_.OAI.CircleDomainRigidity.FiniteTransfer.infty_mem_cutoffCore _root_.OAI.CircleDomainRigidity.FiniteTransfer.infty_mem_sphericalCore _root_.OAI.CircleDomainRigidity.FiniteTransfer.infty_not_mem_sphericalDiskUnion _root_.OAI.CircleDomainRigidity.FiniteTransfer.realChartDomain_union _root_.OAI.CircleDomainRigidity.affineSphere_coe _root_.OAI.CircleDomainRigidity.affineSphere_infty _root_.OAI.CircleDomainRigidity.centeredJordanCoordinate_self _root_.OAI.CircleDomainRigidity.chartSymm_coe_apply _root_.OAI.CircleDomainRigidity.chart_coe_apply _root_.OAI.CircleDomainRigidity.chart_infty_apply _root_.OAI.CircleDomainRigidity.extendAtInfinity_coe _root_.OAI.CircleDomainRigidity.extendAtInfinity_infty _root_.OAI.CircleDomainRigidity.sphereInv_infty _root_.OAI.CircleDomainRigidity.sphereInv_sphereInv _root_.OAI.CircleDomainRigidity.sphereInv_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# A single smooth physical disk about a quotient singleton

Connectedness of the fiber upgrades the finite disjoint cover to a single
disk. The general open-family lemma does not need finiteness.
-/

open Set Function
open scoped Topology Manifold ContDiff

namespace CircleDomainRigidity

theorem exists_member_containing_connected_set
    {X I : Type*} [TopologicalSpace X] {S : Set X} (hS : IsConnected S)
    (U : I → Set X) (hU : ∀ i, IsOpen (U i))
    (hd : Pairwise (Disjoint on U)) (hcover : S ⊆ ⋃ i, U i) :
    ∃ i, S ⊆ U i := by
  classical
  obtain ⟨x, hx⟩ := hS.nonempty
  obtain ⟨i, hxi⟩ := mem_iUnion.mp (hcover hx)
  let V : Set X := ⋃ j ∈ ({i}ᶜ : Set I), U j
  have hV : IsOpen V := isOpen_biUnion (fun j _ => hU j)
  have hUV : Disjoint (U i) V := by
    apply Set.disjoint_left.mpr
    intro z hz hzV
    obtain ⟨j, hj, hzj⟩ := mem_iUnion₂.mp hzV
    exact Set.disjoint_left.mp (hd (fun h => hj (mem_singleton_iff.mpr h.symm))) hz hzj
  have hSC : S ⊆ U i ∪ V := by
    intro z hz
    obtain ⟨j, hzj⟩ := mem_iUnion.mp (hcover hz)
    by_cases hji : j = i
    · exact Or.inl (hji ▸ hzj)
    · exact Or.inr (mem_iUnion₂.mpr ⟨j, by simpa using hji, hzj⟩)
  rcases hS.isPreconnected.subset_or_subset (hU i) hV hUV hSC with h | h
  · exact ⟨i, h⟩
  · exact (Set.disjoint_left.mp hUV hxi (h hx)).elim

theorem isConnected_finite_fiber
    {X : Type*} (π : Sphere → X) (hfibers : ∀ x, IsConnected (π ⁻¹' {x}))
    {x : X} (hne : π OnePoint.infty ≠ x) :
    IsConnected {z : ℂ | π (z : Sphere) = x} := by
  have heq : ((↑) : ℂ → Sphere) '' {z : ℂ | π (z : Sphere) = x} = π ⁻¹' {x} := by
    ext p
    cases p using OnePoint.rec with
    | infty => simp [hne]
    | coe z => simp [OnePoint.coe_injective.mem_set_image]
  have hconn : IsConnected (((↑) : ℂ → Sphere) '' {z : ℂ | π (z : Sphere) = x}) :=
    heq.symm ▸ hfibers x
  refine ⟨?_, OnePoint.isOpenEmbedding_coe.isEmbedding.isInducing.isPreconnected_image.mp
    hconn.isPreconnected⟩
  obtain ⟨p, hp⟩ := hconn.nonempty
  obtain ⟨z, hz, _⟩ := hp
  exact ⟨z, hz⟩

/-- A finite disjoint disk cover of a connected physical fiber contains
one disk covering that entire fiber. -/
theorem SmoothPhysicalDiskCover.exists_single_disk
    {X : Type*} {π : Sphere → X} {x : X} {V F : Set X} {G : Set Sphere}
    (hcover : SmoothPhysicalDiskCover π x V F G)
    (hfiber : IsConnected {z : ℂ | π (z : Sphere) = x}) :
    ∃ (H : ℂ ≃ₜ ℂ) (γ : Circle → ℂ),
      {z : ℂ | π (z : Sphere) = x} ⊆ jordanInterior H ∧
      closure (jordanInterior H) ⊆ (fun z : ℂ => π (z : Sphere)) ⁻¹' V ∧
      ContMDiff (𝓡 1) (𝓘(ℝ, ℂ)) ∞ γ ∧ Topology.IsEmbedding γ ∧
      frontier (jordanInterior H) = range γ ∧
      ∀ z ∈ frontier (jordanInterior H), (z : Sphere) ∈ G ∧ π (z : Sphere) ∉ F := by
  classical
  obtain ⟨f, t, γ, H, s, _, hcov, hd, hinside, hcurves⟩ := hcover
  have hpair : Pairwise (Disjoint on fun i : s => jordanInterior (H i)) := by
    intro i j hij
    exact (hd i.property j.property (fun h => hij (Subtype.ext h))).mono
      subset_closure subset_closure
  have hcov' : {z : ℂ | π (z : Sphere) = x} ⊆ ⋃ i : s, jordanInterior (H i) := by
    intro z hz
    obtain ⟨i, hi, hzi⟩ := mem_iUnion₂.mp (hcov z hz)
    exact mem_iUnion.mpr ⟨⟨i, hi⟩, hzi⟩
  obtain ⟨i, hi⟩ := exists_member_containing_connected_set hfiber
    (fun i : s => jordanInterior (H i)) (fun i => jordanInterior_isOpen (H i)) hpair hcov'
  exact ⟨H i, γ i, hi, hinside i i.property, hcurves i i.property⟩

/-- Exact single-disk form of the small physical neighborhood statement
for the actual component quotient. -/
theorem exists_single_small_physical_disk
    (hsard : SmoothPlanarSard) (hschoenflies : PlanarSchoenflies)
    {X : Type*} [TopologicalSpace X] [CompactSpace X] [T2Space X]
    (G : Set Sphere) (π : Sphere → X) (hπ : Continuous π)
    (hclosed : IsClosedMap π) (hsurj : Surjective π)
    (hr : ∀ x y, π x = π y ↔
      x = y ∨ (x ∈ Gᶜ ∧ y ∈ connectedComponentIn Gᶜ x))
    {F V : Set X} (hF : IsClosed F) {x : X} (hx : x ∈ F)
    (hcomponent : connectedComponentIn F x = {x})
    (hV : IsOpen V) (hxV : x ∈ V) (hVconn : IsConnected Vᶜ)
    (hinfty : π OnePoint.infty ∉ closure V)
    (hbad : ∀ p ∈ Gᶜ, π p ∈ F) :
    ∃ (H : ℂ ≃ₜ ℂ) (γ : Circle → ℂ),
      {z : ℂ | π (z : Sphere) = x} ⊆ jordanInterior H ∧
      closure (jordanInterior H) ⊆ (fun z : ℂ => π (z : Sphere)) ⁻¹' V ∧
      ContMDiff (𝓡 1) (𝓘(ℝ, ℂ)) ∞ γ ∧ Topology.IsEmbedding γ ∧
      frontier (jordanInterior H) = range γ ∧
      ∀ z ∈ frontier (jordanInterior H), (z : Sphere) ∈ G ∧ π (z : Sphere) ∉ F := by
  have hcover := smoothPhysicalDiskCover_of_component_quotient hsard hschoenflies
    G π hπ hclosed hsurj hr hF hx hcomponent hV hxV hVconn hinfty hbad
  apply hcover.exists_single_disk
  apply isConnected_finite_fiber π (connected_fibers_of_component_collapse G π hsurj hr)
  intro heq
  exact hinfty (subset_closure (heq.symm ▸ hxV))

end CircleDomainRigidity

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Topology_SaturatedDisks
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions _root_.OAI.CircleDomainRigidity.finiteSphericalArea _root_.OAI.CircleDomainRigidity.sphereFirstCountableTopology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Saturation of physical Jordan interiors

A connected quotient fiber cannot cross a boundary consisting of singleton
fibers. Thus physical Jordan interiors whose boundaries lie in the original
domain are saturated, and project to open quotient neighborhoods. This is
the saturation assertion preceding the small-disks lemma in Section 1.
-/

open Set Function
open scoped Topology

namespace CircleDomainRigidity

theorem preimage_image_open_of_singleton_boundary_fibers
    {X Y : Type*} [TopologicalSpace X]
    (π : X → Y) (hfibers : ∀ y, IsPreconnected (π ⁻¹' {y}))
    {U : Set X} (hU : IsOpen U)
    (hsing : ∀ p ∈ frontier U, ∀ q, π q = π p → q = p) :
    π ⁻¹' (π '' U) = U := by
  apply Set.Subset.antisymm
  · rintro q ⟨p, hp, hpq⟩
    let K : Set X := π ⁻¹' {π p}
    have hpK : p ∈ K := rfl
    have hmiss : Disjoint K (frontier U) := by
      apply Set.disjoint_left.mpr
      intro z hz hzfront
      have hpz : p = z := hsing z hzfront p hz.symm
      have hpfront : p ∈ frontier U := hpz.symm ▸ hzfront
      rw [hU.frontier_eq] at hpfront
      exact hpfront.2 hp
    have hsplit : K ⊆ U ∨ K ⊆ (closure U)ᶜ := by
      apply (hfibers (π p)).subset_or_subset hU isClosed_closure.isOpen_compl
      · exact Set.disjoint_left.mpr (fun z hz hz' => hz' (subset_closure hz))
      · intro z hz
        by_cases hzU : z ∈ U
        · exact Or.inl hzU
        · right
          intro hzcl
          apply Set.disjoint_left.mp hmiss hz
          rw [hU.frontier_eq]
          exact ⟨hzcl, hzU⟩
    rcases hsplit with hin | hout
    · exact hin hpq.symm
    · exact (hout hpK (subset_closure hp)).elim
  · exact subset_preimage_image π U

/-- Physical Jordan disks with boundary in the domain are saturated for
the actual component-collapse quotient. -/
theorem preimage_image_jordanInterior_of_component_collapse
    {Y : Type*} (G : Set Sphere) (π : Sphere → Y) (hsurj : Surjective π)
    (hr : ∀ x y, π x = π y ↔
      x = y ∨ (x ∈ Gᶜ ∧ y ∈ connectedComponentIn Gᶜ x))
    (H : ℂ ≃ₜ ℂ) (hboundary : ∀ z ∈ frontier (jordanInterior H), (z : Sphere) ∈ G) :
    π ⁻¹' (π '' (((↑) : ℂ → Sphere) '' jordanInterior H)) =
      ((↑) : ℂ → Sphere) '' jordanInterior H := by
  apply preimage_image_open_of_singleton_boundary_fibers π
    (fun y => (connected_fibers_of_component_collapse G π hsurj hr y).isPreconnected)
    (OnePoint.isOpen_image_coe.mpr (jordanInterior_isOpen H))
  intro p hp q hqp
  rw [frontier_sphere_image_jordanInterior] at hp
  obtain ⟨z, hz, rfl⟩ := hp
  rcases (hr (z : Sphere) q).mp hqp.symm with heq | ⟨hznot, _⟩
  · exact heq.symm
  · exact (hznot (hboundary z hz)).elim

/-- The saturated physical disk projects to an open quotient neighborhood. -/
theorem isOpen_image_jordanInterior_of_component_collapse
    {Y : Type*} [TopologicalSpace Y]
    (G : Set Sphere) (π : Sphere → Y) (hπ : Continuous π)
    (hclosed : IsClosedMap π) (hsurj : Surjective π)
    (hr : ∀ x y, π x = π y ↔
      x = y ∨ (x ∈ Gᶜ ∧ y ∈ connectedComponentIn Gᶜ x))
    (H : ℂ ≃ₜ ℂ) (hboundary : ∀ z ∈ frontier (jordanInterior H), (z : Sphere) ∈ G) :
    IsOpen (π '' (((↑) : ℂ → Sphere) '' jordanInterior H)) := by
  apply (hclosed.isQuotientMap hπ hsurj).isOpen_preimage.mp
  rw [preimage_image_jordanInterior_of_component_collapse G π hsurj hr H hboundary]
  exact OnePoint.isOpen_image_coe.mpr (jordanInterior_isOpen H)

end CircleDomainRigidity

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Selection_PhysicalTerminals
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonEmbeddedArc.Arc.graphVertices_finite _root_.OAI.CannonMobius.sphereMetric _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions _root_.OAI.CircleDomainRigidity.finiteSphericalArea _root_.OAI.CircleDomainRigidity.sphereFirstCountableTopology
attribute [-simp] _root_.OAI.CircleDomainRigidity.CompactScalarModel.postcompose_coefficient _root_.OAI.CircleDomainRigidity.FiniteTransfer.coe_mem_sphericalCore _root_.OAI.CircleDomainRigidity.FiniteTransfer.coe_mem_sphericalDiskUnion _root_.OAI.CircleDomainRigidity.FiniteTransfer.infty_mem_cutoffCore _root_.OAI.CircleDomainRigidity.FiniteTransfer.infty_mem_sphericalCore _root_.OAI.CircleDomainRigidity.FiniteTransfer.infty_not_mem_sphericalDiskUnion _root_.OAI.CircleDomainRigidity.FiniteTransfer.realChartDomain_union _root_.OAI.CircleDomainRigidity.affineSphere_coe _root_.OAI.CircleDomainRigidity.affineSphere_infty _root_.OAI.CircleDomainRigidity.centeredJordanCoordinate_self _root_.OAI.CircleDomainRigidity.chartSymm_coe_apply _root_.OAI.CircleDomainRigidity.chart_coe_apply _root_.OAI.CircleDomainRigidity.chart_infty_apply _root_.OAI.CircleDomainRigidity.extendAtInfinity_coe _root_.OAI.CircleDomainRigidity.extendAtInfinity_infty _root_.OAI.CircleDomainRigidity.sphereInv_infty _root_.OAI.CircleDomainRigidity.sphereInv_sphereInv _root_.OAI.CircleDomainRigidity.sphereInv_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Physical terminal disks and their staircase oscillations

A finite set of quotient dust points is surrounded by disjoint smooth
physical Jordan disks, with whole fibers inside the disks and boundaries
in the physical domain. The disks can be confined to prescribed
neighborhoods. Liminf and limsup bounds on those neighborhoods give the
staircase oscillation bound `a + 4h`, uniformly in width and shift.
-/

open Set Filter Function Metric
open scoped Topology Manifold ContDiff

namespace CircleDomainRigidity.FiniteTransfer

/-- Contours chosen in disjoint connected-complement containers have
disjoint physical closures. Total disconnectedness supplies the singleton
component hypothesis of the single-disk construction. -/
theorem exists_physical_terminal_disks_in_disjoint_containers
    (hsard : SmoothPlanarSard) (hschoenflies : PlanarSchoenflies)
    {I : Type*} (G : Set Sphere) (π : Sphere → Sphere)
    (hπ : Continuous π) (hclosed : IsClosedMap π) (hsurj : Surjective π)
    (hr : ∀ x y, π x = π y ↔
      x = y ∨ (x ∈ Gᶜ ∧ y ∈ connectedComponentIn Gᶜ x))
    {B : Set Sphere} (hB : IsClosed B) (hTD : IsTotallyDisconnected B)
    (hbad : ∀ x ∈ Gᶜ, π x ∈ B)
    (p : I → Sphere) (hpB : ∀ i, p i ∈ B) (V : I → Set Sphere)
    (hV : ∀ i, IsOpen (V i)) (hpV : ∀ i, p i ∈ V i)
    (hVconn : ∀ i, IsConnected (V i)ᶜ)
    (hinfty : ∀ i, π OnePoint.infty ∉ closure (V i))
    (hdisj : Pairwise (Disjoint on V)) :
    Nonempty (PhysicalTerminalDisks G π B p V) := by
  classical
  have hcomponent (i : I) : connectedComponentIn B (p i) = {p i} :=
    (hTD _ (connectedComponentIn_subset B (p i))
      isPreconnected_connectedComponentIn).eq_singleton_of_mem
        (mem_connectedComponentIn (hpB i))
  have hsingle (i : I) := exists_single_small_physical_disk
    hsard hschoenflies G π hπ hclosed hsurj hr hB (hpB i)
      (hcomponent i) (hV i) (hpV i) (hVconn i) (hinfty i) hbad
  choose H γ hH using hsingle
  refine ⟨⟨H, γ, fun i => (hH i).1, fun i => (hH i).2.1, ?_,
    fun i => (hH i).2.2.1, fun i => (hH i).2.2.2.1,
    fun i => (hH i).2.2.2.2.1, fun i => (hH i).2.2.2.2.2⟩⟩
  intro i j hij
  exact ((hdisj hij).preimage (fun z : ℂ => π (z : Sphere))).mono
    (hH i).2.1 (hH j).2.1

/-- Finite prescribed neighborhoods can be replaced by disjoint smaller
connected-complement containers. The exclusion of the infinity fiber is
necessary for bounded physical terminal disks. -/
theorem exists_disjoint_physical_terminal_disks
    (hsard : SmoothPlanarSard) (hschoenflies : PlanarSchoenflies)
    {I : Type*} [Fintype I] (G : Set Sphere) (π : Sphere → Sphere)
    (hπ : Continuous π) (hclosed : IsClosedMap π) (hsurj : Surjective π)
    (hr : ∀ x y, π x = π y ↔
      x = y ∨ (x ∈ Gᶜ ∧ y ∈ connectedComponentIn Gᶜ x))
    {B : Set Sphere} (hB : IsClosed B) (hTD : IsTotallyDisconnected B)
    (hbad : ∀ x ∈ Gᶜ, π x ∈ B)
    (p : I → Sphere) (hp : Injective p) (hpB : ∀ i, p i ∈ B)
    (hinfty : ∀ i, p i ≠ π OnePoint.infty)
    (O : I → Set Sphere) (hO : ∀ i, O i ∈ 𝓝 (p i)) :
    Nonempty (PhysicalTerminalDisks G π B p O) := by
  classical
  have hdisj : Pairwise (Disjoint on fun i => ({p i} : Set Sphere)) := by
    intro i j hij
    exact disjoint_singleton.mpr (fun h => hij (hp h))
  have hn : Pairwise (Disjoint on fun i => 𝓝ˢ ({p i} : Set Sphere)) := by
    intro i j hij
    exact disjoint_nhdsSet_nhdsSet isClosed_singleton isClosed_singleton (hdisj hij)
  obtain ⟨W, hW, hWd⟩ := hn.exists_mem_filter_basis_of_disjoint
    (fun i => hasBasis_nhdsSet ({p i} : Set Sphere))
  have hsmall (i : I) : ∃ V : Set Sphere, IsOpen V ∧ p i ∈ V ∧
      closure V ⊆ W i ∩ interior (O i) ∩ ({π OnePoint.infty} : Set Sphere)ᶜ ∧
      IsConnected Vᶜ := by
    apply exists_sphere_neighborhood_connected_compl
      (((hW i).1.inter isOpen_interior).inter isClosed_singleton.isOpen_compl)
    exact ⟨⟨(hW i).2 (mem_singleton _), mem_interior_iff_mem_nhds.mpr (hO i)⟩,
      by simpa using hinfty i⟩
  choose V hV hpV hsub hconn using hsmall
  have hVd : Pairwise (Disjoint on V) := by
    intro i j hij
    exact (hWd hij).mono (fun _ hx => (hsub i (subset_closure hx)).1.1)
      (fun _ hx => (hsub j (subset_closure hx)).1.1)
  obtain ⟨D⟩ := exists_physical_terminal_disks_in_disjoint_containers
    hsard hschoenflies G π hπ hclosed hsurj hr hB hTD hbad p hpB
      V hV hpV hconn (fun i hi => (hsub i hi).2 (mem_singleton _)) hVd
  refine ⟨{ D with closure_subset := ?_ }⟩
  intro i z hz
  change π (z : Sphere) ∈ O i
  exact (interior_subset : interior (O i) ⊆ O i)
    (hsub i (subset_closure (D.closure_subset i hz))).1.2

attribute [local instance] sphereMetric

/-- Actual smooth terminal boundaries obey the enlarged-band staircase
estimate, for all active coordinates simultaneously and for every width
and shift. `hphysical` records that physical points in the prescribed
neighborhood are in the chosen real-branch domain. The neighborhoods may
therefore also impose all desired singularity exclusions. -/
theorem exists_physical_terminals_with_uniform_staircase_oscillation
    (hsard : SmoothPlanarSard) (hschoenflies : PlanarSchoenflies)
    {I J : Type*} [Fintype I] [Fintype J]
    (G : Set Sphere) (π : Sphere → Sphere)
    (hπ : Continuous π) (hclosed : IsClosedMap π) (hsurj : Surjective π)
    (hr : ∀ x y, π x = π y ↔
      x = y ∨ (x ∈ Gᶜ ∧ y ∈ connectedComponentIn Gᶜ x))
    {B : Set Sphere} (hB : IsClosed B) (hTD : IsTotallyDisconnected B)
    (hbad : ∀ x ∈ Gᶜ, π x ∈ B)
    (p : I → Sphere) (hp : Injective p) (hpB : ∀ i, p i ∈ B)
    (hinfty : ∀ i, p i ≠ π OnePoint.infty)
    (O : I → Set Sphere) (hO : ∀ i, O i ∈ 𝓝 (p i))
    (U : I → Set Sphere) (f : I → J → Sphere → ℝ) (M : I → J → ℝ)
    (hM : ∀ i j y, y ∈ U i → |f i j y| ≤ M i j)
    (hphysical : ∀ (i : I) (z : ℂ), (z : Sphere) ∈ G → π (z : Sphere) ∈ O i →
      π (z : Sphere) ∈ U i)
    (active : I → J → Prop) (a : I → J → ℝ)
    (hbudget : ∀ i j, active i j →
      limsup (f i j) (𝓝[U i] (p i)) - liminf (f i j) (𝓝[U i] (p i)) ≤ a i j)
    {h : ℝ} (hh : 0 < h) :
    ∃ D : PhysicalTerminalDisks G π B p O,
      ∀ i j, active i j → ∀ δ θ : ℝ,
        ∀ x ∈ frontier (jordanInterior (D.H i)),
        ∀ y ∈ frontier (jordanInterior (D.H i)),
          |shiftedStaircase h δ θ (f i j (π (x : Sphere))) -
            shiftedStaircase h δ θ (f i j (π (y : Sphere)))| ≤ a i j + 4 * h := by
  classical
  obtain ⟨r, hrpos, hrO, _, hosc⟩ :=
    exists_terminal_balls_with_uniform_staircase_oscillation p hp O hO
      (fun _ => 1) (fun _ => zero_lt_one) U f M hM active a hbudget hh
  obtain ⟨D⟩ := exists_disjoint_physical_terminal_disks hsard hschoenflies
    G π hπ hclosed hsurj hr hB hTD hbad p hp hpB hinfty
      (fun i => ball (p i) (r i)) (fun i => ball_mem_nhds (p i) (hrpos i).1)
  let D' : PhysicalTerminalDisks G π B p O :=
    { D with closure_subset := fun i z hz => hrO i (ball_subset_closedBall
      (D.closure_subset i hz)) }
  refine ⟨D', ?_⟩
  intro i j hj δ θ x hx y hy
  have hxball : π (x : Sphere) ∈ closedBall (p i) (r i) :=
    ball_subset_closedBall (D.closure_subset i (frontier_subset_closure hx))
  have hyball : π (y : Sphere) ∈ closedBall (p i) (r i) :=
    ball_subset_closedBall (D.closure_subset i (frontier_subset_closure hy))
  exact hosc i j hj δ θ (π (x : Sphere))
    ⟨hxball, hphysical i x (D.frontier_good i x hx).1 (hrO i hxball)⟩
    (π (y : Sphere))
    ⟨hyball, hphysical i y (D.frontier_good i y hy).1 (hrO i hyball)⟩

end CircleDomainRigidity.FiniteTransfer

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Uniformization_FiniteCompletion
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions _root_.OAI.CircleDomainRigidity.finiteSphericalArea _root_.OAI.CircleDomainRigidity.sphereFirstCountableTopology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# The retained core and completed domain of a finite disk construction

The core is the spherical complement of all terminal and filling disks.
If the disks cover the preimage of the quotient dust, the core is a compact
subset of the original domain. Filling the second family leaves precisely
the complement of the terminal interiors. This completed compact set has
the open neighborhood consisting of the original domain and the filling
interiors. In a finite chart its bounded closed pieces are compact, even
though the entire planar exterior is unbounded.

The final statements apply the actual finite patching construction to this
open neighborhood and recover local agreement on the retained core.
-/

open Set Filter Function Metric
open scoped Topology ContDiff

namespace CircleDomainRigidity.FiniteTransfer

/-- Covering the actual preimage of the dust removes every point outside
the original domain. -/
theorem completionCore_subset_domain {I J : Type*}
    (T : I → ℂ ≃ₜ ℂ) (F : J → ℂ ≃ₜ ℂ)
    (G B : Set Sphere) (π : Sphere → Sphere)
    (hbad : ∀ x ∈ Gᶜ, π x ∈ B)
    (hcover : π ⁻¹' B ⊆ sphericalDiskUnion T ∪ sphericalDiskUnion F) :
    completionCore T F ⊆ G := by
  intro x hx
  by_contra hxG
  exact hx (hcover (hbad x hxG))

/-- Terminal boundaries in the original domain force whole quotient
fibers to stay on one side, so the union of terminal interiors is saturated. -/
theorem preimage_image_sphericalDiskUnion
    {I : Type*} (T : I → ℂ ≃ₜ ℂ) (G : Set Sphere) (π : Sphere → Sphere)
    (hsurj : Surjective π)
    (hr : ∀ x y, π x = π y ↔
      x = y ∨ (x ∈ Gᶜ ∧ y ∈ connectedComponentIn Gᶜ x))
    (hboundary : ∀ i z, z ∈ frontier (jordanInterior (T i)) → (z : Sphere) ∈ G) :
    π ⁻¹' (π '' sphericalDiskUnion T) = sphericalDiskUnion T := by
  apply Set.Subset.antisymm
  · rintro x ⟨y, hy, heq⟩
    obtain ⟨i, hi⟩ := mem_iUnion.mp hy
    have hx : x ∈ π ⁻¹' (π '' (((↑) : ℂ → Sphere) '' jordanInterior (T i))) :=
      ⟨y, hi, heq⟩
    rw [preimage_image_jordanInterior_of_component_collapse G π hsurj hr (T i)
      (hboundary i)] at hx
    exact mem_iUnion.mpr ⟨i, hx⟩
  · exact subset_preimage_image π _

/-- Filling the quotient dust left after the terminal interiors covers
the complete physical dust preimage. Saturation, rather than just fiber
representative selection, is what makes this implication valid. -/
theorem dust_preimage_covered_of_remainder_cover
    {I J : Type*} (T : I → ℂ ≃ₜ ℂ) (F : J → ℂ ≃ₜ ℂ)
    (G B : Set Sphere) (π : Sphere → Sphere) (hsurj : Surjective π)
    (hr : ∀ x y, π x = π y ↔
      x = y ∨ (x ∈ Gᶜ ∧ y ∈ connectedComponentIn Gᶜ x))
    (hboundary : ∀ i z, z ∈ frontier (jordanInterior (T i)) → (z : Sphere) ∈ G)
    (hfill : π ⁻¹' (B \ (π '' sphericalDiskUnion T)) ⊆ sphericalDiskUnion F) :
    π ⁻¹' B ⊆ sphericalDiskUnion T ∪ sphericalDiskUnion F := by
  intro x hxB
  by_cases hxT : π x ∈ π '' sphericalDiskUnion T
  · left
    have hx : x ∈ π ⁻¹' (π '' sphericalDiskUnion T) := hxT
    rwa [preimage_image_sphericalDiskUnion T G π hsurj hr hboundary] at hx
  · exact Or.inr (hfill ⟨hxB, hxT⟩)

/-- A physical finite-chart filling cover supplies the spherical cover
as soon as the quotient remainder omits the infinity fiber. -/
theorem spherical_remainder_cover_of_physical_cover
    {I J : Type*} (T : I → ℂ ≃ₜ ℂ) (F : J → ℂ ≃ₜ ℂ)
    (B : Set Sphere) (π : Sphere → Sphere)
    (hinfty : π OnePoint.infty ∉ B \ (π '' sphericalDiskUnion T))
    (hfill : (fun z : ℂ => π (z : Sphere)) ⁻¹' (B \ (π '' sphericalDiskUnion T)) ⊆
      ⋃ j, jordanInterior (F j)) :
    π ⁻¹' (B \ (π '' sphericalDiskUnion T)) ⊆ sphericalDiskUnion F := by
  intro x hx
  cases x using OnePoint.rec with
  | infty => exact (hinfty hx).elim
  | coe z =>
    obtain ⟨j, hj⟩ := mem_iUnion.mp (hfill hx)
    exact (coe_mem_sphericalDiskUnion F z).mpr ⟨j, hj⟩

/-- No disjointness is needed for this useful containment: every point
left after deleting the terminals is either physical or inside a filling. -/
theorem completedRegion_subset_extension_domain {I J : Type*}
    (T : I → ℂ ≃ₜ ℂ) (F : J → ℂ ≃ₜ ℂ)
    (G B : Set Sphere) (π : Sphere → Sphere)
    (hbad : ∀ x ∈ Gᶜ, π x ∈ B)
    (hcover : π ⁻¹' B ⊆ sphericalDiskUnion T ∪ sphericalDiskUnion F) :
    completedRegion T ⊆ G ∪ sphericalDiskUnion F := by
  intro x hx
  by_cases hxG : x ∈ G
  · exact Or.inl hxG
  · rcases hcover (hbad x hxG) with hT | hF
    · exact (hx hT).elim
    · exact Or.inr hF

end CircleDomainRigidity.FiniteTransfer

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Transfer_CoreGeometry
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonMobius.sphereMetric _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions _root_.OAI.CircleDomainRigidity.finiteSphericalArea _root_.OAI.CircleDomainRigidity.sphereFirstCountableTopology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Keeping the selected physical core away from all terminal disks

A closed planar core extends across infinity to a compact spherical
core. Its quotient image is disjoint from the quotient dust. Thus the
terminal and filling neighborhoods can be chosen away from the entire
retained core. Compact planar tail pieces suffice for the metric step.
-/

open Set Filter Function Metric
open scoped Topology ContDiff

noncomputable section

namespace CircleDomainRigidity.FiniteTransfer

theorem isCompact_sphericalCore {K : Set (ℝ × ℝ)} (hK : IsClosed K) :
    IsCompact (sphericalCore K) := by
  apply IsClosed.isCompact
  exact (OnePoint.isOpen_image_coe.mpr
    (hK.isOpen_compl.preimage Complex.equivRealProdCLM.continuous)).isClosed_compl

theorem sphericalCore_subset_domain
    {G : Set Sphere} {K : Set (ℝ × ℝ)} (hinfty : OnePoint.infty ∈ G)
    (hKG : ∀ z : ℂ, Complex.equivRealProdCLM z ∈ K → (z : Sphere) ∈ G) :
    sphericalCore K ⊆ G := by
  intro x hx
  cases x using OnePoint.rec with
  | infty => exact hinfty
  | coe z => exact hKG z ((coe_mem_sphericalCore K z).mp hx)

/-- The quotient image of any retained physical core misses every
collapsed complementary component. -/
theorem quotient_core_disjoint_dust
    {G C : Set Sphere} (π : Sphere → Sphere) (hCG : C ⊆ G)
    (hr : ∀ x y, π x = π y ↔
      x = y ∨ (x ∈ Gᶜ ∧ y ∈ connectedComponentIn Gᶜ x)) :
    Disjoint (π '' C) (π '' Gᶜ) := by
  apply Set.disjoint_left.mpr
  rintro _ ⟨x, hx, rfl⟩ ⟨y, hy, heq⟩
  rcases (hr x y).mp heq.symm with hxy | hxG
  · exact hy (hxy ▸ hCG hx)
  · exact hxG.1 (hCG hx)

/-- The complement of the compact quotient image is an open neighborhood
of all dust points, whose full physical preimage avoids the core. -/
theorem quotient_core_safe_open
    {G C : Set Sphere} (π : Sphere → Sphere) (hπ : Continuous π)
    (hC : IsCompact C) (hCG : C ⊆ G)
    (hr : ∀ x y, π x = π y ↔
      x = y ∨ (x ∈ Gᶜ ∧ y ∈ connectedComponentIn Gᶜ x)) :
    IsOpen (π '' C)ᶜ ∧ π '' Gᶜ ⊆ (π '' C)ᶜ ∧
      Disjoint (π ⁻¹' (π '' C)ᶜ) C := by
  refine ⟨(hC.image hπ).isClosed.isOpen_compl, ?_, ?_⟩
  · exact Set.disjoint_left.mp (quotient_core_disjoint_dust π hCG hr).symm
  · exact Set.disjoint_left.mpr (fun x hx hc => hx ⟨x, hc, rfl⟩)

/-- Actual terminal disks in the prescribed quotient neighborhoods avoid
the retained core, including their boundaries. -/
theorem PhysicalTerminalDisks.closure_disjoint_core
    {I : Type*} {G B C : Set Sphere} {π : Sphere → Sphere}
    {p : I → Sphere} {O : I → Set Sphere} (D : PhysicalTerminalDisks G π B p O)
    (hO : ∀ i, O i ⊆ (π '' C)ᶜ) (i : I) :
    Disjoint (((↑) : ℂ → Sphere) '' closure (jordanInterior (D.H i))) C := by
  apply Set.disjoint_left.mpr
  rintro _ ⟨z, hz, rfl⟩ hc
  exact hO i (D.closure_subset i hz) ⟨(z : Sphere), hc, rfl⟩

end CircleDomainRigidity.FiniteTransfer

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Sobolev_CircleEnergy
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Localized energy for periodic differentials

Agreement of circle maps near the retained core implies agreement of
their intrinsic differentials. Original L² energy controls the entire
unbounded core; smoothness on a compact tail controls the remainder.
-/

open Set Filter MeasureTheory Finset
open scoped Topology ContDiff Matrix.Norms.Elementwise

noncomputable section

namespace CircleDomainRigidity.FiniteTransfer

theorem fieldEnergy_spherical (v : (ℝ × ℝ) → ℝ × ℝ) (z : ℝ × ℝ) :
    fieldEnergy v (fun z => sphericalMetricFactor z • 1) z = (v z).1 ^ 2 + (v z).2 ^ 2 := by
  unfold fieldEnergy
  rw [covectorEnergy_eq_matrixEnergy,
    matrixEnergy_pos_smul _ Matrix.PosDef.one (sphericalMetricFactor_pos z),
    ← covectorEnergy_eq_matrixEnergy, covectorEnergy_identity]

theorem integrable_fieldEnergy_spherical_of_memLp
    {μ : Measure (ℝ × ℝ)} {v : (ℝ × ℝ) → ℝ × ℝ} (hv : MemLp v 2 μ) :
    Integrable (fieldEnergy v (fun z => sphericalMetricFactor z • 1)) μ := by
  have hx := (ContinuousLinearMap.fst ℝ ℝ ℝ).comp_memLp' hv
  have hy := (ContinuousLinearMap.snd ℝ ℝ ℝ).comp_memLp' hv
  have hxx : MemLp (fun z => (v z).1 * (v z).1) 1 μ := hx.mul hx
  have hyy : MemLp (fun z => (v z).2 * (v z).2) 1 μ := hy.mul hy
  have hi := (memLp_one_iff_integrable.mp hxx).add (memLp_one_iff_integrable.mp hyy)
  exact hi.congr (Eventually.of_forall fun z => by
    simpa only [pow_two, Pi.add_apply] using (fieldEnergy_spherical v z).symm)

end CircleDomainRigidity.FiniteTransfer

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Rigidity_MaskTopology
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Masks away from their retained boundaries

A connected filling cap disjoint from the mask boundary is wholly on
one side. Away from that boundary, extending a circle coordinate by zero
outside the mask is smooth and its intrinsic differential is exactly
the indicated covector.
-/

open Set Filter Function
open scoped Topology ContDiff

noncomputable section

namespace CircleDomainRigidity.FiniteTransfer

theorem maskCircleMap_eventuallyEq_inside
    {X : Type*} [TopologicalSpace X] (M : Set X) (f : X → UnitAddCircle)
    {x : X} (hx : x ∈ interior M) : maskCircleMap M f =ᶠ[𝓝 x] f := by
  filter_upwards [isOpen_interior.mem_nhds hx] with y hy
  simp only [maskCircleMap, ite_eq_left (interior_subset hy)]

theorem maskCircleMap_eventuallyEq_outside
    {X : Type*} [TopologicalSpace X] {M : Set X} (hM : IsClosed M) (f : X → UnitAddCircle)
    {x : X} (hx : x ∉ M) : maskCircleMap M f =ᶠ[𝓝 x] fun _ => 0 := by
  filter_upwards [hM.isOpen_compl.mem_nhds hx] with y hy
  simp only [maskCircleMap, ite_eq_right hy]

theorem circleGradient_zero (x : ℝ × ℝ) : circleGradient (fun _ => 0) x = 0 := by
  have heq : (fun _ : ℝ × ℝ => ((0 : ℝ) : UnitAddCircle)) =ᶠ[𝓝 x] fun _ => 0 := by simp
  simpa only [planarGradient_const] using
    circleGradient_eq_lift continuousAt_const continuousAt_const heq

theorem circleGradient_maskCircleMap
    {M : Set (ℝ × ℝ)} (hM : IsClosed M) (f : (ℝ × ℝ) → UnitAddCircle)
    {x : ℝ × ℝ} (hx : x ∉ frontier M) :
    circleGradient (maskCircleMap M f) x = M.indicator (circleGradient f) x := by
  by_cases hxM : x ∈ M
  · have hxi : x ∈ interior M := (mem_interior_iff_notMem_frontier hxM).mpr hx
    rw [circleGradient_congr_of_eventuallyEq (maskCircleMap_eventuallyEq_inside M f hxi),
      indicator_of_mem hxM]
  · rw [circleGradient_congr_of_eventuallyEq (maskCircleMap_eventuallyEq_outside hM f hxM),
      circleGradient_zero, indicator_of_notMem hxM]

theorem smoothCircleOn_mask_off_frontier
    {M G : Set (ℝ × ℝ)} (hM : IsClosed M) {f : (ℝ × ℝ) → UnitAddCircle}
    (hf : SmoothCircleOn f (G ∩ interior M)) :
    SmoothCircleOn (maskCircleMap M f) (G \ frontier M) := by
  apply smoothCircleOn_iff_local_lifts.mpr
  intro x hx
  by_cases hxM : x ∈ M
  · have hxi : x ∈ interior M := (mem_interior_iff_notMem_frontier hxM).mpr hx.2
    obtain ⟨u, hu, hproj⟩ := smoothCircleOn_iff_local_lifts.mp hf x ⟨hx.1, hxi⟩
    exact ⟨u, hu, hproj.trans (maskCircleMap_eventuallyEq_inside M f hxi).symm⟩
  · refine ⟨fun _ => 0, contDiffAt_const, ?_⟩
    simpa only [AddCircle.coe_zero] using (maskCircleMap_eventuallyEq_outside hM f hxM).symm

theorem circleWedges_maskCircleMap_eq
    {n : ℕ} (M : Fin n → Set (ℝ × ℝ)) (hM : ∀ i, IsClosed (M i))
    (f : Fin n → (ℝ × ℝ) → UnitAddCircle) {z : ℝ × ℝ}
    (hz : ∀ i, z ∉ frontier (M i)) :
    circleWedges (fun i => maskCircleMap (M i) (f i)) z = maskedCircleWedges M f z := by
  rw [circleWedges, fieldWedges_eq_sum_upperPairs]
  apply Finset.sum_congr rfl
  intro p _
  rw [circleGradient_maskCircleMap (hM _) _ (hz _),
    circleGradient_maskCircleMap (hM _) _ (hz _)]

theorem smoothCircleOn_masks_off_boundaries
    {n : ℕ} {G : Set (ℝ × ℝ)} (M : Fin n → Set (ℝ × ℝ)) (hM : ∀ i, IsClosed (M i))
    (f : Fin n → (ℝ × ℝ) → UnitAddCircle)
    (hf : ∀ i, SmoothCircleOn (f i) (G ∩ interior (M i))) :
    ∀ i, SmoothCircleOn (maskCircleMap (M i) (f i)) (G \ ⋃ j, frontier (M j)) := by
  intro i x hx a ha
  exact smoothCircleOn_mask_off_frontier (hM i) (hf i) x
    ⟨hx.1, fun h => hx.2 (mem_iUnion.mpr ⟨i, h⟩)⟩ a ha

end CircleDomainRigidity.FiniteTransfer

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Rigidity_MaskedCofiniteMetric
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Masked circle energy on a completion containing infinity

Only the closure of the tail needs smooth coordinate branches. This
allows every mask boundary to stay inside the retained core, while the
whole completed region may be unbounded in the finite chart.
-/

open Set Filter MeasureTheory Finset
open scoped Topology ContDiff Matrix.Norms.Elementwise

noncomputable section

namespace CircleDomainRigidity.FiniteTransfer

theorem exists_spherical_metric_for_masked_cofinite_circles
    {n : ℕ} {Ω Q K : Set (ℝ × ℝ)} (hΩ : IsOpen Ω) (hQ : IsClosed Q)
    (hK : IsClosed K) (hKc : IsCompact (closure Kᶜ))
    (htail : Q ∩ closure Kᶜ ⊆ Ω)
    (M : Fin n → Set (ℝ × ℝ)) (hM : ∀ i, IsClosed (M i))
    (hboundary : ∀ i, frontier (M i) ⊆ interior K)
    (f : Fin n → (ℝ × ℝ) → UnitAddCircle)
    (hf : ∀ i, SmoothCircleOn (f i) (Ω ∩ interior (M i)))
    {ε : ℝ} (hbudget : (∫ z in Q \ K, 2 * maskedCircleWedges M f z) < ε) :
    ∃ (R : ℝ) (g : (ℝ × ℝ) → PlanarMetric), 0 < R ∧ ContDiff ℝ ∞ g ∧
      (∀ z, (g z).PosDef) ∧
      (∀ᶠ z in 𝓝ˢ K, g z = sphericalMetricFactor z • 1) ∧
      (∀ z ∉ Metric.closedBall 0 R, g z = sphericalMetricFactor z • 1) ∧
      (∑ i : Fin n, ∫ z in (Q \ K) ∩ M i, fieldEnergy (circleGradient (f i)) g z) < ε := by
  have hC : IsCompact (Q ∩ closure Kᶜ) :=
    hKc.of_isClosed_subset (hQ.inter isClosed_closure) inter_subset_right
  have heq : (Q ∩ closure Kᶜ) \ K = Q \ K := by
    ext z
    constructor
    · exact fun hz => ⟨hz.1.1, hz.2⟩
    · exact fun hz => ⟨⟨hz.1, subset_closure hz.2⟩, hz.2⟩
  obtain ⟨R, g, hR, hg, hPD, hcore, hfar, henergy⟩ :=
    exists_spherical_metric_for_masked_circles hΩ hC htail hK M hM hboundary f hf
      (heq.symm ▸ hbudget)
  exact ⟨R, g, hR, hg, hPD, hcore, hfar, by simpa only [heq] using henergy⟩

end CircleDomainRigidity.FiniteTransfer

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Topology_CirclePatching
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Patching circle coordinates across filling disks

Real collar extensions project to genuine circle maps. Equality of the
projections on full boundary neighborhoods suffices for smooth patching;
global real branches on the retained region are unnecessary.
-/

open Set Filter Function
open scoped Topology ContDiff

noncomputable section

namespace CircleDomainRigidity.FiniteTransfer

theorem smoothCircleOn_patchOpenRegions
    {I : Type*} [Fintype I] (D : I → Set (ℝ × ℝ))
    (hD : ∀ i, IsOpen (D i)) (hdisj : Pairwise (Disjoint on D))
    {Ω : Set (ℝ × ℝ)}
    (f : (ℝ × ℝ) → UnitAddCircle) (hf : SmoothCircleOn f (Ω \ ⋃ i, D i))
    (g : I → (ℝ × ℝ) → ℝ) (hg : ∀ i, ContDiff ℝ ∞ (g i))
    (hagree : ∀ i x, x ∈ Ω ∩ frontier (D i) →
      (fun y => (g i y : UnitAddCircle)) =ᶠ[𝓝 x] f) :
    SmoothCircleOn (patchOpenRegions D (fun i x => (g i x : UnitAddCircle)) f) Ω := by
  apply smoothCircleOn_iff_local_lifts.mpr
  intro x hx
  by_cases hm : ∃ i, x ∈ D i
  · obtain ⟨i, hi⟩ := hm
    exact ⟨g i, (hg i).contDiffAt,
      (patchOpenRegions_eventuallyEq_inside D (fun i x => (g i x : UnitAddCircle))
        f hD hdisj hi).symm⟩
  · have hpatch := patchOpenRegions_eventuallyEq_outside D
      (fun i x => (g i x : UnitAddCircle)) f hD (not_exists.mp hm)
      (fun i hi => hagree i x ⟨hx, hi⟩)
    obtain ⟨u, hu, hproj⟩ := smoothCircleOn_iff_local_lifts.mp hf x
      ⟨hx, fun hi => hm (mem_iUnion.mp hi)⟩
    exact ⟨u, hu, hproj.trans hpatch.symm⟩

theorem circleGradient_patchOpenRegions_inside
    {I : Type*} (D : I → Set (ℝ × ℝ)) (hD : ∀ i, IsOpen (D i))
    (hdisj : Pairwise (Disjoint on D))
    (f : (ℝ × ℝ) → UnitAddCircle)
    (g : I → (ℝ × ℝ) → ℝ) (hg : ∀ i, ContDiff ℝ ∞ (g i))
    {i : I} {x : ℝ × ℝ} (hx : x ∈ D i) :
    circleGradient (patchOpenRegions D (fun i x => (g i x : UnitAddCircle)) f) x =
      planarGradient (g i) x := by
  have heq := patchOpenRegions_eventuallyEq_inside D
    (fun i x => (g i x : UnitAddCircle)) f hD hdisj hx
  have hc : ContinuousAt (patchOpenRegions D (fun i x => (g i x : UnitAddCircle)) f) x :=
    (((AddCircle.continuous_mk' (1 : ℝ)).continuousAt.comp
      (hg i).continuous.continuousAt).congr heq.symm)
  exact circleGradient_eq_lift hc (hg i).continuous.continuousAt heq.symm

/-- Rank-one real extensions retain their zero-wedge property after
projection and patching into the original circle coordinates. -/
theorem circle_patch_wedges_eq_zero_inside
    {I L : Type*} (D : I → Set (ℝ × ℝ)) (hD : ∀ i, IsOpen (D i))
    (hdisj : Pairwise (Disjoint on D))
    (f : L → (ℝ × ℝ) → UnitAddCircle) (g : I → L → (ℝ × ℝ) → ℝ)
    (hg : ∀ i l, ContDiff ℝ ∞ (g i l))
    (hzero : ∀ i l m, l ≠ m → ∀ x ∈ D i,
      planarWedge (planarGradient (g i l) x) (planarGradient (g i m) x) = 0)
    {i : I} {x : ℝ × ℝ} (hx : x ∈ D i) (l m : L) (hlm : l ≠ m) :
    planarWedge
      (circleGradient (patchOpenRegions D (fun i x => (g i l x : UnitAddCircle)) (f l)) x)
      (circleGradient (patchOpenRegions D (fun i x => (g i m x : UnitAddCircle)) (f m)) x) = 0 := by
  rw [circleGradient_patchOpenRegions_inside D hD hdisj (f l) (fun i => g i l)
      (fun i => hg i l) hx,
    circleGradient_patchOpenRegions_inside D hD hdisj (f m) (fun i => g i m)
      (fun i => hg i m) hx]
  exact hzero i l m hlm x hx

end CircleDomainRigidity.FiniteTransfer

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Topology_CircleFillings
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonEmbeddedArc.Arc.graphVertices_finite _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Simultaneous smooth fillings of circle coordinates

Connected collars and one active staircase per disk give actual real
rank-one extensions. Their projections patch into the retained circle
maps. The construction requires only the existing local branches and
does not assert any unproved period or winding statement.
-/

open Set Filter Function
open scoped Topology ContDiff

noncomputable section

namespace CircleDomainRigidity.FiniteTransfer

/-- One common small width produces real rank-one collar extensions
on all disks before any global projection or patching is performed. -/
theorem eventually_exists_rank_one_collar_families
    {I L : Type*} [Fintype I] [Fintype L]
    (D : I → Set (ℝ × ℝ))
    (hfrontc : ∀ i, IsCompact (frontier (D i)))
    (hfrontconn : ∀ i, IsConnected (frontier (D i)))
    (O : I → Set (ℝ × ℝ)) (hO : ∀ i, IsOpen (O i))
    (hDO : ∀ i, frontier (D i) ⊆ O i)
    (u : I → L → (ℝ × ℝ) → ℝ)
    (hu : ∀ i l, ContDiffOn ℝ ∞ (u i l) (O i))
    (active : I → L) {h : ℝ} (hh : 0 < h) (θ : L → ℝ)
    (havoid : ∀ i l, l ≠ active i →
      Disjoint (u i l '' frontier (D i)) (shiftedLattice h (θ l))) :
    ∀ᶠ δ : ℝ in 𝓝[>] 0, ∃ g : I → L → (ℝ × ℝ) → ℝ,
      (∀ i l, ContDiff ℝ ∞ (g i l)) ∧
      (∀ i, ∀ᶠ x in 𝓝ˢ (frontier (D i)), ∀ l,
        g i l x = shiftedStaircase h δ (θ l) (u i l x)) ∧
      ∀ i l m, l ≠ m → ∀ x,
        planarWedge (planarGradient (g i l) x) (planarGradient (g i m) x) = 0 := by
  classical
  choose C hCc hCconn hCfront hCO hCavoid using fun i =>
    exists_inactive_connected_collar (hfrontc i) (hfrontconn i) (hO i) (hDO i)
      (u i) (hu i) (active i) hh θ (havoid i)
  choose z hz using fun i => (hfrontconn i).nonempty
  have hzC (i : I) : z i ∈ C i := subset_of_mem_nhdsSet (hCfront i) (hz i)
  have hconst : ∀ᶠ δ : ℝ in 𝓝[>] 0, ∀ i l, l ≠ active i →
      ∀ x ∈ C i, shiftedStaircase h δ (θ l) (u i l x) =
        shiftedStaircase h δ (θ l) (u i l (z i)) := by
    apply eventually_all.mpr
    intro i
    apply eventually_all.mpr
    intro l
    by_cases hl : l = active i
    · exact Filter.Eventually.of_forall (fun _ h => (h hl).elim)
    · exact (eventually_constant_staircase_on_collar (hCc i) (hCconn i).isPreconnected
        (u i l) ((hu i l).continuousOn.mono (hCO i)) hh (hCavoid i l hl)).mono
        (fun δ hδ _ x hx => hδ.2 x hx (z i) (hzC i))
  have hsmall : ∀ᶠ δ : ℝ in 𝓝[>] 0, 0 < δ ∧ δ < h / 4 := by
    exact (show ∀ᶠ δ : ℝ in 𝓝[>] 0, 0 < δ from self_mem_nhdsWithin).and
      ((eventually_lt_nhds (by positivity : (0 : ℝ) < h / 4)).filter_mono nhdsWithin_le_nhds)
  filter_upwards [hconst, hsmall] with δ hδ hδsmall
  have hlocal (i : I) : ∃ g : L → (ℝ × ℝ) → ℝ,
      (∀ l, ContDiff ℝ ∞ (g l)) ∧
      (∀ᶠ x in 𝓝ˢ (frontier (D i)), ∀ l,
        g l x = shiftedStaircase h δ (θ l) (u i l x)) ∧
      ∀ l m, l ≠ m → ∀ x,
        planarWedge (planarGradient (g l) x) (planarGradient (g m) x) = 0 := by
    have hfrontInt : frontier (D i) ⊆ interior (C i) :=
      subset_interior_iff_mem_nhdsSet.mpr (hCfront i)
    let w : L → (ℝ × ℝ) → ℝ := fun l x => shiftedStaircase h δ (θ l) (u i l x)
    have hw : ContDiffOn ℝ ∞ (w (active i)) (interior (C i)) :=
      (contDiff_shiftedStaircase hh hδsmall.1 hδsmall.2 (θ (active i))).comp_contDiffOn
        ((hu i (active i)).mono (interior_subset.trans (hCO i)))
    obtain ⟨g, hg, hgw, _, hzero⟩ := exists_rank_one_collar_extension (active i)
      isOpen_interior isClosed_frontier hfrontInt w (fun l => w l (z i)) hw
      (fun l hl x hx => hδ i l hl x (interior_subset hx))
    exact ⟨g, hg, hgw, hzero⟩
  choose g hg hagree hzero using hlocal
  exact ⟨g, hg, hagree, hzero⟩

end CircleDomainRigidity.FiniteTransfer

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Sobolev_CircleFilledEnergy
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonEmbeddedArc.Arc.graphVertices_finite _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Charging circle fillings to the original domain

The smooth circle fillings preserve differentials off the disks and
have rank at most one inside them. Thus their cost is charged entirely
to the original domain, and one common spherical metric controls the
actual transferred circle energies.
-/

open Set Filter MeasureTheory Finset
open scoped Topology ContDiff Matrix.Norms.Elementwise

noncomputable section

namespace CircleDomainRigidity.FiniteTransfer

theorem IsFilledCircleFamily.eventuallyEq_outside
    {I L : Type*} [Fintype I] {D : I → Set (ℝ × ℝ)} {Ω : Set (ℝ × ℝ)}
    {v F : L → (ℝ × ℝ) → UnitAddCircle} (hF : IsFilledCircleFamily D Ω v F)
    (hD : ∀ i, IsOpen (D i)) {x : ℝ × ℝ} (hx : ∀ i, x ∉ D i) (l : L) :
    F l =ᶠ[𝓝 x] v l := by
  by_cases hb : ∃ i, x ∈ frontier (D i)
  · obtain ⟨i, hi⟩ := hb
    exact ((hF.2.2.1 i).filter_mono (nhds_le_nhdsSet hi)).mono (fun _ h => h l)
  · have hc (i : I) : x ∉ closure (D i) := by
      intro hi
      apply hb
      refine ⟨i, ?_⟩
      rw [(hD i).frontier_eq]
      exact ⟨hi, hx i⟩
    have hn : ∀ᶠ y in 𝓝 x, ∀ i, y ∉ closure (D i) :=
      eventually_all.mpr (fun i => isClosed_closure.isOpen_compl.mem_nhds (hc i))
    filter_upwards [hn] with y hy
    exact hF.2.1 l y (fun i hi => hy i (subset_closure hi))

theorem continuousOn_circleWedges
    {n : ℕ} {Ω : Set (ℝ × ℝ)} (hΩ : IsOpen Ω)
    (f : Fin n → (ℝ × ℝ) → UnitAddCircle) (hf : ∀ i, SmoothCircleOn (f i) Ω) :
    ContinuousOn (circleWedges f) Ω := by
  have hv (i : Fin n) := (contDiffOn_circleGradient hΩ (hf i)).continuousOn
  have heq : circleWedges f = fun z => ∑ p : UpperPairs n,
      |planarWedge (circleGradient (f (upperPair p).1) z)
        (circleGradient (f (upperPair p).2) z)| := by
    funext z
    exact fieldWedges_eq_sum_upperPairs _ z
  rw [heq]
  apply continuousOn_finsetSum
  intro p _
  exact (((hv _).fst.mul (hv _).snd).sub ((hv _).snd.mul (hv _).fst)).abs

end CircleDomainRigidity.FiniteTransfer

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Rigidity_MaskedCircleEnergy
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonEmbeddedArc.Arc.graphVertices_finite _root_.OAI.CannonMobius.sphereMetric _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Localized energy on the actual coordinate masks

The retained core contains the mask boundaries. Smoothness on the
compact tail and original masked L² data suffice for whole-domain
integrability and comparison after deleting any measurable part of the
core. No extension across a mask boundary is required.
-/

open Set Filter MeasureTheory
open scoped Topology ContDiff Matrix.Norms.Elementwise

noncomputable section

namespace CircleDomainRigidity.FiniteTransfer

theorem continuousOn_maskedCircleWedges_off_boundaries
    {n : ℕ} {Ω : Set (ℝ × ℝ)} (hΩ : IsOpen Ω)
    (M : Fin n → Set (ℝ × ℝ)) (hM : ∀ i, IsClosed (M i))
    (f : Fin n → (ℝ × ℝ) → UnitAddCircle)
    (hf : ∀ i, SmoothCircleOn (f i) (Ω ∩ interior (M i))) :
    ContinuousOn (maskedCircleWedges M f) (Ω \ ⋃ i, frontier (M i)) := by
  have hclosed : IsClosed (⋃ i, frontier (M i)) := isClosed_iUnion_of_finite (fun _ => isClosed_frontier)
  have hc := continuousOn_circleWedges (hΩ.sdiff hclosed)
    (fun i => maskCircleMap (M i) (f i)) (smoothCircleOn_masks_off_boundaries M hM f hf)
  apply hc.congr
  intro z hz
  exact (circleWedges_maskCircleMap_eq M hM f
    (fun i hi => hz.2 (mem_iUnion.mpr ⟨i, hi⟩))).symm

theorem integrableOn_masked_circle_energy_tail
    {Ω Q K M : Set (ℝ × ℝ)} (hΩ : IsOpen Ω) (hQ : IsClosed Q)
    (hKc : IsCompact (closure Kᶜ)) (htail : Q ∩ closure Kᶜ ⊆ Ω)
    (hM : IsClosed M) (hboundary : frontier M ⊆ interior K)
    {f : (ℝ × ℝ) → UnitAddCircle} (hf : SmoothCircleOn f (Ω ∩ interior M))
    {g : (ℝ × ℝ) → PlanarMetric} (hg : Continuous g) (hPD : ∀ z, (g z).PosDef) :
    IntegrableOn (fieldEnergy (circleGradient f) g) ((Q \ K) ∩ M) := by
  have hC : IsCompact ((Q ∩ closure Kᶜ) ∩ M) :=
    (hKc.of_isClosed_subset (hQ.inter isClosed_closure) inter_subset_right).inter_right hM
  have hCΩ : (Q ∩ closure Kᶜ) ∩ M ⊆ Ω ∩ interior M := by
    intro z hz
    refine ⟨htail hz.1, (mem_interior_iff_notMem_frontier hz.2).mpr ?_⟩
    intro hb
    have hn : z ∉ interior K := by
      simpa only [closure_compl, mem_compl_iff] using hz.1.2
    exact hn (hboundary hb)
  have hc := continuousOn_fieldEnergy
    (contDiffOn_circleGradient (hΩ.inter isOpen_interior) hf).continuousOn hg hPD
  exact ((hc.mono hCΩ).integrableOn_compact hC).mono_set
    (fun z hz => ⟨⟨hz.1.1, subset_closure hz.1.2⟩, hz.2⟩)

theorem integrableOn_masked_circle_energy
    {Ω Q G K M : Set (ℝ × ℝ)} (hΩ : IsOpen Ω) (hQ : IsClosed Q)
    (hK : IsClosed K) (hKc : IsCompact (closure Kᶜ))
    (htail : Q ∩ closure Kᶜ ⊆ Ω) (hKG : K ⊆ G)
    (hM : IsClosed M) (hboundary : frontier M ⊆ interior K)
    {f u : (ℝ × ℝ) → UnitAddCircle} (hf : SmoothCircleOn f (Ω ∩ interior M))
    (hu : MemLp (circleGradient u) 2 (volume.restrict (G ∩ M)))
    (hretain : f =ᶠ[𝓝ˢ K] u) {g : (ℝ × ℝ) → PlanarMetric}
    (hg : Continuous g) (hPD : ∀ z, (g z).PosDef)
    (hmetric : ∀ᶠ z in 𝓝ˢ K, g z = sphericalMetricFactor z • 1) :
    IntegrableOn (fieldEnergy (circleGradient f) g) (Q ∩ M) := by
  have ht : IntegrableOn (fieldEnergy (circleGradient f) g) ((Q ∩ M) \ K) := by
    have heq : (Q ∩ M) \ K = (Q \ K) ∩ M := by ext z; simp only [Set.mem_sdiff, mem_inter_iff]; tauto
    rw [heq]
    exact integrableOn_masked_circle_energy_tail hΩ hQ hKc htail hM hboundary hf hg hPD
  have hsource : IntegrableOn (fieldEnergy (circleGradient u)
      (fun z => sphericalMetricFactor z • 1)) (G ∩ M) :=
    integrable_fieldEnergy_spherical_of_memLp hu
  have hc : IntegrableOn (fieldEnergy (circleGradient f) g) ((Q ∩ M) ∩ K) := by
    apply (hsource.mono_set
      (fun z hz => ⟨hKG hz.2, hz.1.2⟩)).congr
    filter_upwards [ae_restrict_mem ((hQ.measurableSet.inter hM.measurableSet).inter hK.measurableSet)] with z hz
    have hgrad := circleGradient_congr_of_eventuallyEq
      (hretain.filter_mono (nhds_le_nhdsSet hz.2))
    simp only [fieldEnergy, hgrad, hmetric.self_of_nhdsSet z hz.2]
  simpa only [inter_union_sdiff] using hc.union ht

theorem localized_masked_circle_energy_lt
    {Ω Q G K M : Set (ℝ × ℝ)} (hΩ : IsOpen Ω) (hQ : IsClosed Q)
    (hG : MeasurableSet G) (hK : IsClosed K) (hKc : IsCompact (closure Kᶜ))
    (htail : Q ∩ closure Kᶜ ⊆ Ω) (hKG : K ⊆ G)
    (hM : IsClosed M) (hboundary : frontier M ⊆ interior K)
    {f u : (ℝ × ℝ) → UnitAddCircle} (hf : SmoothCircleOn f (Ω ∩ interior M))
    (hu : MemLp (circleGradient u) 2 (volume.restrict (G ∩ M)))
    (hretain : f =ᶠ[𝓝ˢ K] u) {g : (ℝ × ℝ) → PlanarMetric}
    (hg : Continuous g) (hPD : ∀ z, (g z).PosDef)
    (hmetric : ∀ᶠ z in 𝓝ˢ K, g z = sphericalMetricFactor z • 1)
    {ε : ℝ} (henergy : (∫ z in (Q \ K) ∩ M, fieldEnergy (circleGradient f) g z) < ε)
    {E : Set (ℝ × ℝ)} (hE : MeasurableSet E) (hEK : E ⊆ K) :
    (∫ z in (Q \ E) ∩ M, fieldEnergy (circleGradient f) g z) <
      (∫ z in (G \ E) ∩ M, fieldEnergy (circleGradient u)
        (fun z => sphericalMetricFactor z • 1) z) + ε := by
  have hswap (S A : Set (ℝ × ℝ)) : (S ∩ M) \ A = (S \ A) ∩ M := by
    ext z
    simp only [Set.mem_sdiff, mem_inter_iff]
    tauto
  have hi := integrableOn_masked_circle_energy hΩ hQ hK hKc htail hKG hM hboundary
    hf hu hretain hg hPD hmetric
  have hu' := integrable_fieldEnergy_spherical_of_memLp hu
  have ht := hi.mono_set (s := (Q ∩ M) \ K) Set.sdiff_subset
  have he : (∫ z in (Q ∩ M) \ K, fieldEnergy (circleGradient f) g z) < ε := by
    simpa only [hswap] using henergy
  have hresult := localized_energy_lt_source
    (hQ.measurableSet.inter hM.measurableSet) (hG.inter hM.measurableSet) hK.measurableSet hE hEK
    (fun z hz => ⟨hKG hz.2, hz.1.2⟩) hi hu' ht
    (fun z _ => covectorEnergy_nonneg _ (Matrix.PosDef.one.smul (sphericalMetricFactor_pos z)))
    (T := fieldEnergy (circleGradient f) g) ?_ (fun _ _ => le_rfl) he
  · simpa only [hswap] using hresult
  · intro z hz
    have hgrad := circleGradient_congr_of_eventuallyEq
      (hretain.filter_mono (nhds_le_nhdsSet hz.2))
    simp only [fieldEnergy, hgrad, hmetric.self_of_nhdsSet z hz.2]

end CircleDomainRigidity.FiniteTransfer

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Rigidity_MaskedWedgeCost
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Random wedge cost on different coordinate masks

Each pair is integrated on the intersection of its two masks. Thus
the original fields need square-integrable norm only on their own masks.
The same independent-shift estimate controls this actual masked cost.
-/

open Set Filter MeasureTheory
open scoped Topology

noncomputable section

namespace CircleDomainRigidity.FiniteTransfer

theorem abs_wedge_indicators {X : Type*} (A B : Set X) (u v : X → ℝ × ℝ) (z : X) :
    |planarWedge (A.indicator u z) (B.indicator v z)| =
      (A ∩ B).indicator (fun z => |planarWedge (u z) (v z)|) z := by
  by_cases ha : z ∈ A <;> by_cases hb : z ∈ B <;>
    simp [ha, hb, planarWedge]

theorem integral_abs_wedge_indicators {X : Type*} [MeasurableSpace X] (μ : Measure X)
    {A B : Set X} (hA : MeasurableSet A) (hB : MeasurableSet B) (u v : X → ℝ × ℝ) :
    (∫ z, |planarWedge (A.indicator u z) (B.indicator v z)| ∂μ) =
      ∫ z in A ∩ B, |planarWedge (u z) (v z)| ∂μ := by
  simp_rw [abs_wedge_indicators]
  exact integral_indicator (hA.inter hB)

theorem maskedStaircaseCost_nonneg
    {X P : Type*} [MeasurableSpace X] [Fintype P] (μ : Measure X) {n : ℕ}
    (pairs : P → Fin n × Fin n) (M : Fin n → Set X)
    (u : Fin n → X → ℝ × ℝ) (c : X → ℝ × ℝ)
    (x : Fin n → X → ℝ) (χ : X → ℝ) (h δ : ℝ) (θ : Fin n → ℝ) :
    0 ≤ maskedStaircaseCost μ pairs M u c x χ h δ θ :=
  Finset.sum_nonneg (fun _ _ => integral_nonneg (fun _ => abs_nonneg _))

theorem integrable_maskedStaircaseCost_and_mean_le
    {X P : Type*} [MeasurableSpace X] [Fintype P] {μ : Measure X} [SFinite μ] {n : ℕ}
    (pairs : P → Fin n × Fin n) (hpairs : ∀ p, (pairs p).1 ≠ (pairs p).2)
    (M : Fin n → Set X) (u : Fin n → X → ℝ × ℝ) (c : X → ℝ × ℝ)
    (x : Fin n → X → ℝ) (χ : X → ℝ)
    (hu : ∀ i, Measurable (u i)) (hc : Measurable c)
    (hx : ∀ i, Measurable (x i)) (hχ : Measurable χ)
    (hu2 : ∀ i, MemLp (u i) 2 (μ.restrict (M i))) (hc2 : MemLp c 2 μ)
    {h δ : ℝ} (hh : 0 < h) (hδ : 0 < δ) (hδh : δ < h / 4)
    (hχ0 : ∀ z, 0 ≤ χ z) (hχ1 : ∀ z, χ z ≤ 1) :
    Integrable (maskedStaircaseCost μ pairs M u c x χ h δ)
        (Measure.pi (fun _ : Fin n => shiftLaw h)) ∧
      (∫ θ, maskedStaircaseCost μ pairs M u c x χ h δ θ
        ∂Measure.pi (fun _ : Fin n => shiftLaw h)) ≤
        (∑ p, ∫ z in M (pairs p).1 ∩ M (pairs p).2,
          |planarWedge (u (pairs p).1 z) (u (pairs p).2 z)| ∂μ) +
          h * (∑ p, ∫ z in M (pairs p).1 ∩ M (pairs p).2,
            |planarWedge (u (pairs p).1 z) (c z)| +
              |planarWedge (c z) (u (pairs p).2 z)| ∂μ) := by
  let ν : P → Measure X := fun p => μ.restrict (M (pairs p).1 ∩ M (pairs p).2)
  have hui p : MemLp (u (pairs p).1) 2 (ν p) :=
    (hu2 _).mono_measure (Measure.restrict_mono inter_subset_left le_rfl)
  have huj p : MemLp (u (pairs p).2) 2 (ν p) :=
    (hu2 _).mono_measure (Measure.restrict_mono inter_subset_right le_rfl)
  have hci p : MemLp c 2 (ν p) := hc2.mono_measure Measure.restrict_le_self
  have hbase p := integrable_abs_planarWedge_of_memLp (hui p) (huj p)
  have herr p := (integrable_abs_planarWedge_of_memLp (hui p) (hci p)).add
    (integrable_abs_planarWedge_of_memLp (hci p) (huj p))
  have hb p := (hbase p).add ((herr p).const_mul h)
  have hi p := integrable_staircasePairCost u c x χ hu hc hx hχ
    hh hδ hδh hχ0 hχ1 (hpairs p) (hb p)
  refine ⟨integrable_finsetSum _ (fun p _ => hi p), ?_⟩
  unfold maskedStaircaseCost
  rw [integral_finsetSum _ (fun p _ => hi p)]
  calc
    _ ≤ ∑ p, ∫ z, |planarWedge (u (pairs p).1 z) (u (pairs p).2 z)| +
        h * (|planarWedge (u (pairs p).1 z) (c z)| +
          |planarWedge (c z) (u (pairs p).2 z)|) ∂ν p := by
      apply Finset.sum_le_sum
      intro p _
      exact expected_integrated_grid_pair_wedge_le (hpairs p)
        (u (pairs p).1) (u (pairs p).2) c (x (pairs p).1) (x (pairs p).2) χ
        hh hδ hδh hχ0 hχ1
        (integrable_staircase_pair_density _ _ _ _ _ _
          (hu _) (hu _) hc (hx _) (hx _) hχ hh hδ hδh hχ0 hχ1 (hb p)) (hb p)
    _ = (∑ p, ((∫ z, |planarWedge (u (pairs p).1 z) (u (pairs p).2 z)| ∂ν p) +
        h * (∫ z, |planarWedge (u (pairs p).1 z) (c z)| +
          |planarWedge (c z) (u (pairs p).2 z)| ∂ν p))) := by
      apply Finset.sum_congr rfl
      intro p _
      exact (integral_add (hbase p) ((herr p).const_mul h)).trans
        (congrArg (fun t => (∫ z, |planarWedge (u (pairs p).1 z) (u (pairs p).2 z)| ∂ν p) + t)
          (integral_const_mul h _))
    _ = _ := by rw [Finset.sum_add_distrib, ← Finset.mul_sum]

end CircleDomainRigidity.FiniteTransfer

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Rigidity_MaskedCircleFillings
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Circle fillings with coordinate-specific masks

Real collar branches still give one simultaneous rank-one filling.
Smoothness is required only on each coordinate's own mask. The common
boundary agreement and zero-wedge identities hold on all filling disks.
-/

open Set Filter Function
open scoped Topology ContDiff

noncomputable section

namespace CircleDomainRigidity.FiniteTransfer

theorem IsMaskedFilledCircleFamily.masked_wedges_eq_zero
    {I : Type*} {n : ℕ} {D : I → Set (ℝ × ℝ)} {Ω : Set (ℝ × ℝ)}
    {M : Fin n → Set (ℝ × ℝ)} {v F : Fin n → (ℝ × ℝ) → UnitAddCircle}
    (hF : IsMaskedFilledCircleFamily D Ω M v F) {i : I} {z : ℝ × ℝ} (hz : z ∈ D i) :
    maskedCircleWedges M F z = 0 := by
  unfold maskedCircleWedges
  apply Finset.sum_eq_zero
  intro p _
  rw [abs_wedge_indicators]
  by_cases hm : z ∈ M (upperPair p).1 ∩ M (upperPair p).2
  · rw [indicator_of_mem hm, hF.2.2.2.2 i _ _ (upperPair_ne p) z hz, abs_zero]
  · rw [indicator_of_notMem hm]

theorem IsMaskedFilledCircleFamily.masked_wedges_eq_outside
    {I : Type*} [Fintype I] {n : ℕ} {D : I → Set (ℝ × ℝ)} {Ω : Set (ℝ × ℝ)}
    {M : Fin n → Set (ℝ × ℝ)} {v F : Fin n → (ℝ × ℝ) → UnitAddCircle}
    (hF : IsMaskedFilledCircleFamily D Ω M v F) (hD : ∀ i, IsOpen (D i))
    {z : ℝ × ℝ} (hz : ∀ i, z ∉ D i) : maskedCircleWedges M F z = maskedCircleWedges M v z := by
  have hgrad (l : Fin n) := circleGradient_congr_of_eventuallyEq (hF.2.eventuallyEq_outside hD hz l)
  unfold maskedCircleWedges
  apply Finset.sum_congr rfl
  intro p _
  rw [abs_wedge_indicators, abs_wedge_indicators]
  by_cases hm : z ∈ M (upperPair p).1 ∩ M (upperPair p).2
  · simp only [indicator_of_mem hm, hgrad]
  · simp only [indicator_of_notMem hm]

end CircleDomainRigidity.FiniteTransfer

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Rigidity_ExteriorMaskReplacement
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Values outside a closed mask can be replaced by a constant on a
closed set separated from that mask and the retained core. This supplies
honest real branches for absent coordinates without changing any masked
differential, any masked cutoff cost, or any retained value. -/

open Set Filter Function MeasureTheory Classical
open scoped Topology ContDiff

noncomputable section
namespace CircleDomainRigidity.FiniteTransfer

 theorem exteriorMaskReplacement_eventuallyEq
    {W A : Set (ℝ × ℝ)} (hW : IsClosed W) (hWA : Disjoint W A)
    (c : UnitAddCircle) (f : (ℝ × ℝ) → UnitAddCircle) :
    exteriorMaskReplacement W c f =ᶠ[𝓝ˢ A] f := by
  apply eventually_nhdsSet_iff_forall.mpr
  intro x hx
  have hxW : x ∉ W := fun h => Set.disjoint_left.mp hWA h hx
  filter_upwards [hW.isOpen_compl.mem_nhds hxW] with y hy
  exact piecewise_eq_of_notMem W _ _ hy

 theorem exteriorMaskReplacement_smooth
    {W M G : Set (ℝ × ℝ)} (hW : IsClosed W) (hWM : Disjoint W M)
    (c : UnitAddCircle) (f : (ℝ × ℝ) → UnitAddCircle)
    (hf : SmoothCircleOn f (G ∩ interior M)) :
    SmoothCircleOn (exteriorMaskReplacement W c f) (G ∩ interior M) := by
  apply smoothCircleOn_iff_local_lifts.mpr
  intro x hx
  obtain ⟨u, hu, huf⟩ := smoothCircleOn_iff_local_lifts.mp hf x hx
  exact ⟨u, hu, huf.trans ((exteriorMaskReplacement_eventuallyEq hW hWM c f).filter_mono
    (nhds_le_nhdsSet (interior_subset hx.2))).symm⟩

 theorem exteriorMaskReplacement_gradient
    {W M : Set (ℝ × ℝ)} (hW : IsClosed W) (hWM : Disjoint W M)
    (c : UnitAddCircle) (f : (ℝ × ℝ) → UnitAddCircle) {x : ℝ × ℝ} (hx : x ∈ M) :
    circleGradient (exteriorMaskReplacement W c f) x = circleGradient f x :=
  circleGradient_congr_of_eventuallyEq
    ((exteriorMaskReplacement_eventuallyEq hW hWM c f).filter_mono (nhds_le_nhdsSet hx))

 theorem exteriorMaskReplacement_memLp
    {W M G : Set (ℝ × ℝ)} (hW : IsClosed W) (hWM : Disjoint W M)
    (hG : MeasurableSet G) (hM : MeasurableSet M) (c : UnitAddCircle) (f : (ℝ × ℝ) → UnitAddCircle)
    (hf : MeasureTheory.MemLp (circleGradient f) 2 (MeasureTheory.volume.restrict (G ∩ M))) :
    MeasureTheory.MemLp (circleGradient (exteriorMaskReplacement W c f)) 2
      (MeasureTheory.volume.restrict (G ∩ M)) := by
  apply MemLp.ae_eq (hf_Lp := hf)
  filter_upwards [MeasureTheory.ae_restrict_mem₀
    ((hG.inter hM).nullMeasurableSet)] with x hx
  · exact (exteriorMaskReplacement_gradient hW hWM c f hx.2).symm

 theorem exteriorMaskReplacement_cutoff_gradient
    {W M : Set (ℝ × ℝ)} (hW : IsClosed W) (hWM : Disjoint W M)
    (c : UnitAddCircle) (f : (ℝ × ℝ) → UnitAddCircle)
    (χ : (ℝ × ℝ) → ℝ) (P : ℝ → ℝ) {x : ℝ × ℝ} (hx : x ∈ M) :
    circleGradient (circleCutoff (exteriorMaskReplacement W c f) χ P) x =
      circleGradient (circleCutoff f χ P) x := by
  apply circleGradient_congr_of_eventuallyEq
  filter_upwards [(exteriorMaskReplacement_eventuallyEq hW hWM c f).filter_mono
    (nhds_le_nhdsSet hx)] with y hy
  simp only [circleCutoff, cutoffStaircase, hy]

 theorem exteriorMaskReplacement_masked_wedges
    {n : ℕ} (W M : Fin n → Set (ℝ × ℝ)) (hW : ∀ l, IsClosed (W l))
    (hWM : ∀ l, Disjoint (W l) (M l)) (c : Fin n → UnitAddCircle)
    (f : Fin n → (ℝ × ℝ) → UnitAddCircle) (χ : (ℝ × ℝ) → ℝ)
    (N : ℕ) (δ : ℝ) (θ : Fin n → ℝ) :
    maskedCircleWedges M (circleCutoffFamily
      (fun l => exteriorMaskReplacement (W l) (c l) (f l)) χ N δ θ) =
      maskedCircleWedges M (circleCutoffFamily f χ N δ θ) := by
  funext x
  unfold maskedCircleWedges
  apply Finset.sum_congr rfl
  intro p _
  rw [abs_wedge_indicators, abs_wedge_indicators]
  by_cases hx : x ∈ M (upperPair p).1 ∩ M (upperPair p).2
  · simp only [indicator_of_mem hx, circleCutoffFamily]
    rw [exteriorMaskReplacement_cutoff_gradient (hW _) (hWM _) _ _ _ _ hx.1,
      exteriorMaskReplacement_cutoff_gradient (hW _) (hWM _) _ _ _ _ hx.2]
  · simp only [indicator_of_notMem hx]

end CircleDomainRigidity.FiniteTransfer

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Rigidity_LocalMaskNeighborhoods
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions _root_.OAI.CircleDomainRigidity.finiteSphericalArea _root_.OAI.CircleDomainRigidity.sphereFirstCountableTopology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Away from the finitely many marked singularities, every dust point
has a common neighborhood on which each masked coordinate is absent or
has one of its given real branches. The mask boundary lies in the domain. -/

open Set Function

noncomputable section
namespace CircleDomainRigidity

 theorem exists_common_mask_branch_neighborhood
    {J : Type*} [Finite J] (I : J → Type*) (U : Set Sphere)
    (M : J → Set Sphere) (hM : ∀ j, IsClosed (M j))
    (hboundary : ∀ j, frontier (M j) ⊆ U)
    (b : J → Sphere) (V : ∀ j, I j → Set Sphere)
    (hV : ∀ j i, IsOpen (V j i))
    (hcover : ∀ j, M j \ {b j} ⊆ ⋃ i, V j i)
    {x : Sphere} (hx : x ∉ U) (hxb : ∀ j, x ≠ b j) :
    ∃ N : Set Sphere, IsOpen N ∧ x ∈ N ∧
      ∀ j, Disjoint N (M j) ∨ ∃ i, N ⊆ interior (M j) ∩ V j i := by
  classical
  have hlocal (j : J) : ∃ N : Set Sphere, IsOpen N ∧ x ∈ N ∧
      (Disjoint N (M j) ∨ ∃ i, N ⊆ interior (M j) ∩ V j i) := by
    by_cases hxm : x ∈ M j
    · have hxi : x ∈ interior (M j) :=
        (mem_interior_iff_notMem_frontier hxm).mpr (fun h => hx (hboundary j h))
      obtain ⟨i, hi⟩ := mem_iUnion.mp (hcover j ⟨hxm, hxb j⟩)
      exact ⟨interior (M j) ∩ V j i, isOpen_interior.inter (hV j i),
        ⟨hxi, hi⟩, Or.inr ⟨i, Subset.rfl⟩⟩
    · exact ⟨(M j)ᶜ, (hM j).isOpen_compl, hxm, Or.inl disjoint_compl_left⟩
  choose N hNo hxN hchoice using hlocal
  refine ⟨⋂ j, N j, isOpen_iInter_of_finite hNo, mem_iInter.mpr hxN, ?_⟩
  intro j
  have hsub : (⋂ k, N k) ⊆ N j := iInter_subset N j
  rcases hchoice j with hd | ⟨i, hi⟩
  · exact Or.inl (hd.mono_left hsub)
  · exact Or.inr ⟨i, hsub.trans hi⟩


 theorem exists_common_mask_branch_neighborhood_of_subset
    {X J : Type*} [TopologicalSpace X] [Finite J] (I : J → Type*)
    (C : Set X) (M : J → Set X) (hM : ∀ j, IsClosed (M j))
    (V : ∀ j, I j → Set X) (hV : ∀ j i, IsOpen (V j i))
    (hchoice : ∀ j, Disjoint C (M j) ∨ ∃ i, C ⊆ interior (M j) ∩ V j i) :
    ∃ N : Set X, IsOpen N ∧ C ⊆ N ∧
      ∀ j, Disjoint N (M j) ∨ ∃ i, N ⊆ interior (M j) ∩ V j i := by
  have hlocal (j : J) : ∃ N : Set X, IsOpen N ∧ C ⊆ N ∧
      (Disjoint N (M j) ∨ ∃ i, N ⊆ interior (M j) ∩ V j i) := by
    rcases hchoice j with hd | ⟨i, hi⟩
    · exact ⟨(M j)ᶜ, (hM j).isOpen_compl, hd.subset_compl_right,
        Or.inl disjoint_compl_left⟩
    · exact ⟨interior (M j) ∩ V j i, isOpen_interior.inter (hV j i),
        hi, Or.inr ⟨i, Subset.rfl⟩⟩
  choose N hNo hCN hchoiceN using hlocal
  refine ⟨⋂ j, N j, isOpen_iInter_of_finite hNo,
    fun x hx => mem_iInter.mpr (fun j => hCN j hx), ?_⟩
  intro j
  have hsub : (⋂ k, N k) ⊆ N j := iInter_subset N j
  rcases hchoiceN j with hd | ⟨i, hi⟩
  · exact Or.inl (hd.mono_left hsub)
  · exact Or.inr ⟨i, hsub.trans hi⟩

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Topology_QuotientDiskTopology
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions _root_.OAI.CircleDomainRigidity.finiteSphericalArea _root_.OAI.CircleDomainRigidity.sphereFirstCountableTopology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Topology of projected physical disks

Physical Jordan disks with boundary in the original domain have saturated
interiors and saturated closures. Their images are open with connected
complements, and disjoint physical closed disks give disjoint quotient closed
disks. These properties allow finite dust covers to be used in the descending
grid construction without postulating a disk-selection lemma.
-/

open Set Function
open scoped Topology

namespace CircleDomainRigidity

theorem isConnected_sphere_compl_jordanInterior (H : ℂ ≃ₜ ℂ) :
    IsConnected ((((↑) : ℂ → Sphere) '' jordanInterior H)ᶜ) := by
  have heq : H.onePointCongr '' (((↑) : ℂ → Sphere) '' Metric.ball (0 : ℂ) 1) =
      ((↑) : ℂ → Sphere) '' jordanInterior H := by
    rw [image_image, jordanInterior, image_image]
    rfl
  rw [← heq, ← H.onePointCongr.image_compl]
  exact (isConnected_sphere_exterior_ball (0 : ℂ) zero_lt_one).image _
    H.onePointCongr.continuous.continuousOn

theorem preimage_image_closure_of_singleton_boundary_fibers
    {X Y : Type*} [TopologicalSpace X]
    (π : X → Y) (hfibers : ∀ y, IsPreconnected (π ⁻¹' {y}))
    {U : Set X} (hU : IsOpen U)
    (hsing : ∀ p ∈ frontier U, ∀ q, π q = π p → q = p) :
    π ⁻¹' (π '' closure U) = closure U := by
  have hsat := preimage_image_open_of_singleton_boundary_fibers π hfibers hU hsing
  apply Set.Subset.antisymm
  · rintro q ⟨p, hp, hpq⟩
    by_cases hpU : p ∈ U
    · apply subset_closure
      rw [← hsat]
      exact ⟨p, hpU, hpq⟩
    · have hpfront : p ∈ frontier U := by
        rw [hU.frontier_eq]
        exact ⟨hp, hpU⟩
      have hqp : q = p := hsing p hpfront q hpq.symm
      simpa only [hqp] using hp
  · exact subset_preimage_image π (closure U)

theorem preimage_image_closed_jordanInterior_of_component_collapse
    {Y : Type*} (G : Set Sphere) (π : Sphere → Y) (hsurj : Surjective π)
    (hr : ∀ x y, π x = π y ↔
      x = y ∨ (x ∈ Gᶜ ∧ y ∈ connectedComponentIn Gᶜ x))
    (H : ℂ ≃ₜ ℂ) (hboundary : ∀ z ∈ frontier (jordanInterior H), (z : Sphere) ∈ G) :
    π ⁻¹' (π '' (((↑) : ℂ → Sphere) '' closure (jordanInterior H))) =
      ((↑) : ℂ → Sphere) '' closure (jordanInterior H) := by
  rw [← closure_sphere_image_jordanInterior]
  apply preimage_image_closure_of_singleton_boundary_fibers π
    (fun y => (connected_fibers_of_component_collapse G π hsurj hr y).isPreconnected)
    (OnePoint.isOpen_image_coe.mpr (jordanInterior_isOpen H))
  intro p hp q hqp
  rw [frontier_sphere_image_jordanInterior] at hp
  obtain ⟨z, hz, rfl⟩ := hp
  rcases (hr (z : Sphere) q).mp hqp.symm with heq | ⟨hznot, _⟩
  · exact heq.symm
  · exact (hznot (hboundary z hz)).elim

theorem image_compl_of_saturated {X Y : Type*} (π : X → Y) (hsurj : Surjective π)
    {U : Set X} (hsat : π ⁻¹' (π '' U) = U) : π '' Uᶜ = (π '' U)ᶜ := by
  ext y
  constructor
  · rintro ⟨p, hp, rfl⟩ hy
    apply hp
    rw [← hsat]
    exact hy
  · intro hy
    obtain ⟨p, rfl⟩ := hsurj y
    refine ⟨p, ?_, rfl⟩
    exact fun hp => hy (mem_image_of_mem _ hp)

theorem isConnected_compl_image_jordanInterior_of_component_collapse
    {Y : Type*} [TopologicalSpace Y]
    (G : Set Sphere) (π : Sphere → Y) (hπ : Continuous π) (hsurj : Surjective π)
    (hr : ∀ x y, π x = π y ↔
      x = y ∨ (x ∈ Gᶜ ∧ y ∈ connectedComponentIn Gᶜ x))
    (H : ℂ ≃ₜ ℂ) (hboundary : ∀ z ∈ frontier (jordanInterior H), (z : Sphere) ∈ G) :
    IsConnected (π '' (((↑) : ℂ → Sphere) '' jordanInterior H))ᶜ := by
  rw [← image_compl_of_saturated π hsurj
    (preimage_image_jordanInterior_of_component_collapse G π hsurj hr H hboundary)]
  exact (isConnected_sphere_compl_jordanInterior H).image π hπ.continuousOn

theorem physical_preimage_image_jordanInterior
    {Y : Type*} (G : Set Sphere) (π : Sphere → Y) (hsurj : Surjective π)
    (hr : ∀ x y, π x = π y ↔
      x = y ∨ (x ∈ Gᶜ ∧ y ∈ connectedComponentIn Gᶜ x))
    (H : ℂ ≃ₜ ℂ) (hboundary : ∀ z ∈ frontier (jordanInterior H), (z : Sphere) ∈ G) :
    (fun z : ℂ => π (z : Sphere)) ⁻¹'
      (π '' (((↑) : ℂ → Sphere) '' jordanInterior H)) = jordanInterior H := by
  change ((↑) : ℂ → Sphere) ⁻¹' (π ⁻¹'
    (π '' (((↑) : ℂ → Sphere) '' jordanInterior H))) = _
  rw [preimage_image_jordanInterior_of_component_collapse G π hsurj hr H hboundary,
    Set.preimage_image_eq _ OnePoint.coe_injective]

theorem closure_image_jordanInterior
    {Y : Type*} [TopologicalSpace Y] (π : Sphere → Y)
    (hπ : Continuous π) (hclosed : IsClosedMap π) (H : ℂ ≃ₜ ℂ) :
    closure (π '' (((↑) : ℂ → Sphere) '' jordanInterior H)) =
      π '' (((↑) : ℂ → Sphere) '' closure (jordanInterior H)) := by
  rw [hclosed.closure_image_eq_of_continuous hπ, closure_sphere_image_jordanInterior]

theorem infty_notMem_closure_image_jordanInterior
    {Y : Type*} [TopologicalSpace Y]
    (G : Set Sphere) (π : Sphere → Y) (hπ : Continuous π)
    (hclosed : IsClosedMap π) (hsurj : Surjective π)
    (hr : ∀ x y, π x = π y ↔
      x = y ∨ (x ∈ Gᶜ ∧ y ∈ connectedComponentIn Gᶜ x))
    (H : ℂ ≃ₜ ℂ) (hboundary : ∀ z ∈ frontier (jordanInterior H), (z : Sphere) ∈ G) :
    π OnePoint.infty ∉ closure (π '' (((↑) : ℂ → Sphere) '' jordanInterior H)) := by
  rw [closure_image_jordanInterior π hπ hclosed H]
  intro h
  have hmem : OnePoint.infty ∈ ((↑) : ℂ → Sphere) '' closure (jordanInterior H) := by
    rw [← preimage_image_closed_jordanInterior_of_component_collapse
      G π hsurj hr H hboundary]
    exact h
  obtain ⟨z, _, hz⟩ := hmem
  exact (OnePoint.coe_ne_infty z) hz

end CircleDomainRigidity

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Topology_DiskRemainder
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonMobius.sphereMetric _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions _root_.OAI.CircleDomainRigidity.finiteSphericalArea _root_.OAI.CircleDomainRigidity.sphereFirstCountableTopology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Dust remaining after a finite contour family

When the physical boundaries miss the dust, removing the interiors of a
finite family leaves compact relatively clopen dust disjoint from every
closed fill. This supplies the invariant for the descending grid stages.
-/

open Set Function
open scoped Topology

namespace CircleDomainRigidity

theorem quotient_cover_of_physical_cover
    {I X : Type*} (π : Sphere → X) (hsurj : Surjective π)
    (U : I → Set ℂ) {A : Set X} (hinfty : π OnePoint.infty ∉ A)
    (hcover : (fun z : ℂ => π (z : Sphere)) ⁻¹' A ⊆ ⋃ i, U i) :
    A ⊆ ⋃ i, π '' (((↑) : ℂ → Sphere) '' U i) := by
  intro x hx
  obtain ⟨p, rfl⟩ := hsurj x
  cases p using OnePoint.rec with
  | infty => exact (hinfty hx).elim
  | coe z =>
    obtain ⟨i, hi⟩ := mem_iUnion.mp (hcover hx)
    exact mem_iUnion.mpr ⟨i, _, ⟨z, hi, rfl⟩, rfl⟩

theorem dust_inter_closed_fills_eq_inter_interiors
    {I X : Type*} (π : Sphere → X) (H : I → ℂ ≃ₜ ℂ) {B : Set X}
    (hboundary : ∀ i z, z ∈ frontier (jordanInterior (H i)) → π (z : Sphere) ∉ B) :
    B ∩ (⋃ i, π '' (((↑) : ℂ → Sphere) '' closure (jordanInterior (H i)))) =
      B ∩ (⋃ i, π '' (((↑) : ℂ → Sphere) '' jordanInterior (H i))) := by
  apply Set.Subset.antisymm
  · rintro x ⟨hxB, hx⟩
    obtain ⟨i, p, hp, hpx⟩ := mem_iUnion.mp hx
    obtain ⟨z, hz, rfl⟩ := hp
    have hzU : z ∈ jordanInterior (H i) := by
      by_contra hzU
      have hzfront : z ∈ frontier (jordanInterior (H i)) := by
        rw [(jordanInterior_isOpen (H i)).frontier_eq]
        exact ⟨hz, hzU⟩
      exact hboundary i z hzfront (hpx.symm ▸ hxB)
    exact ⟨hxB, mem_iUnion.mpr ⟨i, _, ⟨z, hzU, rfl⟩, hpx⟩⟩
  · exact inter_subset_inter_right _ (iUnion_mono fun _ => image_mono (image_mono subset_closure))

theorem compact_clopen_dust_remainder
    {I : Type*} [Finite I]
    (G : Set Sphere) (π : Sphere → Sphere) (hπ : Continuous π)
    (hclosed : IsClosedMap π) (hsurj : Surjective π)
    (hr : ∀ x y, π x = π y ↔
      x = y ∨ (x ∈ Gᶜ ∧ y ∈ connectedComponentIn Gᶜ x))
    (H : I → ℂ ≃ₜ ℂ) {B A : Set Sphere} (hB : IsClosed B)
    (hA : IsCompact A) (hAB : A ⊆ B) (hBA : IsClosed (B \ A))
    (hboundary : ∀ i z, z ∈ frontier (jordanInterior (H i)) →
      (z : Sphere) ∈ G ∧ π (z : Sphere) ∉ B) :
    let U := ⋃ i, π '' (((↑) : ℂ → Sphere) '' jordanInterior (H i))
    let C := ⋃ i, π '' (((↑) : ℂ → Sphere) '' closure (jordanInterior (H i)))
    IsCompact (A \ U) ∧ (A \ U) ⊆ B ∧ IsClosed (B \ (A \ U)) ∧ Disjoint (A \ U) C := by
  dsimp only
  let U := ⋃ i, π '' (((↑) : ℂ → Sphere) '' jordanInterior (H i))
  let C := ⋃ i, π '' (((↑) : ℂ → Sphere) '' closure (jordanInterior (H i)))
  have hU : IsOpen U := isOpen_iUnion fun i =>
    isOpen_image_jordanInterior_of_component_collapse G π hπ hclosed hsurj hr (H i)
      (fun z hz => (hboundary i z hz).1)
  have hC : IsClosed C := isClosed_iUnion_of_finite fun i =>
    (((isCompact_closure_jordanInterior (H i)).image OnePoint.continuous_coe).image hπ).isClosed
  have heq : B ∩ C = B ∩ U :=
    dust_inter_closed_fills_eq_inter_interiors π H (fun i z hz => (hboundary i z hz).2)
  have hdiff : B \ (A \ U) = (B \ A) ∪ (B ∩ C) := by
    rw [heq]
    ext x
    simp only [mem_sdiff, mem_union, mem_inter_iff]
    tauto
  refine ⟨hA.diff hU, (fun _ hx => hAB hx.1), ?_, ?_⟩
  · rw [hdiff]
    exact hBA.union (hB.inter hC)
  · apply Set.disjoint_left.mpr
    intro x hx hxC
    have hxU : x ∈ B ∩ U := heq ▸ ⟨hAB hx.1, hxC⟩
    exact hx.2 hxU.2

theorem remainder_avoids_covered_set
    {X : Type*} {A J U : Set X} (hcover : A ∩ J ⊆ U) :
    Disjoint (A \ U) J := by
  exact Set.disjoint_left.mpr fun _ hx hxJ => hx.2 (hcover ⟨hx.1, hxJ⟩)

end CircleDomainRigidity

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Topology_CompactComponentContours
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions _root_.OAI.CircleDomainRigidity.finiteSphericalArea _root_.OAI.CircleDomainRigidity.sphereFirstCountableTopology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Isolating a compact family of singleton components

A compact target consisting of singleton obstacle components has one compact
relatively clopen obstacle neighborhood inside any prescribed open set.
This strengthens pointwise isolation to the compact targets used at each
stage of the descending grid construction.
-/

open Set Function
open scoped Topology Manifold ContDiff

namespace CircleDomainRigidity

theorem exists_compact_piece_cover_of_singleton_components
    {X : Type*} [TopologicalSpace X] [CompactSpace X] [T2Space X]
    {F T V : Set X} (hF : IsClosed F) (hT : IsCompact T) (hTF : T ⊆ F)
    (hcomponents : ∀ x ∈ T, connectedComponentIn F x = {x})
    (hV : IsOpen V) (hTV : T ⊆ V) :
    ∃ A : Set X, IsCompact A ∧ T ⊆ A ∧ A ⊆ F ∧ A ⊆ V ∧ IsClosed (F \ A) := by
  classical
  choose C hCc hxC hCF hCV hFC using fun x : T =>
    exists_compact_piece_of_singleton_component hF (hTF x.property)
      (hcomponents x x.property) hV (hTV x.property)
  obtain ⟨s, hs⟩ := hT.elim_finite_subcover (fun x : T => (F \ C x)ᶜ)
    (fun x => (hFC x).isOpen_compl) (by
      intro x hx
      refine mem_iUnion.mpr ⟨⟨x, hx⟩, ?_⟩
      exact fun h => h.2 (hxC ⟨x, hx⟩))
  let A := ⋃ x ∈ s, C x
  have hdiff : F \ A = F ∩ ⋂ x ∈ s, (F \ C x) := by
    ext z
    simp only [A, mem_sdiff, mem_iUnion, mem_inter_iff, mem_iInter, not_exists]
    constructor
    · rintro ⟨hzF, hzC⟩
      exact ⟨hzF, fun x hx => ⟨hzF, hzC x hx⟩⟩
    · rintro ⟨hzF, hzC⟩
      exact ⟨hzF, fun x hx => (hzC x hx).2⟩
  refine ⟨A, s.isCompact_biUnion (fun x _ => hCc x), ?_, ?_, ?_, ?_⟩
  · intro x hx
    obtain ⟨y, hy, hxy⟩ := mem_iUnion₂.mp (hs hx)
    have hxyC : x ∈ C y := by
      by_contra h
      exact hxy ⟨hTF hx, h⟩
    exact mem_iUnion₂.mpr ⟨y, hy, hxyC⟩
  · exact iUnion₂_subset fun x _ => hCF x
  · exact iUnion₂_subset fun x _ => hCV x
  · rw [hdiff]
    exact hF.inter (isClosed_biInter (fun x _ => hFC x))

/-- Compact-target version of the physical contour construction. This is
used inside one preliminary disk at a fixed label stage. -/
theorem exists_physical_contours_for_compact_singleton_target
    (hsard : SmoothPlanarSard) (hschoenflies : PlanarSchoenflies)
    {X : Type*} [TopologicalSpace X] [CompactSpace X] [T2Space X]
    (π : Sphere → X) (hπ : Continuous π) {F T V : Set X}
    (hF : IsClosed F) (hT : IsCompact T) (hTF : T ⊆ F)
    (hcomponents : ∀ x ∈ T, connectedComponentIn F x = {x})
    (hV : IsOpen V) (hTV : T ⊆ V) (hinfty : π OnePoint.infty ∉ V)
    (hVconn : IsPreconnected ((fun z : ℂ => π (z : Sphere)) ⁻¹' V)ᶜ)
    (hVunbounded : ¬ Bornology.IsBounded ((fun z : ℂ => π (z : Sphere)) ⁻¹' V)ᶜ)
    {G : Set Sphere} (hbad : ∀ p ∈ Gᶜ, π p ∈ F) :
    ∃ (f : ℂ → ℝ) (t : ℝ)
      (γ : ConnectedComponents {z // f z = t} → Circle → ℂ)
      (H : ConnectedComponents {z // f z = t} → ℂ ≃ₜ ℂ)
      (s : Set (ConnectedComponents {z // f z = t})),
      s.Finite ∧ ((fun z : ℂ => π (z : Sphere)) ⁻¹' T ⊆ ⋃ i ∈ s, jordanInterior (H i)) ∧
      s.Pairwise (fun i j => Disjoint (closure (jordanInterior (H i)))
        (closure (jordanInterior (H j)))) ∧
      (∀ i ∈ s, closure (jordanInterior (H i)) ⊆
        (fun z : ℂ => π (z : Sphere)) ⁻¹' V) ∧
      ∀ i ∈ s, ContMDiff (𝓡 1) (𝓘(ℝ, ℂ)) ∞ (γ i) ∧
        Topology.IsEmbedding (γ i) ∧ frontier (jordanInterior (H i)) = range (γ i) ∧
        (∀ z ∈ frontier (jordanInterior (H i)), (z : Sphere) ∈ G ∧ π (z : Sphere) ∉ F) := by
  obtain ⟨A, hAc, hTA, hAF, hAV, hFA⟩ :=
    exists_compact_piece_cover_of_singleton_components hF hT hTF hcomponents hV hTV
  let q : ℂ → X := fun z => π (z : Sphere)
  have hq : Continuous q := hπ.comp OnePoint.continuous_coe
  have hAp : IsCompact (q ⁻¹' A) :=
    isCompact_finite_preimage (hAc.isClosed.preimage hπ) (fun h => hinfty (hAV h))
  have hFp : IsClosed ((q ⁻¹' F) \ (q ⁻¹' A)) := by
    simpa only [preimage_sdiff] using hFA.preimage hq
  obtain ⟨f, t, γ, H, s, hs, hcov, hd, hinside, hcurves⟩ :=
    exists_finite_smooth_jordan_cover hsard hschoenflies hAp
      (preimage_mono hAF) hFp (hV.preimage hq) (preimage_mono hAV) hVconn hVunbounded
  refine ⟨f, t, γ, H, s, hs, (preimage_mono hTA).trans hcov, hd, hinside, ?_⟩
  intro i hi
  obtain ⟨hsmooth, hemb, hfront, havoid⟩ := hcurves i hi
  refine ⟨hsmooth, hemb, hfront, ?_⟩
  intro z hz
  have hnotF : π (z : Sphere) ∉ F := fun h => Set.disjoint_left.mp havoid hz h
  refine ⟨?_, hnotF⟩
  by_contra h
  exact hnotF (hbad _ h)

end CircleDomainRigidity

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Transfer_GridObstacles
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonEmbeddedArc.Arc.graphVertices_finite _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Singleton components of the lower-grid obstacle

At a free point, each coordinate has a unique trace, so at most one of its
finitely many distinct grid levels contains the point. Pointwise
compatibility for these choices excludes a nondegenerate component of
the lower-grid union. Boundary bumping removes all the other levels,
and adjoining compact totally disconnected dust preserves the singleton.
This is the topological reduction in Step 3 of finite transfer.
-/

open Set Function

namespace CircleDomainRigidity

/-- Pointwise compatibility for every selection of one level per active
label controls the entire finite grid near a point with unique traces. -/
theorem component_finite_grid_eq_singleton
    {X I J : Type*} [TopologicalSpace X] [CompactSpace X] [T2Space X]
    [Fintype I] [Fintype J] [Nonempty J]
    (H : I → J → Set X) (hH : ∀ i j, IsClosed (H i j)) {x : X}
    (hx : x ∈ ⋃ i, ⋃ j, H i j)
    (hunique : ∀ i j k, x ∈ H i j → x ∈ H i k → j = k)
    (hcompat : ∀ (A : Finset I) (k : I → J),
      ¬ (connectedComponentIn (⋃ i ∈ A, H i (k i)) x).Nontrivial) :
    connectedComponentIn (⋃ i, ⋃ j, H i j) x = {x} := by
  classical
  let A : Finset I := Finset.univ.filter (fun i => ∃ j, x ∈ H i j)
  let k : I → J := fun i =>
    if hi : ∃ j, x ∈ H i j then Classical.choose hi else Classical.choice inferInstance
  have hk (i : I) (hi : i ∈ A) : x ∈ H i (k i) := by
    have hi' : ∃ j, x ∈ H i j := (Finset.mem_filter.mp hi).2
    simpa only [k, dite_eq_left hi'] using Classical.choose_spec hi'
  have hpresent : (⋃ p ∈ (Finset.univ : Finset (I × J)),
      ⋃ (_ : x ∈ H p.1 p.2), H p.1 p.2) = ⋃ i ∈ A, H i (k i) := by
    ext y
    constructor
    · intro hy
      obtain ⟨⟨i, j⟩, _, hxij, hyij⟩ := by
        simpa only [mem_iUnion, exists_prop] using hy
      have hi : i ∈ A := Finset.mem_filter.mpr ⟨Finset.mem_univ _, ⟨j, hxij⟩⟩
      have heq : j = k i := hunique i j (k i) hxij (hk i hi)
      exact mem_iUnion₂.mpr ⟨i, hi, heq ▸ hyij⟩
    · intro hy
      obtain ⟨i, hi, hyi⟩ := mem_iUnion₂.mp hy
      exact mem_iUnion₂.mpr ⟨(i, k i), Finset.mem_univ _, mem_iUnion.mpr ⟨hk i hi, hyi⟩⟩
  have hxA : x ∈ ⋃ i ∈ A, H i (k i) := by
    obtain ⟨i, j, hxij⟩ := by simpa only [mem_iUnion] using hx
    have hi : i ∈ A := Finset.mem_filter.mpr ⟨Finset.mem_univ _, ⟨j, hxij⟩⟩
    exact mem_iUnion₂.mpr ⟨i, hi, hk i hi⟩
  have hsingle : connectedComponentIn (⋃ i ∈ A, H i (k i)) x = {x} :=
    (Set.not_nontrivial_iff.mp (hcompat A k)).eq_singleton_of_mem
      (mem_connectedComponentIn hxA)
  have hfull : (⋃ p ∈ (Finset.univ : Finset (I × J)), H p.1 p.2) =
      ⋃ i, ⋃ j, H i j := by
    ext y
    simp only [mem_iUnion, exists_prop, Finset.mem_univ, true_and, Prod.exists]
  rw [← hfull]
  apply component_finite_union_eq_singleton Finset.univ (fun p : I × J => H p.1 p.2)
    (fun p _ => hH p.1 p.2)
  · rwa [hfull]
  · rwa [hpresent]

/-- Adjoining dust creates no nondegenerate component through such a
point. The assertion also covers points absent from every lower grid. -/
theorem component_lower_grid_union_dust_eq_singleton
    {X I J : Type*} [TopologicalSpace X] [CompactSpace X] [T2Space X]
    [Fintype I] [Fintype J] [Nonempty J]
    (H : I → J → Set X) (hH : ∀ i j, IsClosed (H i j))
    {B : Set X} (hB : IsClosed B) (hTD : IsTotallyDisconnected B)
    {x : X} (hxB : x ∈ B)
    (hunique : ∀ i j k, x ∈ H i j → x ∈ H i k → j = k)
    (hcompat : ∀ (A : Finset I) (k : I → J),
      ¬ (connectedComponentIn (⋃ i ∈ A, H i (k i)) x).Nontrivial) :
    connectedComponentIn ((⋃ i, ⋃ j, H i j) ∪ B) x = {x} := by
  apply component_union_dust_eq_singleton
    (isClosed_iUnion_of_finite (fun i => isClosed_iUnion_of_finite (hH i)))
    hB hTD (Or.inr hxB)
  intro hx
  exact component_finite_grid_eq_singleton H hH hx hunique hcompat

end CircleDomainRigidity

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Topology_CompatibleFillingDisks
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Filling disks for the actual free/flagged grid setup

The levels below are the actual equally spaced circle levels of the compact
band graph. At a free point a singleton real band gives one level per label.
At a flagged point outside the terminal collision set, two distinct label
grids cannot occur. The pair family may represent each unordered pair in
either orientation. These facts discharge the lower-obstacle premise of
the descending contour construction.
-/

open Set Function
open scoped Topology Manifold ContDiff

namespace CircleDomainRigidity.FiniteTransfer

theorem reciprocal_circle_levels_injective (θ : ℝ) (N : ℕ) :
    Injective (fun k : Fin (N + 1) =>
      ((θ + (k.val : ℝ) * reciprocalGridStep N : ℝ) : UnitAddCircle)) := by
  intro k l hkl
  obtain ⟨m, hm⟩ := (addCircle_eq_iff_exists_int 1 _ _).mp hkl
  have hh := reciprocalGridStep_pos N
  have hden := reciprocalGridStep_mul_denominator N
  have hbound (i : Fin (N + 1)) : 0 ≤ (i.val : ℝ) * reciprocalGridStep N ∧
      (i.val : ℝ) * reciprocalGridStep N < 1 := by
    refine ⟨mul_nonneg (Nat.cast_nonneg _) hh.le, ?_⟩
    have hi : (i.val : ℝ) < (N : ℝ) + 1 := by exact_mod_cast i.isLt
    nlinarith [mul_pos (sub_pos.mpr hi) hh]
  have hmlo : (-1 : ℤ) < m := by
    have : (-1 : ℝ) < (m : ℝ) := by linarith [(hbound k).1, (hbound l).2]
    exact_mod_cast this
  have hmhi : m < (1 : ℤ) := by
    have : (m : ℝ) < 1 := by linarith [(hbound k).2, (hbound l).1]
    exact_mod_cast this
  have hm0 : m = 0 := by omega
  subst m
  simp only [Int.cast_zero, zero_mul, add_zero] at hm
  apply Fin.ext
  have hk : (k.val : ℝ) = (l.val : ℝ) := by nlinarith
  exact_mod_cast hk

end CircleDomainRigidity.FiniteTransfer

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Transfer_GridCompatibility
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonMobius.sphereMetric _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Transferring almost-everywhere compatibility to actual grid choices

Independent shifts for distinct labels have the required finite product law.
Each shifted grid level has a law absolutely continuous with respect to Haar
measure on the circle. Consequently every completed-product null failure
set remains null for actual grid tuples. Repeated levels of one label are
not treated as independent; the tuple map explicitly requires distinct labels.
-/

open Set MeasureTheory Function ProbabilityTheory

namespace CircleDomainRigidity.FiniteTransfer

/-- Absolute continuity passes to the finite products needed for level laws. -/
theorem absolutelyContinuous_pi_fin {T : Type*} [MeasurableSpace T] :
    ∀ (n : ℕ) (μ ν : Fin n → Measure T) [∀ i, SigmaFinite (μ i)] [∀ i, SigmaFinite (ν i)],
      (∀ i, μ i ≪ ν i) → Measure.pi μ ≪ Measure.pi ν := by
  intro n
  induction n with
  | zero =>
      intro μ ν _ _ _
      rw [Measure.pi_of_empty μ, Measure.pi_of_empty ν]
  | succ n ih =>
      intro μ ν _ _ h
      let e := MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) => T) 0
      have hμ := measurePreserving_piFinSuccAbove μ (0 : Fin (n + 1))
      have hν := measurePreserving_piFinSuccAbove ν (0 : Fin (n + 1))
      have htail := ih (fun i => μ ((0 : Fin (n + 1)).succAbove i))
        (fun i => ν ((0 : Fin (n + 1)).succAbove i))
        (fun i => h ((0 : Fin (n + 1)).succAbove i))
      have hprod := (h 0).prod htail
      have hback := hprod.map e.symm.measurable
      rw [← hμ.map_eq, ← hν.map_eq] at hback
      change ((Measure.pi μ).map e).map e.symm ≪ ((Measure.pi ν).map e).map e.symm at hback
      have heid : e.symm ∘ e = id := by funext x; exact e.symm_apply_apply x
      simpa only [Measure.map_map e.symm.measurable e.measurable, heid, Measure.map_id] using hback

/-- A uniform shift on a subinterval of a period, followed by any circle
translation, has a Haar-absolutely-continuous law. -/
theorem quasiMeasurePreserving_translated_grid_level {h : ℝ}
    (_hh : 0 < h) (hsmall : h ≤ 1) (c : ℝ) :
    Measure.QuasiMeasurePreserving (fun θ : ℝ => ((θ + c : ℝ) : UnitAddCircle))
      (shiftLaw h) volume := by
  have hle : volume.restrict (Icc (0 : ℝ) h) ≤ volume.restrict (Icc (0 : ℝ) 1) :=
    Measure.restrict_mono (Icc_subset_Icc_right hsmall) le_rfl
  have hac : shiftLaw h ≪ volume.restrict (Ioc (0 : ℝ) (0 + 1)) := by
    rw [shiftLaw_eq, zero_add, restrict_Ioc_eq_restrict_Icc]
    exact (Measure.absolutelyContinuous_of_le hle).smul_left _
  have hquot := (AddCircle.measurePreserving_mk (T := (1 : ℝ)) 0).quasiMeasurePreserving.mono_left hac
  have htranslate := (measurePreserving_add_right (volume : Measure UnitAddCircle)
    (c : UnitAddCircle)).quasiMeasurePreserving
  convert htranslate.comp hquot using 1
  all_goals try with_reducible_and_instances rfl
  ext θ
  simp only [Function.comp_apply, AddCircle.coe_add]

/-- Finite products of the translated grid levels remain absolutely
continuous with respect to independent Haar measure. -/
theorem quasiMeasurePreserving_grid_levels {n : ℕ} {h : ℝ}
    (hh : 0 < h) (hsmall : h ≤ 1) (c : Fin n → ℝ) :
    Measure.QuasiMeasurePreserving
      (fun θ : Fin n → ℝ => fun i => ((θ i + c i : ℝ) : UnitAddCircle))
      (Measure.pi (fun _ : Fin n => shiftLaw h))
      (Measure.pi (fun _ : Fin n => volume)) := by
  let := shiftLaw_isProbabilityMeasure hh
  have hf i := quasiMeasurePreserving_translated_grid_level hh hsmall (c i)
  refine ⟨measurable_pi_iff.mpr (fun i => (hf i).measurable.comp (measurable_pi_apply i)), ?_⟩
  rw [Measure.pi_map_pi (fun i => (hf i).aemeasurable)]
  exact absolutelyContinuous_pi_fin n _ _ (fun i => (hf i).absolutelyContinuous)

/-- Selecting distinct labels from an independent finite shift family
preserves their product law. -/
theorem measurePreserving_distinct_grid_labels {m n : ℕ} {h : ℝ}
    (hh : 0 < h) (labels : Fin n → Fin m) (hinj : Injective labels) :
    MeasurePreserving (fun θ : Fin m → ℝ => fun j => θ (labels j))
      (Measure.pi (fun _ : Fin m => shiftLaw h))
      (Measure.pi (fun _ : Fin n => shiftLaw h)) := by
  let := shiftLaw_isProbabilityMeasure hh
  have hind := (iIndepFun_pi (μ := fun _ : Fin m => shiftLaw h)
    (X := fun _ => id) (fun _ => aemeasurable_id)).precomp hinj
  refine ⟨measurable_pi_iff.mpr (fun j => measurable_pi_apply (labels j)), ?_⟩
  have hmap := hind.map_fun_eq_pi_map (fun j => (measurable_pi_apply (labels j)).aemeasurable)
  simpa only [(measurePreserving_eval (fun _ : Fin m => shiftLaw h) _).map_eq] using hmap

/-- Every completed-product null event is avoided almost surely by a
chosen tuple of actual grid levels on distinct labels. Offsets may be
any lattice offsets, since the proof allows every real translation. -/
theorem ae_grid_tuple_avoids_null_event {m d : ℕ} {h : ℝ}
    (hh : 0 < h) (hsmall : h ≤ 1) (labels : Fin (d + 1) → Fin m)
    (hinj : Injective labels) (c : Fin (d + 1) → ℝ)
    (E : Set (UnitAddCircle × (Fin d → UnitAddCircle)))
    (hE : (volume.prod (Measure.pi (fun _ : Fin d => volume))) E = 0) :
    ∀ᵐ θ ∂Measure.pi (fun _ : Fin m => shiftLaw h),
      (((θ (labels 0) + c 0 : ℝ) : UnitAddCircle),
        fun i : Fin d => ((θ (labels i.succ) + c i.succ : ℝ) : UnitAddCircle)) ∉ E := by
  let e := MeasurableEquiv.piFinSuccAbove (fun _ : Fin (d + 1) => UnitAddCircle) 0
  have he := (measurePreserving_piFinSuccAbove
    (fun _ : Fin (d + 1) => (volume : Measure UnitAddCircle)) 0).quasiMeasurePreserving
  have hq := he.comp ((quasiMeasurePreserving_grid_levels hh hsmall c).comp
    (measurePreserving_distinct_grid_labels hh labels hinj).quasiMeasurePreserving)
  have hn := hq.preimage_null hE
  change (Measure.pi (fun _ : Fin m => shiftLaw h))
    {θ | (((θ (labels 0) + c 0 : ℝ) : UnitAddCircle),
      fun i : Fin d => ((θ (labels ((0 : Fin (d + 1)).succAbove i)) +
        c ((0 : Fin (d + 1)).succAbove i) : ℝ) : UnitAddCircle)) ∈ E} = 0 at hn
  apply ae_iff.mpr
  simpa only [not_not, ofPred_mem_eq, Fin.succAbove_zero] using hn

end CircleDomainRigidity.FiniteTransfer

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Transfer_GridFamilies
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonEmbeddedArc.Arc.graphVertices_finite _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Simultaneous compatibility of every lattice tuple

The finite-transfer construction needs one choice of shifts that avoids
every bad tuple formed from distinct labels and lattice levels. The
integer offsets constitute a countable family, so the individual
absolute-continuity conclusions hold simultaneously. In particular they
hold for the finite period-one grids at reciprocal-integer spacings.
-/

open Set MeasureTheory Function

namespace CircleDomainRigidity.FiniteTransfer

/-- All choices of lattice offsets and distinct labels simultaneously
avoid their prescribed completed-product null events. -/
theorem ae_all_grid_tuples_avoid_null_events {m : ℕ} {h : ℝ}
    (hh : 0 < h) (hsmall : h ≤ 1)
    (E : (d : ℕ) → (Fin (d + 1) → Fin m) →
      Set (UnitAddCircle × (Fin d → UnitAddCircle)))
    (hE : ∀ d labels, Injective labels →
      (volume.prod (Measure.pi (fun _ : Fin d => volume))) (E d labels) = 0) :
    ∀ᵐ θ ∂Measure.pi (fun _ : Fin m => shiftLaw h),
      ∀ (d : ℕ) (labels : Fin (d + 1) → Fin m), Injective labels →
      ∀ k : Fin (d + 1) → ℤ,
        (((θ (labels 0) + (k 0 : ℝ) * h : ℝ) : UnitAddCircle),
          fun i : Fin d =>
            ((θ (labels i.succ) + (k i.succ : ℝ) * h : ℝ) : UnitAddCircle)) ∉
          E d labels := by
  apply ae_all_iff.mpr
  intro d
  apply ae_all_iff.mpr
  intro labels
  by_cases hi : Injective labels
  · have hall := ae_all_iff.mpr (fun k : Fin (d + 1) → ℤ =>
      ae_grid_tuple_avoids_null_event hh hsmall labels hi
        (fun i => (k i : ℝ) * h) (E d labels) (hE d labels hi))
    exact hall.mono (fun _ hθ _ => hθ)
  · exact Filter.Eventually.of_forall (fun _ h => False.elim (hi h))

/-- Specialization to the actual product law of reciprocal-integer
grids. Compatibility is retained when the spacing is chosen later. -/
theorem ae_reciprocal_grid_tuples_avoid_null_events {m : ℕ} (N : ℕ)
    (E : (d : ℕ) → (Fin (d + 1) → Fin m) →
      Set (UnitAddCircle × (Fin d → UnitAddCircle)))
    (hE : ∀ d labels, Injective labels →
      (volume.prod (Measure.pi (fun _ : Fin d => volume))) (E d labels) = 0) :
    ∀ᵐ θ ∂reciprocalGridLaw m N,
      ∀ (d : ℕ) (labels : Fin (d + 1) → Fin m), Injective labels →
      ∀ k : Fin (d + 1) → ℤ,
        (((θ (labels 0) + (k 0 : ℝ) * reciprocalGridStep N : ℝ) : UnitAddCircle),
          fun i : Fin d => ((θ (labels i.succ) +
            (k i.succ : ℝ) * reciprocalGridStep N : ℝ) : UnitAddCircle)) ∉ E d labels :=
  ae_all_grid_tuples_avoid_null_events (reciprocalGridStep_pos N)
    (reciprocalGridStep_le_one N) E hE

end CircleDomainRigidity.FiniteTransfer

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Transfer_GraphGridCompatibility
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions _root_.OAI.CircleDomainRigidity.finiteSphericalArea _root_.OAI.CircleDomainRigidity.sphereFirstCountableTopology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Ordered grid selection for a finite list containing both real and
masked period coordinates. It uses their actual closed level graphs. -/

open Set Function Filter MeasureTheory

namespace CircleDomainRigidity.FiniteTransfer

 theorem isClosed_reciprocalGraphLevel
    {R : Set (Sphere × UnitAddCircle)} (hR : IsClosed R)
    (θ : ℝ) (N : ℕ) (k : Fin (N + 1)) :
    IsClosed (reciprocalGraphLevel R θ N k) :=
  hR.preimage (continuous_id.prodMk continuous_const)

theorem ae_ordered_graph_grid_compatibility
    {S : Type*} {n : ℕ}
    (R : Fin n → Set (Sphere × UnitAddCircle)) (B : Set Sphere) (σ : S → Sphere)
    (hnull : ∀ (j : Fin n) (d : ℕ) (labels : Fin d → Fin n),
      (∀ i, (labels i).val < j.val) →
      (volume.prod (Measure.pi (fun _ : Fin d => (volume : Measure UnitAddCircle))))
        (freeComponentFailure (B \ range σ) (R j)
          R labels) = 0)
    (N : ℕ) :
    ∀ᵐ θ ∂reciprocalGridLaw n N, OrderedGraphGridCompatibility R θ N B σ := by
  classical
  let E (d : ℕ) (labels : Fin (d + 1) → Fin n) :
      Set (UnitAddCircle × (Fin d → UnitAddCircle)) :=
    if h : ∀ i : Fin d, (labels i.succ).val < (labels 0).val then
      freeComponentFailure (B \ range σ) (R (labels 0))
        R (fun i => labels i.succ)
    else ∅
  have hE (d : ℕ) (labels : Fin (d + 1) → Fin n) (_ : Injective labels) :
      (volume.prod (Measure.pi (fun _ : Fin d => (volume : Measure UnitAddCircle))))
        (E d labels) = 0 := by
    dsimp only [E]
    split_ifs with h
    · exact hnull _ _ _ h
    · exact measure_empty
  filter_upwards [ae_reciprocal_grid_tuples_avoid_null_events N E hE] with θ hθ
  intro x hxB hxσ j hxj I hIj k hnon
  obtain ⟨kj, hxj⟩ := mem_iUnion.mp hxj
  let e := I.orderEmbOfFin rfl
  have hmem (i : Fin I.card) : e i ∈ I := I.orderEmbOfFin_mem rfl i
  have honto (l : Fin n) (hl : l ∈ I) : ∃ i : Fin I.card, e i = l := by
    let l' : I := ⟨l, hl⟩
    exact ⟨(I.orderIsoOfFin rfl).symm l',
      congrArg Subtype.val ((I.orderIsoOfFin rfl).apply_symm_apply l')⟩
  let labels : Fin (I.card + 1) → Fin n := Fin.cons j e
  have hjnot : j ∉ range e := by
    rintro ⟨i, hi⟩
    have hh := hIj (e i) (hmem i)
    rw [hi] at hh
    exact (lt_irrefl _ hh)
  have hlabels : Injective labels := Fin.cons_injective_of_injective hjnot e.injective
  let offsets : Fin (I.card + 1) → ℤ := Fin.cons (kj.val : ℤ) (fun i => (k (e i)).val)
  let t : UnitAddCircle := ((θ j + (kj.val : ℝ) * reciprocalGridStep N : ℝ) : UnitAddCircle)
  let τ : Fin I.card → UnitAddCircle := fun i =>
    ((θ (e i) + ((k (e i)).val : ℝ) * reciprocalGridStep N : ℝ) : UnitAddCircle)
  have hlt : ∀ i : Fin I.card, (labels i.succ).val < (labels 0).val := by
    intro i
    simpa only [labels, Fin.cons_succ, Fin.cons_zero] using hIj (e i) (hmem i)
  have hav := hθ I.card labels hlabels offsets
  have hnot : (t, τ) ∉ freeComponentFailure (B \ range σ) (R j)
      R e := by
    simpa only [E, dite_eq_left hlt, labels, offsets, Fin.cons_zero, Fin.cons_succ,
      Int.cast_natCast, t, τ] using hav
  apply hnot
  refine ⟨(x, t, τ), ⟨⟨hxB, hxσ⟩, hxj, ?_⟩, rfl⟩
  change (connectedComponentIn
    {z | (z, τ) ∈ finiteLevelUnionGraph R e} x).Nontrivial
  have hset : {z | (z, τ) ∈ finiteLevelUnionGraph R e} =
      ⋃ i ∈ I, reciprocalGraphLevel (R i) (θ i) N (k i) := by
    ext z
    simp only [finiteLevelUnionGraph, mem_iUnion, mem_preimage, mem_ofPred_eq]
    constructor
    · rintro ⟨i, hi⟩
      exact ⟨e i, hmem i, hi⟩
    · rintro ⟨l, hl, hz⟩
      obtain ⟨i, rfl⟩ := honto l hl
      exact ⟨i, hz⟩
  rwa [hset]

end CircleDomainRigidity.FiniteTransfer

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Topology_GraphFillingDisks
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonEmbeddedArc.Arc.graphVertices_finite _root_.OAI.CannonMobius.sphereMetric _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions _root_.OAI.CircleDomainRigidity.finiteSphericalArea _root_.OAI.CircleDomainRigidity.sphereFirstCountableTopology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Actual filling contours for mixed real and masked period graphs.
Only the graph fibers at free points and the original marked band
intervals enter the collision argument. Empty fibers outside a mask
are allowed. -/

open Set Function
open scoped Topology Manifold ContDiff

namespace CircleDomainRigidity.FiniteTransfer

 theorem reciprocalGraphLevel_unique_of_subsingleton
    {R : Set (Sphere × UnitAddCircle)} {x : Sphere} {θ : ℝ} {N : ℕ}
    (htrace : {t : UnitAddCircle | (x, t) ∈ R}.Subsingleton)
    {k l : Fin (N + 1)} (hk : x ∈ reciprocalGraphLevel R θ N k)
    (hl : x ∈ reciprocalGraphLevel R θ N l) : k = l :=
  reciprocal_circle_levels_injective θ N (htrace hk hl)

 theorem latticeBandIncidence_of_reciprocalGraphLevel
    {R : Set (Sphere × UnitAddCircle)} {x : Sphere} {θ a b : ℝ} {N : ℕ}
    (hband : {t : UnitAddCircle | (x, t) ∈ R} ⊆
      ((↑) : ℝ → UnitAddCircle) '' Icc a b)
    {k : Fin (N + 1)} (hk : x ∈ reciprocalGraphLevel R θ N k) :
    θ ∈ latticeBandIncidence (reciprocalGridStep N) a b := by
  obtain ⟨r, hr, heq⟩ := hband hk
  obtain ⟨m, hm⟩ := (addCircle_eq_iff_exists_int 1 _ _).mp heq
  refine ⟨(k.val : ℤ) + m * (N + 1), ?_⟩
  have hden : ((N : ℝ) + 1) * reciprocalGridStep N = 1 := by
    simpa only [mul_comm] using reciprocalGridStep_mul_denominator N
  have hval : θ + (((k.val : ℤ) + m * (N + 1) : ℤ) : ℝ) * reciprocalGridStep N = r := by
    push_cast
    calc
      _ = θ + (k.val : ℝ) * reciprocalGridStep N +
          (m : ℝ) * (((N : ℝ) + 1) * reciprocalGridStep N) := by ring
      _ = r := by rw [hden]; simpa only [mul_one] using hm.symm
  exact hval.symm ▸ hr

theorem no_two_flagged_graph_grids_outside_terminals
    {n N : ℕ} {P S : Type*}
    (R : Fin n → Set (Sphere × UnitAddCircle)) (σ : S → Sphere)
    (a b : Fin n → S → ℝ) (θ : Fin n → ℝ)
    (pairs : P → Fin n × Fin n)
    (hpairs : ∀ i j : Fin n, i ≠ j → ∃ p, pairs p = (i, j) ∨ pairs p = (j, i))
    (F : Set S)
    (hband : ∀ i s, {t : UnitAddCircle | (σ s, t) ∈ R i} ⊆
      ((↑) : ℝ → UnitAddCircle) '' Icc (a i s) (b i s))
    {s : S} (hs : s ∉ gridTerminalIndices F (reciprocalGridStep N) pairs a b θ)
    {i j : Fin n} (hij : i ≠ j)
    (hi : σ s ∈ ⋃ k, reciprocalGraphLevel (R i) (θ i) N k)
    (hj : σ s ∈ ⋃ k, reciprocalGraphLevel (R j) (θ j) N k) : False := by
  obtain ⟨p, hp⟩ := hpairs i j hij
  obtain ⟨k, hk⟩ := mem_iUnion.mp hi
  obtain ⟨l, hl⟩ := mem_iUnion.mp hj
  apply hs
  right
  refine ⟨p, ?_⟩
  change θ (pairs p).1 ∈ latticeBandIncidence _ _ _ ∧
    θ (pairs p).2 ∈ latticeBandIncidence _ _ _
  rcases hp with hp | hp
  · rw [hp]
    exact ⟨latticeBandIncidence_of_reciprocalGraphLevel (hband i s) hk,
      latticeBandIncidence_of_reciprocalGraphLevel (hband j s) hl⟩
  · rw [hp]
    exact ⟨latticeBandIncidence_of_reciprocalGraphLevel (hband j s) hl,
      latticeBandIncidence_of_reciprocalGraphLevel (hband i s) hk⟩

theorem lower_obstacle_singleton_of_compatible_graphs
    {n N : ℕ} {P S : Type*}
    (R : Fin n → Set (Sphere × UnitAddCircle)) (hR : ∀ i, IsClosed (R i))
    (σ : S → Sphere) (a b : Fin n → S → ℝ) (θ : Fin n → ℝ)
    (pairs : P → Fin n × Fin n)
    (hpairs : ∀ i j : Fin n, i ≠ j → ∃ p, pairs p = (i, j) ∨ pairs p = (j, i))
    (F : Set S)
    (hband : ∀ i s, {t : UnitAddCircle | (σ s, t) ∈ R i} ⊆
      ((↑) : ℝ → UnitAddCircle) '' Icc (a i s) (b i s))
    {B A : Set Sphere} (hB : IsClosed B) (hTD : IsTotallyDisconnected B) (hAB : A ⊆ B)
    (hnoterm : Disjoint A (σ '' gridTerminalIndices F (reciprocalGridStep N) pairs a b θ))
    (hfree : ∀ x ∈ A, x ∉ range σ → ∀ i,
      {t : UnitAddCircle | (x, t) ∈ R i}.Subsingleton)
    (hcompat : OrderedGraphGridCompatibility R θ N A σ)
    (j : Fin n) {x : Sphere}
    (hx : x ∈ A ∩ ⋃ k, reciprocalGraphLevel (R j) (θ j) N k) :
    connectedComponentIn
      (B ∪ ⋃ i : Fin n, ⋃ (_ : i.val < j.val), ⋃ k,
        reciprocalGraphLevel (R i) (θ i) N k) x = {x} := by
  let L : Fin n → Fin (N + 1) → Set Sphere := fun i k =>
    reciprocalGraphLevel (R i) (θ i) N k
  have hL (i : Fin n) (k : Fin (N + 1)) : IsClosed (L i k) :=
    isClosed_reciprocalGraphLevel (hR i) (θ i) N k
  by_cases hflag : x ∈ range σ
  · obtain ⟨s, rfl⟩ := hflag
    have hs : s ∉ gridTerminalIndices F (reciprocalGridStep N) pairs a b θ := by
      intro hs
      exact Set.disjoint_left.mp hnoterm hx.1 ⟨s, hs, rfl⟩
    have hlower : σ s ∉ ⋃ i : Fin n, ⋃ (_ : i.val < j.val), ⋃ k, L i k := by
      intro h
      obtain ⟨i, hi⟩ := mem_iUnion.mp h
      obtain ⟨hij, hi⟩ := mem_iUnion.mp hi
      exact no_two_flagged_graph_grids_outside_terminals R σ a b θ pairs hpairs F hband hs
        (fun heq => (ne_of_lt hij) (congrArg Fin.val heq)) hi hx.2
    rw [union_comm]
    apply component_union_dust_eq_singleton
      (isClosed_iUnion_of_finite (fun i => isClosed_iUnion_of_finite
        (fun _ => isClosed_iUnion_of_finite (hL i)))) hB hTD (Or.inr (hAB hx.1))
    exact fun h => (hlower h).elim
  · let e : Fin j.val → Fin n := fun i => ⟨i.val, i.isLt.trans j.isLt⟩
    have heq : (⋃ i : Fin j.val, ⋃ k, L (e i) k) =
        ⋃ i : Fin n, ⋃ (_ : i.val < j.val), ⋃ k, L i k := by
      ext y
      constructor
      · rintro ⟨_, ⟨i, hi, rfl⟩, hy⟩
        exact mem_iUnion₂.mpr ⟨e i, i.isLt, hy⟩
      · intro hy
        obtain ⟨i, hi, hy⟩ := mem_iUnion₂.mp hy
        exact mem_iUnion.mpr ⟨⟨i.val, hi⟩, hy⟩
    have hwhole : connectedComponentIn ((⋃ i : Fin j.val, ⋃ k, L (e i) k) ∪ B) x = {x} := by
      apply component_lower_grid_union_dust_eq_singleton (fun i k => L (e i) k)
        (fun i k => hL (e i) k) hB hTD (hAB hx.1)
      · intro i k l hk hl
        exact reciprocalGraphLevel_unique_of_subsingleton (hfree x hx.1 hflag (e i)) hk hl
      · intro I k hnon
        let k' : Fin n → Fin (N + 1) := fun i => if hi : i.val < j.val then k ⟨i.val, hi⟩ else 0
        have hsmall : ∀ i ∈ I.image e, i.val < j.val := by
          intro i hi
          obtain ⟨r, _, rfl⟩ := Finset.mem_image.mp hi
          exact r.isLt
        apply hcompat x hx.1 hflag j hx.2 (I.image e) hsmall k'
        apply hnon.mono (connectedComponentIn_mono x ?_)
        intro y hy
        obtain ⟨i, hi, hy⟩ := mem_iUnion₂.mp hy
        apply mem_iUnion₂.mpr
        refine ⟨e i, Finset.mem_image.mpr ⟨i, hi, rfl⟩, ?_⟩
        simpa only [k', e, dite_eq_left i.isLt] using hy
    rw [union_comm, ← heq]
    exact hwhole

end CircleDomainRigidity.FiniteTransfer

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Selection_TerminalRemainder
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonEmbeddedArc.Arc.graphVertices_finite _root_.OAI.CannonMobius.sphereMetric _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions _root_.OAI.CircleDomainRigidity.finiteSphericalArea _root_.OAI.CircleDomainRigidity.sphereFirstCountableTopology
attribute [-simp] _root_.OAI.CircleDomainRigidity.CompactScalarModel.postcompose_coefficient _root_.OAI.CircleDomainRigidity.FiniteTransfer.infty_mem_cutoffCore _root_.OAI.CircleDomainRigidity.FiniteTransfer.realChartDomain_sphericalDiskUnion _root_.OAI.CircleDomainRigidity.FiniteTransfer.realChartDomain_union _root_.OAI.CircleDomainRigidity.affineSphere_coe _root_.OAI.CircleDomainRigidity.affineSphere_infty _root_.OAI.CircleDomainRigidity.centeredJordanCoordinate_self _root_.OAI.CircleDomainRigidity.chartSymm_coe_apply _root_.OAI.CircleDomainRigidity.chart_coe_apply _root_.OAI.CircleDomainRigidity.chart_infty_apply _root_.OAI.CircleDomainRigidity.extendAtInfinity_coe _root_.OAI.CircleDomainRigidity.extendAtInfinity_infty _root_.OAI.CircleDomainRigidity.sphereInv_infty _root_.OAI.CircleDomainRigidity.sphereInv_sphereInv _root_.OAI.CircleDomainRigidity.sphereInv_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# The safe region for filling after the terminals are selected

The remaining quotient dust is compact and relatively clopen. Its open
neighborhood is chosen to avoid both the retained physical core and all
closed terminal caps, so every later filling closure inherits both
separations.
-/

open Set Function
open scoped Topology

noncomputable section

namespace CircleDomainRigidity.FiniteTransfer

theorem terminal_remainder_safe_region
    {I : Type*} [Fintype I] {G B C : Set Sphere} {π : Sphere → Sphere}
    (hπ : Continuous π) (hclosed : IsClosedMap π) (hsurj : Surjective π)
    (hr : ∀ x y, π x = π y ↔
      x = y ∨ (x ∈ Gᶜ ∧ y ∈ connectedComponentIn Gᶜ x))
    (hB : IsClosed B) (hBC : B ⊆ (π '' C)ᶜ) (hC : IsCompact C)
    (hinfty : OnePoint.infty ∈ C)
    {p : I → Sphere} {O : I → Set Sphere} (D : PhysicalTerminalDisks G π B p O) :
    let A := terminalRemainder π B D.H
    let W := (π '' C)ᶜ ∩ (closedTerminalImages π D.H)ᶜ
    IsCompact A ∧ A ⊆ B ∧ IsClosed (B \ A) ∧ IsOpen W ∧ A ⊆ W ∧
      π OnePoint.infty ∉ A := by
  have hrem := compact_clopen_dust_remainder G π hπ hclosed hsurj hr D.H hB
    hB.isCompact (Subset.refl B) (by simp) D.frontier_good
  have hrem' : IsCompact (terminalRemainder π B D.H) ∧ terminalRemainder π B D.H ⊆ B ∧
      IsClosed (B \ terminalRemainder π B D.H) ∧
      Disjoint (terminalRemainder π B D.H) (closedTerminalImages π D.H) := by
    simpa only [terminalRemainder, sphericalDiskUnion, Set.image_iUnion, closedTerminalImages] using hrem
  have hclosedT : IsClosed (closedTerminalImages π D.H) :=
    isClosed_iUnion_of_finite (fun i =>
      (((isCompact_closure_jordanInterior (D.H i)).image OnePoint.continuous_coe).image hπ).isClosed)
  refine ⟨hrem'.1, hrem'.2.1, hrem'.2.2.1,
    (hC.image hπ).isClosed.isOpen_compl.inter hclosedT.isOpen_compl, ?_, ?_⟩
  · intro x hx
    exact ⟨hBC (hrem'.2.1 hx), Set.disjoint_left.mp hrem'.2.2.2 hx⟩
  · intro hx
    exact hBC (hrem'.2.1 hx) ⟨OnePoint.infty, hinfty, rfl⟩

theorem PhysicalTerminalDisks.index_mem_quotient_union
    {I : Type*} {G B : Set Sphere} {π : Sphere → Sphere} (hsurj : Surjective π)
    {p : I → Sphere} {O : I → Set Sphere} (D : PhysicalTerminalDisks G π B p O)
    {i : I} (hi : p i ≠ π OnePoint.infty) : p i ∈ π '' sphericalDiskUnion D.H := by
  obtain ⟨x, hx⟩ := hsurj (p i)
  cases x using OnePoint.rec with
  | infty => exact (hi hx.symm).elim
  | coe z =>
    exact ⟨(z : Sphere), (coe_mem_sphericalDiskUnion D.H z).mpr
      ⟨i, D.fiber_subset i hx⟩, hx⟩

theorem PhysicalTerminalDisks.remainder_avoids_indices
    {I : Type*} {G B : Set Sphere} {π : Sphere → Sphere} (hsurj : Surjective π)
    {p : I → Sphere} {O : I → Set Sphere} (D : PhysicalTerminalDisks G π B p O)
    (hp : ∀ i, p i ≠ π OnePoint.infty) :
    Disjoint (terminalRemainder π B D.H) (range p) := by
  apply Set.disjoint_left.mpr
  rintro x hx ⟨i, rfl⟩
  exact hx.2 (D.index_mem_quotient_union hsurj (hp i))

/-- Every closed filling drawn in the safe region misses both the core
and every closed terminal cap. -/
theorem filling_closures_avoid_core_and_terminals
    {I J : Type*} {C : Set Sphere} {π : Sphere → Sphere}
    (T : I → ℂ ≃ₜ ℂ) (F : J → ℂ ≃ₜ ℂ)
    (hF : ∀ j, closure (jordanInterior (F j)) ⊆
      (fun z : ℂ => π (z : Sphere)) ⁻¹' ((π '' C)ᶜ ∩ (closedTerminalImages π T)ᶜ)) :
    (∀ j, Disjoint (((↑) : ℂ → Sphere) '' closure (jordanInterior (F j))) C) ∧
      ∀ i j, Disjoint (closure (jordanInterior (T i))) (closure (jordanInterior (F j))) := by
  constructor
  · intro j
    apply Set.disjoint_left.mpr
    rintro _ ⟨z, hz, rfl⟩ hc
    exact (hF j hz).1 ⟨(z : Sphere), hc, rfl⟩
  · intro i j
    apply Set.disjoint_left.mpr
    intro z hzT hzF
    exact (hF j hzF).2 (mem_iUnion.mpr ⟨i, (z : Sphere), ⟨z, hzT, rfl⟩, rfl⟩)

end CircleDomainRigidity.FiniteTransfer

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Transfer_SubordinateGridStage
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonMobius.sphereMetric _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions _root_.OAI.CircleDomainRigidity.finiteSphericalArea _root_.OAI.CircleDomainRigidity.sphereFirstCountableTopology
attribute [-simp] _root_.OAI.CircleDomainRigidity.CompactScalarModel.postcompose_coefficient _root_.OAI.CircleDomainRigidity.FiniteTransfer.coe_mem_sphericalCore _root_.OAI.CircleDomainRigidity.FiniteTransfer.coe_mem_sphericalDiskUnion _root_.OAI.CircleDomainRigidity.FiniteTransfer.infty_mem_cutoffCore _root_.OAI.CircleDomainRigidity.FiniteTransfer.infty_mem_sphericalCore _root_.OAI.CircleDomainRigidity.FiniteTransfer.infty_not_mem_sphericalDiskUnion _root_.OAI.CircleDomainRigidity.FiniteTransfer.realChartDomain_union _root_.OAI.CircleDomainRigidity.affineSphere_coe _root_.OAI.CircleDomainRigidity.affineSphere_infty _root_.OAI.CircleDomainRigidity.centeredJordanCoordinate_self _root_.OAI.CircleDomainRigidity.chartSymm_coe_apply _root_.OAI.CircleDomainRigidity.chart_coe_apply _root_.OAI.CircleDomainRigidity.chart_infty_apply _root_.OAI.CircleDomainRigidity.extendAtInfinity_coe _root_.OAI.CircleDomainRigidity.extendAtInfinity_infty _root_.OAI.CircleDomainRigidity.sphereInv_infty _root_.OAI.CircleDomainRigidity.sphereInv_sphereInv _root_.OAI.CircleDomainRigidity.sphereInv_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! One descending grid stage retains a prescribed local branch
neighborhood for every selected closed filling disk. -/

open Set Filter Function
open scoped Topology Manifold ContDiff

namespace CircleDomainRigidity

theorem exists_subordinate_grid_stage_contours
    (hsard : SmoothPlanarSard) (hschoenflies : PlanarSchoenflies)
    (G : Set Sphere) (π : Sphere → Sphere) (hπ : Continuous π)
    (hclosed : IsClosedMap π) (hsurj : Surjective π)
    (hr : ∀ x y, π x = π y ↔
      x = y ∨ (x ∈ Gᶜ ∧ y ∈ connectedComponentIn Gᶜ x))
    {B A W J F : Set Sphere} (hB : IsClosed B) (hTD : IsTotallyDisconnected B)
    (hA : IsCompact A) (hAB : A ⊆ B) (hBA : IsClosed (B \ A))
    (hW : IsOpen W) (hAW : A ⊆ W) (hinfty : π OnePoint.infty ∉ A)
    (hJ : IsClosed J) (hF : IsClosed F) (hBF : B ⊆ F)
    (hsingle : ∀ x ∈ A ∩ J, connectedComponentIn F x = {x})
    (hbad : ∀ p ∈ Gᶜ, π p ∈ B)
    (Nbh : A → Set Sphere) (hNbh : ∀ a, IsOpen (Nbh a))
    (haNbh : ∀ a, a.val ∈ Nbh a) :
    ∃ (n : ℕ) (H : Fin n → ℂ ≃ₜ ℂ) (γ : Fin n → Circle → ℂ),
      ((fun z : ℂ => π (z : Sphere)) ⁻¹' (A ∩ J) ⊆ ⋃ i, jordanInterior (H i)) ∧
      Pairwise (Disjoint on fun i => closure (jordanInterior (H i))) ∧
      ∀ i, closure (jordanInterior (H i)) ⊆ (fun z : ℂ => π (z : Sphere)) ⁻¹' W ∧
        ContMDiff (𝓡 1) (𝓘(ℝ, ℂ)) ∞ (γ i) ∧ Topology.IsEmbedding (γ i) ∧
        frontier (jordanInterior (H i)) = range (γ i) ∧
        (∀ z ∈ frontier (jordanInterior (H i)), (z : Sphere) ∈ G ∧ π (z : Sphere) ∉ F) ∧
        ∃ a : A, closure (jordanInterior (H i)) ⊆ (fun z : ℂ => π (z : Sphere)) ⁻¹' Nbh a := by
  classical
  obtain ⟨m, D, _, hcover, hdisj, hD⟩ :=
    exists_subordinate_smooth_physical_dust_cover hsard hschoenflies G π hπ
      hclosed hsurj hr hB hTD hA hAB hBA hW hAW hinfty hbad Nbh hNbh haNbh
  let q : ℂ → Sphere := fun z => π (z : Sphere)
  let V : Fin m → Set Sphere := fun i => π '' (((↑) : ℂ → Sphere) '' jordanInterior (D i))
  let Q : Fin m → Set Sphere := fun i =>
    π '' (((↑) : ℂ → Sphere) '' closure (jordanInterior (D i)))
  let T : Fin m → Set Sphere := fun i => (A ∩ J) ∩ Q i
  have hboundary (i : Fin m) (z : ℂ) (hz : z ∈ frontier (jordanInterior (D i))) :
      (z : Sphere) ∈ G := ((hD i).2.2.2.2.1 z hz).1
  have hVo (i : Fin m) : IsOpen (V i) :=
    isOpen_image_jordanInterior_of_component_collapse G π hπ hclosed hsurj hr
      (D i) (hboundary i)
  have hqV (i : Fin m) : q ⁻¹' V i = jordanInterior (D i) :=
    physical_preimage_image_jordanInterior G π hsurj hr (D i) (hboundary i)
  have hTc (i : Fin m) : IsCompact (T i) :=
    (hA.inter_right hJ).inter_right
      ((((isCompact_closure_jordanInterior (D i)).image OnePoint.continuous_coe).image hπ).isClosed)
  have hTV (i : Fin m) : T i ⊆ V i := by
    rintro x ⟨hx, z, hz, hzx⟩
    obtain ⟨w, hw, rfl⟩ := hz
    by_cases hwU : w ∈ jordanInterior (D i)
    · exact ⟨(w : Sphere), ⟨w, hwU, rfl⟩, hzx⟩
    · have hwfront : w ∈ frontier (jordanInterior (D i)) := by
        rw [(jordanInterior_isOpen (D i)).frontier_eq]
        exact ⟨hw, hwU⟩
      exact (((hD i).2.2.2.2.1 w hwfront).2 (hzx.symm ▸ hAB hx.1)).elim
  have hVphys (i : Fin m) : IsPreconnected (q ⁻¹' V i)ᶜ ∧
      ¬ Bornology.IsBounded (q ⁻¹' V i)ᶜ :=
    physical_exterior_connected_unbounded_of_component_collapse G π hπ hclosed hsurj hr
      (hVo i)
      (isConnected_compl_image_jordanInterior_of_component_collapse
        G π hπ hsurj hr (D i) (hboundary i))
      (infty_notMem_closure_image_jordanInterior G π hπ hclosed hsurj hr
        (D i) (hboundary i))
  have hlocal (i : Fin m) := exists_physical_contours_for_compact_singleton_target
    hsard hschoenflies π hπ hF (hTc i)
      (fun _ hx => hBF (hAB hx.1.1))
      (fun x hx => hsingle x hx.1) (hVo i) (hTV i)
      (fun h => infty_notMem_closure_image_jordanInterior G π hπ hclosed hsurj hr
        (D i) (hboundary i) (subset_closure h))
      (hVphys i).1 (hVphys i).2 (fun p hp => hBF (hbad p hp))
  choose f t γ H s hs hc hd hi hcurves using hlocal
  let : ∀ i : Fin m, Fintype (s i) := fun i => (hs i).fintype
  let P := Σ i : Fin m, s i
  let e : P ≃ Fin (Fintype.card P) := Fintype.equivFin P
  let K : P → ℂ ≃ₜ ℂ := fun p => H p.1 p.2
  have hKinside (p : P) : closure (jordanInterior (K p)) ⊆ jordanInterior (D p.1) := by
    rw [← hqV p.1]
    exact hi p.1 p.2 p.2.property
  have hKdisj : Pairwise (Disjoint on fun p => closure (jordanInterior (K p))) := by
    intro p r hpr
    by_cases heq : p.1 = r.1
    · obtain ⟨i, p⟩ := p
      obtain ⟨j, r⟩ := r
      dsimp at heq
      subst j
      apply hd i p.property r.property
      intro h
      apply hpr
      exact congrArg (Sigma.mk i) (Subtype.ext h)
    · exact (hdisj heq).mono ((hKinside p).trans subset_closure)
        ((hKinside r).trans subset_closure)
  refine ⟨Fintype.card P, (fun k => K (e.symm k)),
    (fun k => γ (e.symm k).1 (e.symm k).2), ?_, ?_, ?_⟩
  · intro z hz
    obtain ⟨i, hzi⟩ := mem_iUnion.mp (hcover hz.1)
    have hzT : q z ∈ T i :=
      ⟨hz, (mem_image_of_mem π (mem_image_of_mem ((↑) : ℂ → Sphere) (subset_closure hzi)))⟩
    obtain ⟨j, hj, hzj⟩ := mem_iUnion₂.mp (hc i hzT)
    refine mem_iUnion.mpr ⟨e ⟨i, ⟨j, hj⟩⟩, ?_⟩
    simpa only [e.symm_apply_apply] using hzj
  · intro i j hij
    exact hKdisj (fun h => hij (e.symm.injective h))
  · intro i
    let p := e.symm i
    obtain ⟨hsm, hemb, hfront, hav⟩ := hcurves p.1 p.2 p.2.property
    obtain ⟨a, ha⟩ := (hD p.1).2.2.2.2.2
    exact ⟨(hKinside p).trans (subset_closure.trans (hD p.1).1),
      hsm, hemb, hfront, hav, a, (hKinside p).trans (subset_closure.trans ha)⟩

end CircleDomainRigidity

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Topology_SubordinateFillingDisks
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonEmbeddedArc.Arc.graphVertices_finite _root_.OAI.CannonMobius.sphereMetric _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions _root_.OAI.CircleDomainRigidity.finiteSphericalArea _root_.OAI.CircleDomainRigidity.sphereFirstCountableTopology
attribute [-simp] _root_.OAI.CircleDomainRigidity.CompactScalarModel.postcompose_coefficient _root_.OAI.CircleDomainRigidity.FiniteTransfer.coe_mem_sphericalCore _root_.OAI.CircleDomainRigidity.FiniteTransfer.coe_mem_sphericalDiskUnion _root_.OAI.CircleDomainRigidity.FiniteTransfer.infty_mem_cutoffCore _root_.OAI.CircleDomainRigidity.FiniteTransfer.infty_mem_sphericalCore _root_.OAI.CircleDomainRigidity.FiniteTransfer.infty_not_mem_sphericalDiskUnion _root_.OAI.CircleDomainRigidity.FiniteTransfer.realChartDomain_union _root_.OAI.CircleDomainRigidity.affineSphere_coe _root_.OAI.CircleDomainRigidity.affineSphere_infty _root_.OAI.CircleDomainRigidity.centeredJordanCoordinate_self _root_.OAI.CircleDomainRigidity.chartSymm_coe_apply _root_.OAI.CircleDomainRigidity.chart_coe_apply _root_.OAI.CircleDomainRigidity.chart_infty_apply _root_.OAI.CircleDomainRigidity.extendAtInfinity_coe _root_.OAI.CircleDomainRigidity.extendAtInfinity_infty _root_.OAI.CircleDomainRigidity.sphereInv_infty _root_.OAI.CircleDomainRigidity.sphereInv_sphereInv _root_.OAI.CircleDomainRigidity.sphereInv_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The complete descending finite-grid construction with each filling
cap contained in one prescribed local coordinate neighborhood. -/

open Set Function
open scoped Topology Manifold ContDiff

namespace CircleDomainRigidity

theorem exists_subordinate_finite_filling_disks
    (hsard : SmoothPlanarSard) (hschoenflies : PlanarSchoenflies)
    (G : Set Sphere) (π : Sphere → Sphere) (hπ : Continuous π)
    (hclosed : IsClosedMap π) (hsurj : Surjective π)
    (hr : ∀ x y, π x = π y ↔
      x = y ∨ (x ∈ Gᶜ ∧ y ∈ connectedComponentIn Gᶜ x))
    {B : Set Sphere} (hB : IsClosed B) (hTD : IsTotallyDisconnected B)
    (J : ℕ → Set Sphere) (hJ : ∀ j, IsClosed (J j))
    (hbad : ∀ p ∈ Gᶜ, π p ∈ B)
    (n : ℕ) {A W : Set Sphere}
    (hA : IsCompact A) (hAB : A ⊆ B) (hBA : IsClosed (B \ A))
    (hW : IsOpen W) (hAW : A ⊆ W) (hinfty : π OnePoint.infty ∉ A)
    (hsingle : ∀ j < n, ∀ x ∈ A ∩ J j,
      connectedComponentIn (B ∪ ⋃ k ∈ Finset.range j, J k) x = {x})
    (Nbh : A → Set Sphere) (hNbh : ∀ a, IsOpen (Nbh a))
    (haNbh : ∀ a, a.val ∈ Nbh a) :
    ∃ (m : ℕ) (H : Fin m → ℂ ≃ₜ ℂ) (γ : Fin m → Circle → ℂ),
      ((fun z : ℂ => π (z : Sphere)) ⁻¹' A ⊆ ⋃ i, jordanInterior (H i)) ∧
      Pairwise (Disjoint on fun i => closure (jordanInterior (H i))) ∧
      ∀ i, closure (jordanInterior (H i)) ⊆ (fun z : ℂ => π (z : Sphere)) ⁻¹' W ∧
        ContMDiff (𝓡 1) (𝓘(ℝ, ℂ)) ∞ (γ i) ∧ Topology.IsEmbedding (γ i) ∧
        frontier (jordanInterior (H i)) = range (γ i) ∧
        (∀ z ∈ frontier (jordanInterior (H i)), (z : Sphere) ∈ G ∧ π (z : Sphere) ∉ B) ∧
        (∃ k : ℕ, ∀ j < n, j ≠ k →
          Disjoint (frontier (jordanInterior (H i))) ((fun z : ℂ => π (z : Sphere)) ⁻¹' J j)) ∧
        ∃ a : A, closure (jordanInterior (H i)) ⊆ (fun z : ℂ => π (z : Sphere)) ⁻¹' Nbh a := by
  classical
  induction n generalizing A W with
  | zero =>
    obtain ⟨m, H, γ, hc, hd, hcurves⟩ :=
      exists_subordinate_smooth_physical_dust_cover hsard hschoenflies G π hπ
        hclosed hsurj hr hB hTD hA hAB hBA hW hAW hinfty hbad Nbh hNbh haNbh
    refine ⟨m, H, γ, hc, hd, ?_⟩
    intro i
    exact ⟨(hcurves i).1, (hcurves i).2.1, (hcurves i).2.2.1,
      (hcurves i).2.2.2.1, (hcurves i).2.2.2.2.1, ⟨0, by simp⟩,
      (hcurves i).2.2.2.2.2⟩
  | succ n ih =>
    let q : ℂ → Sphere := fun z => π (z : Sphere)
    let F : Set Sphere := B ∪ ⋃ k ∈ Finset.range n, J k
    have hF : IsClosed F := hB.union (isClosed_biUnion_finset fun k _ => hJ k)
    obtain ⟨m, H, γ, hcover, hd, hcurves⟩ :=
      exists_subordinate_grid_stage_contours hsard hschoenflies G π hπ hclosed hsurj hr
        hB hTD hA hAB hBA hW hAW hinfty (hJ n) hF subset_union_left
        (hsingle n (Nat.lt_succ_self n)) hbad Nbh hNbh haNbh
    let U : Set Sphere := ⋃ i, π '' (((↑) : ℂ → Sphere) '' jordanInterior (H i))
    let C : Set Sphere := ⋃ i, π '' (((↑) : ℂ → Sphere) '' closure (jordanInterior (H i)))
    let A' := A \ U
    let W' := W \ (C ∪ J n)
    have hb (i : Fin m) (z : ℂ) (hz : z ∈ frontier (jordanInterior (H i))) :
        (z : Sphere) ∈ G ∧ π (z : Sphere) ∉ B :=
      ⟨((hcurves i).2.2.2.2.1 z hz).1,
        fun h => ((hcurves i).2.2.2.2.1 z hz).2 (Or.inl h)⟩
    obtain ⟨hA'c, hA'B, hBA', hA'C⟩ :=
      compact_clopen_dust_remainder G π hπ hclosed hsurj hr H hB hA hAB hBA hb
    have hcovered : A ∩ J n ⊆ U :=
      quotient_cover_of_physical_cover π hsurj (fun i => jordanInterior (H i))
        (fun h => hinfty h.1) hcover
    have hA'Jn : Disjoint A' (J n) := remainder_avoids_covered_set hcovered
    have hC : IsClosed C := isClosed_iUnion_of_finite fun i =>
      (((isCompact_closure_jordanInterior (H i)).image OnePoint.continuous_coe).image hπ).isClosed
    have hW' : IsOpen W' := hW.sdiff (hC.union (hJ n))
    have hA'W' : A' ⊆ W' := by
      intro x hx
      refine ⟨hAW hx.1, ?_⟩
      rintro (hxC | hxJ)
      · exact Set.disjoint_left.mp hA'C hx hxC
      · exact Set.disjoint_left.mp hA'Jn hx hxJ
    obtain ⟨r, K, δ, hcK, hdK, hK⟩ := ih hA'c hA'B hBA' hW' hA'W'
      (fun h => hinfty h.1) (fun j hj x hx => hsingle j (Nat.lt_succ_of_lt hj) x ⟨hx.1.1, hx.2⟩)
      (fun a => Nbh ⟨a.val, a.property.1⟩) (fun a => hNbh _) (fun a => haNbh _)
    let P := Sum (Fin m) (Fin r)
    let e : P ≃ Fin (Fintype.card P) := Fintype.equivFin P
    let D : P → ℂ ≃ₜ ℂ := Sum.elim H K
    let η : P → Circle → ℂ := Sum.elim γ δ
    have hDpair : Pairwise (Disjoint on fun p => closure (jordanInterior (D p))) := by
      intro p t hpt
      cases p with
      | inl i =>
        cases t with
        | inl j => exact hd (fun h => hpt (congrArg Sum.inl h))
        | inr j =>
          apply Set.disjoint_left.mpr
          intro z hzi hzj
          have hqC : q z ∈ C := mem_iUnion.mpr ⟨i, _, ⟨z, hzi, rfl⟩, rfl⟩
          exact ((hK j).1 hzj).2 (Or.inl hqC)
      | inr i =>
        cases t with
        | inl j =>
          apply Set.disjoint_left.mpr
          intro z hzi hzj
          have hqC : q z ∈ C := mem_iUnion.mpr ⟨j, _, ⟨z, hzj, rfl⟩, rfl⟩
          exact ((hK i).1 hzi).2 (Or.inl hqC)
        | inr j => exact hdK (fun h => hpt (congrArg Sum.inr h))
    refine ⟨Fintype.card P, (fun i => D (e.symm i)), (fun i => η (e.symm i)), ?_, ?_, ?_⟩
    · intro z hz
      by_cases hzU : q z ∈ U
      · obtain ⟨i, hi⟩ := mem_iUnion.mp hzU
        have hzi : z ∈ jordanInterior (H i) := by
          rw [← physical_preimage_image_jordanInterior G π hsurj hr (H i)
            (fun w hw => (hb i w hw).1)]
          exact hi
        refine mem_iUnion.mpr ⟨e (Sum.inl i), ?_⟩
        simpa only [e.symm_apply_apply, D, Sum.elim_inl] using hzi
      · obtain ⟨i, hi⟩ := mem_iUnion.mp (hcK ⟨hz, hzU⟩)
        refine mem_iUnion.mpr ⟨e (Sum.inr i), ?_⟩
        simpa only [e.symm_apply_apply, D, Sum.elim_inr] using hi
    · intro i j hij
      exact hDpair (fun h => hij (e.symm.injective h))
    · intro i
      change closure (jordanInterior (D (e.symm i))) ⊆ q ⁻¹' W ∧
        ContMDiff (𝓡 1) (𝓘(ℝ, ℂ)) ∞ (η (e.symm i)) ∧
        Topology.IsEmbedding (η (e.symm i)) ∧
        frontier (jordanInterior (D (e.symm i))) = range (η (e.symm i)) ∧
        (∀ z ∈ frontier (jordanInterior (D (e.symm i))),
          (z : Sphere) ∈ G ∧ π (z : Sphere) ∉ B) ∧
        (∃ k : ℕ, ∀ j < n + 1, j ≠ k →
          Disjoint (frontier (jordanInterior (D (e.symm i)))) (q ⁻¹' J j)) ∧
        ∃ a : A, closure (jordanInterior (D (e.symm i))) ⊆ q ⁻¹' Nbh a
      generalize e.symm i = p
      cases p with
      | inl j =>
        dsimp only [D, η, Sum.elim_inl]
        refine ⟨(hcurves j).1, (hcurves j).2.1, (hcurves j).2.2.1,
          (hcurves j).2.2.2.1, hb j, ⟨n, ?_⟩, (hcurves j).2.2.2.2.2⟩
        intro k hk hkn
        apply Set.disjoint_left.mpr
        intro z hz hzk
        apply ((hcurves j).2.2.2.2.1 z hz).2
        exact Or.inr (mem_iUnion₂.mpr ⟨k,
          Finset.mem_range.mpr (lt_of_le_of_ne (Nat.le_of_lt_succ hk) hkn), hzk⟩)
      | inr j =>
        dsimp only [D, η, Sum.elim_inr]
        obtain ⟨hinside, hsm, hemb, hfront, hav, ⟨k, hk⟩, a, ha⟩ := hK j
        refine ⟨(fun z hz => (hinside hz).1), hsm, hemb, hfront, hav, ⟨k, ?_⟩,
          ⟨a.val, a.property.1⟩, ha⟩
        intro t ht htk
        by_cases htn : t < n
        · exact hk t htn htk
        · have hteq : t = n := by omega
          subst t
          apply Set.disjoint_left.mpr
          intro z hz hzn
          exact (hinside (frontier_subset_closure hz)).2 (Or.inr hzn)

end CircleDomainRigidity

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Transfer_SubordinateGraphFilling
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonEmbeddedArc.Arc.graphVertices_finite _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions _root_.OAI.CircleDomainRigidity.finiteSphericalArea _root_.OAI.CircleDomainRigidity.sphereFirstCountableTopology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Closed real and period level graphs supply filling contours which
also remain inside the required local real-branch neighborhoods. -/

open Set Function
open scoped Topology Manifold ContDiff

namespace CircleDomainRigidity.FiniteTransfer

theorem exists_subordinate_filling_disks_of_compatible_graphs
    (hsard : SmoothPlanarSard) (hschoenflies : PlanarSchoenflies)
    (G : Set Sphere) (π : Sphere → Sphere) (hπ : Continuous π)
    (hclosed : IsClosedMap π) (hsurj : Surjective π)
    (hr : ∀ x y, π x = π y ↔
      x = y ∨ (x ∈ Gᶜ ∧ y ∈ connectedComponentIn Gᶜ x))
    {n N : ℕ} {P S : Type*} (R : Fin n → Set (Sphere × UnitAddCircle)) (hR : ∀ i, IsClosed (R i))
    (σ : S → Sphere) (a b : Fin n → S → ℝ) (θ : Fin n → ℝ)
    (pairs : P → Fin n × Fin n)
    (hpairs : ∀ i j : Fin n, i ≠ j → ∃ p, pairs p = (i, j) ∨ pairs p = (j, i))
    (F : Set S)
    (hband : ∀ i s, {t : UnitAddCircle | (σ s, t) ∈ R i} ⊆
      ((↑) : ℝ → UnitAddCircle) '' Icc (a i s) (b i s))
    {B A W : Set Sphere} (hB : IsClosed B) (hTD : IsTotallyDisconnected B)
    (hA : IsCompact A) (hAB : A ⊆ B) (hBA : IsClosed (B \ A))
    (hW : IsOpen W) (hAW : A ⊆ W) (hinfty : π OnePoint.infty ∉ A)
    (hbad : ∀ p ∈ Gᶜ, π p ∈ B)
    (hnoterm : Disjoint A (σ '' gridTerminalIndices F (reciprocalGridStep N) pairs a b θ))
    (hfree : ∀ x ∈ A, x ∉ range σ → ∀ i,
      {t : UnitAddCircle | (x, t) ∈ R i}.Subsingleton)
    (hcompat : OrderedGraphGridCompatibility R θ N A σ)
    (Nbh : A → Set Sphere) (hNbh : ∀ a, IsOpen (Nbh a))
    (haNbh : ∀ a, a.val ∈ Nbh a) :
    ∃ (m : ℕ) (H : Fin m → ℂ ≃ₜ ℂ) (γ : Fin m → Circle → ℂ),
      ((fun z : ℂ => π (z : Sphere)) ⁻¹' A ⊆ ⋃ i, jordanInterior (H i)) ∧
      Pairwise (Disjoint on fun i => closure (jordanInterior (H i))) ∧
      ∀ i, closure (jordanInterior (H i)) ⊆ (fun z : ℂ => π (z : Sphere)) ⁻¹' W ∧
        ContMDiff (𝓡 1) (𝓘(ℝ, ℂ)) ∞ (γ i) ∧ Topology.IsEmbedding (γ i) ∧
        frontier (jordanInterior (H i)) = range (γ i) ∧
        (∀ z ∈ frontier (jordanInterior (H i)), (z : Sphere) ∈ G ∧ π (z : Sphere) ∉ B) ∧
        (∃ k : ℕ, ∀ j : Fin n, j.val ≠ k →
          Disjoint (frontier (jordanInterior (H i)))
            ((fun z : ℂ => π (z : Sphere)) ⁻¹' (⋃ l, reciprocalGraphLevel (R j) (θ j) N l))) ∧
        ∃ a : A, closure (jordanInterior (H i)) ⊆ (fun z : ℂ => π (z : Sphere)) ⁻¹' Nbh a := by
  classical
  let L : Fin n → Set Sphere := fun j => ⋃ k, reciprocalGraphLevel (R j) (θ j) N k
  let J : ℕ → Set Sphere := fun j => if hj : j < n then L ⟨j, hj⟩ else ∅
  have hJ (j : ℕ) : IsClosed (J j) := by
    by_cases hj : j < n
    · simpa only [J, dite_eq_left hj] using
        (isClosed_iUnion_of_finite (fun k =>
          isClosed_reciprocalGraphLevel (hR ⟨j, hj⟩) (θ ⟨j, hj⟩) N k))
    · simp only [J, dite_eq_right hj, isClosed_empty]
  have hlower (j : Fin n) : (⋃ k ∈ Finset.range j.val, J k) =
      ⋃ i : Fin n, ⋃ (_ : i.val < j.val), L i := by
    ext x
    constructor
    · intro hx
      obtain ⟨k, hk, hx⟩ := mem_iUnion₂.mp hx
      have hkj := Finset.mem_range.mp hk
      have hkn := hkj.trans j.isLt
      exact mem_iUnion₂.mpr ⟨⟨k, hkn⟩, hkj, by simpa only [J, dite_eq_left hkn] using hx⟩
    · intro hx
      obtain ⟨i, hi, hx⟩ := mem_iUnion₂.mp hx
      exact mem_iUnion₂.mpr ⟨i.val, Finset.mem_range.mpr hi,
        by simpa only [J, dite_eq_left i.isLt] using hx⟩
  have hsingle (j : ℕ) (hj : j < n) (x : Sphere) (hx : x ∈ A ∩ J j) :
      connectedComponentIn (B ∪ ⋃ k ∈ Finset.range j, J k) x = {x} := by
    rw [hlower ⟨j, hj⟩]
    apply lower_obstacle_singleton_of_compatible_graphs R hR σ a b θ pairs
      hpairs F hband hB hTD hAB hnoterm hfree hcompat ⟨j, hj⟩
    simpa only [J, dite_eq_left hj] using hx
  obtain ⟨m, H, γ, hc, hd, hcurves⟩ := exists_subordinate_finite_filling_disks hsard hschoenflies
    G π hπ hclosed hsurj hr hB hTD J hJ hbad n hA hAB hBA hW hAW hinfty hsingle Nbh hNbh haNbh
  refine ⟨m, H, γ, hc, hd, ?_⟩
  intro i
  obtain ⟨hi, hsm, hemb, hfront, hb, ⟨k, hk⟩, ha⟩ := hcurves i
  refine ⟨hi, hsm, hemb, hfront, hb, ⟨k, ?_⟩, ha⟩
  intro j hj
  simpa only [J, dite_eq_left j.isLt] using hk j.val j.isLt hj

end CircleDomainRigidity.FiniteTransfer

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Transfer_SubordinateGraphCompletion
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions _root_.OAI.CircleDomainRigidity.finiteSphericalArea _root_.OAI.CircleDomainRigidity.sphereFirstCountableTopology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Complete the physical collision terminals with filling caps lying
inside the chosen local real-branch neighborhoods. -/

open Set Function
open scoped Topology ContDiff Manifold

noncomputable section
namespace CircleDomainRigidity.FiniteTransfer

theorem exists_subordinate_geometric_completion_for_graphs
    (hsard : SmoothPlanarSard) (hschoenflies : PlanarSchoenflies)
    (G : Set Sphere) (π : Sphere → Sphere) (hπ : Continuous π)
    (hclosed : IsClosedMap π) (hsurj : Surjective π)
    (hr : ∀ x y, π x = π y ↔
      x = y ∨ (x ∈ Gᶜ ∧ y ∈ connectedComponentIn Gᶜ x))
    {B C : Set Sphere} (hB : IsClosed B) (hBdef : B = π '' Gᶜ)
    (hTD : IsTotallyDisconnected B) (hC : IsCompact C) (hCG : C ⊆ G)
    (hinfty : OnePoint.infty ∈ C)
    {n N : ℕ} {S : Type*} (R : Fin n → Set (Sphere × UnitAddCircle)) (hR : ∀ i, IsClosed (R i))
    (σ : S → Sphere) (hσB : ∀ s, σ s ∈ B)
    (a b : Fin n → S → ℝ) (θ : Fin n → ℝ) (F : Set S)
    (hband : ∀ i s, {t : UnitAddCircle | (σ s, t) ∈ R i} ⊆
      ((↑) : ℝ → UnitAddCircle) '' Icc (a i s) (b i s))
    (hfin : (gridTerminalIndices F (reciprocalGridStep N) upperPair a b θ).Finite)
    (O : (gridTerminalIndices F (reciprocalGridStep N) upperPair a b θ) → Set Sphere)
    (D : PhysicalTerminalDisks G π B (fun s : gridTerminalIndices F (reciprocalGridStep N)
      upperPair a b θ => σ s) O)
    (hDcore : ∀ i, Disjoint (((↑) : ℂ → Sphere) '' closure (jordanInterior (D.H i))) C)
    (hfree : ∀ x ∈ terminalRemainder π B D.H, x ∉ range σ → ∀ i,
      {t : UnitAddCircle | (x, t) ∈ R i}.Subsingleton)
    (hcompat : OrderedGraphGridCompatibility R θ N (terminalRemainder π B D.H) σ)
    (Nbh : terminalRemainder π B D.H → Set Sphere)
    (hNbh : ∀ a, IsOpen (Nbh a)) (haNbh : ∀ a, a.val ∈ Nbh a) :
    ∃ (m : ℕ) (H : Fin m → ℂ ≃ₜ ℂ) (γ : Fin m → Circle → ℂ),
      Pairwise (Disjoint on fun j => closure (jordanInterior (H j))) ∧
      (∀ i j, Disjoint (closure (jordanInterior (D.H i))) (closure (jordanInterior (H j)))) ∧
      (∀ j, Disjoint (((↑) : ℂ → Sphere) '' closure (jordanInterior (H j))) C) ∧
      π ⁻¹' B ⊆ sphericalDiskUnion D.H ∪ sphericalDiskUnion H ∧
      C ⊆ completionCore D.H H ∧ completionCore D.H H ⊆ G ∧
      (∀ j, ContMDiff (𝓡 1) (𝓘(ℝ, ℂ)) ∞ (γ j) ∧ Topology.IsEmbedding (γ j) ∧
        frontier (jordanInterior (H j)) = range (γ j) ∧
        (∀ z ∈ frontier (jordanInterior (H j)), (z : Sphere) ∈ G ∧ π (z : Sphere) ∉ B) ∧
        (∃ k : ℕ, ∀ i : Fin n, i.val ≠ k →
          Disjoint (frontier (jordanInterior (H j)))
            ((fun z : ℂ => π (z : Sphere)) ⁻¹' (⋃ l, reciprocalGraphLevel (R i) (θ i) N l))) ∧
        ∃ a : terminalRemainder π B D.H, closure (jordanInterior (H j)) ⊆
          (fun z : ℂ => π (z : Sphere)) ⁻¹' Nbh a) := by
  classical
  let : Fintype (gridTerminalIndices F (reciprocalGridStep N) upperPair a b θ) := hfin.fintype
  have hBC : B ⊆ (π '' C)ᶜ := by
    rw [hBdef]
    exact (quotient_core_safe_open π hπ hC hCG hr).2.1
  obtain ⟨hA, hAB, hBA, hW, hAW, hAinf⟩ :=
    terminal_remainder_safe_region hπ hclosed hsurj hr hB hBC hC hinfty D
  have hpinf (s : gridTerminalIndices F (reciprocalGridStep N) upperPair a b θ) :
      σ s ≠ π OnePoint.infty := by
    intro heq
    exact hBC (hσB s) (heq ▸ (show π OnePoint.infty ∈ π '' C from
      ⟨OnePoint.infty, hinfty, rfl⟩))
  have hnoterm : Disjoint (terminalRemainder π B D.H)
      (σ '' gridTerminalIndices F (reciprocalGridStep N) upperPair a b θ) := by
    apply Set.disjoint_left.mpr
    rintro x hx ⟨s, hs, hσ⟩
    exact Set.disjoint_left.mp (D.remainder_avoids_indices hsurj hpinf) hx ⟨⟨s, hs⟩, hσ⟩
  obtain ⟨m, H, γ, hcover, hdisj, hcurves⟩ := exists_subordinate_filling_disks_of_compatible_graphs
    hsard hschoenflies G π hπ hclosed hsurj hr R hR σ a b θ
    upperPair upperPair_covers F hband hB hTD hA hAB hBA hW hAW hAinf
    (fun x hx => hBdef.symm ▸ (show π x ∈ π '' Gᶜ from ⟨x, hx, rfl⟩))
    hnoterm hfree hcompat Nbh hNbh haNbh
  have hsafe := filling_closures_avoid_core_and_terminals D.H H
    (fun j => (hcurves j).1)
  have hfill := spherical_remainder_cover_of_physical_cover D.H H B π hAinf hcover
  have htotal := dust_preimage_covered_of_remainder_cover D.H H G B π hsurj hr
    (fun i z hz => (D.frontier_good i z hz).1) hfill
  refine ⟨m, H, γ, hdisj, hsafe.2, hsafe.1, htotal, ?_,
    completionCore_subset_domain D.H H G B π
      (fun x hx => hBdef.symm ▸ (show π x ∈ π '' Gᶜ from ⟨x, hx, rfl⟩)) htotal, ?_⟩
  · intro x hx hbad
    rcases hbad with ht | hf
    · obtain ⟨i, z, hz, rfl⟩ := mem_iUnion.mp ht
      exact Set.disjoint_left.mp (hDcore i) ⟨z, subset_closure hz, rfl⟩ hx
    · obtain ⟨j, z, hz, rfl⟩ := mem_iUnion.mp hf
      exact Set.disjoint_left.mp (hsafe.1 j) ⟨z, subset_closure hz, rfl⟩ hx
  · intro j
    exact (hcurves j).2

end CircleDomainRigidity.FiniteTransfer

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Rigidity_MaskAtlasGeometricCompletion
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonEmbeddedArc.Arc.graphVertices_finite _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions _root_.OAI.CircleDomainRigidity.finiteSphericalArea _root_.OAI.CircleDomainRigidity.sphereFirstCountableTopology
attribute [-simp] _root_.OAI.CircleDomainRigidity.CompactScalarModel.postcompose_coefficient _root_.OAI.CircleDomainRigidity.FiniteTransfer.infty_mem_cutoffCore _root_.OAI.CircleDomainRigidity.FiniteTransfer.realChartDomain_sphericalDiskUnion _root_.OAI.CircleDomainRigidity.FiniteTransfer.realChartDomain_union _root_.OAI.CircleDomainRigidity.affineSphere_coe _root_.OAI.CircleDomainRigidity.affineSphere_infty _root_.OAI.CircleDomainRigidity.centeredJordanCoordinate_self _root_.OAI.CircleDomainRigidity.chartSymm_coe_apply _root_.OAI.CircleDomainRigidity.chart_coe_apply _root_.OAI.CircleDomainRigidity.chart_infty_apply _root_.OAI.CircleDomainRigidity.extendAtInfinity_coe _root_.OAI.CircleDomainRigidity.extendAtInfinity_infty _root_.OAI.CircleDomainRigidity.sphereInv_infty _root_.OAI.CircleDomainRigidity.sphereInv_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The singularities of a finite masked list are retained as terminals.
Every remaining dust point therefore has a common real-branch neighborhood;
the filling caps can be chosen inside those actual neighborhoods. -/

open Set Function
open scoped Topology ContDiff Manifold

noncomputable section
namespace CircleDomainRigidity.FiniteTransfer

theorem exists_mask_atlas_geometric_completion
    (hsard : SmoothPlanarSard) (hschoenflies : PlanarSchoenflies)
    (G : Set Sphere) (π : Sphere → Sphere) (hπ : Continuous π)
    (hclosed : IsClosedMap π) (hsurj : Surjective π)
    (hr : ∀ x y, π x = π y ↔
      x = y ∨ (x ∈ Gᶜ ∧ y ∈ connectedComponentIn Gᶜ x))
    {B C : Set Sphere} (hB : IsClosed B) (hBdef : B = π '' Gᶜ)
    (hTD : IsTotallyDisconnected B) (hC : IsCompact C) (hCG : C ⊆ G)
    (hinfty : OnePoint.infty ∈ C)
    {n N : ℕ} {S : Type*} (R : Fin n → Set (Sphere × UnitAddCircle)) (hR : ∀ i, IsClosed (R i))
    (σ : S → Sphere) (hσB : ∀ s, σ s ∈ B)
    (a b : Fin n → S → ℝ) (θ : Fin n → ℝ) (F : Set S)
    (hband : ∀ i s, {t : UnitAddCircle | (σ s, t) ∈ R i} ⊆
      ((↑) : ℝ → UnitAddCircle) '' Icc (a i s) (b i s))
    (hfin : (gridTerminalIndices F (reciprocalGridStep N) upperPair a b θ).Finite)
    (O : (gridTerminalIndices F (reciprocalGridStep N) upperPair a b θ) → Set Sphere)
    (D : PhysicalTerminalDisks G π B (fun s : gridTerminalIndices F (reciprocalGridStep N)
      upperPair a b θ => σ s) O)
    (hDcore : ∀ i, Disjoint (((↑) : ℂ → Sphere) '' closure (jordanInterior (D.H i))) C)
    (hfree : ∀ x ∈ terminalRemainder π B D.H, x ∉ range σ → ∀ i,
      {t : UnitAddCircle | (x, t) ∈ R i}.Subsingleton)
    (hcompat : OrderedGraphGridCompatibility R θ N (terminalRemainder π B D.H) σ)
    (L : Fin n → Type*) (M : Fin n → Set Sphere) (hM : ∀ l, IsClosed (M l))
    (hboundary : ∀ l, frontier (M l) ⊆ Bᶜ)
    (singular : Fin n → S) (hflag : ∀ l, singular l ∈ F)
    (P : ∀ l, L l → Set Sphere) (hP : ∀ l i, IsOpen (P l i))
    (hcover : ∀ l, M l \ {σ (singular l)} ⊆ ⋃ i, P l i) :
    ∃ (m : ℕ) (H : Fin m → ℂ ≃ₜ ℂ) (γ : Fin m → Circle → ℂ),
      Pairwise (Disjoint on fun j => closure (jordanInterior (H j))) ∧
      (∀ i j, Disjoint (closure (jordanInterior (D.H i))) (closure (jordanInterior (H j)))) ∧
      (∀ j, Disjoint (((↑) : ℂ → Sphere) '' closure (jordanInterior (H j))) C) ∧
      π ⁻¹' B ⊆ sphericalDiskUnion D.H ∪ sphericalDiskUnion H ∧
      C ⊆ completionCore D.H H ∧ completionCore D.H H ⊆ G ∧
      (∀ j, ContMDiff (𝓡 1) (𝓘(ℝ, ℂ)) ∞ (γ j) ∧ Topology.IsEmbedding (γ j) ∧
        frontier (jordanInterior (H j)) = range (γ j) ∧
        (∀ z ∈ frontier (jordanInterior (H j)), (z : Sphere) ∈ G ∧ π (z : Sphere) ∉ B) ∧
        (∃ k : ℕ, ∀ i : Fin n, i.val ≠ k →
          Disjoint (frontier (jordanInterior (H j)))
            ((fun z : ℂ => π (z : Sphere)) ⁻¹' (⋃ l, reciprocalGraphLevel (R i) (θ i) N l))) ∧
        ∀ l, Disjoint (closure (jordanInterior (H j)))
          ((fun z : ℂ => π (z : Sphere)) ⁻¹' M l) ∨
          ∃ i, closure (jordanInterior (H j)) ⊆
            (fun z : ℂ => π (z : Sphere)) ⁻¹' (interior (M l) ∩ P l i)) := by
  classical
  let : Fintype (gridTerminalIndices F (reciprocalGridStep N) upperPair a b θ) := hfin.fintype
  have hBC : B ⊆ (π '' C)ᶜ := by
    rw [hBdef]
    exact (quotient_core_safe_open π hπ hC hCG hr).2.1
  have hpinf (s : gridTerminalIndices F (reciprocalGridStep N) upperPair a b θ) :
      σ s ≠ π OnePoint.infty := by
    intro heq
    exact hBC (hσB s) (heq ▸ (show π OnePoint.infty ∈ π '' C from
      ⟨OnePoint.infty, hinfty, rfl⟩))
  have hsingular (x : terminalRemainder π B D.H) (l : Fin n) :
      x.val ≠ σ (singular l) := by
    intro heq
    apply Set.disjoint_left.mp (D.remainder_avoids_indices hsurj hpinf) x.property
    exact ⟨⟨singular l, Or.inl (hflag l)⟩, heq.symm⟩
  have hlocal (x : terminalRemainder π B D.H) : ∃ V : Set Sphere,
      IsOpen V ∧ x.val ∈ V ∧ ∀ l,
        Disjoint V (M l) ∨ ∃ i, V ⊆ interior (M l) ∩ P l i :=
    exists_common_mask_branch_neighborhood L Bᶜ M hM hboundary
      (fun l => σ (singular l)) P hP hcover (by simpa using x.property.1) (hsingular x)
  choose V hV hxV hchoice using hlocal
  obtain ⟨m, H, γ, hHd, hDH, hHC, hcov, hCC, hCG', hcurves⟩ :=
    exists_subordinate_geometric_completion_for_graphs hsard hschoenflies
      G π hπ hclosed hsurj hr hB hBdef hTD hC hCG hinfty R hR σ hσB a b θ F
      hband hfin O D hDcore hfree hcompat V hV hxV
  refine ⟨m, H, γ, hHd, hDH, hHC, hcov, hCC, hCG', ?_⟩
  intro j
  obtain ⟨hj, he, hb, hg, hgrid, x, hx⟩ := hcurves j
  refine ⟨hj, he, hb, hg, hgrid, fun l => ?_⟩
  rcases hchoice x l with hd | ⟨i, hi⟩
  · left
    apply Set.disjoint_left.mpr
    intro z hz hm
    exact Set.disjoint_left.mp hd (hx hz) hm
  · exact Or.inr ⟨i, fun z hz => hi (hx hz)⟩

end CircleDomainRigidity.FiniteTransfer

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Topology_CutoffCore
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions _root_.OAI.CircleDomainRigidity.finiteSphericalArea _root_.OAI.CircleDomainRigidity.sphereFirstCountableTopology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# The physical core containing the entire cutoff transition

Taking the complement of the open one-plateau of the cutoff gives a
compact spherical subset of the original domain. Choosing all disk
closures off this larger core guarantees genuine staircase collars.
-/

open Set Filter
open scoped Topology

noncomputable section

namespace CircleDomainRigidity.FiniteTransfer

theorem isCompact_compl_realChartDomain {G : Set Sphere} (hG : IsOpen G)
    (hinfty : OnePoint.infty ∈ G) : IsCompact (realChartDomain G)ᶜ := by
  have hc := ((OnePoint.isOpen_iff_of_mem hinfty).mp hG).2
  exact Complex.equivRealProdCLM.symm.toHomeomorph.isCompact_preimage.mpr hc

theorem isCompact_cutoffCore (χ : (ℝ × ℝ) → ℝ) : IsCompact (cutoffCore χ) :=
  isCompact_sphericalCore isOpen_interior.isClosed_compl

theorem cutoffCore_subset_domain {G : Set Sphere} (hinfty : OnePoint.infty ∈ G)
    (χ : (ℝ × ℝ) → ℝ) (hone : ∀ᶠ z in 𝓝ˢ (realChartDomain G)ᶜ, χ z = 1) :
    cutoffCore χ ⊆ G := by
  apply sphericalCore_subset_domain hinfty
  intro z hz
  by_contra hzG
  have hx : Complex.equivRealProdCLM z ∈ (realChartDomain G)ᶜ := by
    simpa only [realChartDomain, mem_compl_iff, mem_preimage,
      ContinuousLinearEquiv.symm_apply_apply] using hzG
  have hlocal : {x | χ x = 1} ∈ 𝓝 (Complex.equivRealProdCLM z) :=
    hone.filter_mono (nhds_le_nhdsSet hx)
  exact hz (mem_interior_iff_mem_nhds.mpr hlocal)

theorem sphericalCore_subset_cutoffCore {K : Set (ℝ × ℝ)} (χ : (ℝ × ℝ) → ℝ)
    (hzero : ∀ᶠ z in 𝓝ˢ K, χ z = 0) : sphericalCore K ⊆ cutoffCore χ := by
  apply sphericalCore_mono
  intro z hz hzplateau
  have h1 : χ z = 1 := (interior_subset : interior {x | χ x = 1} ⊆ {x | χ x = 1}) hzplateau
  have h0 := hzero.self_of_nhdsSet z hz
  linarith

/-- A filling closure off the cutoff core has its whole boundary in
the open region where the modification is exactly the staircase. -/
theorem boundary_in_one_plateau_of_disjoint_cutoffCore
    (H : ℂ ≃ₜ ℂ) (χ : (ℝ × ℝ) → ℝ)
    (hdisj : Disjoint (((↑) : ℂ → Sphere) '' closure (jordanInterior H)) (cutoffCore χ)) :
    ∀ z ∈ frontier (jordanInterior H), Complex.equivRealProdCLM z ∈ interior {x | χ x = 1} := by
  intro z hz
  by_contra hnot
  exact Set.disjoint_left.mp hdisj ⟨z, frontier_subset_closure hz, rfl⟩
    ((coe_mem_sphericalCore _ z).mpr hnot)

end CircleDomainRigidity.FiniteTransfer

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Transfer_RetainedTerminalGeometry
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonMobius.sphereMetric _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions _root_.OAI.CircleDomainRigidity.finiteSphericalArea _root_.OAI.CircleDomainRigidity.sphereFirstCountableTopology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Terminal contours retaining the prescribed core and oscillation bounds

Intersect the prescribed quotient neighborhoods with the complement of the
core image before choosing terminal contours. This retains the uniform
staircase estimate, confines every terminal to its prescribed neighborhood,
and places the whole core in the open finite completion.
-/

open Set Function Filter
open scoped Topology

noncomputable section

namespace CircleDomainRigidity.FiniteTransfer

theorem PhysicalTerminalDisks.core_subset_openCompletedRegion
    {I : Type*} {G B C : Set Sphere} {π : Sphere → Sphere}
    {p : I → Sphere} {O : I → Set Sphere} (D : PhysicalTerminalDisks G π B p O)
    (havoid : ∀ i, Disjoint (closedTerminalCap (D.H i)) C) :
    C ⊆ openCompletedRegion D.H := by
  intro x hx hbad
  obtain ⟨i, hi⟩ := mem_iUnion.mp hbad
  exact Set.disjoint_left.mp (havoid i) hi hx

theorem exists_retained_physical_terminals_with_staircase_bound
    (hsard : SmoothPlanarSard) (hsch : PlanarSchoenflies)
    {I L : Type*} [Fintype I] [Fintype L]
    {G C : Set Sphere} (hG : IsOpen G) (hC : IsCompact C) (hCG : C ⊆ G)
    (hinfty : OnePoint.infty ∈ C)
    (π : Sphere → Sphere) (hπ : Continuous π) (hclosed : IsClosedMap π)
    (hsurj : Surjective π)
    (hr : ∀ x y, π x = π y ↔
      x = y ∨ (x ∈ Gᶜ ∧ y ∈ connectedComponentIn Gᶜ x))
    (hTD : IsTotallyDisconnected (π '' Gᶜ))
    (p : I → Sphere) (hp : Injective p) (hpB : ∀ i, p i ∈ π '' Gᶜ)
    (O : I → Set Sphere) (hO : ∀ i, O i ∈ 𝓝 (p i))
    (U : I → Set Sphere) (u : I → L → Sphere → ℝ) (M : I → L → ℝ)
    (hM : ∀ i l x, x ∈ U i → |u i l x| ≤ M i l)
    (hphysical : ∀ i (z : ℂ), (z : Sphere) ∈ G → π (z : Sphere) ∈ O i →
      π (z : Sphere) ∈ U i)
    (active : I → L → Prop) (c : I → L → ℝ)
    (hbudget : ∀ i l, active i l →
      limsup (u i l) (𝓝[U i] (p i)) - liminf (u i l) (𝓝[U i] (p i)) ≤ c i l)
    {h : ℝ} (hh : 0 < h) :
    ∃ D : PhysicalTerminalDisks G π (π '' Gᶜ) p O,
      (∀ i, Disjoint (closedTerminalCap (D.H i)) C) ∧
      C ⊆ openCompletedRegion D.H ∧
      ∀ i l, active i l → ∀ δ θ : ℝ,
        ∀ x ∈ frontier (jordanInterior (D.H i)),
        ∀ y ∈ frontier (jordanInterior (D.H i)),
        |shiftedStaircase h δ θ (u i l (π (x : Sphere))) -
          shiftedStaircase h δ θ (u i l (π (y : Sphere)))| ≤ c i l + 4 * h := by
  have hsafe := quotient_core_safe_open π hπ hC hCG hr
  let O' : I → Set Sphere := fun i => O i ∩ (π '' C)ᶜ
  have hO' (i : I) : O' i ∈ 𝓝 (p i) :=
    inter_mem (hO i) (hsafe.1.mem_nhds (hsafe.2.1 (hpB i)))
  have hpinfty (i : I) : p i ≠ π OnePoint.infty := by
    intro heq
    exact hsafe.2.1 (hpB i) (heq ▸ mem_image_of_mem π hinfty)
  obtain ⟨D, hosc⟩ := exists_physical_terminals_with_uniform_staircase_oscillation
    hsard hsch G π hπ hclosed hsurj hr
      (hG.isClosed_compl.isCompact.image hπ).isClosed hTD
      (fun x hx => mem_image_of_mem π hx) p hp hpB hpinfty O' hO' U u M hM
      (fun i z hz hzi => hphysical i z hz hzi.1) active c hbudget hh
  let D' : PhysicalTerminalDisks G π (π '' Gᶜ) p O :=
    { D with closure_subset := fun i z hz => (D.closure_subset i hz).1 }
  have havoid (i : I) : Disjoint (closedTerminalCap (D'.H i)) C :=
    D.closure_disjoint_core (fun _ _ hz => hz.2) i
  exact ⟨D', havoid, D'.core_subset_openCompletedRegion havoid, hosc⟩

end CircleDomainRigidity.FiniteTransfer

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Rigidity_MaskAtlasGeometricAssembly
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonMobius.sphereMetric _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions _root_.OAI.CircleDomainRigidity.finiteSphericalArea _root_.OAI.CircleDomainRigidity.sphereFirstCountableTopology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Assemble physical collision terminals and the remaining filling
contours for a mixed finite list. Nonsingular local real branches give
terminal bounds; closed level graphs give the filling geometry. -/

open Set Function Filter
open scoped Topology Manifold ContDiff

noncomputable section
namespace CircleDomainRigidity.FiniteTransfer

attribute [local instance] sphereMetric

 theorem exists_mask_atlas_geometric_assembly
    (hsard : SmoothPlanarSard) (hsch : PlanarSchoenflies)
    (G : Set Sphere) (hG : IsOpen G) (π : Sphere → Sphere)
    (hπ : Continuous π) (hclosed : IsClosedMap π) (hsurj : Surjective π)
    (hr : ∀ x y, π x = π y ↔
      x = y ∨ (x ∈ Gᶜ ∧ y ∈ connectedComponentIn Gᶜ x))
    (hTD : IsTotallyDisconnected (π '' Gᶜ))
    (C : Set Sphere) (hC : IsCompact C) (hCG : C ⊆ G) (hinfty : OnePoint.infty ∈ C)
    {n N : ℕ} {S : Type*}
    (R : Fin n → Set (Sphere × UnitAddCircle)) (hR : ∀ l, IsClosed (R l))
    (σ : S → Sphere) (hσ : Injective σ) (hσB : ∀ s, σ s ∈ π '' Gᶜ)
    (a b : Fin n → S → ℝ) (θ : Fin n → ℝ) (Flag : Set S)
    (hband : ∀ l s, {t : UnitAddCircle | (σ s, t) ∈ R l} ⊆
      ((↑) : ℝ → UnitAddCircle) '' Icc (a l s) (b l s))
    (hfin : (gridTerminalIndices Flag (reciprocalGridStep N) upperPair a b θ).Finite)
    (O : S → Set Sphere) (hO : ∀ s, O s ∈ 𝓝 (σ s))
    (U : S → Set Sphere) (v : S → Fin n → Sphere → ℝ) (M : S → Fin n → ℝ)
    (hbounded : ∀ s l x, x ∈ U s → |v s l x| ≤ M s l)
    (hphysical : ∀ s (z : ℂ), (z : Sphere) ∈ G → π (z : Sphere) ∈ O s →
      π (z : Sphere) ∈ U s)
    (active : S → Fin n → Prop)
    (hbudget : ∀ s l, active s l →
      limsup (v s l) (𝓝[U s] (σ s)) - liminf (v s l) (𝓝[U s] (σ s)) ≤ b l s - a l s)
    (hfree : ∀ x ∈ π '' Gᶜ, x ∉ range σ → ∀ l,
      {t : UnitAddCircle | (x, t) ∈ R l}.Subsingleton)
    (hcompat : OrderedGraphGridCompatibility R θ N (π '' Gᶜ) σ)
    (L : Fin n → Type*) (Mask : Fin n → Set Sphere) (hMask : ∀ l, IsClosed (Mask l))
    (hboundary : ∀ l, frontier (Mask l) ⊆ (π '' Gᶜ)ᶜ)
    (singular : Fin n → S) (hflag : ∀ l, singular l ∈ Flag)
    (P : ∀ l, L l → Set Sphere) (hP : ∀ l i, IsOpen (P l i))
    (hcover : ∀ l, Mask l \ {σ (singular l)} ⊆ ⋃ i, P l i) :
    ∃ (D : PhysicalTerminalDisks G π (π '' Gᶜ)
        (fun s : gridTerminalIndices Flag (reciprocalGridStep N) upperPair a b θ => σ s)
        (fun s => O s))
      (m : ℕ) (H : Fin m → ℂ ≃ₜ ℂ) (γ : Fin m → Circle → ℂ),
      (∀ s, Disjoint (closedTerminalCap (D.H s)) C) ∧
      C ⊆ openCompletedRegion D.H ∧
      (∀ (s : gridTerminalIndices Flag (reciprocalGridStep N) upperPair a b θ) l,
        active s l → ∀ δ η : ℝ,
        ∀ x ∈ frontier (jordanInterior (D.H s)),
        ∀ y ∈ frontier (jordanInterior (D.H s)),
        |shiftedStaircase (reciprocalGridStep N) δ η (v s l (π (x : Sphere))) -
          shiftedStaircase (reciprocalGridStep N) δ η (v s l (π (y : Sphere)))| ≤
            (b l s - a l s) + 4 * reciprocalGridStep N) ∧
      Pairwise (Disjoint on fun j => closure (jordanInterior (H j))) ∧
      (∀ s j, Disjoint (closure (jordanInterior (D.H s))) (closure (jordanInterior (H j)))) ∧
      (∀ j, Disjoint (closedTerminalCap (H j)) C) ∧
      π ⁻¹' (π '' Gᶜ) ⊆ sphericalDiskUnion D.H ∪ sphericalDiskUnion H ∧
      C ⊆ completionCore D.H H ∧ completionCore D.H H ⊆ G ∧
      (∀ j, ContMDiff (𝓡 1) (𝓘(ℝ, ℂ)) ∞ (γ j) ∧ Topology.IsEmbedding (γ j) ∧
        frontier (jordanInterior (H j)) = range (γ j) ∧
        (∀ z ∈ frontier (jordanInterior (H j)), (z : Sphere) ∈ G ∧ π (z : Sphere) ∉ π '' Gᶜ) ∧
        (∃ k : ℕ, ∀ l : Fin n, l.val ≠ k →
          Disjoint (frontier (jordanInterior (H j)))
            ((fun z : ℂ => π (z : Sphere)) ⁻¹' (⋃ r, reciprocalGraphLevel (R l) (θ l) N r))) ∧
        ∀ l, Disjoint (closure (jordanInterior (H j)))
          ((fun z : ℂ => π (z : Sphere)) ⁻¹' Mask l) ∨
          ∃ i, closure (jordanInterior (H j)) ⊆
            (fun z : ℂ => π (z : Sphere)) ⁻¹' (interior (Mask l) ∩ P l i)) := by
  let A := gridTerminalIndices Flag (reciprocalGridStep N) upperPair a b θ
  let : Fintype A := hfin.fintype
  obtain ⟨D, hD, hCQ, hosc⟩ := exists_retained_physical_terminals_with_staircase_bound
    hsard hsch hG hC hCG hinfty π hπ hclosed hsurj hr hTD
    (fun s : A => σ s) (hσ.comp Subtype.val_injective) (fun s => hσB s)
    (fun s => O s) (fun s => hO s) (fun s => U s) (fun s => v s) (fun s => M s)
    (fun s => hbounded s) (fun s => hphysical s) (fun s => active s)
    (fun s l => b l s - a l s) (fun s => hbudget s) (reciprocalGridStep_pos N)
  obtain ⟨m, H, γ, hHd, hDH, hHC, hcover, hCC, hCG', hcurves⟩ :=
    exists_mask_atlas_geometric_completion hsard hsch G π hπ hclosed hsurj hr
      (hG.isClosed_compl.isCompact.image hπ).isClosed rfl hTD hC hCG hinfty
      R hR σ hσB a b θ Flag hband hfin (fun s => O s) D hD
      (fun x hx => hfree x hx.1) (fun x hx => hcompat x hx.1)
      L Mask hMask hboundary singular hflag P hP hcover
  exact ⟨D, m, H, γ, hD, hCQ, hosc, hHd, hDH, hHC, hcover, hCC, hCG', hcurves⟩

end CircleDomainRigidity.FiniteTransfer

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Rigidity_MaskBranchCollars
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonEmbeddedArc.Arc.graphVertices_finite _root_.OAI.CannonMobius.sphereMetric _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Disjoint compact boundaries admit smaller closed collars. Coordinate
absence on a collar is realized by a constant exterior replacement;
present coordinates retain their given local real branches. -/

open Set Filter Function MeasureTheory Classical
open scoped Topology ContDiff

noncomputable section
namespace CircleDomainRigidity.FiniteTransfer

 theorem exists_disjoint_closed_collars
    {I : Type*} [Finite I] (B : I → Set (ℝ × ℝ))
    (hB : ∀ i, IsCompact (B i)) (hdisj : Pairwise (Disjoint on B))
    (V : I → Set (ℝ × ℝ)) (hV : ∀ i, IsOpen (V i)) (hBV : ∀ i, B i ⊆ V i) :
    ∃ O C : I → Set (ℝ × ℝ),
      (∀ i, IsOpen (O i) ∧ B i ⊆ O i ∧ IsClosed (C i) ∧ O i ⊆ C i ∧ C i ⊆ V i) ∧
      Pairwise (Disjoint on C) := by
  have hn : Pairwise (Disjoint on fun i => 𝓝ˢ (B i)) := fun i j hij =>
    disjoint_nhdsSet_nhdsSet (hB i).isClosed (hB j).isClosed (hdisj hij)
  obtain ⟨W, hW, hWd⟩ := hn.exists_mem_filter_basis_of_disjoint (fun i => hasBasis_nhdsSet (B i))
  have hc (i : I) : ∃ O, IsOpen O ∧ B i ⊆ O ∧ closure O ⊆ W i ∩ V i :=
    (hB i).exists_isOpen_closure_subset
      (((hW i).1.inter (hV i)).mem_nhdsSet.mpr (subset_inter (hW i).2 (hBV i)))
  choose O hOo hBO hOsub using hc
  refine ⟨O, fun i => closure (O i), fun i =>
    ⟨hOo i, hBO i, isClosed_closure, subset_closure, (hOsub i).trans inter_subset_right⟩, ?_⟩
  exact fun i j hij => (hWd hij).mono
    ((hOsub i).trans inter_subset_left) ((hOsub j).trans inter_subset_left)

 theorem midpoint_notMem_shiftedLattice {h θ : ℝ} (hh : 0 < h) :
    θ + h / 2 ∉ shiftedLattice h θ := by
  rintro ⟨k, hk⟩
  have heq : (k : ℝ) = 1 / 2 := by nlinarith
  have hk0 : (0 : ℤ) < k := by exact_mod_cast (show (0 : ℝ) < (k : ℝ) by rw [heq]; norm_num)
  have hk1 : k < (1 : ℤ) := by exact_mod_cast (show (k : ℝ) < 1 by rw [heq]; norm_num)
  omega

 theorem exists_mask_branch_collars
    {I : Type*} [Fintype I] {n : ℕ}
    (B : I → Set (ℝ × ℝ)) (hB : ∀ i, IsCompact (B i))
    (hdisj : Pairwise (Disjoint on B))
    (V : I → Set (ℝ × ℝ)) (hV : ∀ i, IsOpen (V i)) (hBV : ∀ i, B i ⊆ V i)
    {K : Set (ℝ × ℝ)} (hVK : ∀ i, Disjoint (V i) K)
    (M : Fin n → Set (ℝ × ℝ)) (f : Fin n → (ℝ × ℝ) → UnitAddCircle)
    (present : I → Fin n → Prop)
    (habsent : ∀ i l, ¬present i l → Disjoint (V i) (M l))
    (v : I → Fin n → (ℝ × ℝ) → ℝ)
    (hv : ∀ i l, present i l → ContDiffOn ℝ ∞ (v i l) (V i))
    (hproj : ∀ i l, present i l → ∀ x ∈ V i, (v i l x : UnitAddCircle) = f l x)
    {h : ℝ} (hh : 0 < h) (θ : Fin n → ℝ)
    (active : I → Fin n)
    (havoid : ∀ i l, present i l → l ≠ active i →
      Disjoint (v i l '' B i) (shiftedLattice h (θ l))) :
    ∃ (O : I → Set (ℝ × ℝ)) (W : Fin n → Set (ℝ × ℝ))
      (u : I → Fin n → (ℝ × ℝ) → ℝ),
      (∀ i, IsOpen (O i) ∧ B i ⊆ O i ∧ O i ⊆ V i) ∧
      (∀ l, IsClosed (W l) ∧ Disjoint (W l) (M l) ∧ Disjoint (W l) K) ∧
      (∀ i l, ContDiffOn ℝ ∞ (u i l) (O i)) ∧
      (∀ i l x, x ∈ O i → (u i l x : UnitAddCircle) =
        exteriorMaskReplacement (W l) ((θ l + h / 2 : ℝ) : UnitAddCircle) (f l) x) ∧
      (∀ i l, l ≠ active i → Disjoint (u i l '' B i) (shiftedLattice h (θ l))) ∧
      (∀ i l, present i l → EqOn (u i l) (v i l) (O i)) := by
  obtain ⟨O, C, hC, hCd⟩ := exists_disjoint_closed_collars B hB hdisj V hV hBV
  let W : Fin n → Set (ℝ × ℝ) := fun l => ⋃ i : {i // ¬present i l}, C i
  let u : I → Fin n → (ℝ × ℝ) → ℝ := fun i l =>
    if present i l then v i l else fun _ => θ l + h / 2
  have hWM (l : Fin n) : Disjoint (W l) (M l) := by
    apply Set.disjoint_left.mpr
    rintro x hx hm
    obtain ⟨i, hi⟩ := mem_iUnion.mp hx
    exact Set.disjoint_left.mp (habsent i l i.property) ((hC i).2.2.2.2 hi) hm
  have hWK (l : Fin n) : Disjoint (W l) K := by
    apply Set.disjoint_left.mpr
    rintro x hx hk
    obtain ⟨i, hi⟩ := mem_iUnion.mp hx
    exact Set.disjoint_left.mp (hVK i) ((hC i).2.2.2.2 hi) hk
  have hpW (i : I) (l : Fin n) (hi : present i l) {x} (hx : x ∈ O i) : x ∉ W l := by
    intro hw
    obtain ⟨j, hj⟩ := mem_iUnion.mp hw
    have hne : i ≠ j.val := fun heq => j.property (heq ▸ hi)
    exact Set.disjoint_left.mp (hCd hne) ((hC i).2.2.2.1 hx) hj
  refine ⟨O, W, u, fun i => ⟨(hC i).1, (hC i).2.1,
    ((hC i).2.2.2.1).trans (hC i).2.2.2.2⟩,
    fun l => ⟨isClosed_iUnion_of_finite fun i => (hC i).2.2.1, hWM l, hWK l⟩, ?_, ?_, ?_, ?_⟩
  · intro i l
    by_cases hi : present i l
    · simpa only [u, ite_eq_left hi] using (hv i l hi).mono
        (((hC i).2.2.2.1).trans (hC i).2.2.2.2)
    · simp only [u, ite_eq_right hi]
      exact contDiffOn_const
  · intro i l x hx
    by_cases hi : present i l
    · rw [show u i l x = v i l x by simp only [u, ite_eq_left hi]]
      rw [exteriorMaskReplacement, piecewise_eq_of_notMem _ _ _ (hpW i l hi hx)]
      exact hproj i l hi x (((hC i).2.2.2.1).trans (hC i).2.2.2.2 hx)
    · have hxW : x ∈ W l := mem_iUnion.mpr ⟨⟨i, hi⟩, (hC i).2.2.2.1 hx⟩
      simp only [u, ite_eq_right hi, exteriorMaskReplacement, piecewise_eq_of_mem _ _ _ hxW]
  · intro i l hla
    by_cases hi : present i l
    · simpa only [u, ite_eq_left hi] using havoid i l hi hla
    · apply Set.disjoint_left.mpr
      rintro r ⟨x, _, rfl⟩ hr
      exact midpoint_notMem_shiftedLattice hh (by simpa only [u, ite_eq_right hi] using hr)
  · intro i l hi x _
    simp only [u, ite_eq_left hi]

end CircleDomainRigidity.FiniteTransfer

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Rigidity_MaskedGridSelection
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Common grid selection from masked L² fields

The correction terms are integrated only where both coordinates are
present. Their finite sum is independent of width. Shrinking the grid
spacing therefore permits the same terminal-count and good-width
selection used for globally defined coordinates.
-/

open Set Filter MeasureTheory
open scoped Topology

noncomputable section

namespace CircleDomainRigidity.FiniteTransfer

theorem exists_grid_for_masked_wedge_cost
    {X P S : Type*} [MeasurableSpace X] [Fintype P] [Countable S]
    {μ : Measure X} [SFinite μ] {n : ℕ}
    (pairs : P → Fin n × Fin n) (hpairs : ∀ p, (pairs p).1 ≠ (pairs p).2)
    (M : Fin n → Set X) (u : Fin n → X → ℝ × ℝ) (c : X → ℝ × ℝ)
    (x : Fin n → X → ℝ) (χ : X → ℝ)
    (hu : ∀ i, Measurable (u i)) (hc : Measurable c)
    (hx : ∀ i, Measurable (x i)) (hχ : Measurable χ)
    (hu2 : ∀ i, MemLp (u i) 2 (μ.restrict (M i))) (hc2 : MemLp c 2 μ)
    (hχ0 : ∀ z, 0 ≤ χ z) (hχ1 : ∀ z, χ z ≤ 1)
    (F : Set S) (hF : F.Finite) (a b : Fin n → S → ℝ)
    (hwidth : ∀ i s, 0 ≤ b i s - a i s)
    (hwidth2 : ∀ i, Summable (fun s => (b i s - a i s) ^ 2))
    (Q : ℕ → (Fin n → ℝ) → Prop)
    (hQ : ∀ N, ∀ᵐ θ ∂reciprocalGridLaw n N, Q N θ)
    {η ρ : ℝ} (hη : 0 < η) (hρ : 0 < ρ)
    (hsmall : (∑ p, ∫ z in M (pairs p).1 ∩ M (pairs p).2,
      |planarWedge (u (pairs p).1 z) (u (pairs p).2 z)| ∂μ) < η / 4) :
    ∃ (N : ℕ) (θ : Fin n → ℝ), reciprocalGridStep N < ρ ∧ Q N θ ∧
      (gridTerminalIndices F (reciprocalGridStep N) pairs a b θ).Finite ∧
      reciprocalGridStep N *
        Real.sqrt ((gridTerminalIndices F (reciprocalGridStep N) pairs a b θ).ncard : ℝ) < η ∧
      ∃ᶠ k in atTop, maskedStaircaseCost μ pairs M u c x χ (reciprocalGridStep N)
        (staircaseWidth (reciprocalGridStep N) k) θ < η := by
  let W : ℕ → ℕ → (Fin n → ℝ) → ℝ := fun N k =>
    maskedStaircaseCost μ pairs M u c x χ (reciprocalGridStep N)
      (staircaseWidth (reciprocalGridStep N) k)
  have hestimate N k := integrable_maskedStaircaseCost_and_mean_le pairs hpairs
    M u c x χ hu hc hx hχ hu2 hc2 (reciprocalGridStep_pos N)
    (staircaseWidth_pos (reciprocalGridStep_pos N) k)
    (staircaseWidth_lt (reciprocalGridStep_pos N) k) hχ0 hχ1
  have hlimit := ((reciprocalGridStep_tendsto_zero.mul_const
    (∑ p, ∫ z in M (pairs p).1 ∩ M (pairs p).2,
      |planarWedge (u (pairs p).1 z) (c z)| +
        |planarWedge (c z) (u (pairs p).2 z)| ∂μ)).const_add
      (∑ p, ∫ z in M (pairs p).1 ∩ M (pairs p).2,
        |planarWedge (u (pairs p).1 z) (u (pairs p).2 z)| ∂μ))
  simp only [zero_mul, add_zero] at hlimit
  have hmean : ∀ᶠ N in atTop, ∀ k, (∫ θ, W N k θ ∂reciprocalGridLaw n N) < η / 4 := by
    filter_upwards [hlimit.eventually_lt_const hsmall] with N hN k
    exact (hestimate N k).2.trans_lt hN
  exact exists_grid_with_finite_terminals_and_good_widths F hF pairs hpairs a b
    hwidth hwidth2 W Q hη hρ (fun N k => (hestimate N k).1)
    (fun N k => Filter.Eventually.of_forall
      (maskedStaircaseCost_nonneg μ pairs M u c x χ _ _)) hQ hmean

end CircleDomainRigidity.FiniteTransfer

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Rigidity_MaskedCircleCost
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Actual masked circle cost away from the retained core

Mask boundaries lie inside the core. On its complement every active
mask is locally present, so the circle cutoff formula holds there.
This identifies the masked random cost with the actual spatial wedge
sum and proves integrability from each coordinate's own masked L² norm.
-/

open Set Filter MeasureTheory
open scoped Topology ContDiff

noncomputable section

namespace CircleDomainRigidity.FiniteTransfer

theorem masked_circle_cutoff_wedges_integrable_and_eq_cost
    {n : ℕ} {G K : Set (ℝ × ℝ)} (hG : IsOpen G) (hK : MeasurableSet K)
    (M : Fin n → Set (ℝ × ℝ)) (hM : ∀ i, MeasurableSet (M i))
    (hboundary : ∀ i, frontier (M i) ⊆ K)
    (f : Fin n → (ℝ × ℝ) → UnitAddCircle) (χ : (ℝ × ℝ) → ℝ)
    (hf : ∀ i, SmoothCircleOn (f i) (G ∩ interior (M i)))
    (hmf : ∀ i, Measurable (f i)) (hdf : ∀ i, Measurable (circleGradient (f i)))
    (hf2 : ∀ i, MemLp (circleGradient (f i)) 2
      ((volume.restrict (G \ K)).restrict (M i)))
    (hχ : ContDiff ℝ ∞ χ) (hdχ : Measurable (planarGradient χ))
    (hχ2 : MemLp (planarGradient χ) 2 (volume.restrict (G \ K)))
    (N : ℕ) {δ : ℝ} (hδ : 0 < δ) (hδh : δ < reciprocalGridStep N / 4)
    (hχ0 : ∀ z, 0 ≤ χ z) (hχ1 : ∀ z, χ z ≤ 1) (θ : Fin n → ℝ) :
    IntegrableOn (maskedCircleWedges M (circleCutoffFamily f χ N δ θ)) (G \ K) ∧
      (∫ z in G \ K, maskedCircleWedges M (circleCutoffFamily f χ N δ θ) z) =
        maskedStaircaseCost (volume.restrict (G \ K)) upperPair M
          (fun i => circleGradient (f i)) (planarGradient χ)
          (fun i z => circleRepresentative (f i z)) χ (reciprocalGridStep N) δ θ := by
  let μ := volume.restrict (G \ K)
  let d : UpperPairs n → (ℝ × ℝ) → ℝ := fun p z => |planarWedge
    (staircaseCovector (reciprocalGridStep N) δ (χ z) (θ (upperPair p).1)
      (circleRepresentative (f (upperPair p).1 z)) (circleGradient (f (upperPair p).1) z)
      (planarGradient χ z))
    (staircaseCovector (reciprocalGridStep N) δ (χ z) (θ (upperPair p).2)
      (circleRepresentative (f (upperPair p).2 z)) (circleGradient (f (upperPair p).2) z)
      (planarGradient χ z))|
  let e : UpperPairs n → (ℝ × ℝ) → ℝ := fun p z => |planarWedge
    ((M (upperPair p).1).indicator (circleGradient (circleCutoffFamily f χ N δ θ (upperPair p).1)) z)
    ((M (upperPair p).2).indicator (circleGradient (circleCutoffFamily f χ N δ θ (upperPair p).2)) z)|
  have hformula (z : ℝ × ℝ) (hz : z ∈ G \ K) (i : Fin n) (hzM : z ∈ M i) :
      circleGradient (circleCutoffFamily f χ N δ θ i) z =
        staircaseCovector (reciprocalGridStep N) δ (χ z) (θ i)
          (circleRepresentative (f i z)) (circleGradient (f i) z) (planarGradient χ z) := by
    have hzi : z ∈ interior (M i) :=
      (mem_interior_iff_notMem_frontier hzM).mpr (fun hb => hz.2 (hboundary i hb))
    exact circleGradient_reciprocal_cutoff
      ((hf i).continuousOn.continuousAt ((hG.inter isOpen_interior).mem_nhds ⟨hz.1, hzi⟩))
      (hf i z ⟨hz.1, hzi⟩ _ (circleCut_ne (f i) z)) hχ.contDiffAt
      (Filter.Eventually.of_forall (coe_circleBranch (f i) (circleCut (f i) z)))
      N hδ hδh (θ i)
  have heq (p : UpperPairs n) : e p =ᵐ[μ] (M (upperPair p).1 ∩ M (upperPair p).2).indicator (d p) := by
    filter_upwards [ae_restrict_mem (hG.measurableSet.diff hK)] with z hz
    dsimp only [e]
    rw [abs_wedge_indicators]
    by_cases hm : z ∈ M (upperPair p).1 ∩ M (upperPair p).2
    · simp only [indicator_of_mem hm]
      rw [hformula z hz _ hm.1, hformula z hz _ hm.2]
    · simp only [indicator_of_notMem hm]
  have hi (p : UpperPairs n) : Integrable (d p)
      (μ.restrict (M (upperPair p).1 ∩ M (upperPair p).2)) := by
    apply integrable_staircase_pair_at_shifts_of_memLp _ _ _ _ _ _
      (hdf _) (hdf _) hdχ (measurable_circleRepresentative.comp (hmf _))
      (measurable_circleRepresentative.comp (hmf _)) hχ.continuous.measurable
      ((hf2 _).mono_measure (Measure.restrict_mono inter_subset_left le_rfl))
      ((hf2 _).mono_measure (Measure.restrict_mono inter_subset_right le_rfl))
      (hχ2.mono_measure Measure.restrict_le_self)
      (reciprocalGridStep_pos N) hδ hδh hχ0 hχ1
  have hei (p : UpperPairs n) : Integrable (e p) μ :=
    ((integrable_indicator_iff ((hM _).inter (hM _))).2 (hi p)).congr (heq p).symm
  refine ⟨integrable_finsetSum _ (fun p _ => hei p), ?_⟩
  change (∫ z, ∑ p, e p z ∂μ) = ∑ p, ∫ z, d p z ∂μ.restrict (M (upperPair p).1 ∩ M (upperPair p).2)
  rw [integral_finsetSum _ (fun p _ => hei p)]
  apply Finset.sum_congr rfl
  intro p _
  rw [integral_congr_ae (heq p), integral_indicator ((hM _).inter (hM _))]

/-- Grid selection for the actual masked circle cutoff, with finite
terminal indices and an arbitrarily late good width. -/
theorem exists_grid_for_actual_masked_circle_wedges
    {n : ℕ} {S : Type*} [Countable S] {G K : Set (ℝ × ℝ)}
    (hG : IsOpen G) (hK : MeasurableSet K)
    (M : Fin n → Set (ℝ × ℝ)) (hM : ∀ i, MeasurableSet (M i))
    (hboundary : ∀ i, frontier (M i) ⊆ K)
    (f : Fin n → (ℝ × ℝ) → UnitAddCircle) (χ : (ℝ × ℝ) → ℝ)
    (hf : ∀ i, SmoothCircleOn (f i) (G ∩ interior (M i)))
    (hmf : ∀ i, Measurable (f i)) (hdf : ∀ i, Measurable (circleGradient (f i)))
    (hf2 : ∀ i, MemLp (circleGradient (f i)) 2
      ((volume.restrict (G \ K)).restrict (M i)))
    (hχ : ContDiff ℝ ∞ χ) (hdχ : Measurable (planarGradient χ))
    (hχ2 : MemLp (planarGradient χ) 2 (volume.restrict (G \ K)))
    (hχ0 : ∀ z, 0 ≤ χ z) (hχ1 : ∀ z, χ z ≤ 1)
    (F : Set S) (hF : F.Finite) (a b : Fin n → S → ℝ)
    (hwidth : ∀ i s, 0 ≤ b i s - a i s)
    (hwidth2 : ∀ i, Summable (fun s => (b i s - a i s) ^ 2))
    (P : ℕ → (Fin n → ℝ) → Prop) (hP : ∀ N, ∀ᵐ θ ∂reciprocalGridLaw n N, P N θ)
    {η ρ : ℝ} (hη : 0 < η) (hρ : 0 < ρ)
    (hsmall : (∑ p : UpperPairs n, ∫ z in M (upperPair p).1 ∩ M (upperPair p).2,
      |planarWedge (circleGradient (f (upperPair p).1) z)
        (circleGradient (f (upperPair p).2) z)| ∂volume.restrict (G \ K)) < η / 4) :
    ∃ (N : ℕ) (θ : Fin n → ℝ), reciprocalGridStep N < ρ ∧ P N θ ∧
      (gridTerminalIndices F (reciprocalGridStep N) upperPair a b θ).Finite ∧
      reciprocalGridStep N *
        Real.sqrt ((gridTerminalIndices F (reciprocalGridStep N) upperPair a b θ).ncard : ℝ) < η ∧
      (∀ k, IntegrableOn (maskedCircleWedges M (circleCutoffFamily f χ N
        (staircaseWidth (reciprocalGridStep N) k) θ)) (G \ K)) ∧
      ∃ᶠ k in atTop, (∫ z in G \ K, maskedCircleWedges M (circleCutoffFamily f χ N
        (staircaseWidth (reciprocalGridStep N) k) θ) z) < η := by
  obtain ⟨N, θ, hN, hPθ, hfin, hcard, hgood⟩ :=
    exists_grid_for_masked_wedge_cost upperPair upperPair_ne M
      (fun i => circleGradient (f i)) (planarGradient χ)
      (fun i z => circleRepresentative (f i z)) χ hdf hdχ
      (fun i => measurable_circleRepresentative.comp (hmf i)) hχ.continuous.measurable
      hf2 hχ2 hχ0 hχ1 F hF a b hwidth hwidth2 P hP hη hρ hsmall
  have hcost (k : ℕ) := masked_circle_cutoff_wedges_integrable_and_eq_cost hG hK M hM hboundary
    f χ hf hmf hdf hf2 hχ hdχ hχ2 N (staircaseWidth_pos (reciprocalGridStep_pos N) k)
      (staircaseWidth_lt (reciprocalGridStep_pos N) k) hχ0 hχ1 θ
  refine ⟨N, θ, hN, hPθ, hfin, hcard, fun k => (hcost k).1, ?_⟩
  exact hgood.mono (fun k hk => (hcost k).2.trans_lt hk)

end CircleDomainRigidity.FiniteTransfer

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Rigidity_MaskedCorePreparation
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonEmbeddedArc.Arc.graphVertices_finite _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Regular cores for the masked circle data

The original L² bounds on the separate masks make the actual masked
wedge sum integrable. A regular retained core contains all mask
boundaries and leaves an arbitrarily small tail. The original cutoff
construction then supplies the compactly supported smooth interpolation.
-/

open Set Filter MeasureTheory Finset
open scoped Topology ContDiff

noncomputable section

namespace CircleDomainRigidity.FiniteTransfer

theorem integrable_maskedCircleWedges_of_memLp
    {μ : Measure (ℝ × ℝ)} {n : ℕ}
    (M : Fin n → Set (ℝ × ℝ)) (hM : ∀ i, MeasurableSet (M i))
    (f : Fin n → (ℝ × ℝ) → UnitAddCircle)
    (hf : ∀ i, MemLp (circleGradient (f i)) 2 (μ.restrict (M i))) :
    Integrable (maskedCircleWedges M f) μ := by
  have hi (i : Fin n) : MemLp ((M i).indicator (circleGradient (f i))) 2 μ :=
    (memLp_indicator_iff_restrict (hM i)).mpr (hf i)
  exact integrable_finsetSum univ (fun p _ =>
    integrable_abs_planarWedge_of_memLp (hi (upperPair p).1) (hi (upperPair p).2))

theorem maskedCircleWedges_nonneg
    {n : ℕ} (M : Fin n → Set (ℝ × ℝ))
    (f : Fin n → (ℝ × ℝ) → UnitAddCircle) (z : ℝ × ℝ) :
    0 ≤ maskedCircleWedges M f z :=
  sum_nonneg (fun _ _ => abs_nonneg _)

/-- The core is constructed from the original masked energy. Its
regularity uses only the previously identified scalar Sard input. -/
theorem exists_regular_masked_core_and_cutoff
    (hsard : SmoothPlanarSard) {G K₀ : Set (ℝ × ℝ)}
    (hG : IsOpen G) (hGc : IsCompact Gᶜ) (hK₀ : IsClosed K₀) (hK₀G : K₀ ⊆ G)
    {n : ℕ} (M : Fin n → Set (ℝ × ℝ)) (hM : ∀ i, MeasurableSet (M i))
    (hboundaryG : ∀ i, frontier (M i) ⊆ G)
    (f : Fin n → (ℝ × ℝ) → UnitAddCircle)
    (hf : ∀ i, MemLp (circleGradient (f i)) 2 ((volume.restrict G).restrict (M i)))
    {η : ℝ} (hη : 0 < η) :
    ∃ (ψ : (ℝ × ℝ) → ℝ) (t : ℝ) (K : Set (ℝ × ℝ)) (χ : (ℝ × ℝ) → ℝ),
      ContDiff ℝ ∞ ψ ∧ HasCompactSupport ψ ∧ t ∈ Set.Ioo 0 1 ∧
      (∀ z, ψ z = t → fderiv ℝ ψ z ≠ 0) ∧ K = {z | ψ z ≤ t} ∧
      IsClosed K ∧ K₀ ⊆ interior K ∧ K ⊆ G ∧ IsCompact (closure Kᶜ) ∧
      (∀ i, frontier (M i) ⊆ interior K) ∧
      (∫ z in G \ K, maskedCircleWedges M f z) < η ∧
      ContDiff ℝ ∞ χ ∧ HasCompactSupport χ ∧ (∀ z, χ z ∈ Set.Icc 0 1) ∧
      (∀ᶠ z in 𝓝ˢ K, χ z = 0) ∧ (∀ᶠ z in 𝓝ˢ Gᶜ, χ z = 1) ∧
      MemLp (planarGradient χ) 2 volume := by
  let A := K₀ ∪ ⋃ i, frontier (M i)
  have hA : IsClosed A := hK₀.union (isClosed_iUnion_of_finite fun _ => isClosed_frontier)
  have hAG : A ⊆ G := union_subset hK₀G (iUnion_subset hboundaryG)
  obtain ⟨ψ, t, K, hψ, hψc, ht, hreg, hKeq, hK, hAK, hKG, hKc, htail⟩ :=
    exists_regular_core_small_tail hsard hG hGc hA hAG
      (integrable_maskedCircleWedges_of_memLp M hM f hf) (maskedCircleWedges_nonneg M f) hη
  obtain ⟨χ, hχ, hχc, hχrange, hχzero, hχone, hχ2⟩ :=
    exists_cutoff_near_complement hGc hK hKG
  refine ⟨ψ, t, K, χ, hψ, hψc, ht, hreg, hKeq, hK,
    subset_union_left.trans hAK, hKG, hKc, ?_, htail,
    hχ, hχc, hχrange, hχzero, hχone, hχ2⟩
  intro i
  exact (subset_iUnion_of_subset i (Subset.refl _)).trans (subset_union_right.trans hAK)

end CircleDomainRigidity.FiniteTransfer

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Rigidity_MaskedFilledEnergy
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonMobius.sphereMetric _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Charging masked fillings to the original masked cost

Every added disk has zero pairwise wedge cost. Off the disks the
intrinsic differentials agree locally with the retained coordinates.
This proves the full cofinite masked energy estimate.
-/

open Set Filter MeasureTheory Finset
open scoped Topology ContDiff Matrix.Norms.Elementwise

noncomputable section

namespace CircleDomainRigidity.FiniteTransfer

theorem IsMaskedFilledCircleFamily.integral_wedges_le_original
    {I : Type*} [Fintype I] {n : ℕ} {D : I → Set (ℝ × ℝ)}
    {Ω Q K G : Set (ℝ × ℝ)} {M : Fin n → Set (ℝ × ℝ)}
    {v F : Fin n → (ℝ × ℝ) → UnitAddCircle}
    (hF : IsMaskedFilledCircleFamily D Ω M v F) (hD : ∀ i, IsOpen (D i))
    (hΩ : IsOpen Ω) (hQ : IsClosed Q) (hK : IsClosed K) (hKc : IsCompact (closure Kᶜ))
    (htail : Q ∩ closure Kᶜ ⊆ Ω) (hG : MeasurableSet G)
    (hM : ∀ i, IsClosed (M i)) (hboundary : ∀ i, frontier (M i) ⊆ interior K)
    (hcover : Q ⊆ G ∪ ⋃ i, D i)
    (hv : IntegrableOn (fun z => 2 * maskedCircleWedges M v z) (G \ K)) :
    (∫ z in Q \ K, 2 * maskedCircleWedges M F z) ≤
      ∫ z in G \ K, 2 * maskedCircleWedges M v z := by
  let S := (Q \ K) ∩ G
  have hSt : S ⊆ Q \ K := inter_subset_left
  have hSG : S ⊆ G \ K := fun z hz => ⟨hz.2, hz.1.2⟩
  have hS : MeasurableSet S := (hQ.measurableSet.diff hK.measurableSet).inter hG
  have hC : IsCompact (Q ∩ closure Kᶜ) :=
    hKc.of_isClosed_subset (hQ.inter isClosed_closure) inter_subset_right
  have hCΩ : Q ∩ closure Kᶜ ⊆ Ω \ ⋃ i, frontier (M i) := by
    intro z hz
    refine ⟨htail hz, ?_⟩
    intro hb
    obtain ⟨i, hi⟩ := mem_iUnion.mp hb
    have hn : z ∉ interior K := by
      simpa only [closure_compl, mem_compl_iff] using hz.2
    exact hn (hboundary i hi)
  have hcont := ((continuousOn_maskedCircleWedges_off_boundaries hΩ M hM F hF.1).const_mul 2).mono hCΩ
  have hFi : IntegrableOn (fun z => 2 * maskedCircleWedges M F z) (Q \ K) :=
    (hcont.integrableOn_compact hC).mono_set (fun z hz => ⟨hz.1, subset_closure hz.2⟩)
  have hle (z : ℝ × ℝ) : maskedCircleWedges M F z ≤ maskedCircleWedges M v z := by
    by_cases hm : ∃ i, z ∈ D i
    · obtain ⟨i, hi⟩ := hm
      rw [hF.masked_wedges_eq_zero hi]
      exact maskedCircleWedges_nonneg M v z
    · rw [hF.masked_wedges_eq_outside hD (not_exists.mp hm)]
  have heq : (∫ z in Q \ K, 2 * maskedCircleWedges M F z) =
      ∫ z in S, 2 * maskedCircleWedges M F z := by
    apply setIntegral_eq_of_subset_of_forall_sdiff_eq_zero
      (hQ.measurableSet.diff hK.measurableSet) hSt
    intro z hz
    have hzG : z ∉ G := fun hzG => hz.2 ⟨hz.1, hzG⟩
    obtain ⟨i, hi⟩ := mem_iUnion.mp ((hcover hz.1.1).resolve_left hzG)
    rw [hF.masked_wedges_eq_zero hi, mul_zero]
  calc
    _ = ∫ z in S, 2 * maskedCircleWedges M F z := heq
    _ ≤ ∫ z in S, 2 * maskedCircleWedges M v z :=
      setIntegral_mono_on (hFi.mono_set hSt) (hv.mono_set hSG) hS
        (fun z _ => mul_le_mul_of_nonneg_left (hle z) (by norm_num))
    _ ≤ _ := setIntegral_mono_set hv
      (Eventually.of_forall fun z => mul_nonneg (by norm_num) (maskedCircleWedges_nonneg M v z))
      (Eventually.of_forall hSG)

theorem IsMaskedFilledCircleFamily.exists_spherical_metric_of_original_cost
    {I : Type*} [Fintype I] {n : ℕ} {D : I → Set (ℝ × ℝ)}
    {Ω Q K G : Set (ℝ × ℝ)} {M : Fin n → Set (ℝ × ℝ)}
    {v F : Fin n → (ℝ × ℝ) → UnitAddCircle}
    (hF : IsMaskedFilledCircleFamily D Ω M v F) (hD : ∀ i, IsOpen (D i))
    (hΩ : IsOpen Ω) (hQ : IsClosed Q) (hK : IsClosed K) (hKc : IsCompact (closure Kᶜ))
    (htail : Q ∩ closure Kᶜ ⊆ Ω) (hG : MeasurableSet G)
    (hM : ∀ i, IsClosed (M i)) (hboundary : ∀ i, frontier (M i) ⊆ interior K)
    (hcover : Q ⊆ G ∪ ⋃ i, D i)
    (hv : IntegrableOn (fun z => 2 * maskedCircleWedges M v z) (G \ K))
    {ε : ℝ} (hε : (∫ z in G \ K, 2 * maskedCircleWedges M v z) < ε) :
    ∃ (R : ℝ) (g : (ℝ × ℝ) → PlanarMetric), 0 < R ∧ ContDiff ℝ ∞ g ∧
      (∀ z, (g z).PosDef) ∧
      (∀ᶠ z in 𝓝ˢ K, g z = sphericalMetricFactor z • 1) ∧
      (∀ z ∉ Metric.closedBall 0 R, g z = sphericalMetricFactor z • 1) ∧
      (∑ i : Fin n, ∫ z in (Q \ K) ∩ M i, fieldEnergy (circleGradient (F i)) g z) < ε := by
  have hbudget := (hF.integral_wedges_le_original hD hΩ hQ hK hKc htail hG hM hboundary hcover hv).trans_lt hε
  exact exists_spherical_metric_for_masked_cofinite_circles hΩ hQ hK hKc htail M hM hboundary F hF.1 hbudget

end CircleDomainRigidity.FiniteTransfer

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Rigidity_MaskedGridPreparation
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Preparing the actual masked circle transfer

The regular core contains every mask boundary, the cutoff is constructed,
and the actual reciprocal grid and good widths are selected from the
original masked L² data. No modified-coordinate integrability is assumed.
-/

open Set Filter MeasureTheory Finset
open scoped Topology ContDiff

noncomputable section

namespace CircleDomainRigidity.FiniteTransfer

theorem integral_maskedCircleWedges_eq_intersections
    {μ : Measure (ℝ × ℝ)} {n : ℕ}
    (M : Fin n → Set (ℝ × ℝ)) (hM : ∀ i, MeasurableSet (M i))
    (f : Fin n → (ℝ × ℝ) → UnitAddCircle)
    (hf : ∀ i, MemLp (circleGradient (f i)) 2 (μ.restrict (M i))) :
    (∫ z, maskedCircleWedges M f z ∂μ) =
      ∑ p : UpperPairs n, ∫ z in M (upperPair p).1 ∩ M (upperPair p).2,
        |planarWedge (circleGradient (f (upperPair p).1) z)
          (circleGradient (f (upperPair p).2) z)| ∂μ := by
  have hi (i : Fin n) : MemLp ((M i).indicator (circleGradient (f i))) 2 μ :=
    (memLp_indicator_iff_restrict (hM i)).mpr (hf i)
  unfold maskedCircleWedges
  rw [integral_finsetSum _ (fun p _ =>
    integrable_abs_planarWedge_of_memLp (hi (upperPair p).1) (hi (upperPair p).2))]
  apply sum_congr rfl
  intro p _
  exact integral_abs_wedge_indicators μ (hM _) (hM _) _ _

theorem exists_regular_masked_core_cutoff_and_grid
    (hsard : SmoothPlanarSard) {G K₀ : Set (ℝ × ℝ)}
    (hG : IsOpen G) (hGc : IsCompact Gᶜ) (hK₀ : IsClosed K₀) (hK₀G : K₀ ⊆ G)
    {n : ℕ} {S : Type*} [Countable S]
    (M : Fin n → Set (ℝ × ℝ)) (hM : ∀ i, MeasurableSet (M i))
    (hboundaryG : ∀ i, frontier (M i) ⊆ G)
    (f : Fin n → (ℝ × ℝ) → UnitAddCircle)
    (hf : ∀ i, SmoothCircleOn (f i) (G ∩ interior (M i)))
    (hmf : ∀ i, Measurable (f i)) (hdf : ∀ i, Measurable (circleGradient (f i)))
    (hf2 : ∀ i, MemLp (circleGradient (f i)) 2 ((volume.restrict G).restrict (M i)))
    (F : Set S) (hF : F.Finite) (a b : Fin n → S → ℝ)
    (hwidth : ∀ i s, 0 ≤ b i s - a i s)
    (hwidth2 : ∀ i, Summable (fun s => (b i s - a i s) ^ 2))
    (P : ℕ → (Fin n → ℝ) → Prop) (hP : ∀ N, ∀ᵐ θ ∂reciprocalGridLaw n N, P N θ)
    {η ρ : ℝ} (hη : 0 < η) (hρ : 0 < ρ) :
    ∃ (ψ : (ℝ × ℝ) → ℝ) (t : ℝ) (K : Set (ℝ × ℝ))
      (χ : (ℝ × ℝ) → ℝ) (N : ℕ) (θ : Fin n → ℝ),
      ContDiff ℝ ∞ ψ ∧ HasCompactSupport ψ ∧ t ∈ Set.Ioo 0 1 ∧
      (∀ z, ψ z = t → fderiv ℝ ψ z ≠ 0) ∧ K = {z | ψ z ≤ t} ∧
      IsClosed K ∧ K₀ ⊆ interior K ∧ K ⊆ G ∧ IsCompact (closure Kᶜ) ∧
      (∀ i, frontier (M i) ⊆ interior K) ∧
      ContDiff ℝ ∞ χ ∧ HasCompactSupport χ ∧ (∀ z, χ z ∈ Set.Icc 0 1) ∧
      (∀ᶠ z in 𝓝ˢ K, χ z = 0) ∧ (∀ᶠ z in 𝓝ˢ Gᶜ, χ z = 1) ∧
      reciprocalGridStep N < ρ ∧ P N θ ∧
      (gridTerminalIndices F (reciprocalGridStep N) upperPair a b θ).Finite ∧
      reciprocalGridStep N *
        Real.sqrt ((gridTerminalIndices F (reciprocalGridStep N) upperPair a b θ).ncard : ℝ) < η ∧
      (∀ k, IntegrableOn (maskedCircleWedges M (circleCutoffFamily f χ N
        (staircaseWidth (reciprocalGridStep N) k) θ)) (G \ K)) ∧
      ∃ᶠ k in atTop, (∫ z in G \ K, maskedCircleWedges M (circleCutoffFamily f χ N
        (staircaseWidth (reciprocalGridStep N) k) θ) z) < η := by
  obtain ⟨ψ, t, K, χ, hψ, hψc, ht, hreg, hKeq, hK, hK₀K, hKG, hKc,
      hbd, hsmall, hχ, hχc, hχrange, hχzero, hχone, hχ2⟩ :=
    exists_regular_masked_core_and_cutoff hsard hG hGc hK₀ hK₀G M hM hboundaryG f hf2
      (η := η / 4) (div_pos hη (by norm_num))
  have hftail (i : Fin n) : MemLp (circleGradient (f i)) 2
      ((volume.restrict (G \ K)).restrict (M i)) :=
    (hf2 i).mono_measure (Measure.restrict_mono_measure
      (Measure.restrict_mono_set volume Set.sdiff_subset) (M i))
  have hsum : (∑ p : UpperPairs n, ∫ z in M (upperPair p).1 ∩ M (upperPair p).2,
      |planarWedge (circleGradient (f (upperPair p).1) z)
        (circleGradient (f (upperPair p).2) z)| ∂volume.restrict (G \ K)) < η / 4 := by
    rw [← integral_maskedCircleWedges_eq_intersections M hM f hftail]
    exact hsmall
  obtain ⟨N, θ, hN, hPθ, hfin, hcard, hvi, hgood⟩ :=
    exists_grid_for_actual_masked_circle_wedges hG hK.measurableSet M hM
      (fun i => (hbd i).trans interior_subset) f χ hf hmf hdf hftail hχ
      (measurable_planarGradient χ) (hχ2.mono_measure Measure.restrict_le_self)
      (fun z => (hχrange z).1) (fun z => (hχrange z).2)
      F hF a b hwidth hwidth2 P hP hη hρ hsum
  exact ⟨ψ, t, K, χ, N, θ, hψ, hψc, ht, hreg, hKeq, hK, hK₀K, hKG, hKc, hbd,
    hχ, hχc, hχrange, hχzero, hχone, hN, hPθ, hfin, hcard, hvi, hgood⟩

end CircleDomainRigidity.FiniteTransfer

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Topology_FiniteJordanModelInput
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions _root_.OAI.CircleDomainRigidity.finiteSphericalArea _root_.OAI.CircleDomainRigidity.sphereFirstCountableTopology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace CircleDomainRigidity
open Set Function
open FiniteTransfer

namespace FiniteTransfer

lemma uniformize_finite_completion_of_jordan_models
    (hmodels : FiniteJordanModelUniformization)
    {I : Type*} [Finite I] (H : I → ℂ ≃ₜ ℂ)
    (hd : Pairwise (Disjoint on fun i => closure (jordanInterior (H i))))
    {W : Set Sphere} (e : Sphere ≃ₜ Sphere)
    (hW : W ⊆ openCompletedRegion H) (he : IsConformalOn e W) :
    ∃ (V : Set Sphere) (f : Sphere → Sphere),
      IsCircleDomain V ∧ BijOn f (openCompletedRegion H) V ∧ IsConformalOn f W ∧
        IsConformalEquivalence (f ∘ e.symm) (e '' openCompletedRegion H) V := by
  classical
  let : Fintype I := Fintype.ofFinite I
  let a : I ≃ Fin (Fintype.card I) := Fintype.equivFin I
  let H' : Fin (Fintype.card I) → ℂ ≃ₜ ℂ := fun i => H (a.symm i)
  have hd' : Pairwise (Disjoint on fun i => closure (jordanInterior (H' i))) :=
    fun _ _ hij => hd (a.symm.injective.ne hij)
  have hreg : openCompletedRegion H'=openCompletedRegion H := by
    apply congrArg compl
    ext p
    constructor
    · intro hp
      obtain ⟨i,hi⟩ := mem_iUnion.mp hp
      exact mem_iUnion.mpr ⟨a.symm i,hi⟩
    · intro hp
      obtain ⟨i,hi⟩ := mem_iUnion.mp hp
      apply mem_iUnion.mpr
      refine ⟨a i,?_⟩
      simpa only [H',a.symm_apply_apply] using hi
  obtain ⟨V,g,hV,hg⟩ := hmodels (Fintype.card I) H' hd' e
  rw [hreg] at hg
  refine ⟨V,g ∘ e,hV,hg.bijOn.comp e.injective.bijOn_image,
    hg.1.comp he (fun p hp => ⟨p,hW hp,rfl⟩),?_⟩
  have heq : (g ∘ e) ∘ e.symm=g := by funext p; simp only [comp_apply,e.apply_symm_apply]
  simpa only [heq] using hg

end FiniteTransfer
end CircleDomainRigidity

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Transfer_CompletedChart
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions _root_.OAI.CircleDomainRigidity.finiteSphericalArea _root_.OAI.CircleDomainRigidity.sphereFirstCountableTopology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# The actual completed region in the finite real chart

These identifications pass the spherical disk completion to the real
coordinates used by the energy estimates, preserving the original core
and the exact open extension domain.
-/

open Set Function
open scoped Topology

noncomputable section

namespace CircleDomainRigidity.FiniteTransfer

theorem real_completedRegion_subset_extension
    {I J : Type*} (T : I → ℂ ≃ₜ ℂ) (H : J → ℂ ≃ₜ ℂ)
    (G B : Set Sphere) (π : Sphere → Sphere)
    (hbad : ∀ x ∈ Gᶜ, π x ∈ B)
    (hcover : π ⁻¹' B ⊆ sphericalDiskUnion T ∪ sphericalDiskUnion H) :
    realChartDomain (completedRegion T) ⊆ realChartDomain G ∪ ⋃ j, realJordanInterior (H j) := by
  have hsub : realChartDomain (completedRegion T) ⊆ realChartDomain (G ∪ sphericalDiskUnion H) :=
    preimage_mono (completedRegion_subset_extension_domain T H G B π hbad hcover)
  simpa only [realChartDomain_union, realChartDomain_sphericalDiskUnion] using hsub

theorem real_core_avoids_filling
    {J : Type*} {K : Set (ℝ × ℝ)} {C : Set Sphere} (H : J → ℂ ≃ₜ ℂ)
    (hKC : sphericalCore K ⊆ C)
    (hHC : ∀ j, Disjoint (((↑) : ℂ → Sphere) '' closure (jordanInterior (H j))) C) :
    ∀ x ∈ K, ∀ j, x ∉ realJordanInterior (H j) := by
  intro x hx j hj
  obtain ⟨z, hz, rfl⟩ := hj
  exact Set.disjoint_left.mp (hHC j) ⟨z, subset_closure hz, rfl⟩
    (hKC ((coe_mem_sphericalCore K z).mpr hx))

theorem real_boundary_in_domain_and_plateau
    {J : Type*} {G : Set Sphere} (H : J → ℂ ≃ₜ ℂ) (χ : (ℝ × ℝ) → ℝ)
    (hG : ∀ j z, z ∈ frontier (jordanInterior (H j)) → (z : Sphere) ∈ G)
    (hHC : ∀ j, Disjoint (((↑) : ℂ → Sphere) '' closure (jordanInterior (H j))) (cutoffCore χ)) :
    ∀ j z, z ∈ frontier (jordanInterior (H j)) →
      Complex.equivRealProdCLM z ∈ realChartDomain G ∩ interior {x | χ x = 1} := by
  intro j z hz
  refine ⟨?_, boundary_in_one_plateau_of_disjoint_cutoffCore (H j) χ (hHC j) z hz⟩
  simpa only [realChartDomain, mem_preimage, ContinuousLinearEquiv.symm_apply_apply] using hG j z hz

end CircleDomainRigidity.FiniteTransfer

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Topology_CircleMobiusImage
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonMobius.sphereMetric _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions _root_.OAI.CircleDomainRigidity.finiteSphericalArea _root_.OAI.CircleDomainRigidity.sphereFirstCountableTopology
attribute [-simp] _root_.OAI.CannonMobius.affine_coe _root_.OAI.CannonMobius.affine_infty _root_.OAI.CannonMobius.inv_inv_apply _root_.OAI.CannonMobius.roundChart_coe _root_.OAI.CannonMobius.tripleMap_mul _root_.OAI.CircleDomainRigidity.CompactScalarModel.postcompose_coefficient _root_.OAI.CircleDomainRigidity.FiniteTransfer.coe_mem_sphericalCore _root_.OAI.CircleDomainRigidity.FiniteTransfer.coe_mem_sphericalDiskUnion _root_.OAI.CircleDomainRigidity.FiniteTransfer.infty_mem_cutoffCore _root_.OAI.CircleDomainRigidity.FiniteTransfer.infty_mem_sphericalCore _root_.OAI.CircleDomainRigidity.FiniteTransfer.infty_not_mem_sphericalDiskUnion _root_.OAI.CircleDomainRigidity.FiniteTransfer.realChartDomain_union _root_.OAI.CircleDomainRigidity.affineSphere_coe _root_.OAI.CircleDomainRigidity.affineSphere_infty _root_.OAI.CircleDomainRigidity.centeredJordanCoordinate_self _root_.OAI.CircleDomainRigidity.chartSymm_coe_apply _root_.OAI.CircleDomainRigidity.chart_coe_apply _root_.OAI.CircleDomainRigidity.chart_infty_apply _root_.OAI.CircleDomainRigidity.extendAtInfinity_coe _root_.OAI.CircleDomainRigidity.extendAtInfinity_infty _root_.OAI.CircleDomainRigidity.sphereInv_infty _root_.OAI.CircleDomainRigidity.sphereInv_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Circle domains under the normalizing Möbius maps

Round complementary disks transform by multiplication of their defining
matrices. A homeomorphic Möbius map therefore preserves circle domains.
The explicit normalizer sends any prescribed sphere point to infinity.
-/

open Set Function
open scoped Topology OnePoint

noncomputable section

namespace CircleDomainRigidity

theorem isCircleDomain_image_mobius
    {U : Set Sphere} (hU : IsCircleDomain U) (M : Mobius) (e : Sphere ≃ₜ Sphere)
    (he : ∀ p, e p = M • p) : IsCircleDomain (e '' U) := by
  refine ⟨e.isOpenMap _ hU.1, hU.2.1.image e e.continuous.continuousOn, ?_⟩
  intro p hp
  have hpre : e.symm p ∈ Uᶜ := by
    intro hx
    exact hp ⟨e.symm p, hx, e.apply_symm_apply p⟩
  have hcomponent : e '' connectedComponentIn Uᶜ (e.symm p) =
      connectedComponentIn (e '' U)ᶜ p := by
    rw [e.image_connectedComponentIn hpre, e.image_compl, e.apply_symm_apply]
  rcases hU.2.2 (e.symm p) hpre with ⟨q, hq⟩ | hround
  · left
    refine ⟨e q, ?_⟩
    rw [← hcomponent, hq, image_singleton]
  · right
    rw [← hcomponent]
    have hefun : (e : Sphere → Sphere) = fun x => M • x := funext he
    simpa only [hefun] using isRoundClosedDisk_image_mobius hround M

theorem pointToInfinity_eq_smul (p q : Sphere) :
    pointToInfinity p q = pointToInfinityMobius p • q := by
  cases p using OnePoint.rec with
  | infty => simp [pointToInfinity, pointToInfinityMobius]
  | coe z =>
    change CannonMobius.inversion (affineSphere 1 (-z) one_ne_zero q) = _
    rw [inversion_eq_smul, affineSphere_eq_smul, ← mul_smul]
    rfl

theorem pointToInfinity_preserves_circleDomain (p : Sphere)
    {U : Set Sphere} (hU : IsCircleDomain U) :
    IsCircleDomain (pointToInfinity p '' U) :=
  isCircleDomain_image_mobius hU (pointToInfinityMobius p) (pointToInfinity p)
    (pointToInfinity_eq_smul p)

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Uniformization_MetricConformality
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions _root_.OAI.CircleDomainRigidity.finiteSphericalArea _root_.OAI.CircleDomainRigidity.sphereFirstCountableTopology
attribute [-simp] _root_.OAI.CircleDomainRigidity.CompactScalarModel.postcompose_coefficient _root_.OAI.CircleDomainRigidity.FiniteTransfer.coe_mem_sphericalCore _root_.OAI.CircleDomainRigidity.FiniteTransfer.coe_mem_sphericalDiskUnion _root_.OAI.CircleDomainRigidity.FiniteTransfer.infty_mem_cutoffCore _root_.OAI.CircleDomainRigidity.FiniteTransfer.infty_mem_sphericalCore _root_.OAI.CircleDomainRigidity.FiniteTransfer.infty_not_mem_sphericalDiskUnion _root_.OAI.CircleDomainRigidity.FiniteTransfer.realChartDomain_union _root_.OAI.CircleDomainRigidity.affineSphere_coe _root_.OAI.CircleDomainRigidity.affineSphere_infty _root_.OAI.CircleDomainRigidity.centeredJordanCoordinate_self _root_.OAI.CircleDomainRigidity.chartSymm_coe_apply _root_.OAI.CircleDomainRigidity.chart_coe_apply _root_.OAI.CircleDomainRigidity.chart_coe_self _root_.OAI.CircleDomainRigidity.chart_infty_apply _root_.OAI.CircleDomainRigidity.chart_infty_self _root_.OAI.CircleDomainRigidity.extendAtInfinity_coe _root_.OAI.CircleDomainRigidity.extendAtInfinity_infty _root_.OAI.CircleDomainRigidity.finiteCoord_coe _root_.OAI.CircleDomainRigidity.metricBeltramiCoefficient_scalar _root_.OAI.CircleDomainRigidity.sphereInv_infty _root_.OAI.CircleDomainRigidity.sphereInv_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Metric conformality in the concrete sphere charts

Metric conformality records the pullback Gram matrix and positive
orientation of the actual real differential. When the source metric is
a positive scalar multiple of the Euclidean metric, these equations
imply the complex Cauchy--Riemann equation and a nonzero derivative.
-/

open Set Filter
open scoped Topology OnePoint Matrix.Norms.Elementwise

noncomputable section

namespace CircleDomainRigidity

open FiniteTransfer

theorem complex_linear_of_positive_orthogonal_columns
    (A : ℂ →L[ℝ] ℂ) {q : ℝ} (hq : 0 < q)
    (hxx : (A 1).re ^ 2 + (A 1).im ^ 2 = q)
    (hyy : (A Complex.I).re ^ 2 + (A Complex.I).im ^ 2 = q)
    (hxy : (A 1).re * (A Complex.I).re + (A 1).im * (A Complex.I).im = 0)
    (hdet : 0 < (A 1).re * (A Complex.I).im - (A Complex.I).re * (A 1).im) :
    A Complex.I = Complex.I • A 1 ∧ A 1 ≠ 0 := by
  let a := (A 1).re
  let b := (A Complex.I).re
  let c := (A 1).im
  let d := (A Complex.I).im
  change a ^ 2 + c ^ 2 = q at hxx
  change b ^ 2 + d ^ 2 = q at hyy
  change a * b + c * d = 0 at hxy
  change 0 < a * d - b * c at hdet
  have hsquare : (a * d - b * c) ^ 2 = q ^ 2 := by
    calc
      _ = (a ^ 2 + c ^ 2) * (b ^ 2 + d ^ 2) - (a * b + c * d) ^ 2 := by ring
      _ = q ^ 2 := by rw [hxx, hyy, hxy]; ring
  have hdetq : a * d - b * c = q := (sq_eq_sq₀ hdet.le hq.le).mp hsquare
  have hsum : (a - d) ^ 2 + (b + c) ^ 2 = 0 := by nlinarith
  have had : a = d := by nlinarith [sq_nonneg (b + c)]
  have hbc : b = -c := by nlinarith [sq_nonneg (a - d)]
  constructor
  · apply Complex.ext
    · change b = (Complex.I * A 1).re
      simpa only [Complex.mul_re, Complex.I_re, Complex.I_im, zero_mul, one_mul, zero_sub] using hbc
    · change d = (Complex.I * A 1).im
      simpa only [Complex.mul_im, Complex.I_re, Complex.I_im, zero_mul, one_mul, zero_add] using had.symm
  · intro hzero
    have ha : a = 0 := congrArg Complex.re hzero
    have hc : c = 0 := congrArg Complex.im hzero
    nlinarith

theorem IsMetricConformalAt.isConformalAt
    {g : (ℝ × ℝ) → PlanarMetric} {f : Sphere → Sphere} {p : Sphere}
    (hf : IsMetricConformalAt g f p)
    (hscalar : ∃ c : ℝ, 0 < c ∧ sphereChartMetric g p = c • (1 : PlanarMetric)) :
    IsConformalAt f p := by
  obtain ⟨hc, hd, scale, hscale, hxx, hyy, hxy, hdet⟩ := hf
  obtain ⟨c, hpos, hmetric⟩ := hscalar
  rw [hmetric] at hxx hyy hxy
  norm_num [Matrix.smul_apply, Matrix.one_apply] at hxx hyy hxy
  obtain ⟨hCR, hnonzero⟩ := complex_linear_of_positive_orthogonal_columns
    (fderiv ℝ (sphereLocalMap f p) (chart p p)) (mul_pos hscale hpos) hxx hyy hxy hdet
  refine ⟨hc, fderiv ℝ (sphereLocalMap f p) (chart p p) 1, hnonzero, ?_⟩
  exact complexOfReal_hasDerivAt hd hCR

theorem metric_conformal_on_spherical_background
    {g : (ℝ × ℝ) → PlanarMetric} {f : Sphere → Sphere} {U : Set Sphere}
    (hf : ∀ p ∈ U, IsMetricConformalAt g f p)
    (hbackground : ∀ z : ℂ, (z : Sphere) ∈ U →
      g (Complex.equivRealProdCLM z) = sphericalMetricFactor (Complex.equivRealProdCLM z) • 1) :
    IsConformalOn f U := by
  intro p hp
  apply (hf p hp).isConformalAt
  cases p using OnePoint.rec with
  | infty =>
    refine ⟨4, by norm_num, ?_⟩
    rw [sphereChartMetric, ite_eq_left rfl]
  | coe z =>
    refine ⟨sphericalMetricFactor (Complex.equivRealProdCLM z), sphericalMetricFactor_pos _, ?_⟩
    simpa only [sphereChartMetric, OnePoint.coe_ne_infty, ite_false, if_false, finiteCoord, OnePoint.elim_some, id_eq] using hbackground z hp

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Sobolev_MetricComposition
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions _root_.OAI.CircleDomainRigidity.finiteSphericalArea _root_.OAI.CircleDomainRigidity.sphereFirstCountableTopology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Metric conformality after a holomorphic change of target

The actual chart differential is multiplied by the nonzero complex
derivative of the target map. Its Gram matrix is consequently multiplied
by the squared norm of that derivative, and its orientation stays positive.
-/

open Set Filter
open scoped Topology

noncomputable section

namespace CircleDomainRigidity

theorem complex_mul_column_norm (a z : ℂ) :
    (a * z).re ^ 2 + (a * z).im ^ 2 =
      (a.re ^ 2 + a.im ^ 2) * (z.re ^ 2 + z.im ^ 2) := by
  simp only [Complex.mul_re, Complex.mul_im]
  ring

theorem complex_mul_column_dot (a z w : ℂ) :
    (a * z).re * (a * w).re + (a * z).im * (a * w).im =
      (a.re ^ 2 + a.im ^ 2) * (z.re * w.re + z.im * w.im) := by
  simp only [Complex.mul_re, Complex.mul_im]
  ring

theorem complex_mul_column_det (a z w : ℂ) :
    (a * z).re * (a * w).im - (a * w).re * (a * z).im =
      (a.re ^ 2 + a.im ^ 2) * (z.re * w.im - w.re * z.im) := by
  simp only [Complex.mul_re, Complex.mul_im]
  ring

theorem IsMetricConformalAt.comp_conformal
    {g : (ℝ × ℝ) → FiniteTransfer.PlanarMetric} {f h : Sphere → Sphere} {p : Sphere}
    (hf : IsMetricConformalAt g f p) (hh : IsConformalAt h (f p)) :
    IsMetricConformalAt g (h ∘ f) p := by
  obtain ⟨hfc, hd, scale, hscale, hxx, hyy, hxy, hdet⟩ := hf
  obtain ⟨hhc, a, ha, hader⟩ := hh
  have hx : sphereLocalMap f p (chart p p) = chart (f p) (f p) := by
    simp only [sphereLocalMap, chartSymm_chart_self]
  have had : HasFDerivAt (sphereLocalMap h (f p))
      ((ContinuousLinearMap.smulRight (1 : ℂ →L[ℂ] ℂ) a).restrictScalars ℝ)
      (sphereLocalMap f p (chart p p)) := by
    rw [hx]
    exact hader.hasFDerivAt.restrictScalars ℝ
  have hcomp := had.comp (chart p p) hd.hasFDerivAt
  have hcont : Tendsto (fun z => f (chartSymm p z)) (𝓝 (chart p p)) (𝓝 (f p)) := by
    have hfc' : ContinuousAt f (chartSymm p (chart p p)) := by
      rw [chartSymm_chart_self]
      exact hfc
    have hc := hfc'.comp (continuous_chartSymm p).continuousAt
    simpa only [Function.comp_def, chartSymm_chart_self] using hc.tendsto
  have heq : sphereLocalMap (h ∘ f) p =ᶠ[𝓝 (chart p p)]
      (sphereLocalMap h (f p)) ∘ sphereLocalMap f p := by
    filter_upwards [hcont.eventually (eventually_chartSymm_chart (f p))] with z hz
    simp only [sphereLocalMap, Function.comp_apply]
    rw [hz]
  have hdcomp := hcomp.congr_of_eventuallyEq heq
  have hvalue (z : ℂ) : fderiv ℝ (sphereLocalMap (h ∘ f) p) (chart p p) z =
      a * fderiv ℝ (sphereLocalMap f p) (chart p p) z := by
    rw [hdcomp.fderiv]
    change fderiv ℝ (sphereLocalMap f p) (chart p p) z * a =
      a * fderiv ℝ (sphereLocalMap f p) (chart p p) z
    exact mul_comm _ _
  refine ⟨hhc.comp hfc, hdcomp.differentiableAt,
    (a.re ^ 2 + a.im ^ 2) * scale, mul_pos (complex_column_norm_pos ha) hscale, ?_, ?_, ?_, ?_⟩
  · simp only [hvalue, complex_mul_column_norm, hxx]
    ring
  · simp only [hvalue, complex_mul_column_norm, hyy]
    ring
  · simp only [hvalue, complex_mul_column_dot, hxy]
    ring
  · simp only [hvalue, complex_mul_column_det]
    exact mul_pos (complex_column_norm_pos ha) hdet

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Sobolev_SmoothSphereCharts
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions _root_.OAI.CircleDomainRigidity.finiteSphericalArea _root_.OAI.CircleDomainRigidity.sphereFirstCountableTopology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Smooth maps in the concrete sphere charts

This regularity predicate records ordinary real smoothness. For a
holomorphic sphere map it follows from complex analyticity in a
neighborhood; composition follows from the local chart inverse law.
-/

open Set Filter Function
open scoped Topology ContDiff

noncomputable section

namespace CircleDomainRigidity

theorem IsSmoothSphereAt.comp {f g : Sphere → Sphere} {p : Sphere}
    (hg : IsSmoothSphereAt g (f p)) (hf : IsSmoothSphereAt f p) :
    IsSmoothSphereAt (g ∘ f) p := by
  refine ⟨hg.1.comp hf.1, ?_⟩
  have hx : sphereLocalMap f p (chart p p) = chart (f p) (f p) := by
    simp only [sphereLocalMap, chartSymm_chart_self]
  have hd := (hx.symm ▸ hg.2).comp (chart p p) hf.2
  have hcont : Tendsto (fun z => f (chartSymm p z)) (𝓝 (chart p p)) (𝓝 (f p)) := by
    have hfc : ContinuousAt f (chartSymm p (chart p p)) := by
      rw [chartSymm_chart_self]
      exact hf.1
    simpa only [Function.comp_def, chartSymm_chart_self] using
      (hfc.comp (continuous_chartSymm p).continuousAt).tendsto
  apply hd.congr_of_eventuallyEq
  filter_upwards [hcont.eventually (eventually_chartSymm_chart (f p))] with z hz
  change chart (g (f p)) (g (f (chartSymm p z))) =
    chart (g (f p)) (g (chartSymm (f p) (chart (f p) (f (chartSymm p z)))))
  rw [hz]

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Sobolev_SmoothSphereEquivalence
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions _root_.OAI.CircleDomainRigidity.finiteSphericalArea _root_.OAI.CircleDomainRigidity.sphereFirstCountableTopology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Smooth equivalences on sphere regions

Both directions and their actual inverse identities are retained, so a
coordinate can be transported by composing with the constructed inverse.
-/

open Set Function

noncomputable section

namespace CircleDomainRigidity

theorem IsSmoothSphereEquivalence.trans
    {f fi g gi : Sphere → Sphere} {U V W : Set Sphere}
    (hf : IsSmoothSphereEquivalence f fi U V) (hg : IsSmoothSphereEquivalence g gi V W) :
    IsSmoothSphereEquivalence (g ∘ f) (fi ∘ gi) U W := by
  refine ⟨fun p hp => (hg.smooth _ (hf.mapsTo hp)).comp (hf.smooth p hp),
    hg.mapsTo.comp hf.mapsTo,
    fun p hp => (hf.smooth_inv _ (hg.mapsTo_inv hp)).comp (hg.smooth_inv p hp),
    hf.mapsTo_inv.comp hg.mapsTo_inv, ?_, ?_⟩
  · intro p hp
    simp only [Function.comp_apply, hg.left_inv _ (hf.mapsTo hp), hf.left_inv p hp]
  · intro p hp
    simp only [Function.comp_apply, hf.right_inv _ (hg.mapsTo_inv hp), hg.right_inv p hp]

theorem smoothSphereEquivalence_pointToInfinity (p : Sphere) (U : Set Sphere) :
    IsSmoothSphereEquivalence (pointToInfinity p) (pointToInfinity p).symm U
      (pointToInfinity p '' U) := by
  refine ⟨fun q _ => (show IsConformalOn (pointToInfinity p) univ from
    fun r _ => isConformalAt_pointToInfinity p r).isSmoothSphereAt isOpen_univ (mem_univ q),
    mapsTo_image _ _, fun q _ => ?_, ?_, fun q _ => (pointToInfinity p).symm_apply_apply q,
    fun q _ => (pointToInfinity p).apply_symm_apply q⟩
  · exact (show IsConformalOn (pointToInfinity p).symm univ from
      fun r _ => isConformalAt_pointToInfinity_symm p r).isSmoothSphereAt isOpen_univ (mem_univ q)
  · rintro _ ⟨q, hq, rfl⟩
    simpa only [(pointToInfinity p).symm_apply_apply] using hq

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Uniformization_SmoothMetricUniformization
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions _root_.OAI.CircleDomainRigidity.finiteSphericalArea _root_.OAI.CircleDomainRigidity.sphereFirstCountableTopology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Smooth finite metric circle models and their inverses

The smooth version of the same compact uniformization input records
that the uniformizing map is a diffeomorphism for the original smooth
structure. This is the smooth-isothermal-coordinate conclusion of
Jost, *Compact Riemann Surfaces*, third edition (2006), Theorem 3.11.1,
pp. 155--158, followed by Ahlfors, *Conformal Invariants* (1973),
Theorem 10-3, p. 142. Only a smooth metric on the sphere, standard near
infinity, is required. The weaker metric-only input follows immediately.
-/

open Set Filter Function
open scoped Topology ContDiff Matrix.Norms.Elementwise

noncomputable section

namespace CircleDomainRigidity

open FiniteTransfer

namespace FiniteTransfer

theorem smooth_finite_metric_circle_model
    (hcompact : SmoothCompactMetricSphereUniformization) (hfinite : FiniteJordanModelUniformization)
    {I : Type*} [Finite I] (T : I → ℂ ≃ₜ ℂ)
    (hdisj : Pairwise (Disjoint on fun i => closure (jordanInterior (T i))))
    {K : Set (ℝ × ℝ)} (hKQ : sphericalCore K ⊆ openCompletedRegion T)
    (g : (ℝ × ℝ) → PlanarMetric) (hg : ContDiff ℝ ∞ g) (hPD : ∀ z, (g z).PosDef)
    (hfar : ∃ R : ℝ, 0 < R ∧ ∀ z ∉ Metric.closedBall 0 R, g z = sphericalMetricFactor z • 1)
    (hcore : ∀ᶠ z in 𝓝ˢ K, g z = sphericalMetricFactor z • 1) :
    ∃ (V : Set Sphere) (f fi : Sphere → Sphere), IsCircleDomain V ∧
      IsSmoothSphereEquivalence f fi (openCompletedRegion T) V ∧
      IsConformalOn f (sphericalCore K) ∧
      (∀ p ∈ openCompletedRegion T, IsMetricConformalAt g f p) := by
  obtain ⟨e, he, hes, heis⟩ := hcompact g hg hPD hfar
  have hecore : IsConformalOn e (sphericalCore K) := by
    apply metric_conformal_on_spherical_background (fun p _ => he p)
    intro z hz
    exact hcore.self_of_nhdsSet _ ((coe_mem_sphericalCore K z).mp hz)
  obtain ⟨V, f, hV, _, hfcore, hfconf⟩ :=
    uniformize_finite_completion_of_jordan_models hfinite T hdisj e hKQ hecore
  obtain ⟨ki, hki⟩ := hfconf.exists_smooth_inverse
    (e.isOpenMap _ (isOpen_openCompletedRegion T)) hV.1
  have hequiv : IsSmoothSphereEquivalence e e.symm (openCompletedRegion T)
      (e '' openCompletedRegion T) := by
    refine ⟨fun p _ => hes p, mapsTo_image _ _, fun p _ => heis p, ?_,
      fun p _ => e.symm_apply_apply p, fun p _ => e.apply_symm_apply p⟩
    rintro _ ⟨p, hp, rfl⟩
    simpa only [e.symm_apply_apply] using hp
  have heq : (f ∘ e.symm) ∘ e = f := by
    funext p
    simp only [Function.comp_apply, e.symm_apply_apply]
  refine ⟨V, f, e.symm ∘ ki, hV, ?_, hfcore, ?_⟩
  · simpa only [heq] using hequiv.trans hki
  · intro p hp
    simpa only [heq] using (he p).comp_conformal (hfconf.1 _ ⟨p, hp, rfl⟩)

theorem smooth_finite_metric_circle_model_fixing_infty
    (hcompact : SmoothCompactMetricSphereUniformization) (hfinite : FiniteJordanModelUniformization)
    {I : Type*} [Finite I] (T : I → ℂ ≃ₜ ℂ)
    (hdisj : Pairwise (Disjoint on fun i => closure (jordanInterior (T i))))
    {K : Set (ℝ × ℝ)} (hKQ : sphericalCore K ⊆ openCompletedRegion T)
    (g : (ℝ × ℝ) → PlanarMetric) (hg : ContDiff ℝ ∞ g) (hPD : ∀ z, (g z).PosDef)
    (hfar : ∃ R : ℝ, 0 < R ∧ ∀ z ∉ Metric.closedBall 0 R, g z = sphericalMetricFactor z • 1)
    (hcore : ∀ᶠ z in 𝓝ˢ K, g z = sphericalMetricFactor z • 1) :
    ∃ (V : Set Sphere) (f fi : Sphere → Sphere), IsCircleDomain V ∧
      IsSmoothSphereEquivalence f fi (openCompletedRegion T) V ∧
      IsConformalOn f (sphericalCore K) ∧
      (∀ p ∈ openCompletedRegion T, IsMetricConformalAt g f p) ∧
      f OnePoint.infty = OnePoint.infty := by
  obtain ⟨V, f, fi, hV, hequiv, hfcore, hfmetric⟩ :=
    smooth_finite_metric_circle_model hcompact hfinite T hdisj hKQ g hg hPD hfar hcore
  let e := pointToInfinity (f OnePoint.infty)
  refine ⟨e '' V, e ∘ f, fi ∘ e.symm, pointToInfinity_preserves_circleDomain _ hV,
    hequiv.trans (smoothSphereEquivalence_pointToInfinity _ V), ?_, ?_, ?_⟩
  · exact (show IsConformalOn e univ from fun p _ =>
      isConformalAt_pointToInfinity _ p).comp hfcore (mapsTo_univ _ _)
  · intro p hp
    exact (hfmetric p hp).comp_conformal (isConformalAt_pointToInfinity _ _)
  · exact pointToInfinity_apply_self _

end FiniteTransfer
end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Uniformization_PrincipalFiniteModel
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonMobius.sphereMetric _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions _root_.OAI.CircleDomainRigidity.finiteSphericalArea _root_.OAI.CircleDomainRigidity.sphereFirstCountableTopology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Principally normalized finite metric circle models

The spherical metric near infinity supplies an actual open neighborhood
where the metric model is holomorphic. The affine normalization there
preserves the circle domain, the smooth inverse, and the retained core.
-/

open Set Filter Function
open scoped Topology ContDiff Matrix.Norms.Elementwise

noncomputable section

namespace CircleDomainRigidity

open FiniteTransfer

theorem conformal_neighborhood_of_infty
    {f : Sphere → Sphere} {U : Set Sphere} (hU : IsOpen U) (hinf : OnePoint.infty ∈ U)
    {g : (ℝ × ℝ) → PlanarMetric} (hf : ∀ p ∈ U, IsMetricConformalAt g f p)
    {R : ℝ} (hfar : ∀ z ∉ Metric.closedBall 0 R, g z = sphericalMetricFactor z • 1) :
    ∃ W : Set Sphere, IsOpen W ∧ OnePoint.infty ∈ W ∧ W ⊆ U ∧ IsConformalOn f W := by
  let C : Set ℂ := Complex.equivRealProdCLM.symm '' Metric.closedBall 0 R
  have hC : IsCompact C := (isCompact_closedBall (0 : ℝ × ℝ) R).image Complex.equivRealProdCLM.symm.continuous
  let W : Set Sphere := U \ ((↑) : ℂ → Sphere) '' C
  have hW : IsOpen W := hU.sdiff (hC.image OnePoint.continuous_coe).isClosed
  have hi : OnePoint.infty ∈ W := by
    refine ⟨hinf, ?_⟩
    rintro ⟨z, _, hz⟩
    exact OnePoint.coe_ne_infty z hz
  refine ⟨W, hW, hi, sdiff_subset, ?_⟩
  apply metric_conformal_on_spherical_background (fun p hp => hf p hp.1)
  intro z hz
  apply hfar
  intro hzball
  exact hz.2 ⟨z, ⟨Complex.equivRealProdCLM z, hzball,
    Complex.equivRealProdCLM.symm_apply_apply z⟩, rfl⟩

theorem smoothSphereEquivalence_affine (a b : ℂ) (ha : a ≠ 0) (U : Set Sphere) :
    IsSmoothSphereEquivalence (affineSphere a b ha) (affineSphere a b ha).symm U
      (affineSphere a b ha '' U) := by
  refine ⟨fun p _ => (show IsConformalOn (affineSphere a b ha) univ from
    fun q _ => isConformalAt_affineSphere a b ha q).isSmoothSphereAt isOpen_univ (mem_univ p),
    mapsTo_image _ _, fun p _ => ?_, ?_,
    fun p _ => (affineSphere a b ha).symm_apply_apply p,
    fun p _ => (affineSphere a b ha).apply_symm_apply p⟩
  · exact (show IsConformalOn (affineSphere a b ha).symm univ from
      fun q _ => isConformalAt_affineSphere_symm a b ha q).isSmoothSphereAt isOpen_univ (mem_univ p)
  · rintro _ ⟨p, hp, rfl⟩
    simpa only [(affineSphere a b ha).symm_apply_apply] using hp

namespace FiniteTransfer

theorem principal_finite_metric_circle_model
    (hcompact : SmoothCompactMetricSphereUniformization) (hfinite : FiniteJordanModelUniformization)
    {I : Type*} [Finite I] (T : I → ℂ ≃ₜ ℂ)
    (hdisj : Pairwise (Disjoint on fun i => closure (jordanInterior (T i))))
    {K : Set (ℝ × ℝ)} (hKQ : sphericalCore K ⊆ openCompletedRegion T)
    (g : (ℝ × ℝ) → PlanarMetric) (hg : ContDiff ℝ ∞ g) (hPD : ∀ z, (g z).PosDef)
    (hfar : ∃ R : ℝ, 0 < R ∧ ∀ z ∉ Metric.closedBall 0 R, g z = sphericalMetricFactor z • 1)
    (hcore : ∀ᶠ z in 𝓝ˢ K, g z = sphericalMetricFactor z • 1) :
    ∃ (V : Set Sphere) (f fi : Sphere → Sphere), IsCircleDomain V ∧
      IsSmoothSphereEquivalence f fi (openCompletedRegion T) V ∧
      IsConformalOn f (sphericalCore K) ∧
      (∀ p ∈ openCompletedRegion T, IsMetricConformalAt g f p) ∧ IsPrincipalNormalized f := by
  obtain ⟨V, f, fi, hV, heq, hc, hm, hfix⟩ :=
    smooth_finite_metric_circle_model_fixing_infty hcompact hfinite T hdisj hKQ g hg hPD hfar hcore
  obtain ⟨R, _, hR⟩ := hfar
  obtain ⟨W, hW, hiW, hWU, hfW⟩ := conformal_neighborhood_of_infty
    (isOpen_openCompletedRegion T) (hKQ (infty_mem_sphericalCore K)) hm hR
  obtain ⟨a, b, ha, hnorm⟩ := principal_normalize_at_infty hW hfW
    (heq.bijOn.injOn.mono hWU) hiW hfix
  let e := affineSphere a b ha
  refine ⟨e '' V, e ∘ f, fi ∘ e.symm,
    isCircleDomain_image_mobius hV (affineMobius a b ha) e (affineSphere_eq_smul a b ha),
    heq.trans (smoothSphereEquivalence_affine a b ha V), ?_, ?_, hnorm⟩
  · exact (show IsConformalOn e univ from fun p _ =>
      isConformalAt_affineSphere a b ha p).comp hc (mapsTo_univ _ _)
  · intro p hp
    exact (hm p hp).comp_conformal (isConformalAt_affineSphere a b ha _)

end FiniteTransfer
end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Topology_BoundaryGridAvoidance
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# From physical grid avoidance to inactive staircase branches

At reciprocal spacing every integer lattice level represents one of the
finite circle levels. Consequently the actual physical boundary avoidance
constructed by the contour theorem gives exactly the shifted-lattice
avoidance needed by the smooth filling theorem, including for local real
lifts of circle coordinates.
-/

open Set Function
open scoped Topology

noncomputable section

namespace CircleDomainRigidity.FiniteTransfer

theorem exists_reciprocal_level_of_mem_lattice
    {N : ℕ} {θ r : ℝ} (hr : r ∈ shiftedLattice (reciprocalGridStep N) θ) :
    ∃ j : Fin (N + 1), (r : UnitAddCircle) =
      ((θ + (j.val : ℝ) * reciprocalGridStep N : ℝ) : UnitAddCircle) := by
  obtain ⟨k, rfl⟩ := hr
  have hm0 : 0 ≤ k % (N + 1 : ℤ) := Int.emod_nonneg _ (by omega)
  have hmN : k % (N + 1 : ℤ) < N + 1 := Int.emod_lt_of_pos _ (by omega)
  let j : Fin (N + 1) := ⟨(k % (N + 1 : ℤ)).toNat, by omega⟩
  have hj : (j.val : ℤ) = k % (N + 1 : ℤ) := Int.toNat_of_nonneg hm0
  have hki : k = (j.val : ℤ) + (k / (N + 1 : ℤ)) * (N + 1 : ℤ) := by
    rw [hj]
    nlinarith [Int.emod_add_mul_ediv k (N + 1 : ℤ)]
  have hk : (k : ℝ) = (j.val : ℝ) + ((k / (N + 1 : ℤ) : ℤ) : ℝ) * ((N : ℝ) + 1) := by
    exact_mod_cast hki
  refine ⟨j, (addCircle_eq_iff_exists_int 1 _ _).mpr ⟨k / (N + 1 : ℤ), ?_⟩⟩
  calc
    θ + reciprocalGridStep N * (k : ℝ) = θ + (j.val : ℝ) * reciprocalGridStep N +
        ((k / (N + 1 : ℤ) : ℤ) : ℝ) * (reciprocalGridStep N * ((N : ℝ) + 1)) := by
      rw [hk]
      ring
    _ = _ := by rw [reciprocalGridStep_mul_denominator]

/-- A possible exception indexed in the natural numbers can be replaced
by one actual coordinate, even if the exception lies outside the list. -/
theorem exists_active_coordinate_of_single_exception
    {n : ℕ} (hn : 0 < n) (P : Fin n → Prop)
    (hP : ∃ k : ℕ, ∀ i : Fin n, i.val ≠ k → P i) :
    ∃ a : Fin n, ∀ i, i ≠ a → P i := by
  obtain ⟨k, hk⟩ := hP
  by_cases hkn : k < n
  · refine ⟨⟨k, hkn⟩, fun i hi => hk i ?_⟩
    exact fun heq => hi (Fin.ext heq)
  · exact ⟨⟨0, hn⟩, fun i _ => hk i (by omega)⟩

end CircleDomainRigidity.FiniteTransfer

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Rigidity_SubordinateMaskedBranches
attribute [-instance] _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A boundary lying in a common local branch neighborhood gives the
actual masked collar data. The finite graph condition then chooses one
active coordinate on each filling boundary. -/

open Set Function Filter Classical
open scoped Topology ContDiff

noncomputable section
namespace CircleDomainRigidity.FiniteTransfer

 theorem exists_subordinate_masked_branches
    {I : Type*} {n : ℕ} (L : Fin n → Type*)
    (G K : Set (ℝ × ℝ)) (hG : IsOpen G) (hK : IsClosed K)
    (M : Fin n → Set (ℝ × ℝ)) (f : Fin n → (ℝ × ℝ) → UnitAddCircle)
    (P : ∀ l, L l → Set (ℝ × ℝ))
    (v : ∀ l, L l → (ℝ × ℝ) → ℝ)
    (hv : ∀ l a, ContDiffOn ℝ ∞ (v l a) (G ∩ P l a))
    (hproj : ∀ l a x, x ∈ G ∩ P l a → (v l a x : UnitAddCircle) = f l x)
    (B Nbh : I → Set (ℝ × ℝ)) (hNbh : ∀ i, IsOpen (Nbh i))
    (hBN : ∀ i, B i ⊆ Nbh i)
    (hbranch : ∀ i l, Disjoint (Nbh i) (M l) ∨ ∃ a, Nbh i ⊆ interior (M l) ∩ P l a)
    (χ : (ℝ × ℝ) → ℝ)
    (hBG : ∀ i, B i ⊆ G) (hBK : ∀ i, Disjoint (B i) K)
    (hBχ : ∀ i, B i ⊆ interior {x | χ x = 1}) :
    ∃ (O : I → Set (ℝ × ℝ)) (present : I → Fin n → Prop)
      (u : I → Fin n → (ℝ × ℝ) → ℝ),
      (∀ i, IsOpen (O i) ∧ B i ⊆ O i ∧ O i ⊆ G ∧ Disjoint (O i) K ∧
        ∀ x ∈ O i, χ x = 1) ∧
      (∀ i l, ¬present i l → Disjoint (O i) (M l)) ∧
      (∀ i l, present i l → ContDiffOn ℝ ∞ (u i l) (O i)) ∧
      (∀ i l, present i l → ∀ x ∈ O i, (u i l x : UnitAddCircle) = f l x) ∧
      ∀ i l, present i l → O i ⊆ interior (M l) := by
  let present (i : I) (l : Fin n) : Prop := ¬Disjoint (Nbh i) (M l)
  have ha (i : I) (l : Fin n) (h : present i l) : ∃ a, Nbh i ⊆ interior (M l) ∩ P l a :=
    (hbranch i l).resolve_left h
  let u (i : I) (l : Fin n) : (ℝ × ℝ) → ℝ :=
    if h : present i l then v l (Classical.choose (ha i l h)) else fun _ => 0
  let O (i : I) := ((G ∩ Nbh i) ∩ interior {x | χ x = 1}) ∩ Kᶜ
  have hON (i : I) : O i ⊆ Nbh i := fun _ hx => hx.1.1.2
  refine ⟨O, present, u, ?_, ?_, ?_, ?_, ?_⟩
  · intro i
    refine ⟨((hG.inter (hNbh i)).inter isOpen_interior).inter hK.isOpen_compl,
      ?_, fun _ hx => hx.1.1.1, ?_, fun x hx => (show x ∈ {y | χ y = 1} from interior_subset hx.1.2)⟩
    · intro x hx
      exact ⟨⟨⟨hBG i hx, hBN i hx⟩, hBχ i hx⟩,
        fun hk => Set.disjoint_left.mp (hBK i) hx hk⟩
    · exact disjoint_compl_left.mono_left inter_subset_right
  · intro i l h
    exact (not_not.mp h).mono_left (hON i)
  · intro i l h
    simp only [u, dite_eq_left h]
    apply (hv l (Classical.choose (ha i l h))).mono
    intro x hx
    exact ⟨hx.1.1.1, (Classical.choose_spec (ha i l h) (hON i hx)).2⟩
  · intro i l h x hx
    simp only [u, dite_eq_left h]
    exact hproj l (Classical.choose (ha i l h)) x
      ⟨hx.1.1.1, (Classical.choose_spec (ha i l h) (hON i hx)).2⟩
  · intro i l h x hx
    exact (Classical.choose_spec (ha i l h) (hON i hx)).1

end CircleDomainRigidity.FiniteTransfer

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Topology_CircleTerminalBranches
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonEmbeddedArc.Arc.graphVertices_finite _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Actual terminal branches of the transferred circle maps

A real branch on a terminal collar remains a branch after cutoff and
filling. Its boundary oscillation therefore has the stated staircase
bound, even when the completed circle map has no global real lift.
-/

open Set Filter Function
open scoped Topology ContDiff

noncomputable section

namespace CircleDomainRigidity.FiniteTransfer

theorem IsFilledCircleFamily.eventuallyEq_near_set
    {I L : Type*} [Fintype I] [Fintype L] {D : I → Set (ℝ × ℝ)} {Ω A : Set (ℝ × ℝ)}
    {v F : L → (ℝ × ℝ) → UnitAddCircle} (hF : IsFilledCircleFamily D Ω v F)
    (hD : ∀ i, IsOpen (D i)) (hA : ∀ x ∈ A, ∀ i, x ∉ D i) :
    ∀ᶠ x in 𝓝ˢ A, ∀ l, F l x = v l x := by
  apply eventually_nhdsSet_iff_forall.mpr
  intro x hx
  exact eventually_all.mpr (fun l => hF.eventuallyEq_outside hD (hA x hx) l)

/-- Boundary diameter of the actual chosen real branch. -/
theorem staircase_branch_diameter_le
    {A : Set (ℝ × ℝ)} (u : (ℝ × ℝ) → ℝ) (P : ℝ → ℝ) {a h : ℝ}
    (hbound : 0 ≤ a + 4 * h)
    (hosc : ∀ x ∈ A, ∀ y ∈ A, |P (u x) - P (u y)| ≤ a + 4 * h) :
    Metric.diam ((fun x => P (u x)) '' A) ≤ a + 4 * h := by
  apply Metric.diam_le_of_forall_dist_le hbound
  rintro x ⟨p, hp, rfl⟩ y ⟨q, hq, rfl⟩
  simpa only [Real.dist_eq] using hosc p hp q hq

end CircleDomainRigidity.FiniteTransfer

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Rigidity_MaskedTerminalBranches
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Actual nonsingular terminal branches and their summed excess

Only the nonsingular terminal subfamily is used for each coordinate.
The real branches project to the filled circle maps on full collars,
and the original band bound gives the required square-sum estimate.
-/

open Set Filter Function
open scoped Topology ContDiff

noncomputable section

namespace CircleDomainRigidity.FiniteTransfer

theorem terminal_staircase_is_actual_masked_branch
    {J : Type*} [Fintype J] {n : ℕ}
    {D : J → Set (ℝ × ℝ)} (hD : ∀ j, IsOpen (D j))
    {Ω A O : Set (ℝ × ℝ)} (hO : IsOpen O) (hAO : A ⊆ O)
    (hA : ∀ x ∈ A, ∀ j, x ∉ D j)
    (M : Fin n → Set (ℝ × ℝ)) (f F : Fin n → (ℝ × ℝ) → UnitAddCircle)
    (χ u : (ℝ × ℝ) → ℝ) (l : Fin n)
    (hu : ContDiffOn ℝ ∞ u O) (hproj : ∀ x ∈ O, (u x : UnitAddCircle) = f l x)
    (hχone : ∀ x ∈ O, χ x = 1)
    (N : ℕ) {δ : ℝ} (hδ : 0 < δ) (hδh : δ < reciprocalGridStep N / 4) (θ : Fin n → ℝ)
    (hF : IsMaskedFilledCircleFamily D Ω M (circleCutoffFamily f χ N δ θ) F) :
    ContDiffOn ℝ ∞ (fun x => shiftedStaircase (reciprocalGridStep N) δ (θ l) (u x)) O ∧
      ∀ᶠ x in 𝓝ˢ A, (shiftedStaircase (reciprocalGridStep N) δ (θ l) (u x) : UnitAddCircle) = F l x := by
  have hP (r : ℝ) : shiftedStaircase (reciprocalGridStep N) δ (θ l) (r + 1) =
      shiftedStaircase (reciprocalGridStep N) δ (θ l) r + 1 := by
    simpa only [reciprocalGridStep, Nat.cast_succ] using
      shiftedStaircase_add_one (Nat.succ_pos N) δ (θ l) r
  refine ⟨(contDiff_shiftedStaircase (reciprocalGridStep_pos N) hδ hδh (θ l)).comp_contDiffOn hu, ?_⟩
  filter_upwards [hF.2.eventuallyEq_near_set hD hA, hO.mem_nhdsSet.mpr hAO] with x hx hxO
  have heq := circleCutoff_eq_lift (f l) χ hP (hproj x hxO)
  have hc := cutoffStaircase_of_one (u := u)
    (P := shiftedStaircase (reciprocalGridStep N) δ (θ l)) (hχone x hxO)
  exact (congrArg ((↑) : ℝ → UnitAddCircle) hc).symm.trans (heq.symm.trans (hx l).symm)

/-- Directly consume the uniform staircase oscillation supplied by the
physical terminal construction. The width may be selected afterwards. -/
theorem actual_masked_terminal_branches_of_staircase_bound
    {I J : Type*} [Fintype I] [Fintype J] {n : ℕ}
    {D : J → Set (ℝ × ℝ)} (hD : ∀ j, IsOpen (D j))
    {Ω : Set (ℝ × ℝ)} (A O : I → Set (ℝ × ℝ)) (hO : ∀ i, IsOpen (O i))
    (hAO : ∀ i, A i ⊆ O i) (hAD : ∀ i x, x ∈ A i → ∀ j, x ∉ D j)
    (M : Fin n → Set (ℝ × ℝ)) (f F : Fin n → (ℝ × ℝ) → UnitAddCircle)
    (χ : (ℝ × ℝ) → ℝ) (u : I → Fin n → (ℝ × ℝ) → ℝ)
    (S : Fin n → Finset I) (a : I → Fin n → ℝ)
    (hu : ∀ l i, i ∈ S l → ContDiffOn ℝ ∞ (u i l) (O i))
    (hproj : ∀ l i, i ∈ S l → ∀ x ∈ O i, (u i l x : UnitAddCircle) = f l x)
    (hχone : ∀ i x, x ∈ O i → χ x = 1)
    (N : ℕ) {δ η : ℝ} (hδ : 0 < δ) (hδh : δ < reciprocalGridStep N / 4) (θ : Fin n → ℝ)
    (hF : IsMaskedFilledCircleFamily D Ω M (circleCutoffFamily f χ N δ θ) F)
    (ha : ∀ l i, i ∈ S l → 0 ≤ a i l)
    (hbound : ∀ l i, i ∈ S l → ∀ x ∈ A i, ∀ y ∈ A i,
      |shiftedStaircase (reciprocalGridStep N) δ (θ l) (u i l x) -
        shiftedStaircase (reciprocalGridStep N) δ (θ l) (u i l y)| ≤
          a i l + 4 * reciprocalGridStep N)
    (hsmall : reciprocalGridStep N * Real.sqrt (Fintype.card I : ℝ) < η) :
    ∃ w : I → Fin n → (ℝ × ℝ) → ℝ,
      (∀ l i, i ∈ S l → ContDiffOn ℝ ∞ (w i l) (O i) ∧
        ∀ᶠ x in 𝓝ˢ (A i), (w i l x : UnitAddCircle) = F l x) ∧
      ∀ l, Real.sqrt (∑ i ∈ S l, max (Metric.diam (w i l '' A i) - a i l) 0 ^ 2) < 4 * η := by
  classical
  let w : I → Fin n → (ℝ × ℝ) → ℝ := fun i l x =>
    shiftedStaircase (reciprocalGridStep N) δ (θ l) (u i l x)
  refine ⟨w, ?_, ?_⟩
  · intro l i hi
    exact terminal_staircase_is_actual_masked_branch hD (hO i) (hAO i) (hAD i)
      M f F χ (u i l) l (hu l i hi) (hproj l i hi) (hχone i) N hδ hδh θ hF
  · intro l
    have hd (i : I) (hi : i ∈ S l) : Metric.diam (w i l '' A i) ≤ a i l + 4 * reciprocalGridStep N :=
      staircase_branch_diameter_le (u i l) (shiftedStaircase (reciprocalGridStep N) δ (θ l))
        (by positivity [ha l i hi, reciprocalGridStep_pos N]) (hbound l i hi)
    exact sqrt_sum_terminal_excess_sq_lt (S l) Finset.univ (Finset.subset_univ _)
      (fun i => Metric.diam (w i l '' A i)) (fun i => a i l)
      (le_of_lt (reciprocalGridStep_pos N)) hd
      (by simpa only [Finset.card_univ] using hsmall)

end CircleDomainRigidity.FiniteTransfer

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Rigidity_PhysicalMaskedBranches
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Nonsingular branches on the actual physical terminal boundaries

The disjointness of terminal and filling caps supplies the untouched
boundary condition. The uniform staircase bounds from the physical
terminal construction then give the actual filled branches and the
square-sum excess estimate on each nonsingular subfamily.
-/

open Set Filter Function
open scoped Topology ContDiff

noncomputable section

namespace CircleDomainRigidity.FiniteTransfer

theorem physical_masked_terminal_branches
    {I J : Type*} [Fintype I] [Fintype J] {n : ℕ}
    (T : I → ℂ ≃ₜ ℂ) (H : J → ℂ ≃ₜ ℂ)
    (hTH : ∀ i j, Disjoint (closure (jordanInterior (T i))) (closure (jordanInterior (H j))))
    {Ω : Set (ℝ × ℝ)} (O : I → Set (ℝ × ℝ)) (hO : ∀ i, IsOpen (O i))
    (hTO : ∀ i, frontier (realJordanInterior (T i)) ⊆ O i)
    (M : Fin n → Set (ℝ × ℝ)) (f F : Fin n → (ℝ × ℝ) → UnitAddCircle)
    (χ : (ℝ × ℝ) → ℝ) (u : I → Fin n → (ℝ × ℝ) → ℝ)
    (S : Fin n → Finset I) (a : I → Fin n → ℝ)
    (hu : ∀ l i, i ∈ S l → ContDiffOn ℝ ∞ (u i l) (O i))
    (hproj : ∀ l i, i ∈ S l → ∀ x ∈ O i, (u i l x : UnitAddCircle) = f l x)
    (hχone : ∀ i x, x ∈ O i → χ x = 1)
    (N : ℕ) {δ η : ℝ} (hδ : 0 < δ) (hδh : δ < reciprocalGridStep N / 4) (θ : Fin n → ℝ)
    (hF : IsMaskedFilledCircleFamily (fun j => realJordanInterior (H j)) Ω M
      (circleCutoffFamily f χ N δ θ) F)
    (ha : ∀ l i, i ∈ S l → 0 ≤ a i l)
    (hbound : ∀ l i, i ∈ S l → ∀ x ∈ frontier (jordanInterior (T i)),
      ∀ y ∈ frontier (jordanInterior (T i)),
      |shiftedStaircase (reciprocalGridStep N) δ (θ l) (u i l (Complex.equivRealProdCLM x)) -
        shiftedStaircase (reciprocalGridStep N) δ (θ l) (u i l (Complex.equivRealProdCLM y))| ≤
          a i l + 4 * reciprocalGridStep N)
    (hsmall : reciprocalGridStep N * Real.sqrt (Fintype.card I : ℝ) < η) :
    ∃ w : I → Fin n → (ℝ × ℝ) → ℝ,
      (∀ l i, i ∈ S l → ContDiffOn ℝ ∞ (w i l) (O i) ∧
        ∀ᶠ x in 𝓝ˢ (frontier (realJordanInterior (T i))), (w i l x : UnitAddCircle) = F l x) ∧
      ∀ l, Real.sqrt (∑ i ∈ S l,
        max (Metric.diam (w i l '' frontier (realJordanInterior (T i))) - a i l) 0 ^ 2) < 4 * η := by
  apply actual_masked_terminal_branches_of_staircase_bound
    (fun j => (realJordanInterior_geometry (H j)).1)
    (fun i => frontier (realJordanInterior (T i))) O hO hTO ?_
    M f F χ u S a hu hproj hχone N hδ hδh θ hF ha ?_ hsmall
  · intro i x hx j hj
    rw [frontier_realJordanInterior] at hx
    obtain ⟨z, hz, rfl⟩ := hx
    obtain ⟨y, hy, hyz⟩ := hj
    have heq : y = z := Complex.equivRealProdCLM.injective hyz
    exact Set.disjoint_left.mp (hTH i j) (frontier_subset_closure hz)
      (heq ▸ subset_closure hy)
  · intro l i hi x hx y hy
    rw [frontier_realJordanInterior] at hx hy
    obtain ⟨z, hz, rfl⟩ := hx
    obtain ⟨w, hw, rfl⟩ := hy
    exact hbound l i hi z hz w hw

end CircleDomainRigidity.FiniteTransfer

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Rigidity_MaskedModelTerminalBranches
attribute [-instance] _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The same filled model has actual staircase branches on every selected
nonsingular terminal inside its mask. Exterior constant replacements do
not change these branches or their original-band excess estimate. -/

open Set Function Filter
open scoped Topology ContDiff

noncomputable section
namespace CircleDomainRigidity.FiniteTransfer

 theorem MaskedModelData.terminal_branches
    {I J : Type*} [Fintype I] [Fintype J] {n N : ℕ}
    {T : I → ℂ ≃ₜ ℂ} {H : J → ℂ ≃ₜ ℂ}
    {G K : Set (ℝ × ℝ)} {M : Fin n → Set (ℝ × ℝ)}
    {f : Fin n → (ℝ × ℝ) → UnitAddCircle} {χ : (ℝ × ℝ) → ℝ}
    {θ : Fin n → ℝ} {ε : ℝ}
    (Q : MaskedModelData T H G K M f χ N θ ε)
    (hTH : ∀ i j, Disjoint (closure (jordanInterior (T i))) (closure (jordanInterior (H j))))
    (O : I → Set (ℝ × ℝ)) (hO : ∀ i, IsOpen (O i))
    (hTO : ∀ i, frontier (realJordanInterior (T i)) ⊆ O i)
    (u : I → Fin n → (ℝ × ℝ) → ℝ) (S : Fin n → Finset I) (a : I → Fin n → ℝ)
    (hu : ∀ l i, i ∈ S l → ContDiffOn ℝ ∞ (u i l) (O i))
    (hOM : ∀ l i, i ∈ S l → O i ⊆ M l)
    (hproj : ∀ l i, i ∈ S l → ∀ x ∈ O i, (u i l x : UnitAddCircle) = f l x)
    (hχone : ∀ i x, x ∈ O i → χ x = 1)
    (ha : ∀ l i, i ∈ S l → 0 ≤ a i l)
    (hbound : ∀ l i, i ∈ S l → ∀ x ∈ frontier (jordanInterior (T i)),
      ∀ y ∈ frontier (jordanInterior (T i)),
      |shiftedStaircase (reciprocalGridStep N)
          (staircaseWidth (reciprocalGridStep N) Q.widthIndex) (θ l)
          (u i l (Complex.equivRealProdCLM x)) -
        shiftedStaircase (reciprocalGridStep N)
          (staircaseWidth (reciprocalGridStep N) Q.widthIndex) (θ l)
          (u i l (Complex.equivRealProdCLM y))| ≤ a i l + 4 * reciprocalGridStep N)
    {η : ℝ} (hsmall : reciprocalGridStep N * Real.sqrt (Fintype.card I : ℝ) < η) :
    ∃ w : I → Fin n → (ℝ × ℝ) → ℝ,
      (∀ l i, i ∈ S l → ContDiffOn ℝ ∞ (w i l) (O i) ∧
        ∀ᶠ x in 𝓝ˢ (frontier (realJordanInterior (T i))), (w i l x : UnitAddCircle) = Q.functions l x) ∧
      ∀ l, Real.sqrt (∑ i ∈ S l,
        max (Metric.diam (w i l '' frontier (realJordanInterior (T i))) - a i l) 0 ^ 2) < 4 * η := by
  apply physical_masked_terminal_branches T H hTH O hO hTO M Q.base Q.functions χ u S a hu
    ?_ hχone N (staircaseWidth_pos (reciprocalGridStep_pos N) Q.widthIndex)
    (staircaseWidth_lt (reciprocalGridStep_pos N) Q.widthIndex) θ Q.filled ha hbound hsmall
  intro l i hi x hx
  exact (hproj l i hi x hx).trans ((Q.base_mask l).self_of_nhdsSet (hOM l i hi hx)).symm

end CircleDomainRigidity.FiniteTransfer

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Rigidity_MaskedTransferWithData
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonEmbeddedArc.Arc.graphVertices_finite _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Retain additional data attached to the actual filling at the chosen
width. The width and metric selection do not change the filled functions. -/

open Set Filter MeasureTheory Finset
open scoped Topology ContDiff Matrix.Norms.Elementwise
noncomputable section
namespace CircleDomainRigidity.FiniteTransfer

theorem exists_masked_circle_transfer_with_data
    {I : Type*} [Fintype I] {n : ℕ}
    (D : I → Set (ℝ × ℝ)) (hD : ∀ i, IsOpen (D i))
    {Ω Q G K : Set (ℝ × ℝ)} (hΩ : IsOpen Ω) (hQ : IsClosed Q)
    (hG : MeasurableSet G) (hK : IsClosed K) (hKc : IsCompact (closure Kᶜ))
    (htail : Q ∩ closure Kᶜ ⊆ Ω) (hKG : K ⊆ G)
    (hcover : Q ⊆ G ∪ ⋃ i, D i) (hKD : ∀ x ∈ K, ∀ i, x ∉ D i)
    (M : Fin n → Set (ℝ × ℝ)) (hM : ∀ i, IsClosed (M i))
    (hboundary : ∀ i, frontier (M i) ⊆ interior K)
    (v : ℝ → Fin n → (ℝ × ℝ) → UnitAddCircle)
    (u : Fin n → (ℝ × ℝ) → UnitAddCircle)
    (hu : ∀ i, MemLp (circleGradient (u i)) 2 (volume.restrict (G ∩ M i)))
    (hretain : ∀ δ, ∀ᶠ x in 𝓝ˢ K, ∀ i, v δ i x = u i x)
    {h : ℝ} (hh : 0 < h)
    (P : ℝ → (Fin n → (ℝ × ℝ) → UnitAddCircle) → Prop)
    (hfill : ∀ᶠ δ : ℝ in 𝓝[>] 0, ∃ F : Fin n → (ℝ × ℝ) → UnitAddCircle,
      IsMaskedFilledCircleFamily D Ω M (v δ) F ∧ P δ F)
    (hvi : ∀ k, IntegrableOn
      (fun z => 2 * maskedCircleWedges M (v (staircaseWidth h k)) z) (G \ K))
    {ε : ℝ} (hgood : ∃ᶠ k in atTop,
      (∫ z in G \ K, 2 * maskedCircleWedges M (v (staircaseWidth h k)) z) < ε)
    (k₀ : ℕ) :
    ∃ (k : ℕ) (F : Fin n → (ℝ × ℝ) → UnitAddCircle)
      (R : ℝ) (g : (ℝ × ℝ) → PlanarMetric),
      k₀ ≤ k ∧ IsMaskedFilledCircleFamily D Ω M (v (staircaseWidth h k)) F ∧
      (∀ᶠ z in 𝓝ˢ K, ∀ i, F i z = u i z) ∧
      0 < R ∧ ContDiff ℝ ∞ g ∧ (∀ z, (g z).PosDef) ∧
      (∀ᶠ z in 𝓝ˢ K, g z = sphericalMetricFactor z • 1) ∧
      (∀ z ∉ Metric.closedBall 0 R, g z = sphericalMetricFactor z • 1) ∧
      (∑ i : Fin n, ∫ z in (Q \ K) ∩ M i, fieldEnergy (circleGradient (F i)) g z) < ε ∧
      (∀ i : Fin n, ∀ E : Set (ℝ × ℝ), MeasurableSet E → E ⊆ K →
        (∫ z in (Q \ E) ∩ M i, fieldEnergy (circleGradient (F i)) g z) <
          (∫ z in (G \ E) ∩ M i, fieldEnergy (circleGradient (u i))
            (fun z => sphericalMetricFactor z • 1) z) + ε) ∧ P (staircaseWidth h k) F := by
  have hwidth : Tendsto (staircaseWidth h) atTop (𝓝[>] (0 : ℝ)) :=
    tendsto_nhdsWithin_iff.mpr ⟨staircaseWidth_tendsto_zero h,
      Filter.Eventually.of_forall (staircaseWidth_pos hh)⟩
  obtain ⟨k, hkcost, hlate, F, hF, hP⟩ :=
    (hgood.and_eventually ((eventually_ge_atTop k₀).and (hwidth.eventually hfill))).exists
  have hcore : ∀ᶠ z in 𝓝ˢ K, ∀ i, F i z = u i z := by
    apply eventually_nhdsSet_iff_forall.mpr
    intro z hz
    apply eventually_all.mpr
    intro i
    have hvu := (hretain (staircaseWidth h k)).filter_mono (nhds_le_nhdsSet hz)
    filter_upwards [hF.2.eventuallyEq_outside hD (hKD z hz) i, hvu] with x hx hxu
    exact hx.trans (hxu i)
  obtain ⟨R, g, hR, hg, hPD, hmetric, hfar, hsum⟩ :=
    hF.exists_spherical_metric_of_original_cost hD hΩ hQ hK hKc htail hG hM hboundary
      hcover (hvi k) hkcost
  refine ⟨k, F, R, g, hlate, hF, hcore, hR, hg, hPD, hmetric, hfar, hsum, ?_, hP⟩
  intro i E hE hEK
  have hsingle : (∫ z in (Q \ K) ∩ M i, fieldEnergy (circleGradient (F i)) g z) < ε := by
    apply lt_of_le_of_lt _ hsum
    exact single_le_sum
      (f := fun j : Fin n => ∫ z in (Q \ K) ∩ M j, fieldEnergy (circleGradient (F j)) g z)
      (fun j _ => integral_nonneg fun z => covectorEnergy_nonneg _ (hPD z)) (mem_univ i)
  exact localized_masked_circle_energy_lt hΩ hQ hG hK hKc htail hKG (hM i) (hboundary i)
    (hF.1 i) (hu i) (hcore.mono fun _ hz => hz i) hg.continuous hPD hmetric hsingle hE hEK

end CircleDomainRigidity.FiniteTransfer

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Rigidity_PreparedMaskAtlasGeometry
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions _root_.OAI.CircleDomainRigidity.finiteSphericalArea _root_.OAI.CircleDomainRigidity.sphereFirstCountableTopology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Select one regular core, cutoff and reciprocal grid for the actual
finite masked list, then construct its terminal and subordinate filling
caps using that very grid. All cost and terminal estimates retain these
same choices. -/

open Set Function Filter MeasureTheory
open scoped Topology Manifold ContDiff

noncomputable section
namespace CircleDomainRigidity.FiniteTransfer

attribute [local instance] sphereMetric

 theorem exists_prepared_mask_atlas_geometry
    (hsard : SmoothPlanarSard) (hsch : PlanarSchoenflies)
    (G : Set Sphere) (hG : IsOpen G) (π : Sphere → Sphere)
    (hπ : Continuous π) (hclosed : IsClosedMap π) (hsurj : Surjective π)
    (hr : ∀ x y, π x = π y ↔
      x = y ∨ (x ∈ Gᶜ ∧ y ∈ connectedComponentIn Gᶜ x))
    (hTD : IsTotallyDisconnected (π '' Gᶜ))
    (hinfty : OnePoint.infty ∈ G)
    {K₀ : Set (ℝ × ℝ)} (hK₀ : IsClosed K₀) (hK₀G : K₀ ⊆ realChartDomain G)
    {n : ℕ} {S : Type*} [Countable S]
    (R : Fin n → Set (Sphere × UnitAddCircle)) (hR : ∀ l, IsClosed (R l))
    (σ : S → Sphere) (hσ : Injective σ) (hσB : ∀ s, σ s ∈ π '' Gᶜ)
    (a b : Fin n → S → ℝ) (Flag : Set S) (hFlag : Flag.Finite)
    (hwidth : ∀ l s, 0 ≤ b l s - a l s)
    (hwidth2 : ∀ l, Summable (fun s => (b l s - a l s) ^ 2))
    (hband : ∀ l s, {t : UnitAddCircle | (σ s, t) ∈ R l} ⊆
      ((↑) : ℝ → UnitAddCircle) '' Icc (a l s) (b l s))
    (Mm : Fin n → Set (ℝ × ℝ)) (hMm : ∀ l, MeasurableSet (Mm l))
    (hMmB : ∀ l, frontier (Mm l) ⊆ realChartDomain G)
    (f : Fin n → (ℝ × ℝ) → UnitAddCircle)
    (hf : ∀ l, SmoothCircleOn (f l) (realChartDomain G ∩ interior (Mm l)))
    (hmf : ∀ l, Measurable (f l)) (hdf : ∀ l, Measurable (circleGradient (f l)))
    (hf2 : ∀ l, MemLp (circleGradient (f l)) 2 ((volume.restrict (realChartDomain G)).restrict (Mm l)))
    (O : S → Set Sphere) (hO : ∀ s, O s ∈ 𝓝 (σ s))
    (U : S → Set Sphere) (v : S → Fin n → Sphere → ℝ) (M : S → Fin n → ℝ)
    (hbounded : ∀ s l x, x ∈ U s → |v s l x| ≤ M s l)
    (hphysical : ∀ s (z : ℂ), (z : Sphere) ∈ G → π (z : Sphere) ∈ O s →
      π (z : Sphere) ∈ U s)
    (active : S → Fin n → Prop)
    (hbudget : ∀ s l, active s l →
      limsup (v s l) (𝓝[U s] (σ s)) - liminf (v s l) (𝓝[U s] (σ s)) ≤ b l s - a l s)
    (hfree : ∀ x ∈ π '' Gᶜ, x ∉ range σ → ∀ l,
      {t : UnitAddCircle | (x, t) ∈ R l}.Subsingleton)
    (hcompat : ∀ (j : Fin n) (d : ℕ) (labels : Fin d → Fin n),
      (∀ i, (labels i).val < j.val) →
      (volume.prod (Measure.pi (fun _ : Fin d => (volume : Measure UnitAddCircle))))
        (freeComponentFailure ((π '' Gᶜ) \ range σ) (R j) R labels) = 0)
    (L : Fin n → Type*) (Mask : Fin n → Set Sphere) (hMask : ∀ l, IsClosed (Mask l))
    (hboundary : ∀ l, frontier (Mask l) ⊆ (π '' Gᶜ)ᶜ)
    (singular : Fin n → S) (hflag : ∀ l, singular l ∈ Flag)
    (P : ∀ l, L l → Set Sphere) (hP : ∀ l i, IsOpen (P l i))
    (hcover : ∀ l, Mask l \ {σ (singular l)} ⊆ ⋃ i, P l i)
    {η ρ : ℝ} (hη : 0 < η) (hρ : 0 < ρ) :
    ∃ (K : Set (ℝ × ℝ)) (χ : (ℝ × ℝ) → ℝ) (N : ℕ) (θ : Fin n → ℝ),
      IsClosed K ∧ K₀ ⊆ interior K ∧ K ⊆ realChartDomain G ∧ IsCompact (closure Kᶜ) ∧
      (∀ l, frontier (Mm l) ⊆ interior K) ∧
      ContDiff ℝ ∞ χ ∧ (∀ᶠ z in 𝓝ˢ K, χ z = 0) ∧
      (∀ᶠ z in 𝓝ˢ (realChartDomain G)ᶜ, χ z = 1) ∧ reciprocalGridStep N < ρ ∧
      (gridTerminalIndices Flag (reciprocalGridStep N) upperPair a b θ).Finite ∧
      reciprocalGridStep N *
        Real.sqrt ((gridTerminalIndices Flag (reciprocalGridStep N) upperPair a b θ).ncard : ℝ) < η ∧
      (∀ k, IntegrableOn (maskedCircleWedges Mm (circleCutoffFamily f χ N
        (staircaseWidth (reciprocalGridStep N) k) θ)) (realChartDomain G \ K)) ∧
      (∃ᶠ k in atTop, (∫ z in realChartDomain G \ K, maskedCircleWedges Mm
        (circleCutoffFamily f χ N (staircaseWidth (reciprocalGridStep N) k) θ) z) < η) ∧
    ∃ (D : PhysicalTerminalDisks G π (π '' Gᶜ)
        (fun s : gridTerminalIndices Flag (reciprocalGridStep N) upperPair a b θ => σ s)
        (fun s => O s))
      (m : ℕ) (H : Fin m → ℂ ≃ₜ ℂ) (γ : Fin m → Circle → ℂ),
      (∀ s, Disjoint (closedTerminalCap (D.H s)) (cutoffCore χ)) ∧
      cutoffCore χ ⊆ openCompletedRegion D.H ∧
      (∀ (s : gridTerminalIndices Flag (reciprocalGridStep N) upperPair a b θ) l,
        active s l → ∀ δ η : ℝ,
        ∀ x ∈ frontier (jordanInterior (D.H s)),
        ∀ y ∈ frontier (jordanInterior (D.H s)),
        |shiftedStaircase (reciprocalGridStep N) δ η (v s l (π (x : Sphere))) -
          shiftedStaircase (reciprocalGridStep N) δ η (v s l (π (y : Sphere)))| ≤
            (b l s - a l s) + 4 * reciprocalGridStep N) ∧
      Pairwise (Disjoint on fun j => closure (jordanInterior (H j))) ∧
      (∀ s j, Disjoint (closure (jordanInterior (D.H s))) (closure (jordanInterior (H j)))) ∧
      (∀ j, Disjoint (closedTerminalCap (H j)) (cutoffCore χ)) ∧
      π ⁻¹' (π '' Gᶜ) ⊆ sphericalDiskUnion D.H ∪ sphericalDiskUnion H ∧
      cutoffCore χ ⊆ completionCore D.H H ∧ completionCore D.H H ⊆ G ∧
      (∀ j, ContMDiff (𝓡 1) (𝓘(ℝ, ℂ)) ∞ (γ j) ∧ Topology.IsEmbedding (γ j) ∧
        frontier (jordanInterior (H j)) = range (γ j) ∧
        (∀ z ∈ frontier (jordanInterior (H j)), (z : Sphere) ∈ G ∧ π (z : Sphere) ∉ π '' Gᶜ) ∧
        (∃ k : ℕ, ∀ l : Fin n, l.val ≠ k →
          Disjoint (frontier (jordanInterior (H j)))
            ((fun z : ℂ => π (z : Sphere)) ⁻¹' (⋃ r, reciprocalGraphLevel (R l) (θ l) N r))) ∧
        ∀ l, Disjoint (closure (jordanInterior (H j)))
          ((fun z : ℂ => π (z : Sphere)) ⁻¹' Mask l) ∨
          ∃ i, closure (jordanInterior (H j)) ⊆
            (fun z : ℂ => π (z : Sphere)) ⁻¹' (interior (Mask l) ∩ P l i)) := by
  let Pgrid (N : ℕ) (θ : Fin n → ℝ) : Prop :=
    OrderedGraphGridCompatibility R θ N (π '' Gᶜ) σ
  obtain ⟨ψ, t, K, χ, N, θ, _, _, _, _, _, hK, hK₀K, hKG, hKc, hbd,
      hχ, _, _, hχzero, hχone, hN, hPgrid, hfin, hcard, hvi, hgood⟩ :=
    exists_regular_masked_core_cutoff_and_grid hsard (isOpen_realChartDomain hG)
      (isCompact_compl_realChartDomain hG hinfty) hK₀ hK₀G Mm hMm hMmB f hf hmf hdf hf2
      Flag hFlag a b hwidth hwidth2 Pgrid
      (fun N => ae_ordered_graph_grid_compatibility R (π '' Gᶜ) σ hcompat N) hη hρ
  obtain ⟨D, m, H, γ, hD, hCQ, hosc, hHd, hDH, hHC, hcov, hCC, hCG', hcurves⟩ :=
    exists_mask_atlas_geometric_assembly hsard hsch G hG π hπ hclosed hsurj hr hTD
      (cutoffCore χ) (isCompact_cutoffCore χ) (cutoffCore_subset_domain hinfty χ hχone)
      (infty_mem_cutoffCore χ) R hR σ hσ hσB a b θ Flag hband hfin O hO U v M
      hbounded hphysical active hbudget hfree hPgrid L Mask hMask hboundary singular hflag P hP hcover
  exact ⟨K, χ, N, θ, hK, hK₀K, hKG, hKc, hbd, hχ, hχzero, hχone, hN, hfin, hcard,
    hvi, hgood, D, m, H, γ, hD, hCQ, hosc, hHd, hDH, hHC, hcov, hCC, hCG', hcurves⟩

end CircleDomainRigidity.FiniteTransfer

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Rigidity_RealCapMaskNeighborhoods
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonEmbeddedArc.Arc.graphVertices_finite _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions _root_.OAI.CircleDomainRigidity.finiteSphericalArea _root_.OAI.CircleDomainRigidity.sphereFirstCountableTopology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Convert the subordinate physical cap certificates into the open
real-plane mask/branch neighborhoods consumed by finite transfer. -/

open Set Function
open scoped Topology

noncomputable section
namespace CircleDomainRigidity.FiniteTransfer

 theorem closure_realJordanInterior (H : ℂ ≃ₜ ℂ) :
    closure (realJordanInterior H) = Complex.equivRealProdCLM '' closure (jordanInterior H) :=
  (Complex.equivRealProdCLM.toHomeomorph.image_closure _).symm

 theorem exists_real_cap_mask_neighborhoods
    {I : Type*} {n : ℕ} (H : I → ℂ ≃ₜ ℂ)
    (q : ℂ → Sphere) (hq : Continuous q)
    (L : Fin n → Type*) (M : Fin n → Set Sphere) (hM : ∀ l, IsClosed (M l))
    (P : ∀ l, L l → Set Sphere) (hP : ∀ l a, IsOpen (P l a))
    (hcap : ∀ i l, Disjoint (closure (jordanInterior (H i))) (q ⁻¹' M l) ∨
      ∃ a, closure (jordanInterior (H i)) ⊆ q ⁻¹' (interior (M l) ∩ P l a)) :
    ∃ N : I → Set (ℝ × ℝ),
      (∀ i, IsOpen (N i) ∧ frontier (realJordanInterior (H i)) ⊆ N i) ∧
      ∀ i l, Disjoint (N i) ((q ∘ Complex.equivRealProdCLM.symm) ⁻¹' M l) ∨
        ∃ a, N i ⊆ interior ((q ∘ Complex.equivRealProdCLM.symm) ⁻¹' M l) ∩
          ((q ∘ Complex.equivRealProdCLM.symm) ⁻¹' P l a) := by
  have hqr : Continuous (q ∘ Complex.equivRealProdCLM.symm) :=
    hq.comp Complex.equivRealProdCLM.symm.continuous
  have hlocal (i : I) : ∃ N : Set (ℝ × ℝ), IsOpen N ∧
      closure (realJordanInterior (H i)) ⊆ N ∧
      ∀ l, Disjoint N ((q ∘ Complex.equivRealProdCLM.symm) ⁻¹' M l) ∨
        ∃ a, N ⊆ interior ((q ∘ Complex.equivRealProdCLM.symm) ⁻¹' M l) ∩
          ((q ∘ Complex.equivRealProdCLM.symm) ⁻¹' P l a) := by
    apply exists_common_mask_branch_neighborhood_of_subset L _ _
      (fun l => (hM l).preimage hqr) _ (fun l a => (hP l a).preimage hqr)
    intro l
    rcases hcap i l with hd | ⟨a, ha⟩
    · left
      apply Set.disjoint_left.mpr
      intro p hp hm
      rw [closure_realJordanInterior] at hp
      obtain ⟨z, hz, rfl⟩ := hp
      exact Set.disjoint_left.mp hd hz (by simpa only [mem_preimage, Function.comp_apply,
        ContinuousLinearEquiv.symm_apply_apply] using hm)
    · right
      refine ⟨a, ?_⟩
      intro p hp
      rw [closure_realJordanInterior] at hp
      obtain ⟨z, hz, rfl⟩ := hp
      have hm := ha hz
      refine ⟨preimage_interior_subset_interior_preimage hqr ?_, ?_⟩
      · simpa only [mem_preimage, Function.comp_apply, ContinuousLinearEquiv.symm_apply_apply] using hm.1
      · simpa only [mem_preimage, Function.comp_apply, ContinuousLinearEquiv.symm_apply_apply] using hm.2
  choose N hN hCN hchoice using hlocal
  exact ⟨N, fun i => ⟨hN i, frontier_subset_closure.trans (hCN i)⟩, hchoice⟩

end CircleDomainRigidity.FiniteTransfer

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Selection_CountableMarks
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Finite mandatory mark sets that eventually contain every mark. -/

open Set Function Filter

namespace CircleDomainRigidity

theorem exists_increasing_finite_marks (S : Type*) [Countable S] :
    ∃ F : ℕ → Set S, (∀ n, (F n).Finite) ∧ Monotone F ∧
      ∀ s, ∀ᶠ n in atTop, s ∈ F n := by
  obtain ⟨e, he⟩ := exists_injective_nat S
  refine ⟨fun n => {s | e s < n + 1}, ?_, ?_, ?_⟩
  · intro n
    exact (Set.finite_lt_nat (n + 1)).preimage he.injOn
  · intro n m hnm s hs
    dsimp only [mem_ofPred_eq] at hs ⊢
    omega
  · intro s
    filter_upwards [eventually_ge_atTop (e s)] with n hn
    omega

end CircleDomainRigidity

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Topology_OrderedCoordinateExhaustion
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Finite coordinate lists keep their given order. A prescribed real
subfamily is retained through an explicit injection into every sufficiently
large list, even when the full countable order has type greater than omega. -/

open Set Function Filter
noncomputable section
namespace CircleDomainRigidity.FiniteTransfer

theorem exists_ordered_coordinate_exhaustion
    {C : Type*} [LinearOrder C] [Countable C] (real : ℕ → C) (hinj : Injective real) :
    ∃ (size : ℕ → ℕ) (label : ∀ n, Fin (size n) ↪o C)
      (slot : ∀ n, Fin (n + 1) → Fin (size n)),
      (∀ n, 0 < size n) ∧
      (∀ n, Injective (slot n)) ∧
      (∀ n j, label n (slot n j) = real j) ∧
      Monotone (fun n => range (label n)) ∧
      ∀ c, ∀ᶠ n in atTop, c ∈ range (label n) := by
  classical
  obtain ⟨F, hF, hmono, hcover⟩ := exists_increasing_finite_marks C
  let L (n : ℕ) : Finset C := (hF n).toFinset ∪ (Finset.range (n + 1)).image real
  let label (n : ℕ) : Fin (L n).card ↪o C := (L n).orderEmbOfFin rfl
  have hmem (n : ℕ) (j : Fin (n + 1)) : real j ∈ L n := by
    exact Finset.mem_union_right _ (Finset.mem_image.mpr ⟨j, Finset.mem_range.mpr j.isLt, rfl⟩)
  let slot (n : ℕ) (j : Fin (n + 1)) : Fin (L n).card :=
    ((L n).orderIsoOfFin rfl).symm ⟨real j, hmem n j⟩
  have hslot (n : ℕ) (j : Fin (n + 1)) : label n (slot n j) = real j :=
    congrArg Subtype.val (((L n).orderIsoOfFin rfl).apply_symm_apply ⟨real j, hmem n j⟩)
  have hrange (n : ℕ) : range (label n) = (L n : Set C) := (L n).range_orderEmbOfFin rfl
  refine ⟨fun n => (L n).card, label, slot, ?_, ?_, hslot, ?_, ?_⟩
  · intro n
    exact Finset.card_pos.mpr ⟨real 0, hmem n ⟨0, Nat.succ_pos n⟩⟩
  · intro n i j hij
    apply Fin.ext
    apply hinj
    exact (hslot n i).symm.trans ((congrArg (label n) hij).trans (hslot n j))
  · intro n m hnm
    change range (label n) ⊆ range (label m)
    rw [hrange, hrange]
    intro c hc
    rcases Finset.mem_union.mp hc with hc | hc
    · exact Finset.mem_union_left _ ((hF m).mem_toFinset.mpr
        (hmono hnm ((hF n).mem_toFinset.mp hc)))
    · obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hc
      exact Finset.mem_union_right _ (Finset.mem_image.mpr
        ⟨j, Finset.mem_range.mpr (lt_of_lt_of_le (Finset.mem_range.mp hj) (Nat.add_le_add_right hnm 1)), rfl⟩)
  · intro c
    filter_upwards [hcover c] with n hn
    rw [hrange]
    exact Finset.mem_union_left _ ((hF n).mem_toFinset.mpr hn)

end CircleDomainRigidity.FiniteTransfer

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Topology_MarkedBranchNeighborhoods
attribute [-instance] _root_.OAI.CannonEmbeddedArc.Arc.graphVertices_finite _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions _root_.OAI.CircleDomainRigidity.finiteSphericalArea _root_.OAI.CircleDomainRigidity.sphereFirstCountableTopology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Common neighborhoods of marked points retain the very branches used
to define their band endpoints. The local limiting oscillation is then
exactly the selected width, including after intersecting all patches. -/

open Set Function Filter Classical
open scoped Topology

noncomputable section
namespace CircleDomainRigidity

 theorem exists_marked_branch_neighborhoods
    {n : ℕ} {S : Type*} (L : Fin n → Type*)
    (U : Set Sphere) (M : Fin n → Set Sphere) (hM : ∀ l, IsClosed (M l))
    (hboundary : ∀ l, frontier (M l) ⊆ U)
    (σ : S → Sphere) (hσ : ∀ s, σ s ∉ U) (singular : Fin n → Sphere)
    (P : ∀ l, L l → Set Sphere) (hP : ∀ l i, IsOpen (P l i))
    (v : ∀ l, L l → Sphere → ℝ) (B : ∀ l, L l → ℝ)
    (hbound : ∀ l i x, |v l i x| ≤ B l i)
    (a b : Fin n → S → ℝ)
    (hband : ∀ s l, σ s ∈ M l → σ s ≠ singular l → ∃ i : L l,
      σ s ∈ P l i ∧ a l s = liminf (v l i) (𝓝[U] (σ s)) ∧
        b l s = limsup (v l i) (𝓝[U] (σ s))) :
    ∃ (N : S → Set Sphere) (u : S → Fin n → Sphere → ℝ) (C : S → Fin n → ℝ),
      (∀ s, IsOpen (N s) ∧ σ s ∈ N s) ∧
      (∀ s l, σ s ∈ M l → N s ⊆ interior (M l)) ∧
      (∀ s l, σ s ∉ M l → Disjoint (N s) (M l)) ∧
      (∀ s l x, |u s l x| ≤ C s l) ∧
      (∀ s l, σ s ∈ M l → σ s ≠ singular l → ∃ i : L l,
        N s ⊆ P l i ∧ u s l = v l i) ∧
      ∀ s l, σ s ∈ M l → σ s ≠ singular l →
        limsup (u s l) (𝓝[U ∩ N s] (σ s)) -
          liminf (u s l) (𝓝[U ∩ N s] (σ s)) = b l s - a l s := by
  let A (s : S) (l : Fin n) : Prop := σ s ∈ M l ∧ σ s ≠ singular l
  let idx (s : S) (l : Fin n) (h : A s l) : L l := Classical.choose (hband s l h.1 h.2)
  have hi (s : S) (l : Fin n) (h : A s l) :
      σ s ∈ P l (idx s l h) ∧ a l s = liminf (v l (idx s l h)) (𝓝[U] (σ s)) ∧
        b l s = limsup (v l (idx s l h)) (𝓝[U] (σ s)) := Classical.choose_spec (hband s l h.1 h.2)
  let V (s : S) (l : Fin n) : Set Sphere :=
    if h : A s l then interior (M l) ∩ P l (idx s l h)
    else if σ s ∈ M l then interior (M l) else (M l)ᶜ
  let N (s : S) : Set Sphere := ⋂ l, V s l
  let u (s : S) (l : Fin n) : Sphere → ℝ :=
    if h : A s l then v l (idx s l h) else fun _ => 0
  let C (s : S) (l : Fin n) : ℝ := if h : A s l then B l (idx s l h) else 0
  have hint (s : S) (l : Fin n) (hs : σ s ∈ M l) : σ s ∈ interior (M l) :=
    (mem_interior_iff_notMem_frontier hs).mpr (fun hb => hσ s (hboundary l hb))
  have hV (s : S) (l : Fin n) : IsOpen (V s l) ∧ σ s ∈ V s l := by
    by_cases h : A s l
    · simp only [V, dite_eq_left h]
      exact ⟨isOpen_interior.inter (hP l _), hint s l h.1, (hi s l h).1⟩
    · simp only [V, dite_eq_right h]
      by_cases hm : σ s ∈ M l
      · simp only [ite_eq_left hm]
        exact ⟨isOpen_interior, hint s l hm⟩
      · simp only [ite_eq_right hm]
        exact ⟨(hM l).isOpen_compl, hm⟩
  have hN (s : S) : IsOpen (N s) ∧ σ s ∈ N s :=
    ⟨isOpen_iInter_of_finite (fun l => (hV s l).1), mem_iInter.mpr (fun l => (hV s l).2)⟩
  have hsub (s : S) (l : Fin n) : N s ⊆ V s l := iInter_subset (V s) l
  refine ⟨N, u, C, hN, ?_, ?_, ?_, ?_, ?_⟩
  · intro s l hm x hx
    have hxV := hsub s l hx
    by_cases h : A s l
    · have hx' : x ∈ interior (M l) ∩ P l (idx s l h) := by
        simpa only [V, dite_eq_left h] using hxV
      exact hx'.1
    · simpa only [V, dite_eq_right h, ite_eq_left hm] using hxV
  · intro s l hm
    have ha : ¬A s l := fun h => hm h.1
    have hs : N s ⊆ (M l)ᶜ := by
      simpa only [V, dite_eq_right ha, ite_eq_right hm] using hsub s l
    exact Set.disjoint_left.mpr (fun _ hx hxm => hs hx hxm)
  · intro s l x
    by_cases h : A s l
    · simpa only [u, C, dite_eq_left h] using hbound l (idx s l h) x
    · simp only [u, C, dite_eq_right h, abs_zero, le_refl]
  · intro s l hm hb
    let h : A s l := ⟨hm, hb⟩
    refine ⟨idx s l h, ?_, by simp only [u, dite_eq_left h]⟩
    intro x hx
    have hxV : x ∈ interior (M l) ∩ P l (idx s l h) := by
      simpa only [V, dite_eq_left h] using hsub s l hx
    exact hxV.2
  · intro s l hm hb
    let h : A s l := ⟨hm, hb⟩
    have hn : 𝓝[U ∩ N s] (σ s) = 𝓝[U] (σ s) :=
      nhdsWithin_inter_of_mem' (nhdsWithin_le_nhds ((hN s).1.mem_nhds (hN s).2))
    rw [hn]
    simp only [u, dite_eq_left h]
    rw [← (hi s l h).2.1, ← (hi s l h).2.2]

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Selection_MarkedPhysicalBranches
attribute [-instance] _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions _root_.OAI.CircleDomainRigidity.finiteSphericalArea _root_.OAI.CircleDomainRigidity.sphereFirstCountableTopology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The selected marked bands determine common physical branch
neighborhoods. Smoothness, projection, and the original widths refer to
the same chosen branches. -/

open Set Function Filter Classical
open scoped Topology ContDiff
noncomputable section
namespace CircleDomainRigidity
open FiniteTransfer

theorem exists_marked_physical_branches
    {n : ℕ} {S : Type*} (L : Fin n → Type*)
    (U G : Set Sphere) (π : Sphere → Sphere)
    (M : Fin n → Set Sphere) (hM : ∀ l, IsClosed (M l))
    (hboundary : ∀ l, frontier (M l) ⊆ U)
    (σ : S → Sphere) (hσ : ∀ s, σ s ∉ U) (singular : Fin n → Sphere)
    (P : ∀ l, L l → Set Sphere) (hP : ∀ l i, IsOpen (P l i))
    (v : ∀ l, L l → Sphere → ℝ) (B : ∀ l, L l → ℝ)
    (hbound : ∀ l i x, |v l i x| ≤ B l i)
    (a b : Fin n → S → ℝ)
    (hband : ∀ s l, σ s ∈ M l → σ s ≠ singular l → ∃ i : L l,
      σ s ∈ P l i ∧ a l s = liminf (v l i) (𝓝[U] (σ s)) ∧
        b l s = limsup (v l i) (𝓝[U] (σ s)))
    (f : Fin n → (ℝ × ℝ) → UnitAddCircle)
    (hv : ∀ l i, ContDiffOn ℝ ∞
      (fun x : ℝ × ℝ => v l i (π (Complex.equivRealProdCLM.symm x : Sphere)))
      (realChartDomain G ∩ realChartDomain (π ⁻¹' P l i)))
    (hproj : ∀ l i x, x ∈ realChartDomain G ∩ realChartDomain (π ⁻¹' P l i) →
      (v l i (π (Complex.equivRealProdCLM.symm x : Sphere)) : UnitAddCircle) = f l x) :
    ∃ (N : S → Set Sphere) (u : S → Fin n → Sphere → ℝ) (C : S → Fin n → ℝ),
      (∀ s, IsOpen (N s) ∧ σ s ∈ N s) ∧
      (∀ s l, σ s ∈ M l → N s ⊆ interior (M l)) ∧
      (∀ s l, σ s ∉ M l → Disjoint (N s) (M l)) ∧
      (∀ s l x, |u s l x| ≤ C s l) ∧
      (∀ s l, σ s ∈ M l → σ s ≠ singular l →
        limsup (u s l) (𝓝[U ∩ N s] (σ s)) -
          liminf (u s l) (𝓝[U ∩ N s] (σ s)) = b l s - a l s) ∧
      (∀ s l, σ s ∈ M l → σ s ≠ singular l → ContDiffOn ℝ ∞
        (fun x : ℝ × ℝ => u s l (π (Complex.equivRealProdCLM.symm x : Sphere)))
        (realChartDomain G ∩ realChartDomain (π ⁻¹' N s))) ∧
      (∀ s l, σ s ∈ M l → σ s ≠ singular l → ∀ x,
        x ∈ realChartDomain G ∩ realChartDomain (π ⁻¹' N s) →
        (u s l (π (Complex.equivRealProdCLM.symm x : Sphere)) : UnitAddCircle) = f l x) := by
  obtain ⟨N, u, C, hN, hNM, hdisj, hb, hchosen, hwidth⟩ :=
    exists_marked_branch_neighborhoods L U M hM hboundary σ hσ singular P hP v B hbound a b hband
  refine ⟨N, u, C, hN, hNM, hdisj, hb, hwidth, ?_, ?_⟩
  · intro s l hs hne
    obtain ⟨i, hNP, hu⟩ := hchosen s l hs hne
    rw [hu]
    apply (hv l i).mono
    intro x hx
    exact ⟨hx.1, hNP hx.2⟩
  · intro s l hs hne x hx
    obtain ⟨i, hNP, hu⟩ := hchosen s l hs hne
    rw [hu]
    exact hproj l i x ⟨hx.1, hNP hx.2⟩

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Transfer_MarkedModelTerminalControl
attribute [-instance] _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions _root_.OAI.CircleDomainRigidity.finiteSphericalArea _root_.OAI.CircleDomainRigidity.sphereFirstCountableTopology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Actual quotient branch neighborhoods induce the physical terminal
collars needed by the common masked model. -/

open Set Function Filter
open scoped Topology ContDiff
noncomputable section
namespace CircleDomainRigidity.FiniteTransfer

theorem marked_model_terminal_control
    {I J : Type*} [Fintype I] [Fintype J] {n N : ℕ}
    {G B : Set Sphere} (hG : IsOpen G) {π : Sphere → Sphere} (hπ : Continuous π)
    {p : I → Sphere} {O : I → Set Sphere}
    (D : PhysicalTerminalDisks G π B p O) (H : J → ℂ ≃ₜ ℂ)
    (hTH : ∀ i j, Disjoint (closure (jordanInterior (D.H i))) (closure (jordanInterior (H j))))
    {K : Set (ℝ × ℝ)} (Mask : Fin n → Set Sphere)
    {f : Fin n → (ℝ × ℝ) → UnitAddCircle} {χ : (ℝ × ℝ) → ℝ}
    {θ : Fin n → ℝ} {ε : ℝ}
    (Q : MaskedModelData D.H H (realChartDomain G) K (fun l => physicalMask π (Mask l)) f χ N θ ε)
    (hTC : ∀ i, Disjoint (closedTerminalCap (D.H i)) (cutoffCore χ))
    (V : I → Set Sphere) (hV : ∀ i, IsOpen (V i)) (hOV : ∀ i, O i ⊆ V i)
    (u : I → Fin n → Sphere → ℝ) (S : Fin n → Finset I) (a : I → Fin n → ℝ)
    (hVM : ∀ l i, i ∈ S l → V i ⊆ Mask l)
    (hu : ∀ l i, i ∈ S l → ContDiffOn ℝ ∞
      (fun x : ℝ × ℝ => u i l (π (Complex.equivRealProdCLM.symm x : Sphere)))
      (realChartDomain G ∩ realChartDomain (π ⁻¹' V i)))
    (hproj : ∀ l i, i ∈ S l → ∀ x,
      x ∈ realChartDomain G ∩ realChartDomain (π ⁻¹' V i) →
      (u i l (π (Complex.equivRealProdCLM.symm x : Sphere)) : UnitAddCircle) = f l x)
    (ha : ∀ l i, i ∈ S l → 0 ≤ a i l)
    (hbound : ∀ l i, i ∈ S l → ∀ x ∈ frontier (jordanInterior (D.H i)),
      ∀ y ∈ frontier (jordanInterior (D.H i)),
      |shiftedStaircase (reciprocalGridStep N)
          (staircaseWidth (reciprocalGridStep N) Q.widthIndex) (θ l) (u i l (π (x : Sphere))) -
        shiftedStaircase (reciprocalGridStep N)
          (staircaseWidth (reciprocalGridStep N) Q.widthIndex) (θ l) (u i l (π (y : Sphere)))| ≤
          a i l + 4 * reciprocalGridStep N)
    {η : ℝ} (hsmall : reciprocalGridStep N * Real.sqrt (Fintype.card I : ℝ) < η) :
    ∃ (E : I → Set (ℝ × ℝ)) (w : I → Fin n → (ℝ × ℝ) → ℝ),
      (∀ i, IsOpen (E i) ∧ frontier (realJordanInterior (D.H i)) ⊆ E i) ∧
      (∀ l i, i ∈ S l → ContDiffOn ℝ ∞ (w i l) (E i) ∧
        ∀ᶠ x in 𝓝ˢ (frontier (realJordanInterior (D.H i))), (w i l x : UnitAddCircle) = Q.functions l x) ∧
      ∀ l, Real.sqrt (∑ i ∈ S l,
        max (Metric.diam (w i l '' frontier (realJordanInterior (D.H i))) - a i l) 0 ^ 2) < 4 * η := by
  let E (i : I) := (realChartDomain G ∩ realChartDomain (π ⁻¹' V i)) ∩ interior {x | χ x = 1}
  have hE (i : I) : IsOpen (E i) :=
    ((isOpen_realChartDomain hG).inter (isOpen_realChartDomain ((hV i).preimage hπ))).inter isOpen_interior
  have hDE (i : I) : frontier (realJordanInterior (D.H i)) ⊆ E i := by
    rw [frontier_realJordanInterior]
    rintro x ⟨z, hz, rfl⟩
    refine ⟨⟨?_, ?_⟩, ?_⟩
    · simpa only [realChartDomain, mem_preimage, ContinuousLinearEquiv.symm_apply_apply] using
        (D.frontier_good i z hz).1
    · simpa only [realChartDomain, mem_preimage, ContinuousLinearEquiv.symm_apply_apply] using
        hOV i (D.closure_subset i (frontier_subset_closure hz))
    · exact boundary_in_one_plateau_of_disjoint_cutoffCore (D.H i) χ (hTC i) z hz
  obtain ⟨w, hw, hexcess⟩ := Q.terminal_branches hTH E hE hDE
    (fun i l x => u i l (π (Complex.equivRealProdCLM.symm x : Sphere))) S a
    (fun l i hi => (hu l i hi).mono inter_subset_left)
    (fun l i hi x hx => hVM l i hi hx.1.2)
    (fun l i hi x hx => hproj l i hi x hx.1)
    (fun i x hx => (show x ∈ {y | χ y = 1} from interior_subset hx.2)) ha
    (fun l i hi x hx y hy => by
      simpa only [ContinuousLinearEquiv.symm_apply_apply] using hbound l i hi x hx y hy) hsmall
  exact ⟨E, w, fun i => ⟨hE i, hDE i⟩, hw, hexcess⟩

end CircleDomainRigidity.FiniteTransfer

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Selection_SubfamilyOverride
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Retain a prescribed real subfamily when choosing local branches. -/

open Function Classical
noncomputable section
namespace CircleDomainRigidity.FiniteTransfer

theorem subfamilyOverride_at {A L Y : Type*} (ι : A → L) (hι : Injective ι)
    (r : A → Y) (u : L → Y) (j : A) : subfamilyOverride ι r u (ι j) = r j := by
  have h : ∃ k, ι k = ι j := ⟨j, rfl⟩
  have he : Classical.choose h = j := hι (Classical.choose_spec h)
  simp only [subfamilyOverride, dite_eq_left h, he]

theorem subfamilyOverride_of_notMem {A L Y : Type*} (ι : A → L)
    (r : A → Y) (u : L → Y) {l : L} (hl : l ∉ Set.range ι) :
    subfamilyOverride ι r u l = u l := by
  simp only [subfamilyOverride, dite_eq_right (show ¬∃ j, ι j = l from hl)]

end CircleDomainRigidity.FiniteTransfer

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Selection_RealPreservingBranches
attribute [-instance] _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Choose the supplied global real branch on real coordinates and the
local atlas branch on all remaining coordinates. -/

open Set Function Filter Classical
open scoped Topology ContDiff
noncomputable section
namespace CircleDomainRigidity.FiniteTransfer

theorem exists_real_preserving_subordinate_branches
    {I : Type*} {n : ℕ} (L : Fin n → Type*)
    (G K : Set (ℝ × ℝ)) (hG : IsOpen G) (hK : IsClosed K)
    (M : Fin n → Set (ℝ × ℝ)) (f : Fin n → (ℝ × ℝ) → UnitAddCircle)
    (P : ∀ l, L l → Set (ℝ × ℝ)) (v : ∀ l, L l → (ℝ × ℝ) → ℝ)
    (hv : ∀ l a, ContDiffOn ℝ ∞ (v l a) (G ∩ P l a))
    (hproj : ∀ l a x, x ∈ G ∩ P l a → (v l a x : UnitAddCircle) = f l x)
    (B Nbh : I → Set (ℝ × ℝ)) (hNbh : ∀ i, IsOpen (Nbh i))
    (hBN : ∀ i, B i ⊆ Nbh i)
    (hbranch : ∀ i l, Disjoint (Nbh i) (M l) ∨ ∃ a, Nbh i ⊆ interior (M l) ∩ P l a)
    (χ : (ℝ × ℝ) → ℝ) (hBG : ∀ i, B i ⊆ G) (hBK : ∀ i, Disjoint (B i) K)
    (hBχ : ∀ i, B i ⊆ interior {x | χ x = 1})
    {J : Type*} (ι : J → Fin n) (hι : Injective ι)
    (r : J → (ℝ × ℝ) → ℝ) (hr : ∀ j, ContDiffOn ℝ ∞ (r j) G)
    (hrproj : ∀ j x, (r j x : UnitAddCircle) = f (ι j) x) :
    ∃ (O : I → Set (ℝ × ℝ)) (present : I → Fin n → Prop)
      (u : I → Fin n → (ℝ × ℝ) → ℝ),
      (∀ i, IsOpen (O i) ∧ B i ⊆ O i ∧ O i ⊆ G ∧ Disjoint (O i) K ∧
        ∀ x ∈ O i, χ x = 1) ∧
      (∀ i l, ¬present i l → Disjoint (O i) (M l)) ∧
      (∀ i l, present i l → ContDiffOn ℝ ∞ (u i l) (O i)) ∧
      (∀ i l, present i l → ∀ x ∈ O i, (u i l x : UnitAddCircle) = f l x) ∧
      (∀ i l, present i l → O i ⊆ interior (M l)) ∧
      ∀ i j, u i (ι j) = r j := by
  obtain ⟨O, present, u, hO, habsent, hu, hproj', hOM⟩ :=
    exists_subordinate_masked_branches L G K hG hK M f P v hv hproj
      B Nbh hNbh hBN hbranch χ hBG hBK hBχ
  let u' (i : I) (l : Fin n) : (ℝ × ℝ) → ℝ :=
    if h : ∃ j, ι j = l then r (Classical.choose h) else u i l
  refine ⟨O, present, u', hO, habsent, ?_, ?_, hOM, ?_⟩
  · intro i l hl
    by_cases h : ∃ j, ι j = l
    · simpa only [u', dite_eq_left h] using (hr (Classical.choose h)).mono (hO i).2.2.1
    · simpa only [u', dite_eq_right h] using hu i l hl
  · intro i l hl x hx
    by_cases h : ∃ j, ι j = l
    · simpa only [u', dite_eq_left h, Classical.choose_spec h] using hrproj (Classical.choose h) x
    · simpa only [u', dite_eq_right h] using hproj' i l hl x hx
  · intro i j
    have h : ∃ j', ι j' = ι j := ⟨j, rfl⟩
    have hj : Classical.choose h = j := hι (Classical.choose_spec h)
    simp only [u', dite_eq_left h, hj]

end CircleDomainRigidity.FiniteTransfer

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Topology_MixedCircleFillings
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonEmbeddedArc.Arc.graphVertices_finite _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Simultaneous real and circle fillings using the same rank-one collar
extensions. Exact real values are retained for the designated real coordinates. -/

open Set Filter Function
open scoped Topology ContDiff

noncomputable section
namespace CircleDomainRigidity.FiniteTransfer

theorem eventually_exists_mixed_filled_coordinates
    {I : Type*} [Fintype I] {n : ℕ}
    (D : I → Set (ℝ × ℝ)) (hD : ∀ i, IsOpen (D i))
    (hdisj : Pairwise (Disjoint on fun i => closure (D i)))
    (hfrontc : ∀ i, IsCompact (frontier (D i)))
    (hfrontconn : ∀ i, IsConnected (frontier (D i)))
    (O : I → Set (ℝ × ℝ)) (hO : ∀ i, IsOpen (O i))
    (hDO : ∀ i, frontier (D i) ⊆ O i)
    (u : I → Fin n → (ℝ × ℝ) → ℝ)
    (hu : ∀ i l, ContDiffOn ℝ ∞ (u i l) (O i))
    (active : I → Fin n) {h : ℝ} (hh : 0 < h) (θ : Fin n → ℝ)
    (havoid : ∀ i l, l ≠ active i →
      Disjoint (u i l '' frontier (D i)) (shiftedLattice h (θ l)))
    (v : ℝ → Fin n → (ℝ × ℝ) → UnitAddCircle)
    (Ω : Set (ℝ × ℝ)) (M : Fin n → Set (ℝ × ℝ))
    (hv : ∀ δ, 0 < δ → δ < h / 4 → ∀ l,
      SmoothCircleOn (v δ l) ((Ω ∩ interior (M l)) \ ⋃ i, D i))
    (hbranch : ∀ δ i l x, x ∈ O i →
      (shiftedStaircase h δ (θ l) (u i l x) : UnitAddCircle) = v δ l x)
    {J : Type*} [Fintype J] (ι : J → Fin n) (hι : Injective ι)
    (w : ℝ → J → (ℝ × ℝ) → ℝ)
    (hw : ∀ δ, 0 < δ → δ < h / 4 → ∀ j x, x ∈ Ω →
      (∀ i, x ∉ D i) → ContDiffAt ℝ ∞ (w δ j) x)
    (hwbranch : ∀ δ i j, EqOn (w δ j)
      (fun x => shiftedStaircase h δ (θ (ι j)) (u i (ι j) x)) (O i))
    (hwproj : ∀ δ j x, (w δ j x : UnitAddCircle) = v δ (ι j) x) :
    ∀ᶠ δ : ℝ in 𝓝[>] 0, ∃ F : Fin n → (ℝ × ℝ) → UnitAddCircle,
      IsMaskedFilledCircleFamily D Ω M (v δ) F ∧
      ∃ W : J → (ℝ × ℝ) → ℝ, IsFilledCoordinateFamily D Ω (w δ) W ∧
        ∀ j x, (W j x : UnitAddCircle) = F (ι j) x := by
  classical
  have hlocal := eventually_exists_rank_one_collar_families D hfrontc hfrontconn
    O hO hDO u hu active hh θ havoid
  have hsmall : ∀ᶠ δ : ℝ in 𝓝[>] 0, 0 < δ ∧ δ < h / 4 :=
    (show ∀ᶠ δ : ℝ in 𝓝[>] 0, 0 < δ from self_mem_nhdsWithin).and
      ((eventually_lt_nhds (by positivity : (0 : ℝ) < h / 4)).filter_mono nhdsWithin_le_nhds)
  filter_upwards [hlocal, hsmall] with δ hδ hδsmall
  obtain ⟨g, hg, hagree, hzero⟩ := hδ
  have hpair : Pairwise (Disjoint on D) := fun i j hij =>
    (hdisj hij).mono subset_closure subset_closure
  have hproj (i : I) : ∀ᶠ x in 𝓝ˢ (frontier (D i)), ∀ l,
      (g i l x : UnitAddCircle) = v δ l x := by
    filter_upwards [hagree i, (hO i).mem_nhdsSet.mpr (hDO i)] with x hx hxO l
    exact (congrArg ((↑) : ℝ → UnitAddCircle) (hx l)).trans (hbranch δ i l x hxO)
  have hagreeAt (i : I) (x : ℝ × ℝ) (hx : x ∈ frontier (D i)) (l : Fin n) :
      (fun y => (g i l y : UnitAddCircle)) =ᶠ[𝓝 x] v δ l :=
    ((hproj i).filter_mono (nhds_le_nhdsSet hx)).mono (fun _ hy => hy l)
  let F : Fin n → (ℝ × ℝ) → UnitAddCircle := fun l =>
    patchOpenRegions D (fun i x => (g i l x : UnitAddCircle)) (v δ l)
  have hF : IsMaskedFilledCircleFamily D Ω M (v δ) F := by
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · intro l
      exact smoothCircleOn_patchOpenRegions D hD hpair (v δ l) (hv δ hδsmall.1 hδsmall.2 l)
        (fun i => g i l) (fun i => hg i l) (fun i x hx => hagreeAt i x hx.2 l)
    · intro l x hx
      exact False.elim hx
    · intro l x hx
      exact patchOpenRegions_eq_of_notMem D (fun i x => (g i l x : UnitAddCircle)) (v δ l) hx
    · intro i
      apply eventually_nhdsSet_iff_forall.mpr
      intro x hx
      have houtside : ∀ j, x ∉ D j := by
        intro j hxj
        by_cases hji : j = i
        · subst j
          rw [(hD i).frontier_eq] at hx
          exact hx.2 hxj
        · exact Set.disjoint_left.mp (hdisj hji) (subset_closure hxj) (frontier_subset_closure hx)
      apply eventually_all.mpr
      intro l
      exact patchOpenRegions_eventuallyEq_outside D (fun i x => (g i l x : UnitAddCircle))
        (v δ l) hD houtside (fun j hj => hagreeAt j x hj l)
    · intro i l m hlm x hx
      exact circle_patch_wedges_eq_zero_inside D hD hpair (v δ) g hg
        (fun i l m hlm x _ => hzero i l m hlm x) hx l m hlm
  let W : J → (ℝ × ℝ) → ℝ := fun j =>
    patchOpenRegions D (fun i => g i (ι j)) (w δ j)
  have hrealAt (i : I) (x : ℝ × ℝ) (hx : x ∈ frontier (D i)) (j : J) :
      g i (ι j) =ᶠ[𝓝 x] w δ j := by
    have he : ∀ᶠ y in 𝓝ˢ (frontier (D i)), g i (ι j) y = w δ j y := by
      filter_upwards [hagree i, (hO i).mem_nhdsSet.mpr (hDO i)] with y hy hyO
      exact (hy (ι j)).trans (hwbranch δ i j hyO).symm
    exact he.filter_mono (nhds_le_nhdsSet hx)
  refine ⟨F, hF, W, ⟨?_, ?_, ?_, ?_⟩, ?_⟩
  · intro j
    exact contDiffOn_patchOpenRegions D (fun i => g i (ι j)) (w δ j) hD hpair
      (hw δ hδsmall.1 hδsmall.2 j)
      (fun i _ _ => (hg i (ι j)).contDiffAt)
      (fun i x hx => hrealAt i x hx.2 j)
  · intro j x hx
    exact patchOpenRegions_eq_of_notMem D (fun i => g i (ι j)) (w δ j) hx
  · intro i
    apply eventually_nhdsSet_iff_forall.mpr
    intro x hx
    have houtside : ∀ k, x ∉ D k := by
      intro k hxk
      by_cases hki : k = i
      · subst k
        rw [(hD i).frontier_eq] at hx
        exact hx.2 hxk
      · exact Set.disjoint_left.mp (hdisj hki) (subset_closure hxk) (frontier_subset_closure hx)
    change ∀ᶠ y in 𝓝 x, ∀ j, W j y = w δ j y
    apply eventually_all.mpr
    intro j
    exact patchOpenRegions_eventuallyEq_outside D (fun k => g k (ι j)) (w δ j) hD houtside
      (fun k hk => hrealAt k x hk j)
  · intro i j k hjk x hx
    exact patchOpenRegions_wedges_eq_zero_inside D (fun i j => g i (ι j)) (w δ) hD hpair
      (fun i j k hjk x _ => hzero i (ι j) (ι k) (fun h => hjk (hι h)) x) hx j k hjk
  · intro j x
    by_cases hm : ∃ i, x ∈ D i
    · obtain ⟨i, hi⟩ := hm
      change ((patchOpenRegions D (fun i => g i (ι j)) (w δ j) x : ℝ) : UnitAddCircle) =
        patchOpenRegions D (fun i x => (g i (ι j) x : UnitAddCircle)) (v δ (ι j)) x
      exact (congrArg ((↑) : ℝ → UnitAddCircle)
        (patchOpenRegions_eq_of_mem D (fun i => g i (ι j)) (w δ j) hpair hi)).trans
        (patchOpenRegions_eq_of_mem D (fun i x => (g i (ι j) x : UnitAddCircle))
          (v δ (ι j)) hpair hi).symm
    · change ((patchOpenRegions D (fun i => g i (ι j)) (w δ j) x : ℝ) : UnitAddCircle) =
        patchOpenRegions D (fun i x => (g i (ι j) x : UnitAddCircle)) (v δ (ι j)) x
      exact (congrArg ((↑) : ℝ → UnitAddCircle)
        (patchOpenRegions_eq_of_notMem D (fun i => g i (ι j)) (w δ j) (not_exists.mp hm))).trans
        ((hwproj δ j x).trans
          (patchOpenRegions_eq_of_notMem D (fun i x => (g i (ι j) x : UnitAddCircle))
            (v δ (ι j)) (not_exists.mp hm)).symm)

theorem eventually_fill_actual_mixed_cutoff
    {I : Type*} [Fintype I] {n : ℕ}
    (D : I → Set (ℝ × ℝ)) (hD : ∀ i, IsOpen (D i))
    (hdisj : Pairwise (Disjoint on fun i => closure (D i)))
    (hfrontc : ∀ i, IsCompact (frontier (D i)))
    (hfrontconn : ∀ i, IsConnected (frontier (D i)))
    {G : Set (ℝ × ℝ)} (hG : IsOpen G) (M : Fin n → Set (ℝ × ℝ))
    (f : Fin n → (ℝ × ℝ) → UnitAddCircle)
    (hf : ∀ l, SmoothCircleOn (f l) (G ∩ interior (M l)))
    (χ : (ℝ × ℝ) → ℝ) (hχ : ContDiff ℝ ∞ χ)
    (O : I → Set (ℝ × ℝ)) (hO : ∀ i, IsOpen (O i))
    (hDO : ∀ i, frontier (D i) ⊆ O i)
    (hχone : ∀ i x, x ∈ O i → χ x = 1)
    (u : I → Fin n → (ℝ × ℝ) → ℝ) (hu : ∀ i l, ContDiffOn ℝ ∞ (u i l) (O i))
    (hproj : ∀ i l x, x ∈ O i → (u i l x : UnitAddCircle) = f l x)
    (N : ℕ) (active : I → Fin n) (θ : Fin n → ℝ)
    (havoid : ∀ i l, l ≠ active i →
      Disjoint (u i l '' frontier (D i)) (shiftedLattice (reciprocalGridStep N) (θ l)))
    {J : Type*} [Fintype J] (ι : J → Fin n) (hι : Injective ι)
    (r : J → (ℝ × ℝ) → ℝ) (hr : ∀ j, ContDiffOn ℝ ∞ (r j) G)
    (hrproj : ∀ j x, (r j x : UnitAddCircle) = f (ι j) x)
    (hreal : ∀ i j, EqOn (u i (ι j)) (r j) (O i)) :
    ∀ᶠ δ : ℝ in 𝓝[>] 0, ∃ F : Fin n → (ℝ × ℝ) → UnitAddCircle,
      IsMaskedFilledCircleFamily D (G ∪ ⋃ i, D i) M
        (fun l => circleCutoff (f l) χ (shiftedStaircase (reciprocalGridStep N) δ (θ l))) F ∧
      ∃ W : J → (ℝ × ℝ) → ℝ,
        IsFilledCoordinateFamily D (G ∪ ⋃ i, D i)
          (fun j => cutoffStaircase (r j) χ
            (shiftedStaircase (reciprocalGridStep N) δ (θ (ι j)))) W ∧
        ∀ j x, (W j x : UnitAddCircle) = F (ι j) x := by
  refine eventually_exists_mixed_filled_coordinates D hD hdisj hfrontc hfrontconn
    O hO hDO u hu active (reciprocalGridStep_pos N) θ havoid
    (fun δ l => circleCutoff (f l) χ (shiftedStaircase (reciprocalGridStep N) δ (θ l)))
    (G ∪ ⋃ i, D i) M ?_ ?_ ι hι (fun δ j => cutoffStaircase (r j) χ
      (shiftedStaircase (reciprocalGridStep N) δ (θ (ι j)))) ?_ ?_ ?_
  · intro δ hδ hδh l z hz a ha
    have hzG : z ∈ G := hz.1.1.resolve_right hz.2
    exact smoothCircleOn_reciprocal_cutoff (hf l) χ hχ N hδ hδh (θ l) z ⟨hzG, hz.1.2⟩ a ha
  · intro δ i l x hx
    have hP (r : ℝ) : shiftedStaircase (reciprocalGridStep N) δ (θ l) (r + 1) =
        shiftedStaircase (reciprocalGridStep N) δ (θ l) r + 1 := by
      simpa only [reciprocalGridStep, Nat.cast_succ] using
        shiftedStaircase_add_one (Nat.succ_pos N) δ (θ l) r
    have heq := circleCutoff_eq_lift (f l) χ hP (hproj i l x hx)
    exact (congrArg ((↑) : ℝ → UnitAddCircle)
      (cutoffStaircase_of_one (u := u i l)
        (P := shiftedStaircase (reciprocalGridStep N) δ (θ l)) (hχone i x hx))).symm.trans heq.symm
  · intro δ hδ hδh j x hx houtside
    have hxG : x ∈ G := hx.resolve_right (fun hi => let ⟨i, hi⟩ := mem_iUnion.mp hi; houtside i hi)
    have hrc := (hr j x hxG).contDiffAt (hG.mem_nhds hxG)
    exact hrc.add (hχ.contDiffAt.mul
      (((contDiff_shiftedStaircase (reciprocalGridStep_pos N) hδ hδh (θ (ι j))).contDiffAt.comp x hrc).sub hrc))
  · intro δ i j x hx
    rw [cutoffStaircase_of_one (hχone i x hx)]
    exact congrArg (shiftedStaircase (reciprocalGridStep N) δ (θ (ι j))) (hreal i j hx).symm
  · intro δ j x
    have hP (t : ℝ) : shiftedStaircase (reciprocalGridStep N) δ (θ (ι j)) (t + 1) =
        shiftedStaircase (reciprocalGridStep N) δ (θ (ι j)) t + 1 := by
      simpa only [reciprocalGridStep, Nat.cast_succ] using
        shiftedStaircase_add_one (Nat.succ_pos N) δ (θ (ι j)) t
    exact (circleCutoff_eq_lift (f (ι j)) χ hP (hrproj j x)).symm

end CircleDomainRigidity.FiniteTransfer

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Transfer_ActualMixedTransfer
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonEmbeddedArc.Arc.graphVertices_finite _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Transfer real barriers and masked period coordinates using one width
and one metric, retaining the exact real barriers near the chosen core. -/

open Set Filter Function MeasureTheory
open scoped Topology ContDiff Matrix.Norms.Elementwise
noncomputable section
namespace CircleDomainRigidity.FiniteTransfer

theorem transfer_actual_mixed_cutoff
    {I : Type*} [Fintype I] {n : ℕ}
    (D : I → Set (ℝ × ℝ)) (hD : ∀ i, IsOpen (D i))
    (hdisj : Pairwise (Disjoint on fun i => closure (D i)))
    (hfrontc : ∀ i, IsCompact (frontier (D i)))
    (hfrontconn : ∀ i, IsConnected (frontier (D i)))
    {G Q K : Set (ℝ × ℝ)} (hG : IsOpen G) (hQ : IsClosed Q)
    (hK : IsClosed K) (hKc : IsCompact (closure Kᶜ)) (hKG : K ⊆ G)
    (hcover : Q ⊆ G ∪ ⋃ i, D i) (hKD : ∀ x ∈ K, ∀ i, x ∉ D i)
    (M : Fin n → Set (ℝ × ℝ)) (hM : ∀ i, IsClosed (M i))
    (hboundary : ∀ i, frontier (M i) ⊆ interior K)
    (f : Fin n → (ℝ × ℝ) → UnitAddCircle)
    (hf : ∀ l, SmoothCircleOn (f l) (G ∩ interior (M l)))
    (hf2 : ∀ l, MemLp (circleGradient (f l)) 2 (volume.restrict (G ∩ M l)))
    (χ : (ℝ × ℝ) → ℝ) (hχ : ContDiff ℝ ∞ χ)
    (hχzero : ∀ᶠ x in 𝓝ˢ K, χ x = 0)
    (O : I → Set (ℝ × ℝ)) (hO : ∀ i, IsOpen (O i))
    (hDO : ∀ i, frontier (D i) ⊆ O i)
    (hχone : ∀ i x, x ∈ O i → χ x = 1)
    (u : I → Fin n → (ℝ × ℝ) → ℝ) (hu : ∀ i l, ContDiffOn ℝ ∞ (u i l) (O i))
    (hproj : ∀ i l x, x ∈ O i → (u i l x : UnitAddCircle) = f l x)
    (N : ℕ) (active : I → Fin n) (θ : Fin n → ℝ)
    (havoid : ∀ i l, l ≠ active i →
      Disjoint (u i l '' frontier (D i)) (shiftedLattice (reciprocalGridStep N) (θ l)))
    {J : Type*} [Fintype J] (ι : J → Fin n) (hι : Injective ι)
    (r : J → (ℝ × ℝ) → ℝ) (hr : ∀ j, ContDiffOn ℝ ∞ (r j) G)
    (hrproj : ∀ j x, (r j x : UnitAddCircle) = f (ι j) x)
    (hreal : ∀ i j, EqOn (u i (ι j)) (r j) (O i))
    (hvi : ∀ k, IntegrableOn (maskedCircleWedges M (circleCutoffFamily f χ N
      (staircaseWidth (reciprocalGridStep N) k) θ)) (G \ K))
    {ε : ℝ} (hgood : ∃ᶠ k in atTop, (∫ z in G \ K, maskedCircleWedges M
      (circleCutoffFamily f χ N (staircaseWidth (reciprocalGridStep N) k) θ) z) < ε / 2)
    (k₀ : ℕ) :
    ∃ (k : ℕ) (F : Fin n → (ℝ × ℝ) → UnitAddCircle)
      (R : ℝ) (g : (ℝ × ℝ) → PlanarMetric),
      k₀ ≤ k ∧ IsMaskedFilledCircleFamily D (G ∪ ⋃ i, D i) M
        (circleCutoffFamily f χ N (staircaseWidth (reciprocalGridStep N) k) θ) F ∧
      (∀ᶠ z in 𝓝ˢ K, ∀ i, F i z = f i z) ∧
      0 < R ∧ ContDiff ℝ ∞ g ∧ (∀ z, (g z).PosDef) ∧
      (∀ᶠ z in 𝓝ˢ K, g z = sphericalMetricFactor z • 1) ∧
      (∀ z ∉ Metric.closedBall 0 R, g z = sphericalMetricFactor z • 1) ∧
      (∑ i : Fin n, ∫ z in (Q \ K) ∩ M i, fieldEnergy (circleGradient (F i)) g z) < ε ∧
      (∀ i : Fin n, ∀ E : Set (ℝ × ℝ), MeasurableSet E → E ⊆ K →
        (∫ z in (Q \ E) ∩ M i, fieldEnergy (circleGradient (F i)) g z) <
          (∫ z in (G \ E) ∩ M i, fieldEnergy (circleGradient (f i))
            (fun z => sphericalMetricFactor z • 1) z) + ε) ∧
      ∃ W : J → (ℝ × ℝ) → ℝ,
        IsFilledCoordinateFamily D (G ∪ ⋃ i, D i)
          (fun j => cutoffStaircase (r j) χ (shiftedStaircase (reciprocalGridStep N)
            (staircaseWidth (reciprocalGridStep N) k) (θ (ι j)))) W ∧
        (∀ j x, (W j x : UnitAddCircle) = F (ι j) x) ∧
        (∀ᶠ x in 𝓝ˢ K, ∀ j, W j x = r j x) := by
  have hfill := eventually_fill_actual_mixed_cutoff D hD hdisj hfrontc hfrontconn
    hG M f hf χ hχ O hO hDO hχone u hu hproj N active θ havoid ι hι r hr hrproj hreal
  have hretain (δ : ℝ) : ∀ᶠ x in 𝓝ˢ K, ∀ i, circleCutoffFamily f χ N δ θ i x = f i x := by
    filter_upwards [hχzero] with x hx i
    exact circleCutoff_eq_of_zero (f i) χ (shiftedStaircase (reciprocalGridStep N) δ (θ i)) hx
  have hcost : ∃ᶠ k in atTop, (∫ z in G \ K, 2 * maskedCircleWedges M
      (circleCutoffFamily f χ N (staircaseWidth (reciprocalGridStep N) k) θ) z) < ε := by
    apply hgood.mono
    intro k hk
    rw [integral_const_mul]
    linarith
  obtain ⟨k, F, R, g, hlate, hF, hcore, hR, hg, hPD, hmetric, hfar, hsum, hlocal,
      W, hW, hWproj⟩ := exists_masked_circle_transfer_with_data D hD
    (hG.union (isOpen_iUnion hD)) hQ hG.measurableSet hK hKc
    (fun z hz => hcover hz.1) hKG hcover hKD M hM hboundary
    (fun δ => circleCutoffFamily f χ N δ θ) f hf2 hretain (reciprocalGridStep_pos N)
    (fun δ F => ∃ W : J → (ℝ × ℝ) → ℝ,
      IsFilledCoordinateFamily D (G ∪ ⋃ i, D i)
        (fun j => cutoffStaircase (r j) χ
          (shiftedStaircase (reciprocalGridStep N) δ (θ (ι j)))) W ∧
      ∀ j x, (W j x : UnitAddCircle) = F (ι j) x)
    hfill (fun k => (hvi k).const_mul 2) hcost k₀
  refine ⟨k, F, R, g, hlate, hF, hcore, hR, hg, hPD, hmetric, hfar, hsum,
    hlocal, W, hW, hWproj, ?_⟩
  apply eventually_nhdsSet_iff_forall.mpr
  intro x hx
  apply eventually_all.mpr
  intro j
  filter_upwards [hW.eventuallyEq_outside hD (hKD x hx) j,
    hχzero.filter_mono (nhds_le_nhdsSet hx)] with y hy hyχ
  exact hy.trans (cutoffStaircase_of_zero hyχ)

end CircleDomainRigidity.FiniteTransfer

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Transfer_FiniteMixedModel
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions _root_.OAI.CircleDomainRigidity.finiteSphericalArea _root_.OAI.CircleDomainRigidity.sphereFirstCountableTopology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The same principal model transports both the real barriers and the
masked circle coordinates, with exact energy identities for each. -/

open Set Filter Function MeasureTheory
open scoped Topology ContDiff Matrix.Norms.Elementwise
noncomputable section
namespace CircleDomainRigidity.FiniteTransfer

theorem finite_metric_model_with_mixed_fillings
    (hcompact : SmoothCompactMetricSphereUniformization) (hfinite : FiniteJordanModelUniformization)
    {I : Type*} [Finite I] (T : I → ℂ ≃ₜ ℂ)
    (hdisj : Pairwise (Disjoint on fun i => closure (jordanInterior (T i))))
    {K Ω : Set (ℝ × ℝ)} (hKQ : sphericalCore K ⊆ openCompletedRegion T)
    (hQΩ : realChartDomain (completedRegion T) ⊆ Ω)
    (g : (ℝ × ℝ) → PlanarMetric) (hg : ContDiff ℝ ∞ g) (hPD : ∀ z, (g z).PosDef)
    (hfar : ∃ R : ℝ, 0 < R ∧ ∀ z ∉ Metric.closedBall 0 R, g z = sphericalMetricFactor z • 1)
    (hcore : ∀ᶠ z in 𝓝ˢ K, g z = sphericalMetricFactor z • 1)
    {J : Type*} {n : ℕ} {D : J → Set (ℝ × ℝ)} {M : Fin n → Set (ℝ × ℝ)}
    {v F : Fin n → (ℝ × ℝ) → UnitAddCircle}
    (hF : IsMaskedFilledCircleFamily D Ω M v F)
    {R : Type*} (W : R → (ℝ × ℝ) → ℝ)
    (hW : ∀ j, ContDiffOn ℝ ∞ (W j) Ω) :
    ∃ (V : Set Sphere) (f fi : Sphere → Sphere), IsCircleDomain V ∧
      IsSmoothSphereEquivalence f fi (openCompletedRegion T) V ∧
      IsConformalOn f (sphericalCore K) ∧ IsPrincipalNormalized f ∧
      (∀ l, IsOpen (sphereRealMap f '' (realChartDomain (openCompletedRegion T) ∩ interior (M l))) ∧
        SmoothCircleOn (F l ∘ sphereRealMap fi)
          (sphereRealMap f '' (realChartDomain (openCompletedRegion T) ∩ interior (M l))) ∧
        (∀ x ∈ realChartDomain (openCompletedRegion T) ∩ interior (M l),
          ((F l ∘ sphereRealMap fi) ∘ sphereRealMap f) =ᶠ[𝓝 x] F l)) ∧
      (∀ l (s : Set (ℝ × ℝ)), MeasurableSet s →
        s ⊆ realChartDomain (openCompletedRegion T) ∩ interior (M l) →
        (∫ y in sphereRealMap f '' s,
          fieldEnergy (circleGradient (F l ∘ sphereRealMap fi)) (fun _ => 1) y) =
        ∫ x in s, fieldEnergy (circleGradient (F l)) g x) ∧
      (∀ j, ContDiffOn ℝ ∞ (W j ∘ sphereRealMap fi) (realChartDomain V) ∧
        ∀ x ∈ realChartDomain (openCompletedRegion T),
          ((W j ∘ sphereRealMap fi) ∘ sphereRealMap f) =ᶠ[𝓝 x] W j) ∧
      (∀ j (s : Set (ℝ × ℝ)), MeasurableSet s → s ⊆ realChartDomain (openCompletedRegion T) →
        (∫ y in sphereRealMap f '' s, gradientEnergy (W j ∘ sphereRealMap fi) (fun _ => 1) y) =
          ∫ x in s, gradientEnergy (W j) g x) ∧
      (∀ p ∈ openCompletedRegion T, IsMetricConformalAt g f p) := by
  obtain ⟨V, f, fi, hV, heq, hconf, hmetric, hnorm⟩ :=
    principal_finite_metric_circle_model hcompact hfinite T hdisj hKQ g hg hPD hfar hcore
  have hinf := hKQ (infty_mem_sphericalCore K)
  have hO : IsOpen (realChartDomain (openCompletedRegion T)) :=
    isOpen_realChartDomain (isOpen_openCompletedRegion T)
  have hFO (l : Fin n) : SmoothCircleOn (F l)
      (realChartDomain (openCompletedRegion T) ∩ interior (M l)) := by
    intro x hx
    exact hF.1 l x ⟨hQΩ (openCompletedRegion_subset_completedRegion T hx.1), hx.2⟩
  have hWO (j : R) : ContDiffOn ℝ ∞ (W j) (realChartDomain (openCompletedRegion T)) :=
    (hW j).mono (fun _ hx => hQΩ (openCompletedRegion_subset_completedRegion T hx))
  have himage : sphereRealMap f '' realChartDomain (openCompletedRegion T) =
      realChartDomain V := (heq.real_bijOn hinf hnorm.1).image_eq
  refine ⟨V, f, fi, hV, heq, hconf, hnorm, ?_, ?_, ?_, ?_, hmetric⟩
  · intro l
    exact transported_circle_coordinate heq hV.1 hinf hnorm.1
      (hO.inter isOpen_interior) inter_subset_left (F l) (hFO l)
  · intro l s hs hsO
    exact integral_transported_circle_coordinate heq hV.1 hinf hnorm.1
      (hO.inter isOpen_interior) inter_subset_left (F l) (hFO l) hs hsO
      hmetric (fun x _ => hPD x)
  · intro j
    obtain ⟨_, hsmooth, hpull⟩ := transported_real_coordinate heq hV.1 hinf hnorm.1
      hO (Subset.refl _) (W j) (hWO j)
    exact ⟨himage ▸ hsmooth, hpull⟩
  · intro j s hs hsO
    exact integral_transported_real_coordinate heq hV.1 hinf hnorm.1 hO (Subset.refl _)
      (W j) (hWO j) hs hsO hmetric (fun x _ => hPD x)

end CircleDomainRigidity.FiniteTransfer

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Transfer_PrincipalMixedTransfer
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions _root_.OAI.CircleDomainRigidity.finiteSphericalArea _root_.OAI.CircleDomainRigidity.sphereFirstCountableTopology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Principal finite models retaining the same actual real barriers and
circle coordinates used for the common metric construction. -/

open Set Filter Function MeasureTheory
open scoped Topology ContDiff Matrix.Norms.Elementwise
noncomputable section
namespace CircleDomainRigidity.FiniteTransfer

theorem principal_actual_mixed_transfer
    (hcompact : SmoothCompactMetricSphereUniformization) (hfinite : FiniteJordanModelUniformization)
    {J : Type*} [Finite J] (T : J → ℂ ≃ₜ ℂ)
    (hTdisj : Pairwise (Disjoint on fun j => closure (jordanInterior (T j))))
    {I : Type*} [Fintype I] {n : ℕ}
    (D : I → Set (ℝ × ℝ)) (hD : ∀ i, IsOpen (D i))
    (hdisj : Pairwise (Disjoint on fun i => closure (D i)))
    (hfrontc : ∀ i, IsCompact (frontier (D i)))
    (hfrontconn : ∀ i, IsConnected (frontier (D i)))
    {G K : Set (ℝ × ℝ)} (hG : IsOpen G)
    (hK : IsClosed K) (hKc : IsCompact (closure Kᶜ)) (hKG : K ⊆ G)
    (hKQ : sphericalCore K ⊆ openCompletedRegion T)
    (hcover : realChartDomain (completedRegion T) ⊆ G ∪ ⋃ i, D i)
    (hKD : ∀ x ∈ K, ∀ i, x ∉ D i)
    (M : Fin n → Set (ℝ × ℝ)) (hM : ∀ i, IsClosed (M i))
    (hboundary : ∀ i, frontier (M i) ⊆ interior K)
    (f : Fin n → (ℝ × ℝ) → UnitAddCircle)
    (hf : ∀ l, SmoothCircleOn (f l) (G ∩ interior (M l)))
    (hf2 : ∀ l, MemLp (circleGradient (f l)) 2 (volume.restrict (G ∩ M l)))
    (χ : (ℝ × ℝ) → ℝ) (hχ : ContDiff ℝ ∞ χ)
    (hχzero : ∀ᶠ x in 𝓝ˢ K, χ x = 0)
    (O : I → Set (ℝ × ℝ)) (hO : ∀ i, IsOpen (O i))
    (hDO : ∀ i, frontier (D i) ⊆ O i)
    (hχone : ∀ i x, x ∈ O i → χ x = 1)
    (u : I → Fin n → (ℝ × ℝ) → ℝ) (hu : ∀ i l, ContDiffOn ℝ ∞ (u i l) (O i))
    (hproj : ∀ i l x, x ∈ O i → (u i l x : UnitAddCircle) = f l x)
    (N : ℕ) (active : I → Fin n) (θ : Fin n → ℝ)
    (havoid : ∀ i l, l ≠ active i →
      Disjoint (u i l '' frontier (D i)) (shiftedLattice (reciprocalGridStep N) (θ l)))
    {A : Type*} [Fintype A] (ι : A → Fin n) (hι : Injective ι)
    (r : A → (ℝ × ℝ) → ℝ) (hr : ∀ j, ContDiffOn ℝ ∞ (r j) G)
    (hrproj : ∀ j x, (r j x : UnitAddCircle) = f (ι j) x)
    (hreal : ∀ i j, EqOn (u i (ι j)) (r j) (O i))
    (hvi : ∀ k, IntegrableOn (maskedCircleWedges M (circleCutoffFamily f χ N
      (staircaseWidth (reciprocalGridStep N) k) θ)) (G \ K))
    {ε : ℝ} (hgood : ∃ᶠ k in atTop, (∫ z in G \ K, maskedCircleWedges M
      (circleCutoffFamily f χ N (staircaseWidth (reciprocalGridStep N) k) θ) z) < ε / 2)
    (k₀ : ℕ) :
    ∃ (k : ℕ) (F : Fin n → (ℝ × ℝ) → UnitAddCircle)
      (R : ℝ) (g : (ℝ × ℝ) → PlanarMetric)
      (V : Set Sphere) (φ φi : Sphere → Sphere),
      k₀ ≤ k ∧ IsMaskedFilledCircleFamily D (G ∪ ⋃ i, D i) M
        (circleCutoffFamily f χ N (staircaseWidth (reciprocalGridStep N) k) θ) F ∧
      (∀ᶠ z in 𝓝ˢ K, ∀ i, F i z = f i z) ∧
      0 < R ∧ ContDiff ℝ ∞ g ∧ (∀ z, (g z).PosDef) ∧
      (∀ᶠ z in 𝓝ˢ K, g z = sphericalMetricFactor z • 1) ∧
      (∀ z ∉ Metric.closedBall 0 R, g z = sphericalMetricFactor z • 1) ∧
      (∑ i : Fin n, ∫ z in (realChartDomain (completedRegion T) \ K) ∩ M i,
        fieldEnergy (circleGradient (F i)) g z) < ε ∧
      (∀ i : Fin n, ∀ E : Set (ℝ × ℝ), MeasurableSet E → E ⊆ K →
        (∫ z in (realChartDomain (completedRegion T) \ E) ∩ M i,
          fieldEnergy (circleGradient (F i)) g z) <
        (∫ z in (G \ E) ∩ M i, fieldEnergy (circleGradient (f i))
          (fun z => sphericalMetricFactor z • 1) z) + ε) ∧
      IsCircleDomain V ∧ IsSmoothSphereEquivalence φ φi (openCompletedRegion T) V ∧
      IsConformalOn φ (sphericalCore K) ∧ IsPrincipalNormalized φ ∧
      (∀ l, IsOpen (sphereRealMap φ '' (realChartDomain (openCompletedRegion T) ∩ interior (M l))) ∧
        SmoothCircleOn (F l ∘ sphereRealMap φi)
          (sphereRealMap φ '' (realChartDomain (openCompletedRegion T) ∩ interior (M l))) ∧
        (∀ x ∈ realChartDomain (openCompletedRegion T) ∩ interior (M l),
          ((F l ∘ sphereRealMap φi) ∘ sphereRealMap φ) =ᶠ[𝓝 x] F l)) ∧
      (∀ l (s : Set (ℝ × ℝ)), MeasurableSet s →
        s ⊆ realChartDomain (openCompletedRegion T) ∩ interior (M l) →
        (∫ y in sphereRealMap φ '' s,
          fieldEnergy (circleGradient (F l ∘ sphereRealMap φi)) (fun _ => 1) y) =
        ∫ x in s, fieldEnergy (circleGradient (F l)) g x) ∧
      ∃ W : A → (ℝ × ℝ) → ℝ,
        IsFilledCoordinateFamily D (G ∪ ⋃ i, D i)
          (fun j => cutoffStaircase (r j) χ (shiftedStaircase (reciprocalGridStep N)
            (staircaseWidth (reciprocalGridStep N) k) (θ (ι j)))) W ∧
        (∀ j x, (W j x : UnitAddCircle) = F (ι j) x) ∧
        (∀ᶠ x in 𝓝ˢ K, ∀ j, W j x = r j x) ∧
        (∀ j, ContDiffOn ℝ ∞ (W j ∘ sphereRealMap φi) (realChartDomain V) ∧
          ∀ x ∈ realChartDomain (openCompletedRegion T),
            ((W j ∘ sphereRealMap φi) ∘ sphereRealMap φ) =ᶠ[𝓝 x] W j) ∧
        (∀ j (s : Set (ℝ × ℝ)), MeasurableSet s → s ⊆ realChartDomain (openCompletedRegion T) →
          (∫ y in sphereRealMap φ '' s, gradientEnergy (W j ∘ sphereRealMap φi) (fun _ => 1) y) =
            ∫ x in s, gradientEnergy (W j) g x) ∧
        (∀ p ∈ openCompletedRegion T, IsMetricConformalAt g φ p) := by
  obtain ⟨k, F, R, g, hlate, hfill, hretain, hR, hg, hPD, hcore, hfar, htail, hlocal, W, hW, hWproj, hWretain⟩ :=
    transfer_actual_mixed_cutoff D hD hdisj hfrontc hfrontconn hG
      (isClosed_real_completedRegion T) hK hKc hKG hcover hKD M hM hboundary f hf hf2
      χ hχ hχzero O hO hDO hχone u hu hproj N active θ havoid ι hι r hr hrproj hreal hvi hgood k₀
  obtain ⟨V, φ, φi, hV, heq, hconf, hnorm, hcoordinates, henergy, hWcoords, hWenergy, hmetric⟩ :=
    finite_metric_model_with_mixed_fillings hcompact hfinite T hTdisj hKQ hcover
      g hg hPD ⟨R, hR, hfar⟩ hcore hfill W hW.1
  exact ⟨k, F, R, g, V, φ, φi, hlate, hfill, hretain, hR, hg, hPD, hcore, hfar,
    htail, hlocal, hV, heq, hconf, hnorm, hcoordinates, henergy,
    W, hW, hWproj, hWretain, hWcoords, hWenergy, hmetric⟩

end CircleDomainRigidity.FiniteTransfer

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Transfer_PrincipalAbsentMixedTransfer
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonEmbeddedArc.Arc.graphVertices_finite _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions _root_.OAI.CircleDomainRigidity.finiteSphericalArea _root_.OAI.CircleDomainRigidity.sphereFirstCountableTopology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Exterior replacements preserve every full-mask real coordinate,
including its exact real collar branch and its transported real filling. -/

open Set Filter Function MeasureTheory
open scoped Topology ContDiff Matrix.Norms.Elementwise
noncomputable section
namespace CircleDomainRigidity.FiniteTransfer

theorem principal_absent_mixed_transfer
    (hcompact : SmoothCompactMetricSphereUniformization) (hfinite : FiniteJordanModelUniformization)
    {J : Type*} [Finite J] (T : J → ℂ ≃ₜ ℂ)
    (hTdisj : Pairwise (Disjoint on fun j => closure (jordanInterior (T j))))
    {I : Type*} [Fintype I] {n : ℕ}
    (D : I → Set (ℝ × ℝ)) (hD : ∀ i, IsOpen (D i))
    (hdisj : Pairwise (Disjoint on fun i => closure (D i)))
    (hfrontc : ∀ i, IsCompact (frontier (D i)))
    (hfrontconn : ∀ i, IsConnected (frontier (D i)))
    {G K : Set (ℝ × ℝ)} (hG : IsOpen G)
    (hK : IsClosed K) (hKc : IsCompact (closure Kᶜ)) (hKG : K ⊆ G)
    (hKQ : sphericalCore K ⊆ openCompletedRegion T)
    (hcover : realChartDomain (completedRegion T) ⊆ G ∪ ⋃ i, D i)
    (hKD : ∀ x ∈ K, ∀ i, x ∉ D i)
    (M : Fin n → Set (ℝ × ℝ)) (hM : ∀ i, IsClosed (M i))
    (hboundary : ∀ i, frontier (M i) ⊆ interior K)
    (f : Fin n → (ℝ × ℝ) → UnitAddCircle)
    (hf : ∀ l, SmoothCircleOn (f l) (G ∩ interior (M l)))
    (hf2 : ∀ l, MemLp (circleGradient (f l)) 2 (volume.restrict (G ∩ M l)))
    (χ : (ℝ × ℝ) → ℝ) (hχ : ContDiff ℝ ∞ χ)
    (hχzero : ∀ᶠ x in 𝓝ˢ K, χ x = 0)
    (O : I → Set (ℝ × ℝ)) (hO : ∀ i, IsOpen (O i))
    (hDO : ∀ i, frontier (D i) ⊆ O i)
    (hχone : ∀ i x, x ∈ O i → χ x = 1)
    (hOK : ∀ i, Disjoint (O i) K)
    (present : I → Fin n → Prop)
    (habsent : ∀ i l, ¬present i l → Disjoint (O i) (M l))
    (u : I → Fin n → (ℝ × ℝ) → ℝ) (hu : ∀ i l, present i l → ContDiffOn ℝ ∞ (u i l) (O i))
    (hproj : ∀ i l, present i l → ∀ x, x ∈ O i → (u i l x : UnitAddCircle) = f l x)
    (N : ℕ) (active : I → Fin n) (θ : Fin n → ℝ)
    (havoid : ∀ i l, present i l → l ≠ active i →
      Disjoint (u i l '' frontier (D i)) (shiftedLattice (reciprocalGridStep N) (θ l)))
    {A : Type*} [Fintype A] (ι : A → Fin n) (hι : Injective ι)
    (r : A → (ℝ × ℝ) → ℝ) (hr : ∀ j, ContDiffOn ℝ ∞ (r j) G)
    (hRM : ∀ j, M (ι j) = univ)
    (hrproj : ∀ j x, (r j x : UnitAddCircle) = f (ι j) x)
    (hreal : ∀ i j, EqOn (u i (ι j)) (r j) (O i))
    (hvi : ∀ k, IntegrableOn (maskedCircleWedges M (circleCutoffFamily f χ N
      (staircaseWidth (reciprocalGridStep N) k) θ)) (G \ K))
    {ε : ℝ} (hgood : ∃ᶠ k in atTop, (∫ z in G \ K, maskedCircleWedges M
      (circleCutoffFamily f χ N (staircaseWidth (reciprocalGridStep N) k) θ) z) < ε / 2)
    (k₀ : ℕ) :
    ∃ f₀ : Fin n → (ℝ × ℝ) → UnitAddCircle,
      (∀ l, f₀ l =ᶠ[𝓝ˢ (M l)] f l) ∧
      (∀ᶠ z in 𝓝ˢ K, ∀ l, f₀ l z = f l z) ∧
    ∃ (k : ℕ) (F : Fin n → (ℝ × ℝ) → UnitAddCircle)
      (R : ℝ) (g : (ℝ × ℝ) → PlanarMetric)
      (V : Set Sphere) (φ φi : Sphere → Sphere),
      k₀ ≤ k ∧ IsMaskedFilledCircleFamily D (G ∪ ⋃ i, D i) M
        (circleCutoffFamily f₀ χ N (staircaseWidth (reciprocalGridStep N) k) θ) F ∧
      (∀ᶠ z in 𝓝ˢ K, ∀ i, F i z = f i z) ∧
      0 < R ∧ ContDiff ℝ ∞ g ∧ (∀ z, (g z).PosDef) ∧
      (∀ᶠ z in 𝓝ˢ K, g z = sphericalMetricFactor z • 1) ∧
      (∀ z ∉ Metric.closedBall 0 R, g z = sphericalMetricFactor z • 1) ∧
      (∑ i : Fin n, ∫ z in (realChartDomain (completedRegion T) \ K) ∩ M i,
        fieldEnergy (circleGradient (F i)) g z) < ε ∧
      (∀ i : Fin n, ∀ E : Set (ℝ × ℝ), MeasurableSet E → E ⊆ K →
        (∫ z in (realChartDomain (completedRegion T) \ E) ∩ M i,
          fieldEnergy (circleGradient (F i)) g z) <
        (∫ z in (G \ E) ∩ M i, fieldEnergy (circleGradient (f i))
          (fun z => sphericalMetricFactor z • 1) z) + ε) ∧
      IsCircleDomain V ∧ IsSmoothSphereEquivalence φ φi (openCompletedRegion T) V ∧
      IsConformalOn φ (sphericalCore K) ∧ IsPrincipalNormalized φ ∧
      (∀ l, IsOpen (sphereRealMap φ '' (realChartDomain (openCompletedRegion T) ∩ interior (M l))) ∧
        SmoothCircleOn (F l ∘ sphereRealMap φi)
          (sphereRealMap φ '' (realChartDomain (openCompletedRegion T) ∩ interior (M l))) ∧
        (∀ x ∈ realChartDomain (openCompletedRegion T) ∩ interior (M l),
          ((F l ∘ sphereRealMap φi) ∘ sphereRealMap φ) =ᶠ[𝓝 x] F l)) ∧
      (∀ l (s : Set (ℝ × ℝ)), MeasurableSet s →
        s ⊆ realChartDomain (openCompletedRegion T) ∩ interior (M l) →
        (∫ y in sphereRealMap φ '' s,
          fieldEnergy (circleGradient (F l ∘ sphereRealMap φi)) (fun _ => 1) y) =
        ∫ x in s, fieldEnergy (circleGradient (F l)) g x) ∧
      ∃ W : A → (ℝ × ℝ) → ℝ,
        IsFilledCoordinateFamily D (G ∪ ⋃ i, D i)
          (fun j => cutoffStaircase (r j) χ (shiftedStaircase (reciprocalGridStep N)
            (staircaseWidth (reciprocalGridStep N) k) (θ (ι j)))) W ∧
        (∀ j x, (W j x : UnitAddCircle) = F (ι j) x) ∧
        (∀ᶠ x in 𝓝ˢ K, ∀ j, W j x = r j x) ∧
        (∀ j, ContDiffOn ℝ ∞ (W j ∘ sphereRealMap φi) (realChartDomain V) ∧
          ∀ x ∈ realChartDomain (openCompletedRegion T),
            ((W j ∘ sphereRealMap φi) ∘ sphereRealMap φ) =ᶠ[𝓝 x] W j) ∧
        (∀ j (s : Set (ℝ × ℝ)), MeasurableSet s → s ⊆ realChartDomain (openCompletedRegion T) →
          (∫ y in sphereRealMap φ '' s, gradientEnergy (W j ∘ sphereRealMap φi) (fun _ => 1) y) =
            ∫ x in s, gradientEnergy (W j) g x) ∧
        (∀ p ∈ openCompletedRegion T, IsMetricConformalAt g φ p) := by
  classical
  have hBd : Pairwise (Disjoint on fun i => frontier (D i)) :=
    fun i j hij => (hdisj hij).mono frontier_subset_closure frontier_subset_closure
  obtain ⟨V, W, v, hV, hW, hv, hvproj, hvavoid, hvreal⟩ := exists_mask_branch_collars
    (fun i => frontier (D i)) hfrontc hBd O hO hDO hOK M f present habsent u hu hproj
      (reciprocalGridStep_pos N) θ active havoid
  let f₀ : Fin n → (ℝ × ℝ) → UnitAddCircle := fun l =>
    exteriorMaskReplacement (W l) ((θ l + reciprocalGridStep N / 2 : ℝ) : UnitAddCircle) (f l)
  have heqM (l : Fin n) : f₀ l =ᶠ[𝓝ˢ (M l)] f l :=
    exteriorMaskReplacement_eventuallyEq (hW l).1 (hW l).2.1 _ _
  have heqK : ∀ᶠ z in 𝓝ˢ K, ∀ l, f₀ l z = f l z :=
    eventually_all.mpr fun l =>
      exteriorMaskReplacement_eventuallyEq (hW l).1 (hW l).2.2 _ _
  have hgrad (l : Fin n) (z : ℝ × ℝ) (hz : z ∈ M l) :
      circleGradient (f₀ l) z = circleGradient (f l) z :=
    exteriorMaskReplacement_gradient (hW l).1 (hW l).2.1 _ _ hz
  have hcost (k : ℕ) : maskedCircleWedges M
      (circleCutoffFamily f₀ χ N (staircaseWidth (reciprocalGridStep N) k) θ) =
      maskedCircleWedges M (circleCutoffFamily f χ N
        (staircaseWidth (reciprocalGridStep N) k) θ) :=
    exteriorMaskReplacement_masked_wedges W M (fun l => (hW l).1)
      (fun l => (hW l).2.1) _ f χ N _ θ
  have hpres (i : I) (j : A) : present i (ι j) := by
    by_contra hp
    obtain ⟨x, hx⟩ := (hfrontconn i).nonempty
    exact Set.disjoint_left.mp (habsent i (ι j) hp) (hDO i hx) (by rw [hRM]; trivial)
  have hrproj₀ (j : A) (x : ℝ × ℝ) : (r j x : UnitAddCircle) = f₀ (ι j) x := by
    exact (hrproj j x).trans ((heqM (ι j)).self_of_nhdsSet (by rw [hRM]; trivial)).symm
  obtain ⟨k, F, R, g, V₀, φ, φi, hlate, hfill, hretain, hR, hg, hPD, hcore, hfar,
      htail, hlocal, hV₀, heq, hconf, hnorm, hcoordinates, henergy,
      Wreal, hWreal, hWproj, hWretain, hWcoords, hWenergy, hmetric⟩ :=
    principal_actual_mixed_transfer hcompact hfinite T hTdisj D hD hdisj hfrontc hfrontconn
      hG hK hKc hKG hKQ hcover hKD M hM hboundary f₀
      (fun l => exteriorMaskReplacement_smooth (hW l).1 (hW l).2.1 _ _ (hf l))
      (fun l => exteriorMaskReplacement_memLp (hW l).1 (hW l).2.1
        hG.measurableSet (hM l).measurableSet _ _ (hf2 l))
      χ hχ hχzero V (fun i => (hV i).1) (fun i => (hV i).2.1)
      (fun i z hz => hχone i z ((hV i).2.2 hz)) v hv hvproj N active θ hvavoid
      ι hι r hr hrproj₀
      (fun i j x hx => (hvreal i (ι j) (hpres i j) hx).trans
        (hreal i j ((hV i).2.2 hx)))
      (fun k => by rw [hcost k]; exact hvi k)
      (hgood.mono fun k hk => by rw [hcost k]; exact hk) k₀
  refine ⟨f₀, heqM, heqK, k, F, R, g, V₀, φ, φi, hlate, hfill, ?_, hR, hg, hPD,
    hcore, hfar, htail, ?_, hV₀, heq, hconf, hnorm, hcoordinates, henergy,
    Wreal, hWreal, hWproj, hWretain, hWcoords, hWenergy, hmetric⟩
  · filter_upwards [hretain, heqK] with z hz he l
    exact (hz l).trans (he l)
  · intro l E hE hEK
    have hi := hlocal l E hE hEK
    have he : (∫ z in (G \ E) ∩ M l, fieldEnergy (circleGradient (f₀ l))
        (fun z => sphericalMetricFactor z • 1) z) =
        ∫ z in (G \ E) ∩ M l, fieldEnergy (circleGradient (f l))
          (fun z => sphericalMetricFactor z • 1) z := by
      apply setIntegral_congr_fun ((hG.measurableSet.diff hE).inter (hM l).measurableSet)
      intro z hz
      simp only [fieldEnergy, hgrad l z hz.2]
    rwa [he] at hi

end CircleDomainRigidity.FiniteTransfer

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Transfer_PrincipalSubordinateMixedTransfer
attribute [-instance] _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions _root_.OAI.CircleDomainRigidity.finiteSphericalArea _root_.OAI.CircleDomainRigidity.sphereFirstCountableTopology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Construct the common mixed model from subordinate graph geometry,
using the original global real branches at every real coordinate. -/

open Set Filter Function MeasureTheory
open scoped Topology ContDiff Matrix.Norms.Elementwise
noncomputable section
namespace CircleDomainRigidity.FiniteTransfer

theorem principal_subordinate_mixed_transfer
    (hcompact : SmoothCompactMetricSphereUniformization) (hfinite : FiniteJordanModelUniformization)
    {J : Type*} [Finite J] (T : J → ℂ ≃ₜ ℂ)
    (hTdisj : Pairwise (Disjoint on fun j => closure (jordanInterior (T j))))
    {I : Type*} [Fintype I] {n : ℕ} (hn : 0 < n)
    (D : I → Set (ℝ × ℝ)) (hD : ∀ i, IsOpen (D i))
    (hdisj : Pairwise (Disjoint on fun i => closure (D i)))
    (hfrontc : ∀ i, IsCompact (frontier (D i)))
    (hfrontconn : ∀ i, IsConnected (frontier (D i)))
    {G K : Set (ℝ × ℝ)} (hG : IsOpen G)
    (hK : IsClosed K) (hKc : IsCompact (closure Kᶜ)) (hKG : K ⊆ G)
    (hKQ : sphericalCore K ⊆ openCompletedRegion T)
    (hcover : realChartDomain (completedRegion T) ⊆ G ∪ ⋃ i, D i)
    (hKD : ∀ x ∈ K, ∀ i, x ∉ D i)
    (M : Fin n → Set (ℝ × ℝ)) (hM : ∀ i, IsClosed (M i))
    (hboundary : ∀ i, frontier (M i) ⊆ interior K)
    (f : Fin n → (ℝ × ℝ) → UnitAddCircle)
    (hf : ∀ l, SmoothCircleOn (f l) (G ∩ interior (M l)))
    (hf2 : ∀ l, MemLp (circleGradient (f l)) 2 (volume.restrict (G ∩ M l)))
    (χ : (ℝ × ℝ) → ℝ) (hχ : ContDiff ℝ ∞ χ)
    (hχzero : ∀ᶠ x in 𝓝ˢ K, χ x = 0)
    (L : Fin n → Type*) (P : ∀ l, L l → Set (ℝ × ℝ))
    (v : ∀ l, L l → (ℝ × ℝ) → ℝ)
    (hv : ∀ l a, ContDiffOn ℝ ∞ (v l a) (G ∩ P l a))
    (hproj : ∀ l a x, x ∈ G ∩ P l a → (v l a x : UnitAddCircle) = f l x)
    (Nbh : I → Set (ℝ × ℝ)) (hNbh : ∀ i, IsOpen (Nbh i))
    (hBN : ∀ i, frontier (D i) ⊆ Nbh i)
    (hbranch : ∀ i l, Disjoint (Nbh i) (M l) ∨
      ∃ a, Nbh i ⊆ interior (M l) ∩ P l a)
    (hBG : ∀ i, frontier (D i) ⊆ G)
    (hBK : ∀ i, Disjoint (frontier (D i)) K)
    (hBχ : ∀ i, frontier (D i) ⊆ interior {x | χ x = 1})
    (R : Fin n → Set (Sphere × UnitAddCircle)) (q : (ℝ × ℝ) → Sphere)
    (hgraph : ∀ l x, x ∈ G ∩ interior (M l) → (q x, f l x) ∈ R l)
    (N : ℕ) (θ : Fin n → ℝ)
    (hgrid : ∀ i, ∃ k : ℕ, ∀ l : Fin n, l.val ≠ k →
      Disjoint (frontier (D i)) (q ⁻¹' (⋃ j, reciprocalGraphLevel (R l) (θ l) N j)))
    {A : Type*} [Fintype A] (ι : A → Fin n) (hι : Injective ι)
    (r : A → (ℝ × ℝ) → ℝ) (hr : ∀ j, ContDiffOn ℝ ∞ (r j) G)
    (hRM : ∀ j, M (ι j) = univ)
    (hrproj : ∀ j x, (r j x : UnitAddCircle) = f (ι j) x)
    (hvi : ∀ k, IntegrableOn (maskedCircleWedges M (circleCutoffFamily f χ N
      (staircaseWidth (reciprocalGridStep N) k) θ)) (G \ K))
    {ε : ℝ} (hgood : ∃ᶠ k in atTop, (∫ z in G \ K, maskedCircleWedges M
      (circleCutoffFamily f χ N (staircaseWidth (reciprocalGridStep N) k) θ) z) < ε / 2)
    (k₀ : ℕ) :
    ∃ f₀ : Fin n → (ℝ × ℝ) → UnitAddCircle,
      (∀ l, f₀ l =ᶠ[𝓝ˢ (M l)] f l) ∧
      (∀ᶠ z in 𝓝ˢ K, ∀ l, f₀ l z = f l z) ∧
    ∃ (k : ℕ) (F : Fin n → (ℝ × ℝ) → UnitAddCircle)
      (R : ℝ) (g : (ℝ × ℝ) → PlanarMetric)
      (V : Set Sphere) (φ φi : Sphere → Sphere),
      k₀ ≤ k ∧ IsMaskedFilledCircleFamily D (G ∪ ⋃ i, D i) M
        (circleCutoffFamily f₀ χ N (staircaseWidth (reciprocalGridStep N) k) θ) F ∧
      (∀ᶠ z in 𝓝ˢ K, ∀ i, F i z = f i z) ∧
      0 < R ∧ ContDiff ℝ ∞ g ∧ (∀ z, (g z).PosDef) ∧
      (∀ᶠ z in 𝓝ˢ K, g z = sphericalMetricFactor z • 1) ∧
      (∀ z ∉ Metric.closedBall 0 R, g z = sphericalMetricFactor z • 1) ∧
      (∑ i : Fin n, ∫ z in (realChartDomain (completedRegion T) \ K) ∩ M i,
        fieldEnergy (circleGradient (F i)) g z) < ε ∧
      (∀ i : Fin n, ∀ E : Set (ℝ × ℝ), MeasurableSet E → E ⊆ K →
        (∫ z in (realChartDomain (completedRegion T) \ E) ∩ M i,
          fieldEnergy (circleGradient (F i)) g z) <
        (∫ z in (G \ E) ∩ M i, fieldEnergy (circleGradient (f i))
          (fun z => sphericalMetricFactor z • 1) z) + ε) ∧
      IsCircleDomain V ∧ IsSmoothSphereEquivalence φ φi (openCompletedRegion T) V ∧
      IsConformalOn φ (sphericalCore K) ∧ IsPrincipalNormalized φ ∧
      (∀ l, IsOpen (sphereRealMap φ '' (realChartDomain (openCompletedRegion T) ∩ interior (M l))) ∧
        SmoothCircleOn (F l ∘ sphereRealMap φi)
          (sphereRealMap φ '' (realChartDomain (openCompletedRegion T) ∩ interior (M l))) ∧
        (∀ x ∈ realChartDomain (openCompletedRegion T) ∩ interior (M l),
          ((F l ∘ sphereRealMap φi) ∘ sphereRealMap φ) =ᶠ[𝓝 x] F l)) ∧
      (∀ l (s : Set (ℝ × ℝ)), MeasurableSet s →
        s ⊆ realChartDomain (openCompletedRegion T) ∩ interior (M l) →
        (∫ y in sphereRealMap φ '' s,
          fieldEnergy (circleGradient (F l ∘ sphereRealMap φi)) (fun _ => 1) y) =
        ∫ x in s, fieldEnergy (circleGradient (F l)) g x) ∧
      ∃ W : A → (ℝ × ℝ) → ℝ,
        IsFilledCoordinateFamily D (G ∪ ⋃ i, D i)
          (fun j => cutoffStaircase (r j) χ (shiftedStaircase (reciprocalGridStep N)
            (staircaseWidth (reciprocalGridStep N) k) (θ (ι j)))) W ∧
        (∀ j x, (W j x : UnitAddCircle) = F (ι j) x) ∧
        (∀ᶠ x in 𝓝ˢ K, ∀ j, W j x = r j x) ∧
        (∀ j, ContDiffOn ℝ ∞ (W j ∘ sphereRealMap φi) (realChartDomain V) ∧
          ∀ x ∈ realChartDomain (openCompletedRegion T),
            ((W j ∘ sphereRealMap φi) ∘ sphereRealMap φ) =ᶠ[𝓝 x] W j) ∧
        (∀ j (s : Set (ℝ × ℝ)), MeasurableSet s → s ⊆ realChartDomain (openCompletedRegion T) →
          (∫ y in sphereRealMap φ '' s, gradientEnergy (W j ∘ sphereRealMap φi) (fun _ => 1) y) =
            ∫ x in s, gradientEnergy (W j) g x) ∧
        (∀ p ∈ openCompletedRegion T, IsMetricConformalAt g φ p) := by
  classical
  obtain ⟨O, present, u, hO, habsent, hu, hproj', hOM, hreal⟩ :=
    exists_real_preserving_subordinate_branches L G K hG hK M f P v hv hproj
      (fun i => frontier (D i)) Nbh hNbh hBN hbranch χ hBG hBK hBχ ι hι r hr hrproj
  have hex (i : I) : ∃ a : Fin n, ∀ l, l ≠ a →
      (present i l → Disjoint (u i l '' frontier (D i))
        (shiftedLattice (reciprocalGridStep N) (θ l))) := by
    apply exists_active_coordinate_of_single_exception hn
    obtain ⟨k, hk⟩ := hgrid i
    refine ⟨k, fun l hl hp => ?_⟩
    apply Set.disjoint_left.mpr
    rintro r ⟨x, hx, rfl⟩ hr
    obtain ⟨j, hj⟩ := exists_reciprocal_level_of_mem_lattice hr
    apply Set.disjoint_left.mp (hk l hl) hx
    refine mem_iUnion.mpr ⟨j, ?_⟩
    change (q x, ((θ l + (j.val : ℝ) * reciprocalGridStep N : ℝ) : UnitAddCircle)) ∈ R l
    rw [← hj, hproj' i l hp x ((hO i).2.1 hx)]
    exact hgraph l x ⟨hBG i hx, hOM i l hp ((hO i).2.1 hx)⟩
  choose active hactive using hex
  exact principal_absent_mixed_transfer hcompact hfinite T hTdisj
    D hD hdisj hfrontc hfrontconn hG hK hKc hKG hKQ hcover hKD
    M hM hboundary f hf hf2 χ hχ hχzero O (fun i => (hO i).1)
    (fun i => (hO i).2.1) (fun i => (hO i).2.2.2.2)
    (fun i => (hO i).2.2.2.1) present habsent u hu hproj' N active θ
    (fun i l hp hl => hactive i l hl hp)
    ι hι r hr hRM hrproj (fun i j x _ => congrFun (hreal i j) x) hvi hgood k₀

end CircleDomainRigidity.FiniteTransfer

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Transfer_AssembledMixedModel
attribute [-instance] _root_.Graph.instFiniteElemEdgeSetOfFinite _root_.Graph.instFiniteElemVertexSetOfFinite _root_.OAI.CannonEmbeddedArc.Arc.graphVertices_finite _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions _root_.OAI.CircleDomainRigidity.finiteSphericalArea _root_.OAI.CircleDomainRigidity.sphereFirstCountableTopology
attribute [-simp] _root_.OAI.CircleDomainRigidity.CompactScalarModel.postcompose_coefficient _root_.OAI.CircleDomainRigidity.extendAtInfinity_coe _root_.OAI.CircleDomainRigidity.extendAtInfinity_infty _root_.OAI.CircleDomainRigidity.metricBeltramiCoefficient_scalar
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! One common geometric and metric model, retaining the exact real
barriers in addition to all masked period coordinates. -/

open Set Function Filter MeasureTheory
open scoped Topology ContDiff Matrix.Norms.Elementwise
noncomputable section
namespace CircleDomainRigidity.FiniteTransfer

 theorem exists_assembled_mixed_model
    (hsard : SmoothPlanarSard) (hsch : PlanarSchoenflies) (hcompact : SmoothCompactMetricSphereUniformization)
    (hfinite : FiniteJordanModelUniformization)
    (G : Set Sphere) (hG : IsOpen G) (hinfty : OnePoint.infty ∈ G)
    (π : Sphere → Sphere) (hπ : Continuous π) (hclosed : IsClosedMap π) (hsurj : Surjective π)
    (hr : ∀ x y, π x = π y ↔ x = y ∨ (x ∈ Gᶜ ∧ y ∈ connectedComponentIn Gᶜ x))
    (hTD : IsTotallyDisconnected (π '' Gᶜ))
    {K₀ : Set (ℝ × ℝ)} (hK₀ : IsClosed K₀) (hK₀G : K₀ ⊆ realChartDomain G)
    {n : ℕ} (hn : 0 < n) {S : Type*} [Countable S]
    (R : Fin n → Set (Sphere × UnitAddCircle)) (hR : ∀ l, IsClosed (R l))
    (σ : S → Sphere) (hσ : Injective σ) (hσB : ∀ s, σ s ∈ π '' Gᶜ)
    (a b : Fin n → S → ℝ) (Flag : Set S) (hFlag : Flag.Finite)
    (hwidth : ∀ l s, 0 ≤ b l s - a l s)
    (hwidth2 : ∀ l, Summable (fun s => (b l s - a l s) ^ 2))
    (hband : ∀ l s, {t : UnitAddCircle | (σ s, t) ∈ R l} ⊆
      ((↑) : ℝ → UnitAddCircle) '' Icc (a l s) (b l s))
    (L : Fin n → Type*) (Mask : Fin n → Set Sphere) (hMask : ∀ l, IsClosed (Mask l))
    (hboundary : ∀ l, frontier (Mask l) ⊆ (π '' Gᶜ)ᶜ)
    (singular : Fin n → S) (hflag : ∀ l, singular l ∈ Flag)
    (P : ∀ l, L l → Set Sphere) (hP : ∀ l i, IsOpen (P l i))
    (hcover : ∀ l, Mask l \ {σ (singular l)} ⊆ ⋃ i, P l i)
    (f : Fin n → (ℝ × ℝ) → UnitAddCircle)
    (hf : ∀ l, SmoothCircleOn (f l) (realChartDomain G ∩ interior (physicalMask π (Mask l))))
    (hmf : ∀ l, Measurable (f l)) (hdf : ∀ l, Measurable (circleGradient (f l)))
    (hf2 : ∀ l, MemLp (circleGradient (f l)) 2
      ((volume.restrict (realChartDomain G)).restrict (physicalMask π (Mask l))))
    (vp : ∀ l, L l → (ℝ × ℝ) → ℝ)
    (hvp : ∀ l i, ContDiffOn ℝ ∞ (vp l i)
      (realChartDomain G ∩ realChartDomain (π ⁻¹' P l i)))
    (hproj : ∀ l i x, x ∈ realChartDomain G ∩ realChartDomain (π ⁻¹' P l i) →
      (vp l i x : UnitAddCircle) = f l x)
    (hgraph : ∀ l x, x ∈ realChartDomain G ∩ interior (physicalMask π (Mask l)) →
      (π (Complex.equivRealProdCLM.symm x : Sphere), f l x) ∈ R l)
    {J : Type*} [Fintype J] (ι : J → Fin n) (hι : Injective ι)
    (real : J → (ℝ × ℝ) → ℝ)
    (hreal : ∀ j, ContDiffOn ℝ ∞ (real j) (realChartDomain G))
    (hRealMask : ∀ j, Mask (ι j) = univ)
    (hRealProj : ∀ j x, (real j x : UnitAddCircle) = f (ι j) x)
    (O : S → Set Sphere) (hO : ∀ s, O s ∈ 𝓝 (σ s))
    (U : S → Set Sphere) (v : S → Fin n → Sphere → ℝ) (B : S → Fin n → ℝ)
    (hbounded : ∀ s l x, x ∈ U s → |v s l x| ≤ B s l)
    (hphysical : ∀ s (z : ℂ), (z : Sphere) ∈ G → π (z : Sphere) ∈ O s → π (z : Sphere) ∈ U s)
    (active : S → Fin n → Prop)
    (hbudget : ∀ s l, active s l →
      limsup (v s l) (𝓝[U s] (σ s)) - liminf (v s l) (𝓝[U s] (σ s)) ≤ b l s - a l s)
    (hfree : ∀ x ∈ π '' Gᶜ, x ∉ range σ → ∀ l, {t : UnitAddCircle | (x, t) ∈ R l}.Subsingleton)
    (hcompat : ∀ (j : Fin n) (d : ℕ) (labels : Fin d → Fin n),
      (∀ i, (labels i).val < j.val) →
      (volume.prod (Measure.pi (fun _ : Fin d => (volume : Measure UnitAddCircle))))
        (freeComponentFailure ((π '' Gᶜ) \ range σ) (R j) R labels) = 0)
    {ε ρ : ℝ} (hε : 0 < ε) (hρ : 0 < ρ) (k₀ : ℕ) :
    ∃ (K : Set (ℝ × ℝ)) (χ : (ℝ × ℝ) → ℝ) (N : ℕ) (θ : Fin n → ℝ),
      let A := gridTerminalIndices Flag (reciprocalGridStep N) upperPair a b θ
      A.Finite ∧ ∃ (D : PhysicalTerminalDisks G π (π '' Gᶜ) (fun s : A => σ s) (fun s => O s))
        (m : ℕ) (H : Fin m → ℂ ≃ₜ ℂ)
        (Q : MaskedModelData D.H H (realChartDomain G) K
          (fun l => physicalMask π (Mask l)) f χ N θ ε)
        (_W : ModelRealSubfamily Q ι real),
        k₀ ≤ Q.widthIndex ∧ IsClosed K ∧ K₀ ⊆ interior K ∧ K ⊆ realChartDomain G ∧
        IsCompact (closure Kᶜ) ∧ sphericalCore K ⊆ openCompletedRegion D.H ∧
        (∀ l, frontier (physicalMask π (Mask l)) ⊆ interior K) ∧
        ContDiff ℝ ∞ χ ∧ (∀ᶠ z in 𝓝ˢ K, χ z = 0) ∧
        (∀ s, Disjoint (closedTerminalCap (D.H s)) (cutoffCore χ)) ∧
        (∀ s j, Disjoint (closure (jordanInterior (D.H s))) (closure (jordanInterior (H j)))) ∧
        reciprocalGridStep N < ρ ∧ reciprocalGridStep N * Real.sqrt (A.ncard : ℝ) < ε / 8 ∧
        ∀ (s : A) l, active s l → ∀ δ η : ℝ,
          ∀ x ∈ frontier (jordanInterior (D.H s)), ∀ y ∈ frontier (jordanInterior (D.H s)),
          |shiftedStaircase (reciprocalGridStep N) δ η (v s l (π (x : Sphere))) -
            shiftedStaircase (reciprocalGridStep N) δ η (v s l (π (y : Sphere)))| ≤
              b l s - a l s + 4 * reciprocalGridStep N := by
  classical
  let q : ℂ → Sphere := fun z => π (z : Sphere)
  let qr : (ℝ × ℝ) → Sphere := q ∘ Complex.equivRealProdCLM.symm
  have hq : Continuous q := hπ.comp OnePoint.continuous_coe
  have hqr : Continuous qr := hq.comp Complex.equivRealProdCLM.symm.continuous
  let Mm : Fin n → Set (ℝ × ℝ) := fun l => physicalMask π (Mask l)
  have hMm (l : Fin n) : IsClosed (Mm l) := (hMask l).preimage hqr
  have hMmB (l : Fin n) : frontier (Mm l) ⊆ realChartDomain G := by
    intro x hx
    have hm := hqr.frontier_preimage_subset (Mask l) hx
    have hn := hboundary l hm
    change (Complex.equivRealProdCLM.symm x : Sphere) ∈ G
    by_contra hg
    exact hn ⟨(Complex.equivRealProdCLM.symm x : Sphere), hg, rfl⟩
  obtain ⟨K, χ, N, θ, hK, hK₀K, hKG, hKc, hbd, hχ, hχzero, hχone, hN, hfin, hcard,
      hvi, hgood, D, m, H, γ, hD, hCQ, hosc, hHd, hDH, hHC, hcov, _, _, hcurves⟩ :=
    exists_prepared_mask_atlas_geometry hsard hsch G hG π hπ hclosed hsurj hr hTD
      hinfty hK₀ hK₀G R hR σ hσ hσB a b Flag hFlag hwidth hwidth2 hband
      Mm (fun l => (hMm l).measurableSet) hMmB f hf hmf hdf hf2
      O hO U v B hbounded hphysical active hbudget hfree hcompat L Mask hMask hboundary
      singular hflag P hP hcover (div_pos hε (by norm_num : (0 : ℝ) < 8)) hρ
  let A := gridTerminalIndices Flag (reciprocalGridStep N) upperPair a b θ
  let : Fintype A := hfin.fintype
  have hKQ : sphericalCore K ⊆ openCompletedRegion D.H :=
    (sphericalCore_subset_cutoffCore χ hχzero).trans hCQ
  have hbad : ∀ x ∈ Gᶜ, π x ∈ π '' Gᶜ := fun x hx => mem_image_of_mem π hx
  obtain ⟨Nbh, hNbh, hbranches⟩ := exists_real_cap_mask_neighborhoods H q hq L Mask hMask P hP
    (fun j => (hcurves j).2.2.2.2.2)
  have hbg := real_boundary_in_domain_and_plateau H χ
    (fun j z hz => ((hcurves j).2.2.2.1 z hz).1) hHC
  have hBG (j : Fin m) : frontier (realJordanInterior (H j)) ⊆ realChartDomain G := by
    rw [frontier_realJordanInterior]
    rintro x ⟨z, hz, rfl⟩
    exact (hbg j z hz).1
  have hBχ (j : Fin m) : frontier (realJordanInterior (H j)) ⊆ interior {x | χ x = 1} := by
    rw [frontier_realJordanInterior]
    rintro x ⟨z, hz, rfl⟩
    exact (hbg j z hz).2
  have hBK (j : Fin m) : Disjoint (frontier (realJordanInterior (H j))) K := by
    apply Set.disjoint_left.mpr
    intro x hx hk
    have h1 : χ x = 1 := (show x ∈ {x | χ x = 1} from interior_subset (hBχ j hx))
    have h0 := hχzero.self_of_nhdsSet x hk
    linarith
  have hgrid (j : Fin m) : ∃ k : ℕ, ∀ l : Fin n, l.val ≠ k →
      Disjoint (frontier (realJordanInterior (H j)))
        (qr ⁻¹' (⋃ r, reciprocalGraphLevel (R l) (θ l) N r)) := by
    obtain ⟨k, hk⟩ := (hcurves j).2.2.2.2.1
    refine ⟨k, fun l hl => ?_⟩
    apply Set.disjoint_left.mpr
    intro x hx hm
    rw [frontier_realJordanInterior] at hx
    obtain ⟨z, hz, rfl⟩ := hx
    exact Set.disjoint_left.mp (hk l hl) hz (by
      simpa only [qr, q, Function.comp_apply, mem_preimage, ContinuousLinearEquiv.symm_apply_apply] using hm)
  have h2 (l : Fin n) : MemLp (circleGradient (f l)) 2 (volume.restrict (realChartDomain G ∩ Mm l)) := by
    have hh := hf2 l
    change MemLp (circleGradient (f l)) 2 ((volume.restrict (realChartDomain G)).restrict (Mm l)) at hh
    simpa only [Measure.restrict_restrict (hMm l).measurableSet, inter_comm] using hh
  obtain ⟨f₀, heqM, heqK, k, F, r, g, V, φ, φi, hk, hF, hretain, hrpos, hg, hPD,
      hcore, hfar, htail, hlocal, hV, heq, hconf, hnorm, htrans, henergy,
      Wreal, hWreal, hWproj, hWretain, hWcoords, hWenergy, hmetric⟩ :=
    principal_subordinate_mixed_transfer (ε := ε) hcompact hfinite D.H D.disjoint_closures hn
      (fun j => realJordanInterior (H j)) (fun j => (realJordanInterior_geometry (H j)).1)
      (pairwise_disjoint_realJordan_closures H hHd)
      (fun j => (realJordanInterior_geometry (H j)).2.1)
      (fun j => (realJordanInterior_geometry (H j)).2.2) (isOpen_realChartDomain hG)
      hK hKc hKG hKQ (real_completedRegion_subset_extension D.H H G (π '' Gᶜ) π hbad hcov)
      (real_core_avoids_filling H (sphericalCore_subset_cutoffCore χ hχzero) hHC)
      Mm hMm hbd f hf h2 χ hχ hχzero L (fun l i => realChartDomain (π ⁻¹' P l i)) vp hvp hproj
      Nbh (fun j => (hNbh j).1) (fun j => (hNbh j).2) hbranches hBG hBK hBχ
      R qr hgraph N θ hgrid ι hι real hreal
      (fun j => by simp only [Mm, physicalMask, hRealMask, preimage_univ, realChartDomain])
      hRealProj hvi (hgood.mono fun k hk => hk.trans (by linarith)) k₀
  let Q : MaskedModelData D.H H (realChartDomain G) K Mm f χ N θ ε := {
    widthIndex := k, base := f₀, base_mask := heqM, base_core := heqK,
    functions := F, filled := hF,
    extension_contains := real_completedRegion_subset_extension D.H H G (π '' Gᶜ) π hbad hcov,
    mask_boundary_core := hbd, retained := hretain, radius := r, radius_pos := hrpos,
    metric := g, metric_smooth := hg, metric_pos := hPD, metric_core := hcore, metric_far := hfar,
    tail := htail, localized := hlocal, domain := V, forward := φ, inverse := φi,
    circle_domain := hV, equivalence := heq, conformal_core := hconf, principal := hnorm,
    transported := htrans, transported_energy := henergy }
  let W : ModelRealSubfamily Q ι real := {
    functions := Wreal, filled := hWreal,
    extension_contains := real_completedRegion_subset_extension D.H H G (π '' Gᶜ) π hbad hcov,
    projection := hWproj, retained := hWretain,
    transported := hWcoords, transported_energy := hWenergy, metric_conformal := hmetric }
  exact ⟨K, χ, N, θ, hfin, D, m, H, Q, W, hk, hK, hK₀K, hKG, hKc, hKQ, hbd,
    hχ, hχzero, hD, hDH, hN, hcard, hosc⟩

end CircleDomainRigidity.FiniteTransfer

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Transfer_ModelRealTerminals
attribute [-instance] _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions _root_.OAI.CircleDomainRigidity.finiteSphericalArea _root_.OAI.CircleDomainRigidity.sphereFirstCountableTopology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Actual boundary oscillation control for the preserved real barriers
of a mixed model. -/

open Set Function Filter
open scoped Topology
noncomputable section
namespace CircleDomainRigidity.FiniteTransfer

variable {J I A : Type*} {n N : ℕ} {T : J → ℂ ≃ₜ ℂ} {H : I → ℂ ≃ₜ ℂ}
  {G K : Set (ℝ × ℝ)} {M : Fin n → Set (ℝ × ℝ)}
  {f : Fin n → (ℝ × ℝ) → UnitAddCircle} {χ : (ℝ × ℝ) → ℝ}
  {θ : Fin n → ℝ} {ε : ℝ} {Q : MaskedModelData T H G K M f χ N θ ε}
  {ι : A → Fin n} {r : A → (ℝ × ℝ) → ℝ}

theorem ModelRealSubfamily.terminal_value (W : ModelRealSubfamily Q ι r)
    (hTH : ∀ i j, Disjoint (closure (jordanInterior (T i))) (closure (jordanInterior (H j))))
    (hTC : ∀ i, Disjoint (closedTerminalCap (T i)) (cutoffCore χ))
    (i : J) (j : A) {z : ℂ} (hz : z ∈ frontier (jordanInterior (T i))) :
    W.functions j (Complex.equivRealProdCLM z) =
      shiftedStaircase (reciprocalGridStep N)
        (staircaseWidth (reciprocalGridStep N) Q.widthIndex) (θ (ι j))
        (r j (Complex.equivRealProdCLM z)) := by
  have hnot (k : I) : Complex.equivRealProdCLM z ∉ realJordanInterior (H k) := by
    rintro ⟨w, hw, heq⟩
    have hwz : w = z := Complex.equivRealProdCLM.injective heq
    exact Set.disjoint_left.mp (hTH i k) (frontier_subset_closure hz) (hwz ▸ subset_closure hw)
  have hχ : χ (Complex.equivRealProdCLM z) = 1 :=
    (interior_subset : interior {x | χ x = 1} ⊆ {x | χ x = 1})
      (boundary_in_one_plateau_of_disjoint_cutoffCore (T i) χ (hTC i) z hz)
  exact (W.filled.2.1 j _ hnot).trans (cutoffStaircase_of_one hχ)

theorem ModelRealSubfamily.terminal_oscillation (W : ModelRealSubfamily Q ι r)
    (hTH : ∀ i j, Disjoint (closure (jordanInterior (T i))) (closure (jordanInterior (H j))))
    (hTC : ∀ i, Disjoint (closedTerminalCap (T i)) (cutoffCore χ))
    (a : J → A → ℝ) (ha : ∀ i j, 0 ≤ a i j)
    (hbound : ∀ i j x, x ∈ frontier (jordanInterior (T i)) →
      ∀ y ∈ frontier (jordanInterior (T i)),
        |shiftedStaircase (reciprocalGridStep N)
            (staircaseWidth (reciprocalGridStep N) Q.widthIndex) (θ (ι j))
            (r j (Complex.equivRealProdCLM x)) -
          shiftedStaircase (reciprocalGridStep N)
            (staircaseWidth (reciprocalGridStep N) Q.widthIndex) (θ (ι j))
            (r j (Complex.equivRealProdCLM y))| ≤ a i j + 4 * reciprocalGridStep N) :
    ∀ i j, terminalOscillation (T i) (W.functions j) ≤ a i j + 4 * reciprocalGridStep N := by
  intro i j
  apply Metric.diam_le_of_forall_dist_le (by linarith [ha i j, reciprocalGridStep_pos N])
  rintro x ⟨p, hp, rfl⟩ y ⟨q, hq, rfl⟩
  rw [frontier_realJordanInterior] at hp hq
  obtain ⟨z, hz, rfl⟩ := hp
  obtain ⟨w, hw, rfl⟩ := hq
  rw [W.terminal_value hTH hTC i j hz, W.terminal_value hTH hTC i j hw]
  simpa only [Real.dist_eq] using hbound i j z hz w hw

end CircleDomainRigidity.FiniteTransfer

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Transfer_MixedCoordinateModel
attribute [-instance] _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions _root_.OAI.CircleDomainRigidity.finiteSphericalArea _root_.OAI.CircleDomainRigidity.sphereFirstCountableTopology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Construct the actual common model for both real barriers and masked
periods. Real terminal bounds include every mark. -/

open Set Function Filter MeasureTheory Classical
open scoped Topology ContDiff Matrix.Norms.Elementwise
noncomputable section
namespace CircleDomainRigidity.FiniteTransfer

theorem nonempty_mixed_coordinate_stage
    (hsard : SmoothPlanarSard) (hsch : PlanarSchoenflies) (hcompact : SmoothCompactMetricSphereUniformization)
    (hfinite : FiniteJordanModelUniformization)
    {G U : Set Sphere} (hG : IsOpen G) (hinfty : OnePoint.infty ∈ G)
    (π : Sphere → Sphere) (hπ : Continuous π) (hclosed : IsClosedMap π) (hsurj : Surjective π)
    (hr : ∀ x y, π x = π y ↔ x = y ∨ (x ∈ Gᶜ ∧ y ∈ connectedComponentIn Gᶜ x))
    (hTD : IsTotallyDisconnected (π '' Gᶜ)) (hUB : U ⊆ (π '' Gᶜ)ᶜ)
    (hPU : ∀ z : ℂ, (z : Sphere) ∈ G → π (z : Sphere) ∈ U)
    {K₀ : Set (ℝ × ℝ)} (hK₀ : IsClosed K₀) (hK₀G : K₀ ⊆ realChartDomain G)
    {n : ℕ} (hn : 0 < n) {S : Type*} [Countable S]
    (σ : S → Sphere) (hσ : Injective σ) (hσB : ∀ s, σ s ∈ π '' Gᶜ)
    (hσU : ∀ s, σ s ∉ U) (C : Fin n → MaskedCoordinateData G U π σ)
    {m : ℕ} (ι : Fin m → Fin n) (hι : Injective ι) (R : RealCoordinateSubfamily C ι)
    (Flag : Set S) (hFlag : Flag.Finite) (hflag : ∀ l, (C l).singular ∈ Flag)
    (hcompat : ∀ (j : Fin n) (d : ℕ) (labels : Fin d → Fin n),
      (∀ i, (labels i).val < j.val) →
      (volume.prod (Measure.pi (fun _ : Fin d => (volume : Measure UnitAddCircle))))
        (freeComponentFailure ((π '' Gᶜ) \ range σ) (C j).graph (fun l => (C l).graph) labels) = 0)
    (O : S → Set Sphere) (hO : ∀ s, O s ∈ 𝓝 (σ s))
    {ε ρ : ℝ} (hε : 0 < ε) (hρ : 0 < ρ) (k₀ : ℕ) :
    Nonempty (MixedCoordinateStage C ι R.physical Flag O K₀ ε ρ k₀) := by
  classical
  obtain ⟨V, u, B, hV, hVM, _, hub, hwidth, hus, hup⟩ :=
    exists_marked_physical_branches (fun l => (C l).Index) U G π
      (fun l => (C l).mask) (fun l => (C l).mask_closed) (fun l => (C l).mask_frontier)
      σ hσU (fun l => σ (C l).singular) (fun l => (C l).patch) (fun l => (C l).patch_open)
      (fun l => (C l).branch) (fun l => (C l).bound) (fun l => (C l).branch_bounded)
      (fun l => (C l).lower) (fun l => (C l).upper) (fun s l => (C l).marked_branch s)
      (fun l => (C l).physical) (fun l => (C l).branch_smooth) (fun l => (C l).branch_projection)
  let v (s : S) := subfamilyOverride ι R.quotient (u s)
  let B' (s : S) := subfamilyOverride ι R.bound (B s)
  have hvreal (s : S) (j : Fin m) : v s (ι j) = R.quotient j :=
    subfamilyOverride_at ι hι R.quotient (u s) j
  have hvother (s : S) {l : Fin n} (hl : l ∉ range ι) : v s l = u s l :=
    subfamilyOverride_of_notMem ι R.quotient (u s) hl
  have hvbound (s : S) (l : Fin n) (x : Sphere) (hx : x ∈ U ∩ V s) :
      |v s l x| ≤ B' s l := by
    by_cases hl : l ∈ range ι
    · obtain ⟨j, rfl⟩ := hl
      rw [hvreal, show B' s (ι j) = R.bound j from subfamilyOverride_at ι hι _ _ j]
      exact R.bounded j x hx.1
    · rw [hvother s hl, show B' s l = B s l from subfamilyOverride_of_notMem ι _ _ hl]
      exact hub s l x
  let O' (s : S) := O s ∩ V s
  have hO' (s : S) : O' s ∈ 𝓝 (σ s) := inter_mem (hO s) ((hV s).1.mem_nhds (hV s).2)
  let active (s : S) (l : Fin n) := l ∈ range ι ∨
    (σ s ∈ (C l).mask ∧ σ s ≠ σ (C l).singular)
  have hvwidth (s : S) (l : Fin n) (hl : active s l) :
      limsup (v s l) (𝓝[U ∩ V s] (σ s)) -
        liminf (v s l) (𝓝[U ∩ V s] (σ s)) ≤ (C l).upper s - (C l).lower s := by
    by_cases hi : l ∈ range ι
    · obtain ⟨j, rfl⟩ := hi
      rw [hvreal, nhdsWithin_inter_of_mem' (nhdsWithin_le_nhds ((hV s).1.mem_nhds (hV s).2))]
      exact R.width j s
    · rw [hvother s hi]
      exact (hwidth s l (hl.resolve_left hi).1 (hl.resolve_left hi).2).le
  have hvsmooth (s : S) (l : Fin n) (hs : σ s ∈ (C l).mask)
      (hne : σ s ≠ σ (C l).singular) : ContDiffOn ℝ ∞
      (fun x : ℝ × ℝ => v s l (π (Complex.equivRealProdCLM.symm x : Sphere)))
      (realChartDomain G ∩ realChartDomain (π ⁻¹' V s)) := by
    by_cases hi : l ∈ range ι
    · obtain ⟨j, rfl⟩ := hi
      rw [hvreal]
      exact ((R.smooth j).mono inter_subset_left).congr
        (fun x hx => R.pullback j x hx.1)
    · rw [hvother s hi]
      exact hus s l hs hne
  have hvproj (s : S) (l : Fin n) (hs : σ s ∈ (C l).mask)
      (hne : σ s ≠ σ (C l).singular) (x : ℝ × ℝ)
      (hx : x ∈ realChartDomain G ∩ realChartDomain (π ⁻¹' V s)) :
      (v s l (π (Complex.equivRealProdCLM.symm x : Sphere)) : UnitAddCircle) = (C l).physical x := by
    by_cases hi : l ∈ range ι
    · obtain ⟨j, rfl⟩ := hi
      rw [hvreal, R.pullback j x hx.1]
      exact R.projection j x
    · rw [hvother s hi]
      exact hup s l hs hne x hx
  obtain ⟨K, χ, N, θ, hA, D, k, H, Q, W, hk, hK, hK₀K, hKG, hKc, hKQ,
      _, _, _, hTC, hTH, hN, hcard, hosc⟩ :=
    exists_assembled_mixed_model hsard hsch hcompact hfinite G hG hinfty
      π hπ hclosed hsurj hr hTD hK₀ hK₀G hn (fun l => (C l).graph)
      (fun l => (C l).graph_closed) σ hσ hσB (fun l => (C l).lower)
      (fun l => (C l).upper) Flag hFlag (fun l => (C l).width_nonneg)
      (fun l => (C l).width_summable) (fun l => (C l).marked_fiber)
      (fun l => (C l).Index) (fun l => (C l).mask) (fun l => (C l).mask_closed)
      (fun l => ((C l).mask_frontier).trans hUB) (fun l => (C l).singular) hflag
      (fun l => (C l).patch) (fun l => (C l).patch_open) (fun l => (C l).cover)
      (fun l => (C l).physical) (fun l => (C l).smooth) (fun l => (C l).measurable)
      (fun l => (C l).gradient_measurable) (fun l => (C l).energy)
      (fun l i x => (C l).branch i (π (Complex.equivRealProdCLM.symm x : Sphere)))
      (fun l => (C l).branch_smooth) (fun l => (C l).branch_projection)
      (fun l => (C l).physical_graph) ι hι R.physical R.smooth R.full_mask R.projection
      O' hO' (fun s => U ∩ V s) v B' hvbound
      (fun s z hzG hz => ⟨hPU z hzG, hz.2⟩) active hvwidth
      (fun x hx hfree l => (C l).free_fiber x hx hfree) hcompat hε hρ k₀
  let A := gridTerminalIndices Flag (reciprocalGridStep N) upperPair
    (fun l => (C l).lower) (fun l => (C l).upper) θ
  let : Fintype A := hA.fintype
  let selected (l : Fin n) : Finset A := Finset.univ.filter
    (fun s => σ s ∈ (C l).mask ∧ σ s ≠ σ (C l).singular)
  obtain ⟨E, w, hE, hw, hexcess⟩ := marked_model_terminal_control hG hπ D H hTH
    (fun l => (C l).mask) Q hTC (fun s => V s) (fun s => (hV s).1)
    (fun s => inter_subset_right) (fun s => v s) selected
    (fun s l => (C l).upper s - (C l).lower s)
    (fun l s hs => (hVM s l (Finset.mem_filter.mp hs).2.1).trans interior_subset)
    (fun l s hs => hvsmooth s l (Finset.mem_filter.mp hs).2.1 (Finset.mem_filter.mp hs).2.2)
    (fun l s hs => hvproj s l (Finset.mem_filter.mp hs).2.1 (Finset.mem_filter.mp hs).2.2)
    (fun l s _ => (C l).width_nonneg s)
    (fun l s hs => hosc s l (Or.inr (Finset.mem_filter.mp hs).2) _ _)
    (by simpa only [A, Set.fintypeCard_eq_ncard] using hcard)
  have hrealosc := W.terminal_oscillation hTH hTC
    (fun (s : A) j => (C (ι j)).upper s - (C (ι j)).lower s)
    (fun s j => (C (ι j)).width_nonneg s) (fun s j x hx y hy => by
      have h := hosc s (ι j) (Or.inl (mem_range_self j))
        (staircaseWidth (reciprocalGridStep N) Q.widthIndex) (θ (ι j)) x hx y hy
      rw [hvreal] at h
      have hp (z : ℂ) (hz : z ∈ frontier (jordanInterior (D.H s))) :
          R.quotient j (π (z : Sphere)) = R.physical j (Complex.equivRealProdCLM z) := by
        simpa only [ContinuousLinearEquiv.symm_apply_apply] using
          R.pullback j (Complex.equivRealProdCLM z) (by
            simpa only [realChartDomain, mem_preimage, ContinuousLinearEquiv.symm_apply_apply] using
              (D.frontier_good s z hz).1)
      simpa only [hp x hx, hp y hy] using h)
  let D' : PhysicalTerminalDisks G π (π '' Gᶜ) (fun s : A => σ s) (fun s => O s) :=
    { D with closure_subset := fun s z hz => (D.closure_subset s hz).1 }
  refine ⟨{
    indices := A
    indices_finite := hA
    flags := fun _ hs => Or.inl hs
    terminals := D'
    fillCount := k
    filling := H
    core := K
    core_closed := hK
    core_contains := hK₀K
    core_source := hKG
    core_cocompact := hKc
    core_model := hKQ
    cutoff := χ
    grid := N
    offset := θ
    small_grid := hN
    model := Q
    late_width := hk
    terminal_domain := E
    terminal_branch := w
    terminal_open := fun s => (hE s).1
    terminal_frontier := fun s => (hE s).2
    terminal_lift := ?_
    terminal_excess := ?_
    real := W
    real_excess := ?_ }⟩
  · intro l s hs hn
    exact hw l s (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hs, hn⟩)
  · intro l
    have he : (∑' s : {s : A // σ s ∈ (C l).mask ∧ σ s ≠ σ (C l).singular},
        max (Metric.diam (w s l '' frontier (realJordanInterior (D.H s))) -
          ((C l).upper s - (C l).lower s)) 0 ^ 2) =
        ∑ s ∈ selected l, max (Metric.diam (w s l '' frontier (realJordanInterior (D.H s))) -
          ((C l).upper s - (C l).lower s)) 0 ^ 2 := by
      rw [tsum_fintype]
      exact (Finset.sum_subtype
        (p := fun s : A => σ s ∈ (C l).mask ∧ σ s ≠ σ (C l).singular) (selected l)
        (by intro s; simp only [selected, Finset.mem_filter, Finset.mem_univ, true_and])
        (fun s => max (Metric.diam (w s l '' frontier (realJordanInterior (D.H s))) -
          ((C l).upper s - (C l).lower s)) 0 ^ 2)).symm
    rw [he]
    exact (hexcess l).trans (by linarith)
  · intro j
    rw [tsum_fintype]
    have h := sqrt_sum_terminal_excess_sq_lt Finset.univ Finset.univ (Subset.refl _)
      (fun s : A => terminalOscillation (D.H s) (W.functions j))
      (fun s : A => (C (ι j)).upper s - (C (ι j)).lower s) (reciprocalGridStep_pos N).le
      (fun s _ => hrealosc s j)
      (by simpa only [Finset.card_univ, A, Set.fintypeCard_eq_ncard] using hcard)
    exact h.trans (by linarith)

end CircleDomainRigidity.FiniteTransfer

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Selection_CountableMixedStages
attribute [-instance] _root_.OAI.CannonEmbeddedArc.Arc.graphVertices_finite _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions _root_.OAI.CircleDomainRigidity.finiteSphericalArea _root_.OAI.CircleDomainRigidity.sphereFirstCountableTopology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Actual mixed transfers of a countable ordered coordinate family.
The finite lists inherit the original order, and every prescribed mark
and every coordinate is eventually included. -/

open Set Function Filter MeasureTheory
open scoped Topology ContDiff
noncomputable section
namespace CircleDomainRigidity.FiniteTransfer

theorem exists_countable_mixed_stages_oai
    (hsard : SmoothPlanarSard) (hsch : PlanarSchoenflies) (hcompact : SmoothCompactMetricSphereUniformization)
    (hfinite : FiniteJordanModelUniformization)
    {G U : Set Sphere} (hG : IsOpen G) (hinfty : OnePoint.infty ∈ G)
    (π : Sphere → Sphere) (hπ : Continuous π) (hclosed : IsClosedMap π) (hsurj : Surjective π)
    (hr : ∀ x y, π x = π y ↔ x = y ∨ (x ∈ Gᶜ ∧ y ∈ connectedComponentIn Gᶜ x))
    (hTD : IsTotallyDisconnected (π '' Gᶜ)) (hUB : U ⊆ (π '' Gᶜ)ᶜ)
    (hPU : ∀ z : ℂ, (z : Sphere) ∈ G → π (z : Sphere) ∈ U)
    {S : Type*} [Countable S] (σ : S → Sphere) (hσ : Injective σ)
    (hσB : ∀ s, σ s ∈ π '' Gᶜ) (hσU : ∀ s, σ s ∉ U)
    {C : Type*} [LinearOrder C] [Countable C]
    (data : C → MaskedCoordinateData G U π σ)
    (retained : ℕ → C) (hinj : Injective retained)
    (R : RealCoordinateSubfamily data retained)
    (hcompat : ∀ (c : C) (d : ℕ) (labels : Fin d → C), (∀ i, labels i < c) →
      (volume.prod (Measure.pi (fun _ : Fin d => (volume : Measure UnitAddCircle))))
        (freeComponentFailure ((π '' Gᶜ) \ range σ) (data c).graph
          (fun c => (data c).graph) labels) = 0)
    (K₀ : ℕ → Set (ℝ × ℝ)) (hK₀ : ∀ n, IsClosed (K₀ n))
    (hK₀G : ∀ n, K₀ n ⊆ realChartDomain G)
    (O : ℕ → S → Set Sphere) (hO : ∀ n s, O n s ∈ 𝓝 (σ s))
    (ε ρ : ℕ → ℝ) (hε : ∀ n, 0 < ε n) (hρ : ∀ n, 0 < ρ n) :
    ∃ (size : ℕ → ℕ) (label : ∀ n, Fin (size n) ↪o C)
      (slot : ∀ n, Fin (n + 1) → Fin (size n)) (Flag : ℕ → Set S),
      (∀ n, Injective (slot n)) ∧
      (∀ n j, label n (slot n j) = retained j) ∧
      (∀ c, ∀ᶠ n in atTop, c ∈ range (label n)) ∧
      (∀ n, (Flag n).Finite) ∧ Monotone Flag ∧ (∀ n, (Flag n).Nonempty) ∧
      ∃ Q : ∀ n, MixedCoordinateStage (fun j => data (label n j)) (slot n)
        (fun j => R.physical j)
        (Flag n) (O n) (K₀ n) (ε n) (ρ n) n,
        ∀ s, ∀ᶠ n in atTop, s ∈ (Q n).indices := by
  classical
  obtain ⟨size, label, slot, hsize, hslot, hretained, hmono, hcover⟩ :=
    exists_ordered_coordinate_exhaustion retained hinj
  obtain ⟨F, hF, hFm, hFc⟩ := exists_increasing_finite_marks S
  let Flag (n : ℕ) : Set S := F n ∪ (fun c => (data c).singular) '' range (label n)
  have hFlag (n : ℕ) : (Flag n).Finite :=
    (hF n).union ((Set.finite_range (label n)).image (fun c => (data c).singular))
  have hflag (n : ℕ) (j : Fin (size n)) : (data (label n j)).singular ∈ Flag n :=
    Or.inr ⟨label n j, mem_range_self j, rfl⟩
  have hFlagm : Monotone Flag := fun n m hnm =>
    union_subset_union (hFm hnm) (image_mono (hmono hnm))
  have hnonempty (n : ℕ) : Nonempty (MixedCoordinateStage (fun j => data (label n j)) (slot n)
      (fun j => R.physical j)
      (Flag n) (O n) (K₀ n) (ε n) (ρ n) n) := by
    apply nonempty_mixed_coordinate_stage hsard hsch hcompact hfinite hG hinfty
      π hπ hclosed hsurj hr hTD hUB hPU (hK₀ n) (hK₀G n) (hsize n)
      σ hσ hσB hσU (fun j => data (label n j)) (slot n) (hslot n)
      (R.reindex (label n) (fun j : Fin (n + 1) => (j : ℕ)) (slot n) (hretained n))
      (Flag n) (hFlag n) (hflag n)
      ?_ (O n) (hO n) (hε n) (hρ n) n
    intro j d labels hlabels
    exact hcompat (label n j) d (fun i => label n (labels i))
      (fun i => (label n).strictMono (hlabels i))
  let Q (n : ℕ) := Classical.choice (hnonempty n)
  refine ⟨size, label, slot, Flag, hslot, hretained, hcover, hFlag, hFlagm,
    (fun n => ⟨(data (label n ⟨0, hsize n⟩)).singular, hflag n _⟩), Q, ?_⟩
  intro s
  exact (hFc s).mono (fun n hn => (Q n).flags (Or.inl hn))

end CircleDomainRigidity.FiniteTransfer

end

end OAI
end

theorem solution.{u_1, u_2} : type_of% @OAI.CircleDomainRigidity.FiniteTransfer.exists_countable_mixed_stages_oai.{u_1, u_2} := @OAI.CircleDomainRigidity.FiniteTransfer.exists_countable_mixed_stages_oai.{u_1, u_2}
