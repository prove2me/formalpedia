-- Prove2me | solution 1 for OAI.BoltzmannNonuniqueness.JetCopyDatum.exists_uniform_cap_solution_q80
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-31T20:56:38.915922+00:00
-- url     : https://prove2.me/submissions/20dff625-c441-40f2-8344-24861662a29b

import Mathlib
import Definitions.Def_BoltzmannNonuniqueness
import Definitions.Def_OAIQ080A002
import Theorems.Thm_OAI_BoltzmannNonuniqueness_JetCopyDatum_capped_total_bound_q80
import Theorems.Thm_OAI_BoltzmannNonuniqueness_JetCopyDatum_exists_uniform_zero_solution_large_q80

section
-- module Solutions.OAIQ080_BZ.Compat
namespace OAI

/-! Compatibility with the newer Lean core OpenAI's code was written against: lemmas it uses by
names this environment (Lean 4.33.1, Mathlib 0df444a) does not have yet. Each is the
corresponding `if_pos` / `if_neg` / `dif_pos` / `dif_neg`. The `dite` forms are stated as
`dite p a b`, not with the `if hp : p then …` notation: its eta-expanded lambdas form is a higher-order pattern
that `rw` cannot find (DepthThree, PeriodicTiling 2026-10-25). -/
section OAICompat434
/-- Mathlib's newer name for `measurable_pi_lambda` (with `f` implicit). -/
theorem Measurable.of_eval {δ ι : Type*} {π : ι → Type*} [MeasurableSpace δ]
    [∀ i, MeasurableSpace (π i)] {f : δ → ∀ i, π i}
    (h : ∀ i, Measurable fun a => f a i) : Measurable f := measurable_pi_lambda f h
end OAICompat434

end OAI
end

section
-- module Solutions.OAIQ080_BZ.Boltzmann_Approximation_ColoredDifferenceAlgebra
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

/-! # A finite-family quadratic difference estimate in the sum norm -/

noncomputable section

namespace BoltzmannNonuniqueness.ColoredAlgebra

theorem sum_abs_product_difference_le {I : Type*} (s : Finset I) {R E : ℝ}
    (hR : 0 ≤ R) (a b c d : I → ℝ)
    (hb : ∀ i ∈ s, 0 ≤ b i ∧ b i ≤ R) (hc : ∀ i ∈ s, 0 ≤ c i ∧ c i ≤ R)
    (hac : (∑ i ∈ s, |a i-c i|) ≤ E) (hbd : (∑ i ∈ s, |b i-d i|) ≤ E) :
    (∑ i ∈ s, |a i*b i-c i*d i|) ≤ 2*R*E := by
  calc
    _ ≤ ∑ i ∈ s, (R* |a i-c i| + R* |b i-d i|) := by
      apply Finset.sum_le_sum
      intro i hi
      calc
        _ = |(a i-c i)*b i+c i*(b i-d i)| := by congr 1; ring
        _ ≤ |(a i-c i)*b i| + |c i*(b i-d i)| := abs_add_le _ _
        _ = |a i-c i| * b i+c i* |b i-d i| := by
          rw [abs_mul,abs_mul,abs_of_nonneg (hb i hi).1,abs_of_nonneg (hc i hi).1]
        _ ≤ |a i-c i| * R+R* |b i-d i| := add_le_add
          (mul_le_mul_of_nonneg_left (hb i hi).2 (abs_nonneg _))
          (mul_le_mul_of_nonneg_right (hc i hi).2 (abs_nonneg _))
        _ = _ := by ring
    _ = R*(∑ i ∈ s, |a i-c i|)+R*(∑ i ∈ s, |b i-d i|) := by
      rw [Finset.sum_add_distrib,Finset.mul_sum,Finset.mul_sum]
    _ ≤ R*E+R*E := add_le_add (mul_le_mul_of_nonneg_left hac hR) (mul_le_mul_of_nonneg_left hbd hR)
    _ = _ := by ring

end BoltzmannNonuniqueness.ColoredAlgebra

end

end

end OAI
end

section
-- module Solutions.OAIQ080_BZ.Boltzmann_Collision_VelocityWeight
attribute [-instance] _root_.OAI.BoltzmannNonuniqueness.ChartKernel.coordinateKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ChartKernel.offAxis_sFinite _root_.OAI.BoltzmannNonuniqueness.CollisionCompactness.DoubleGain.incomingBallFinite _root_.OAI.BoltzmannNonuniqueness.CollisionCompactness.DoubleGain.parameterMeasureFinite _root_.OAI.BoltzmannNonuniqueness.EuclideanFlight.sourcePullback_finite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.characteristicGainKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.hotKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.mixedKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.retainedKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.coldCylinderVolume_finite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.copyColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.mainCoreKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.selectedColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCoreSheet.coreKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCoreSheet.dilatedColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCoreSheet.kineticColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.PeriodicApproximation.fiberMeasure_finite _root_.OAI.BoltzmannNonuniqueness.PositiveIteration.awayOriginKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.PositiveIteration.nearOriginKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamNormalCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamNormalRetainedKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.dampedCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.densityScaledCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.eventParameterMeasure_isFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalBeamKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalCollision_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalPhysicalEvent_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalWindowEvent_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.markedEventMeasure_isFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.physicalEventMeasure_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.scaledBeamNormalKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.TransverseAverage.circleArea_isFiniteMeasure _root_.OAI.BoltzmannNonuniqueness.WeakTime.phaseEndpointKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.WeakTime.phaseIncrement_finite _root_.OAI.BoltzmannNonuniqueness.WeakTime.phaseSeed_sFinite _root_.OAI.BoltzmannNonuniqueness.WeakTime.residenceKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.normalParameters_sFinite _root_.OAI.BoltzmannNonuniqueness.normalPhaseGainKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.Compactness.instNonemptyPositivePhaseTest _root_.OAI.BoltzmannNonuniqueness.Compactness.instSecondCountableTopologyPositivePhaseTest _root_.OAI.BoltzmannNonuniqueness.Compactness.instNonemptySupportedTest _root_.OAI.BoltzmannNonuniqueness.Compactness.instSecondCountableTopologySupportedTest
attribute [-simp] _root_.OAI.BoltzmannNonuniqueness.EuclideanFlight.phaseEquiv_snd _root_.OAI.BoltzmannNonuniqueness.KineticTest.timeShift_toFun _root_.OAI.BoltzmannNonuniqueness.timeTranslation_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
attribute [local instance] OAI.circleMeasurableSpace OAI.circleBorelSpace

namespace OAI

section

/-!
# The transverse singularity in the velocity majorant

Section 3 uses `H(v) = exp(-‖v‖²) * ⟨v⟩^(-100) * (1 + ‖v̄‖^(-q))`.
Thus its polynomial factor is `(1 + ‖v‖²)^(-50)`. The values assigned on
the velocity axis use Mathlib's real-power convention and do not affect
Lebesgue integrability.
-/

noncomputable section

open MeasureTheory Set

namespace BoltzmannNonuniqueness.VelocityWeight

theorem singularity_nonneg (q : ℝ) (u : Transverse) : 0 ≤ singularity q u :=
  Real.rpow_nonneg (norm_nonneg _) _

/-- Gaussian decay retains transverse powers whenever their exponent exceeds `-2`. -/
theorem integrable_transverse_gaussian_rpow {β s : ℝ} (hβ : 0 < β) (hs : -2 < s) :
    Integrable (fun u : Transverse => ‖u‖ ^ s * Real.exp (-β * ‖u‖ ^ 2)) := by
  apply (integrable_fun_norm_addHaar (volume : Measure Transverse)
    (f := fun r : ℝ => r ^ s * Real.exp (-β * r ^ 2))).mpr
  have hi : IntegrableOn (fun r : ℝ => r ^ (s + 1) * Real.exp (-β * r ^ 2)) (Ioi 0) :=
    integrableOn_rpow_mul_exp_neg_mul_sq hβ (by linarith)
  apply hi.congr_fun _ measurableSet_Ioi
  intro r hr
  have hr' : 0 < r := hr
  simp only [finrank_euclideanSpace, Fintype.card_fin, Nat.reduceSub, pow_one, smul_eq_mul]
  rw [Real.rpow_add hr' s 1, Real.rpow_one]
  ring

theorem integrable_gaussianMajorant {β q : ℝ} (hβ : 0 < β) (hq : q < 2) :
    Integrable (gaussianMajorant β q) := by
  have hb₀ : Integrable (fun u : Transverse => Real.exp (-β * ‖u‖ ^ 2)) := by
    simpa only [Real.rpow_zero, one_mul] using
      integrable_transverse_gaussian_rpow (s := 0) hβ (by norm_num)
  have hb₁ := integrable_transverse_gaussian_rpow (s := -q) hβ (by linarith)
  have hb : Integrable (fun u : Transverse =>
      (1 + singularity q u) * Real.exp (-β * ‖u‖ ^ 2)) := by
    convert hb₀.add hb₁ using 1
    all_goals try with_reducible_and_instances rfl
    funext u
    simp only [singularity, Pi.add_apply]
    ring
  have ha := integrable_exp_neg_mul_sq hβ
  have hp := ha.mul_prod hb
  have hc := split_measurePreserving.integrable_comp_of_integrable hp
  convert hc using 1
  all_goals try with_reducible_and_instances rfl
  funext v
  simp only [gaussianMajorant, Function.comp_apply, split_apply]
  have he : Real.exp (-β * ‖v‖ ^ 2) =
      Real.exp (-β * ‖transverse v‖ ^ 2) * Real.exp (-β * (axial v) ^ 2) := by
    rw [norm_sq_split, mul_add, Real.exp_add]
  rw [he]
  ring

theorem H_nonneg (q : ℝ) (v : Velocity) : 0 ≤ H q v := by
  unfold H singularity
  positivity

theorem H_le_gaussianMajorant (q : ℝ) (v : Velocity) :
    H q v ≤ gaussianMajorant 1 q v := by
  have hp : (1 + ‖v‖ ^ 2) ^ (-50 : ℝ) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (le_add_of_nonneg_right (sq_nonneg _)) (by norm_num)
  unfold H gaussianMajorant
  simp only [neg_mul, one_mul]
  have hw : 0 ≤ 1 + singularity q (transverse v) :=
    add_nonneg zero_le_one (singularity_nonneg q (transverse v))
  simpa only [mul_one] using mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left hp (Real.exp_nonneg _)) hw

theorem integrable_H {q : ℝ} (hq : q < 2) : Integrable (H q) := by
  apply (integrable_gaussianMajorant zero_lt_one hq).mono'
  · unfold H singularity transverse
    fun_prop
  · filter_upwards [] with v
    rw [Real.norm_eq_abs, abs_of_nonneg (H_nonneg q v)]
    exact H_le_gaussianMajorant q v

theorem H_pos (q : ℝ) (v : Velocity) : 0 < H q v := by
  unfold H
  apply mul_pos
  · exact mul_pos (Real.exp_pos _) (Real.rpow_pos_of_pos (by positivity) _)
  · linarith [singularity_nonneg q (transverse v)]

end BoltzmannNonuniqueness.VelocityWeight

end

end

end OAI
end

section
-- module Solutions.OAIQ080_BZ.Boltzmann_Branching_DatumBounds
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Summable cold-jet datum bounds

Section 4 of the supplied manuscript bounds the mass and energy of each annulus by a constant
times `s_j²`, and its absolute entropy by a constant times `s_j² (1 + |log s_j|)`.
Those scalar bounds are summable for the stated geometric scales, and their tails converge
to zero. Indices start at zero; the manuscript's indices starting at one
are obtained by removing the first term.
-/

noncomputable section

open Filter Finset
open scoped Topology BigOperators

namespace BoltzmannNonuniqueness.DatumBounds

theorem scale_pos {s₀ η : ℝ} (hs₀ : 0 < s₀) (j : ℕ) : 0 < scale s₀ η j :=
  mul_pos hs₀ (Real.exp_pos _)

end BoltzmannNonuniqueness.DatumBounds

end

end OAI
end

section
-- module Solutions.OAIQ080_BZ.Boltzmann_Jets_JetProfiles
attribute [-instance] _root_.OAI.BoltzmannNonuniqueness.ChartKernel.coordinateKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ChartKernel.offAxis_sFinite _root_.OAI.BoltzmannNonuniqueness.CollisionCompactness.DoubleGain.incomingBallFinite _root_.OAI.BoltzmannNonuniqueness.CollisionCompactness.DoubleGain.parameterMeasureFinite _root_.OAI.BoltzmannNonuniqueness.EuclideanFlight.sourcePullback_finite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.characteristicGainKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.hotKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.mixedKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.retainedKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.coldCylinderVolume_finite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.copyColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.instCountableLabel _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.mainCoreKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.selectedColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCoreSheet.coreKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCoreSheet.dilatedColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCoreSheet.kineticColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.PeriodicApproximation.fiberMeasure_finite _root_.OAI.BoltzmannNonuniqueness.PositiveIteration.awayOriginKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.PositiveIteration.nearOriginKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamNormalCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamNormalRetainedKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.dampedCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.densityScaledCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.eventParameterMeasure_isFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalBeamKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalCollision_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalPhysicalEvent_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalWindowEvent_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.markedEventMeasure_isFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.physicalEventMeasure_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.scaledBeamNormalKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.WeakTime.phaseEndpointKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.WeakTime.phaseIncrement_finite _root_.OAI.BoltzmannNonuniqueness.WeakTime.phaseSeed_sFinite _root_.OAI.BoltzmannNonuniqueness.WeakTime.residenceKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.normalParameters_sFinite _root_.OAI.BoltzmannNonuniqueness.normalPhaseGainKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.Compactness.instSecondCountableTopologyPositivePhaseTest _root_.OAI.BoltzmannNonuniqueness.Compactness.instSecondCountableTopologySupportedTest
attribute [-simp] _root_.OAI.BoltzmannNonuniqueness.EuclideanFlight.phaseEquiv_snd _root_.OAI.BoltzmannNonuniqueness.KineticTest.timeShift_toFun _root_.OAI.BoltzmannNonuniqueness.timeTranslation_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

/-! # The cold-jet annuli and opposite stripe enlargements

These are the actual spatial masks of Section 4. The geometric scale is
indexed from zero here, representing the manuscript's first positive index.
-/

noncomputable section

open Set Metric
open BoltzmannNonuniqueness.VelocityWeight
open BoltzmannNonuniqueness.DatumBounds

namespace BoltzmannNonuniqueness.JetGeometry

theorem gapCoefficient_pos {η : ℝ} (hη : 0 < η) : 0 < gapCoefficient η := by
  have h := Real.one_lt_exp_iff.mpr hη
  unfold gapCoefficient
  linarith

theorem gapCoefficient_le {η : ℝ} (hη : η ≤ Real.log 2) : gapCoefficient η ≤ 1 / 16 := by
  have h := Real.exp_le_exp.mpr hη
  rw [Real.exp_log (by norm_num : (0 : ℝ) < 2)] at h
  unfold gapCoefficient
  linarith

theorem enlargementWidth_pos {η s : ℝ} (hη : 0 < η) (hs : 0 < s) :
    0 < enlargementWidth η s := by
  have := gapCoefficient_pos hη
  unfold enlargementWidth
  positivity

theorem enlargement_witness {η s : ℝ} (hη : 0 < η) (hs : 0 < s)
    {positive : Bool} {y : Transverse} (hy : y ∈ enlargement η s positive) :
    ∃ x ∈ mask η s positive, dist y x ≤ 2 * enlargementWidth η s := by
  have hδ := enlargementWidth_pos hη hs
  obtain ⟨x, hx, hd⟩ := mem_iUnion₂.mp (cthickening_subset_iUnion_closedBall_of_lt (mask η s positive)
    (by positivity : 0 < 2 * enlargementWidth η s) (by linarith) hy)
  exact ⟨x, hx, mem_closedBall.mp hd⟩

theorem enlargement_subset_annulus {η s : ℝ} (hη : 0 < η) (hs : 0 < s)
    (positive : Bool) :
    enlargement η s positive ⊆ {y : Transverse | s < ‖y‖ ∧ ‖y‖ < Real.exp η * s} := by
  intro y hy
  obtain ⟨x, hx, hdist⟩ := enlargement_witness hη hs hy
  have h₁ := norm_sub_norm_le y x
  have h₂ := norm_sub_norm_le x y
  rw [← dist_eq_norm] at h₁ h₂
  rw [dist_comm x y] at h₂
  have hgap : 0 < gapCoefficient η * s ^ 2 := mul_pos (gapCoefficient_pos hη) (sq_pos_of_pos hs)
  have hcore := hx.1
  change s + gapCoefficient η * s ^ 2 < ‖x‖ ∧
    ‖x‖ < Real.exp η * s - gapCoefficient η * s ^ 2 at hcore
  dsimp only [enlargementWidth] at hdist
  constructor <;> linarith [hcore.1, hcore.2]

theorem scale_antitone {s₀ η : ℝ} (hs₀ : 0 ≤ s₀) (hη : 0 ≤ η) :
    Antitone (scale s₀ η) := by
  intro i j hij
  unfold scale
  apply mul_le_mul_of_nonneg_left _ hs₀
  apply Real.exp_le_exp.mpr
  have hcast : (i : ℝ) ≤ j := by exact_mod_cast hij
  nlinarith

theorem outerRadius_eq (s₀ η : ℝ) (j : ℕ) :
    Real.exp η * jetScale s₀ η j = scale s₀ η j := by
  unfold jetScale scale
  rw [mul_left_comm, ← Real.exp_add]
  congr 2
  push_cast
  ring

theorem ordered_annuli {s₀ η : ℝ} (hs₀ : 0 ≤ s₀) (hη : 0 ≤ η)
    {i j : ℕ} (hij : i < j) :
    Real.exp η * jetScale s₀ η j ≤ jetScale s₀ η i := by
  rw [outerRadius_eq]
  exact scale_antitone hs₀ hη (Nat.succ_le_iff.mpr hij)

theorem distinct_scale_disjoint {s₀ η : ℝ} (hs₀ : 0 < s₀) (hη : 0 < η)
    {i j : ℕ} (hij : i ≠ j) (a b : Bool) :
    Disjoint (enlargement η (jetScale s₀ η i) a) (enlargement η (jetScale s₀ η j) b) := by
  apply disjoint_left.mpr
  intro y hyi hyj
  have hi := enlargement_subset_annulus hη (scale_pos hs₀ _) a hyi
  have hj := enlargement_subset_annulus hη (scale_pos hs₀ _) b hyj
  rcases lt_or_gt_of_ne hij with hij | hji
  · have h := ordered_annuli hs₀.le hη.le hij
    dsimp only [jetScale] at h
    exact not_lt_of_ge h (hi.1.trans hj.2)
  · have h := ordered_annuli hs₀.le hη.le hji
    dsimp only [jetScale] at h
    exact not_lt_of_ge h (hj.1.trans hi.2)

theorem stripe_distance {s : ℝ} (hs : 0 < s) {x y : Transverse}
    (hx : x ∈ stripe s true) (hy : y ∈ stripe s false) : s ^ 2 / 4 < dist x y := by
  obtain ⟨k, hk₁, hk₂⟩ := hx
  obtain ⟨l, hl₁, hl₂⟩ := hy
  simp only [Bool.false_eq_true, ↓reduceIte, add_zero] at hk₁ hk₂ hl₁ hl₂
  have hcoord : |x 0 - y 0| ≤ dist x y := by
    simpa only [PiLp.sub_apply, Real.norm_eq_abs, dist_eq_norm] using PiLp.norm_apply_le (x - y) 0
  have hp : 0 < s ^ 2 := sq_pos_of_pos hs
  rcases le_or_gt k l with hkl | hlk
  · have hcast : (k : ℝ) ≤ l := by exact_mod_cast hkl
    have hh := mul_le_mul_of_nonneg_right hcast hp.le
    have : s ^ 2 / 4 < y 0 - x 0 := by nlinarith
    exact this.trans_le ((le_abs_self _).trans (by simpa only [abs_sub_comm] using hcoord))
  · have hcast : (l : ℝ) + 1 ≤ k := by exact_mod_cast (Int.add_one_le_iff.mpr hlk)
    have hh := mul_le_mul_of_nonneg_right hcast hp.le
    have : s ^ 2 / 4 < x 0 - y 0 := by nlinarith
    exact this.trans_le ((le_abs_self _).trans hcoord)

theorem opposite_enlargements_disjoint {η s : ℝ} (hη : 0 < η)
    (hηmax : η ≤ Real.log 2) (hs : 0 < s) :
    Disjoint (enlargement η s true) (enlargement η s false) := by
  apply disjoint_left.mpr
  intro y hy₁ hy₂
  obtain ⟨x, hx, hxy⟩ := enlargement_witness hη hs hy₁
  obtain ⟨z, hz, hzy⟩ := enlargement_witness hη hs hy₂
  have hsep := stripe_distance hs hx.2 hz.2
  have hdist := dist_triangle x y z
  rw [dist_comm x y] at hdist
  have hc := mul_le_mul_of_nonneg_right (gapCoefficient_le hηmax) (sq_nonneg s)
  unfold enlargementWidth at hxy hzy
  nlinarith

theorem enlargement_inside_baseBall {s₀ η : ℝ} (hs₀ : 0 < s₀) (hη : 0 < η)
    (j : ℕ) (a : Bool) : enlargement η (jetScale s₀ η j) a ⊆ ball 0 s₀ := by
  intro y hy
  have h := (enlargement_subset_annulus hη (scale_pos hs₀ _) a hy).2
  change ‖y‖ < Real.exp η * jetScale s₀ η j at h
  rw [outerRadius_eq] at h
  have hj := scale_antitone hs₀.le hη.le (Nat.zero_le j)
  have hzero : scale s₀ η 0 = s₀ := by simp [scale]
  rw [hzero] at hj
  simpa only [mem_ball, dist_zero_right] using h.trans_le hj

end BoltzmannNonuniqueness.JetGeometry

end

end

section

/-! # Pairwise disjoint periodic cold-jet spatial enlargements -/

noncomputable section

open Set Metric
open BoltzmannNonuniqueness.VelocityWeight
open BoltzmannNonuniqueness.JetGeometry

namespace BoltzmannNonuniqueness.JetLattice

theorem integer_distance {m n : ℤ} (h : m ≠ n) : (1 : ℝ) ≤ |(m : ℝ) - n| := by
  have h' := Int.one_le_abs (sub_ne_zero.mpr h)
  exact_mod_cast h'

theorem distinct_transverse_shifts {m n : Lattice}
    (h : ∃ k : Fin 2, m k.castSucc ≠ n k.castSucc) :
    1 ≤ ‖transverseShift m - transverseShift n‖ := by
  obtain ⟨k, hk⟩ := h
  have hn := PiLp.norm_apply_le (transverseShift m - transverseShift n) k
  change ‖(m k.castSucc : ℝ) - n k.castSucc‖ ≤ _ at hn
  rw [Real.norm_eq_abs] at hn
  exact (integer_distance hk).trans hn

theorem common_point_transverse_lattice {s₀ η : ℝ} (hs₀ : 0 < s₀)
    (hsmax : s₀ ≤ 1 / 8) (hη : 0 < η) {t : ℝ} {i j : Label} {x : Velocity}
    (hi : x ∈ spatialEnlargement s₀ η t i) (hj : x ∈ spatialEnlargement s₀ η t j) :
    ∀ k : Fin 2, i.lattice k.castSucc = j.lattice k.castSucc := by
  by_contra! h
  have hsep := distinct_transverse_shifts h
  have hi' := enlargement_inside_baseBall hs₀ hη i.annulus i.positive hi.1
  have hj' := enlargement_inside_baseBall hs₀ hη j.annulus j.positive hj.1
  rw [mem_ball, dist_zero_right] at hi' hj'
  have htri := norm_sub_le (transverse x - transverseShift j.lattice)
    (transverse x - transverseShift i.lattice)
  have he : transverse x - transverseShift j.lattice - (transverse x - transverseShift i.lattice) =
      transverseShift i.lattice - transverseShift j.lattice := by abel
  rw [he] at htri
  linarith

theorem common_point_axial_lattice {t : ℝ} (ht : t ≤ 1 / 32)
    {s₀ η : ℝ} {i j : Label} {x : Velocity}
    (hi : x ∈ spatialEnlargement s₀ η t i) (hj : x ∈ spatialEnlargement s₀ η t j) :
    i.lattice (Fin.last 2) = j.lattice (Fin.last 2) := by
  by_contra h
  have hsep := integer_distance h
  have htri := abs_sub_le (axialShift i.lattice) (axial x) (axialShift j.lattice)
  rw [abs_sub_comm (axialShift i.lattice) (axial x)] at htri
  have hi' := hi.2
  have hj' := hj.2
  change |axial x - axialShift i.lattice| ≤ 1 / 8 + 2 * t + 1 / 16 at hi'
  change |axial x - axialShift j.lattice| ≤ 1 / 8 + 2 * t + 1 / 16 at hj'
  change 1 ≤ |axialShift i.lattice - axialShift j.lattice| at hsep
  linarith

theorem common_point_lattice {s₀ η t : ℝ} (hs₀ : 0 < s₀) (hsmax : s₀ ≤ 1 / 8)
    (hη : 0 < η) (ht : t ≤ 1 / 32) {i j : Label} {x : Velocity}
    (hi : x ∈ spatialEnlargement s₀ η t i) (hj : x ∈ spatialEnlargement s₀ η t j) :
    i.lattice = j.lattice := by
  have htrans := common_point_transverse_lattice hs₀ hsmax hη hi hj
  have haxial := common_point_axial_lattice ht hi hj
  funext k
  refine Fin.lastCases haxial htrans k

theorem common_point_label {s₀ η t : ℝ} (hs₀ : 0 < s₀) (hsmax : s₀ ≤ 1 / 8)
    (hη : 0 < η) (hηmax : η ≤ Real.log 2) (ht : t ≤ 1 / 32) {i j : Label} {x : Velocity}
    (hi : x ∈ spatialEnlargement s₀ η t i) (hj : x ∈ spatialEnlargement s₀ η t j) : i = j := by
  have hn := common_point_lattice hs₀ hsmax hη ht hi hj
  have hi' := hi.1
  have hj' := hj.1
  rw [← hn] at hj'
  have ha : i.annulus = j.annulus := by
    by_contra h
    exact (disjoint_left.mp (distinct_scale_disjoint hs₀ hη h i.positive j.positive)) hi' hj'
  have hs : i.positive = j.positive := by
    rw [← ha] at hj'
    by_contra h
    have hd := opposite_enlargements_disjoint hη hηmax
      (DatumBounds.scale_pos (η := η) hs₀ (i.annulus + 1))
    cases hiBool : i.positive <;> cases hjBool : j.positive
    · exact h (hiBool.trans hjBool.symm)
    · rw [hiBool] at hi'
      rw [hjBool] at hj'
      exact (disjoint_left.mp hd) hj' hi'
    · rw [hiBool] at hi'
      rw [hjBool] at hj'
      exact (disjoint_left.mp hd) hi' hj'
    · exact h (hiBool.trans hjBool.symm)
  cases i
  cases j
  simp_all

end BoltzmannNonuniqueness.JetLattice

end

end

section

/-! # Area bounds for the original striped cold-jet masks -/

noncomputable section

open MeasureTheory Set Metric
open scoped ENNReal
open BoltzmannNonuniqueness.VelocityWeight
open BoltzmannNonuniqueness.JetGeometry

namespace BoltzmannNonuniqueness.JetMaskMeasure

theorem measurableSet_stripe (s : ℝ) (a : Bool) : MeasurableSet (stripe s a) := by
  unfold stripe
  simp only [ofPred_exists]
  apply MeasurableSet.iUnion
  intro k
  exact (measurableSet_lt measurable_const (by fun_prop : Measurable (fun y : Transverse => y 0))).inter
    (measurableSet_lt (by fun_prop : Measurable (fun y : Transverse => y 0)) measurable_const)

theorem measurableSet_annularCore (η s : ℝ) : MeasurableSet (annularCore η s) :=
  (measurableSet_lt measurable_const measurable_norm).inter
    (measurableSet_lt measurable_norm measurable_const)

theorem measurableSet_mask (η s : ℝ) (a : Bool) : MeasurableSet (mask η s a) :=
  (measurableSet_annularCore η s).inter (measurableSet_stripe s a)

end BoltzmannNonuniqueness.JetMaskMeasure

end

end

section

/-! # A fixed smooth compactly supported thermal probability kernel -/

noncomputable section

open MeasureTheory Set Metric
open BoltzmannNonuniqueness.VelocityWeight

namespace BoltzmannNonuniqueness.JetThermalKernel

theorem J_nonneg (v : Velocity) : 0 ≤ J v := bump.nonneg_normed v

theorem J_smooth : ContDiff ℝ (⊤ : ℕ∞) J := bump.contDiff_normed

theorem J_support : Function.support J = ball 0 1 := bump.support_normed_eq

theorem J_zero {v : Velocity} (hv : 1 ≤ ‖v‖) : J v = 0 := by
  by_contra h
  have hs : v ∈ Function.support J := h
  rw [J_support, mem_ball, dist_zero_right] at hs
  exact not_lt_of_ge hv hs

theorem bound_pos : 0 < bound := inv_pos.mpr bump.integral_pos

theorem J_le (v : Velocity) : J v ≤ bound := by
  unfold J ContDiffBump.normed bound
  exact (div_le_div_of_nonneg_right bump.le_one bump.integral_pos.le).trans_eq (one_div _)

end BoltzmannNonuniqueness.JetThermalKernel

end

end

section

/-! # Mass, support and integrability of translated thermal profiles -/

noncomputable section

open MeasureTheory Set Metric
open BoltzmannNonuniqueness.VelocityWeight
open BoltzmannNonuniqueness.JetThermalKernel

namespace BoltzmannNonuniqueness.JetThermalLaw

theorem density_nonneg {d : ℝ} (hd : 0 ≤ d) (a v : Velocity) : 0 ≤ density d a v :=
  mul_nonneg (inv_nonneg.mpr (pow_nonneg hd _)) (J_nonneg _)

theorem density_zero {d : ℝ} (hd : 0 < d) (a v : Velocity) (hv : d ≤ ‖v - a‖) :
    density d a v = 0 := by
  have h : 1 ≤ ‖d⁻¹ • (v - a)‖ := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hd)]
    exact (one_le_inv_mul₀ hd).mpr hv
  simp only [density, scaled, J_zero h, mul_zero]

theorem density_velocity_bound {d : ℝ} (hd : 0 < d) {a v : Velocity}
    (hv : density d a v ≠ 0) : ‖v‖ < ‖a‖ + d := by
  have hdist : ‖v - a‖ < d := lt_of_not_ge (fun h => hv (density_zero hd a v h))
  have hnorm := norm_add_le (v - a) a
  rw [sub_add_cancel] at hnorm
  linarith

theorem density_le {d : ℝ} (hd : 0 ≤ d) (a v : Velocity) :
    density d a v ≤ (d ^ 3)⁻¹ * bound :=
  mul_le_mul_of_nonneg_left (J_le _) (inv_nonneg.mpr (pow_nonneg hd _))

end BoltzmannNonuniqueness.JetThermalLaw

end

end

end OAI
end

section
-- module Solutions.OAIQ080_BZ.Boltzmann_Collision_WeightAlgebra
attribute [-instance] _root_.OAI.BoltzmannNonuniqueness.ChartKernel.coordinateKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ChartKernel.offAxis_sFinite _root_.OAI.BoltzmannNonuniqueness.CollisionCompactness.DoubleGain.incomingBallFinite _root_.OAI.BoltzmannNonuniqueness.CollisionCompactness.DoubleGain.parameterMeasureFinite _root_.OAI.BoltzmannNonuniqueness.EuclideanFlight.sourcePullback_finite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.characteristicGainKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.hotKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.mixedKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.retainedKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.copyColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.mainCoreKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.selectedColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCoreSheet.coreKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCoreSheet.dilatedColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCoreSheet.kineticColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.PeriodicApproximation.fiberMeasure_finite _root_.OAI.BoltzmannNonuniqueness.PositiveIteration.awayOriginKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.PositiveIteration.nearOriginKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamNormalCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamNormalRetainedKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.dampedCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.densityScaledCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.eventParameterMeasure_isFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalBeamKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalCollision_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalPhysicalEvent_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalWindowEvent_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.markedEventMeasure_isFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.physicalEventMeasure_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.scaledBeamNormalKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.WeakTime.phaseEndpointKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.WeakTime.phaseIncrement_finite _root_.OAI.BoltzmannNonuniqueness.WeakTime.phaseSeed_sFinite _root_.OAI.BoltzmannNonuniqueness.WeakTime.residenceKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.normalParameters_sFinite _root_.OAI.BoltzmannNonuniqueness.normalPhaseGainKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.Compactness.instSecondCountableTopologyPositivePhaseTest _root_.OAI.BoltzmannNonuniqueness.Compactness.instSecondCountableTopologySupportedTest
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Weight transfer on a collision plane

The exact Gaussian identity and polynomial transfer turn the normalized
gain weight into the tilted cold measure used in `ker:tilted-kernel`.
-/

noncomputable section

open scoped RealInnerProductSpace

namespace BoltzmannNonuniqueness.VelocityWeight

theorem tiltConstant_pos : 0 < tiltConstant := by unfold tiltConstant; positivity

theorem polynomial_le_gaussian (p : Velocity) :
    (1 + ‖p‖ ^ 2) ^ (50 : ℕ) ≤ tiltConstant * Real.exp (‖p‖ ^ 2) := by
  have hf : 0 < (Nat.factorial 50 : ℝ) := by positivity
  have h := (div_le_iff₀ hf).mp
    (Real.pow_div_factorial_le_exp (1 + ‖p‖ ^ 2) (by positivity) 50)
  calc
    _ ≤ Real.exp (1 + ‖p‖ ^ 2) * (Nat.factorial 50 : ℝ) := h
    _ = _ := by unfold tiltConstant; rw [Real.exp_add]; ring

end BoltzmannNonuniqueness.VelocityWeight

end

end OAI
end

section
-- module Solutions.OAIQ080_BZ.Boltzmann_Branching_GainNonnegative
attribute [-instance] _root_.OAI.BoltzmannNonuniqueness.AnnularEnvelope.instIsFiniteMeasureProdRealPositionTimePositionVolume _root_.OAI.BoltzmannNonuniqueness.ChartKernel.coordinateKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ChartKernel.offAxis_sFinite _root_.OAI.BoltzmannNonuniqueness.CollisionCompactness.DoubleGain.incomingBallFinite _root_.OAI.BoltzmannNonuniqueness.CollisionCompactness.DoubleGain.parameterMeasureFinite _root_.OAI.BoltzmannNonuniqueness.EuclideanFlight.sourcePullback_finite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.characteristicGainKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.hotKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.mixedKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.retainedKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.copyColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.mainCoreKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.selectedColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCoreSheet.coreKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCoreSheet.dilatedColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCoreSheet.kineticColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.PeriodicApproximation.fiberMeasure_finite _root_.OAI.BoltzmannNonuniqueness.PositiveIteration.awayOriginKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.PositiveIteration.nearOriginKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamNormalCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamNormalRetainedKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.dampedCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.densityScaledCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.eventParameterMeasure_isFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalBeamKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalCollision_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalPhysicalEvent_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalWindowEvent_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.markedEventMeasure_isFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.physicalEventMeasure_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.scaledBeamNormalKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.WeakTime.phaseEndpointKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.WeakTime.phaseIncrement_finite _root_.OAI.BoltzmannNonuniqueness.WeakTime.phaseSeed_sFinite _root_.OAI.BoltzmannNonuniqueness.WeakTime.residenceKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.normalParameters_sFinite _root_.OAI.BoltzmannNonuniqueness.normalPhaseGainKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.Compactness.instSecondCountableTopologyPositivePhaseTest _root_.OAI.BoltzmannNonuniqueness.Compactness.instSecondCountableTopologySupportedTest
attribute [-simp] _root_.OAI.BoltzmannNonuniqueness.EuclideanFlight.phaseEquiv_snd _root_.OAI.BoltzmannNonuniqueness.KineticTest.timeShift_toFun _root_.OAI.BoltzmannNonuniqueness.timeTranslation_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

/-! # Positivity and domination for the original gain integral -/

noncomputable section

open MeasureTheory

namespace BoltzmannNonuniqueness.GainOrder

theorem integrand_nonneg {f : Velocity → ℝ} (hf : ∀ w, 0 ≤ f w)
    (v : Velocity) (p : Velocity × Sphere) : 0 ≤ integrand f v p :=
  mul_nonneg (mul_nonneg (collisionKernel_nonneg _ _ _) (hf _)) (hf _)

theorem integrand_mono {f g : Velocity → ℝ} (hf : ∀ w, 0 ≤ f w) (hfg : ∀ w, f w ≤ g w)
    (v : Velocity) (p : Velocity × Sphere) : integrand f v p ≤ integrand g v p := by
  unfold integrand
  exact mul_le_mul (mul_le_mul_of_nonneg_left (hfg _) (collisionKernel_nonneg _ _ _))
    (hfg _) (hf _) (mul_nonneg (collisionKernel_nonneg _ _ _) ((hf _).trans (hfg _)))

theorem integrand_measurable {f : Velocity → ℝ} (hf : Measurable f) (v : Velocity) :
    Measurable (integrand f v) := by
  have hleft : Measurable (fun p : Velocity × Sphere => scatterLeft v p.1 p.2) := by
    unfold scatterLeft normalComponent
    fun_prop
  have hright : Measurable (fun p : Velocity × Sphere => scatterRight v p.1 p.2) := by
    unfold scatterRight normalComponent
    fun_prop
  have hk : Measurable (fun p : Velocity × Sphere => collisionKernel v p.1 p.2) := by
    unfold collisionKernel normalComponent
    fun_prop
  exact (hk.mul (hf.comp hleft)).mul (hf.comp hright)

theorem integrable_of_le {f g : Velocity → ℝ} (hm : Measurable f)
    (hf : ∀ w, 0 ≤ f w) (hfg : ∀ w, f w ≤ g w) (v : Velocity)
    (hg : Integrable (integrand g v) ((volume : Measure Velocity).prod sphereArea)) :
    Integrable (integrand f v) ((volume : Measure Velocity).prod sphereArea) := by
  apply hg.mono' (integrand_measurable hm v).aestronglyMeasurable
  filter_upwards [] with p
  rw [Real.norm_eq_abs, abs_of_nonneg (integrand_nonneg hf v p)]
  exact integrand_mono hf hfg v p

theorem gain_mono {f g : Velocity → ℝ} (hm : Measurable f)
    (hf : ∀ w, 0 ≤ f w) (hfg : ∀ w, f w ≤ g w) (v : Velocity) (x : Position)
    (hg : Integrable (integrand g v) ((volume : Measure Velocity).prod sphereArea)) :
    gain (fun p => f p.2) x v ≤ gain (fun p => g p.2) x v :=
  integral_mono (integrable_of_le hm hf hfg v hg) hg (integrand_mono hf hfg v)

theorem gain_const_mul (c : ℝ) (f : Velocity → ℝ) (v : Velocity) (x : Position) :
    gain (fun p => c * f p.2) x v = c ^ 2 * gain (fun p => f p.2) x v := by
  unfold gain
  rw [← integral_const_mul]
  apply integral_congr_ae
  filter_upwards [] with p
  ring

theorem integrable_const_mul (c : ℝ) {f : Velocity → ℝ} (v : Velocity)
    (hf : Integrable (integrand f v) ((volume : Measure Velocity).prod sphereArea)) :
    Integrable (integrand (fun w => c * f w) v) ((volume : Measure Velocity).prod sphereArea) := by
  convert hf.const_mul (c ^ 2) using 1
  all_goals try with_reducible_and_instances rfl
  funext p
  unfold integrand
  ring

end BoltzmannNonuniqueness.GainOrder

end

end

section

/-! # Conversion from the nonnegative Carleman gain to the real collision operator -/

noncomputable section

open MeasureTheory

namespace BoltzmannNonuniqueness.GainNonnegative

theorem self_eq_lintegral {f : Velocity → ℝ} (hf : ∀ w, 0 ≤ f w) (v : Velocity) :
    nonnegativeGain (fun w => ENNReal.ofReal (f w)) (fun w => ENNReal.ofReal (f w)) v =
      ∫⁻ p, ENNReal.ofReal (GainOrder.integrand f v p)
        ∂((volume : Measure Velocity).prod sphereArea) := by
  unfold nonnegativeGain gainPairMeasure
  apply lintegral_congr
  intro p
  have hp := mul_nonneg (hf (scatterLeft v p.1 p.2)) (hf (scatterRight v p.1 p.2))
  have he : ENNReal.ofReal (collisionKernel v p.1 p.2) / 2 =
      ENNReal.ofReal (collisionKernel v p.1 p.2 / 2) := by
    rw [ENNReal.ofReal_div_of_pos (by norm_num : (0 : ℝ) < 2)]
    norm_num
  rw [← ENNReal.ofReal_mul (hf (scatterLeft v p.1 p.2)),
    ← ENNReal.ofReal_add hp hp, he,
    ← ENNReal.ofReal_mul (div_nonneg (collisionKernel_nonneg _ _ _) (by norm_num))]
  congr 1
  unfold GainOrder.integrand
  ring

theorem integrable_of_bound {f : Velocity → ℝ} (hm : Measurable f) (hf : ∀ w, 0 ≤ f w)
    {B : ℝ} (v : Velocity)
    (hb : nonnegativeGain (fun w => ENNReal.ofReal (f w)) (fun w => ENNReal.ofReal (f w)) v ≤
      ENNReal.ofReal B) :
    Integrable (GainOrder.integrand f v) ((volume : Measure Velocity).prod sphereArea) := by
  refine ⟨(GainOrder.integrand_measurable hm v).aestronglyMeasurable, ?_⟩
  rw [hasFiniteIntegral_iff_ofReal (ae_of_all _ (GainOrder.integrand_nonneg hf v)),
    ← self_eq_lintegral hf v]
  exact hb.trans_lt ENNReal.ofReal_lt_top

theorem gain_le_of_bound {f : Velocity → ℝ} (hm : Measurable f) (hf : ∀ w, 0 ≤ f w)
    {B : ℝ} (hB : 0 ≤ B) (v : Velocity) (x : Position)
    (hb : nonnegativeGain (fun w => ENNReal.ofReal (f w)) (fun w => ENNReal.ofReal (f w)) v ≤
      ENNReal.ofReal B) : gain (fun p => f p.2) x v ≤ B := by
  have hi := integrable_of_bound hm hf v hb
  have he : gain (fun p => f p.2) x v =
      (nonnegativeGain (fun w => ENNReal.ofReal (f w)) (fun w => ENNReal.ofReal (f w)) v).toReal := by
    rw [self_eq_lintegral hf]
    exact integral_eq_lintegral_of_nonneg_ae (ae_of_all _ (GainOrder.integrand_nonneg hf v)) hi.aestronglyMeasurable
  rw [he]
  simpa only [ENNReal.toReal_ofReal hB] using ENNReal.toReal_mono ENNReal.ofReal_ne_top hb

end BoltzmannNonuniqueness.GainNonnegative

end

end

end OAI
end

section
-- module Solutions.OAIQ080_BZ.Boltzmann_Collision_CollisionMeasure
attribute [-instance] _root_.OAI.BoltzmannNonuniqueness.AnnularEnvelope.instIsFiniteMeasureProdRealPositionTimePositionVolume _root_.OAI.BoltzmannNonuniqueness.ChartKernel.coordinateKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ChartKernel.offAxis_sFinite _root_.OAI.BoltzmannNonuniqueness.CollisionCompactness.DoubleGain.incomingBallFinite _root_.OAI.BoltzmannNonuniqueness.CollisionCompactness.DoubleGain.parameterMeasureFinite _root_.OAI.BoltzmannNonuniqueness.EuclideanFlight.sourcePullback_finite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.characteristicGainKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.hotKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.mixedKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.retainedKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.copyColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.mainCoreKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.selectedColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCoreSheet.coreKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCoreSheet.dilatedColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCoreSheet.kineticColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.PeriodicApproximation.fiberMeasure_finite _root_.OAI.BoltzmannNonuniqueness.PositiveIteration.awayOriginKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.PositiveIteration.nearOriginKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamNormalCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamNormalRetainedKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.dampedCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.densityScaledCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.eventParameterMeasure_isFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalBeamKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalCollision_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalPhysicalEvent_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalWindowEvent_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.markedEventMeasure_isFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.physicalEventMeasure_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.scaledBeamNormalKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.WeakTime.phaseEndpointKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.WeakTime.phaseIncrement_finite _root_.OAI.BoltzmannNonuniqueness.WeakTime.phaseSeed_sFinite _root_.OAI.BoltzmannNonuniqueness.WeakTime.residenceKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.normalParameters_sFinite _root_.OAI.BoltzmannNonuniqueness.normalPhaseGainKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.Compactness.instSecondCountableTopologyPositivePhaseTest _root_.OAI.BoltzmannNonuniqueness.Compactness.instSecondCountableTopologySupportedTest
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

/-!
# Measure preservation for a hard-sphere collision

For each fixed unit normal, the pre/post-collisional map is an orthogonal
involution on the six-dimensional velocity-pair space. Its Euclidean norm is
implemented with `WithLp 2`; the final measure statement uses the ordinary
product of the two three-dimensional Lebesgue measures.
-/

noncomputable section

open MeasureTheory
open scoped RealInnerProductSpace

namespace BoltzmannNonuniqueness

/-- Fixed-normal pre/post collision change of variables preserves product Lebesgue measure. -/
theorem scatterPair_measurePreserving (ω : Velocity) (hω : ‖ω‖ = 1) :
    MeasurePreserving (scatterPair ω)
      ((volume : Measure Velocity).prod volume)
      ((volume : Measure Velocity).prod volume) := by
  have h := (WithLp.volume_preserving_ofLp Velocity Velocity).comp
    ((scatterLinearIsometryEquiv ω hω).measurePreserving.comp
      (WithLp.volume_preserving_toLp Velocity Velocity))
  exact h

end BoltzmannNonuniqueness

end

end

section

/-! # The relative-speed cutoff used in the finite approximations -/

noncomputable section

open MeasureTheory

namespace BoltzmannNonuniqueness.CollisionCutoff

theorem rate_nonneg (b : ℝ) (v w : Velocity) : 0 ≤ rate b v w := by
  unfold rate
  split_ifs <;> positivity

theorem rate_le {b : ℝ} (hb : 0 ≤ b) (v w : Velocity) : rate b v w ≤ b := by
  unfold rate
  split_ifs with h
  · exact h.le
  · exact hb

theorem measurable_rate (b : ℝ) (v : Velocity) : Measurable (rate b v) := by
  unfold rate
  exact Measurable.ite (measurableSet_lt (by fun_prop) measurable_const) (by fun_prop) measurable_const

theorem integrable_frequency {b : ℝ} (hb : 0 ≤ b) {f : Velocity → ℝ} (hf : Integrable f)
    (v : Velocity) : Integrable (fun w => rate b v w * f w) := by
  apply (hf.norm.const_mul b).mono' ((measurable_rate b v).aestronglyMeasurable.mul hf.aestronglyMeasurable)
  filter_upwards [] with w
  dsimp only [Pi.mul_apply]
  rw [norm_mul, Real.norm_eq_abs, abs_of_nonneg (rate_nonneg b v w)]
  exact mul_le_mul_of_nonneg_right (rate_le hb v w) (norm_nonneg _)

theorem abs_frequency_le {b : ℝ} (hb : 0 ≤ b) {f : Velocity → ℝ} (hf : Integrable f)
    (v : Velocity) : |frequency b f v| ≤ 2 * Real.pi * b * ∫ w, |f w| := by
  have hi := integrable_frequency hb hf v
  have hm : Integrable (fun w => b * |f w|) := by simpa only [Real.norm_eq_abs] using hf.norm.const_mul b
  have hpoint (w : Velocity) : |rate b v w * f w| ≤ b * |f w| := by
    rw [abs_mul, abs_of_nonneg (rate_nonneg b v w)]
    exact mul_le_mul_of_nonneg_right (rate_le hb v w) (abs_nonneg _)
  calc
    _ = 2 * Real.pi * |∫ w, rate b v w * f w| := by
      rw [frequency, abs_mul, abs_of_pos (by positivity : 0 < 2 * Real.pi)]
    _ ≤ 2 * Real.pi * ∫ w, |rate b v w * f w| :=
      mul_le_mul_of_nonneg_left abs_integral_le_integral_abs (by positivity)
    _ ≤ 2 * Real.pi * ∫ w, b * |f w| := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      exact integral_mono (by simpa only [Real.norm_eq_abs] using hi.norm) hm hpoint
    _ = _ := by rw [integral_const_mul]; ring

theorem kernel_nonneg (b : ℝ) (v w : Velocity) (ω : Sphere) : 0 ≤ kernel b v w ω := by
  unfold kernel
  split_ifs
  · exact collisionKernel_nonneg _ _ _
  · exact le_rfl

theorem kernel_le (b : ℝ) (v w : Velocity) (ω : Sphere) : kernel b v w ω ≤ collisionKernel v w ω := by
  unfold kernel
  split_ifs
  · exact le_rfl
  · exact collisionKernel_nonneg _ _ _

theorem integrand_le (b : ℝ) {f : Velocity → ℝ} (hf : ∀ w, 0 ≤ f w)
    (v : Velocity) (p : Velocity × Sphere) : integrand b f v p ≤ GainOrder.integrand f v p := by
  unfold integrand GainOrder.integrand
  exact mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_right (kernel_le b v p.1 p.2) (hf _)) (hf _)

theorem integrable_gain (b : ℝ) {f : Velocity → ℝ} (hm : Measurable f) (hf : ∀ w, 0 ≤ f w)
    (v : Velocity) (hi : Integrable (GainOrder.integrand f v) ((volume : Measure Velocity).prod sphereArea)) :
    Integrable (integrand b f v) ((volume : Measure Velocity).prod sphereArea) := by
  have he (p : Velocity × Sphere) : integrand b f v p =
      if ‖v - p.1‖ < b then GainOrder.integrand f v p else 0 := by
    unfold integrand kernel GainOrder.integrand
    split_ifs <;> simp only [zero_mul]
  change Integrable (fun p => integrand b f v p) _
  simp_rw [he]
  apply hi.mono'
  · exact ((GainOrder.integrand_measurable hm v).ite
      (measurableSet_lt (by fun_prop) measurable_const) measurable_const).aestronglyMeasurable
  · filter_upwards [] with p
    split_ifs
    · rw [Real.norm_eq_abs, abs_of_nonneg (GainOrder.integrand_nonneg hf v p)]
    · simpa only [norm_zero] using GainOrder.integrand_nonneg hf v p

theorem gain_le (b : ℝ) {f : Velocity → ℝ} (hm : Measurable f) (hf : ∀ w, 0 ≤ f w)
    (v : Velocity) (x : Position)
    (hi : Integrable (GainOrder.integrand f v) ((volume : Measure Velocity).prod sphereArea)) :
    gain b f v ≤ BoltzmannNonuniqueness.gain (fun p => f p.2) x v :=
  integral_mono (integrable_gain b hm hf v hi) hi (integrand_le b hf v)

end BoltzmannNonuniqueness.CollisionCutoff

end

end

section

/-! # Collision operators respect almost-everywhere representatives -/

noncomputable section

open MeasureTheory MeasureTheory.Measure

namespace BoltzmannNonuniqueness.CollisionNullSets

theorem left_pair (ω : Sphere) : QuasiMeasurePreserving
    (fun p : Velocity × Velocity => scatterLeft p.1 p.2 ω)
    ((volume : Measure Velocity).prod volume) volume :=
  MeasureTheory.QuasiMeasurePreserving.fst
    (scatterPair_measurePreserving ω (mem_sphere_zero_iff_norm.mp ω.property)).quasiMeasurePreserving

theorem right_pair (ω : Sphere) : QuasiMeasurePreserving
    (fun p : Velocity × Velocity => scatterRight p.1 p.2 ω)
    ((volume : Measure Velocity).prod volume) volume :=
  MeasureTheory.QuasiMeasurePreserving.snd
    (scatterPair_measurePreserving ω (mem_sphere_zero_iff_norm.mp ω.property)).quasiMeasurePreserving

theorem left_quasiMeasurePreserving : QuasiMeasurePreserving left
    ((volume : Measure Velocity).prod ((volume : Measure Velocity).prod sphereArea)) volume := by
  let : SFinite ((volume : Measure Velocity).prod (volume : Measure Velocity)) := Measure.prod.instSFinite
  have h : QuasiMeasurePreserving
      (fun p : (Velocity × Velocity) × Sphere => scatterLeft p.1.1 p.1.2 p.2)
      (((volume : Measure Velocity).prod volume).prod sphereArea) volume := by
    apply MeasureTheory.QuasiMeasurePreserving.prod_of_left
    · unfold scatterLeft normalComponent
      fun_prop
    · exact ae_of_all _ left_pair
  exact h.comp ((measurePreserving_prodAssoc (volume : Measure Velocity) volume sphereArea).symm
    MeasurableEquiv.prodAssoc).quasiMeasurePreserving

theorem right_quasiMeasurePreserving : QuasiMeasurePreserving right
    ((volume : Measure Velocity).prod ((volume : Measure Velocity).prod sphereArea)) volume := by
  let : SFinite ((volume : Measure Velocity).prod (volume : Measure Velocity)) := Measure.prod.instSFinite
  have h : QuasiMeasurePreserving
      (fun p : (Velocity × Velocity) × Sphere => scatterRight p.1.1 p.1.2 p.2)
      (((volume : Measure Velocity).prod volume).prod sphereArea) volume := by
    apply MeasureTheory.QuasiMeasurePreserving.prod_of_left
    · unfold scatterRight normalComponent
      fun_prop
    · exact ae_of_all _ right_pair
  exact h.comp ((measurePreserving_prodAssoc (volume : Measure Velocity) volume sphereArea).symm
    MeasurableEquiv.prodAssoc).quasiMeasurePreserving

theorem frequency_congr {f g : Velocity → ℝ} (hfg : f =ᵐ[volume] g) (b : ℝ) (v : Velocity) :
    CollisionCutoff.frequency b f v = CollisionCutoff.frequency b g v := by
  unfold CollisionCutoff.frequency
  congr 1
  apply integral_congr_ae
  filter_upwards [hfg] with w hw
  rw [hw]

end BoltzmannNonuniqueness.CollisionNullSets

end

end

end OAI
end

section
-- module Solutions.OAIQ080_BZ.Boltzmann_Compactness_KineticDensityMeasurable
attribute [-instance] _root_.OAI.BoltzmannNonuniqueness.ChartKernel.coordinateKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ChartKernel.offAxis_sFinite _root_.OAI.BoltzmannNonuniqueness.CollisionCompactness.DoubleGain.incomingBallFinite _root_.OAI.BoltzmannNonuniqueness.CollisionCompactness.DoubleGain.parameterMeasureFinite _root_.OAI.BoltzmannNonuniqueness.EuclideanFlight.sourcePullback_finite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.characteristicGainKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.hotKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.mixedKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.retainedKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.copyColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.mainCoreKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.selectedColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCoreSheet.coreKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCoreSheet.dilatedColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCoreSheet.kineticColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.PeriodicApproximation.fiberMeasure_finite _root_.OAI.BoltzmannNonuniqueness.PositiveIteration.awayOriginKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.PositiveIteration.nearOriginKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamNormalCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamNormalRetainedKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.dampedCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.densityScaledCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.eventParameterMeasure_isFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalBeamKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalCollision_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalPhysicalEvent_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalWindowEvent_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.markedEventMeasure_isFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.physicalEventMeasure_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.scaledBeamNormalKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.WeakTime.phaseEndpointKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.WeakTime.phaseIncrement_finite _root_.OAI.BoltzmannNonuniqueness.WeakTime.phaseSeed_sFinite _root_.OAI.BoltzmannNonuniqueness.WeakTime.residenceKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.normalParameters_sFinite _root_.OAI.BoltzmannNonuniqueness.normalPhaseGainKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.Compactness.instSecondCountableTopologyPositivePhaseTest _root_.OAI.BoltzmannNonuniqueness.Compactness.instSecondCountableTopologySupportedTest
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

/-! # Collision representative invariance with space and time parameters -/

noncomputable section

open MeasureTheory MeasureTheory.Measure

namespace BoltzmannNonuniqueness.KineticCollisionNullSets

variable {X : Type*} [MeasurableSpace X]

theorem left_quasiMeasurePreserving (μ : Measure X) [SFinite μ] :
    QuasiMeasurePreserving (left (X := X))
      ((μ.prod (volume : Measure Velocity)).prod ((volume : Measure Velocity).prod sphereArea))
      (μ.prod (volume : Measure Velocity)) := by
  let : SFinite ((volume : Measure Velocity).prod sphereArea) := Measure.prod.instSFinite
  let : SFinite ((volume : Measure Velocity).prod ((volume : Measure Velocity).prod sphereArea)) :=
    Measure.prod.instSFinite
  have h := MeasureTheory.QuasiMeasurePreserving.prodMap
    (MeasurePreserving.id μ).quasiMeasurePreserving CollisionNullSets.left_quasiMeasurePreserving
  exact h.comp (measurePreserving_prodAssoc μ (volume : Measure Velocity)
    ((volume : Measure Velocity).prod sphereArea)).quasiMeasurePreserving

theorem right_quasiMeasurePreserving (μ : Measure X) [SFinite μ] :
    QuasiMeasurePreserving (right (X := X))
      ((μ.prod (volume : Measure Velocity)).prod ((volume : Measure Velocity).prod sphereArea))
      (μ.prod (volume : Measure Velocity)) := by
  let : SFinite ((volume : Measure Velocity).prod sphereArea) := Measure.prod.instSFinite
  let : SFinite ((volume : Measure Velocity).prod ((volume : Measure Velocity).prod sphereArea)) :=
    Measure.prod.instSFinite
  have h := MeasureTheory.QuasiMeasurePreserving.prodMap
    (MeasurePreserving.id μ).quasiMeasurePreserving CollisionNullSets.right_quasiMeasurePreserving
  exact h.comp (measurePreserving_prodAssoc μ (volume : Measure Velocity)
    ((volume : Measure Velocity).prod sphereArea)).quasiMeasurePreserving

theorem gain_congr (μ : Measure X) [SFinite μ] {f g : X × Velocity → ℝ}
    (hfg : f =ᵐ[μ.prod volume] g) (b : ℝ) : gain b f =ᵐ[μ.prod volume] gain b g := by
  let : SFinite ((volume : Measure Velocity).prod sphereArea) := Measure.prod.instSFinite
  have hl := ae_ae_of_ae_prod ((left_quasiMeasurePreserving μ).ae hfg)
  have hr := ae_ae_of_ae_prod ((right_quasiMeasurePreserving μ).ae hfg)
  filter_upwards [hl, hr] with p hlp hrp
  apply integral_congr_ae
  filter_upwards [hlp, hrp] with q hlq hrq
  change f (p.1, scatterLeft p.2 q.1 q.2) = g (p.1, scatterLeft p.2 q.1 q.2) at hlq
  change f (p.1, scatterRight p.2 q.1 q.2) = g (p.1, scatterRight p.2 q.1 q.2) at hrq
  unfold CollisionCutoff.integrand
  dsimp only
  rw [hlq, hrq]

theorem measurable_gain {f : X × Velocity → ℝ} (hf : Measurable f) (b : ℝ) :
    Measurable (gain b f) := by
  let : SFinite ((volume : Measure Velocity).prod sphereArea) := Measure.prod.instSFinite
  have hL : Measurable (fun p : (X × Velocity) × (Velocity × Sphere) => f (left p)) := by
    apply hf.comp
    unfold left scatterLeft normalComponent
    fun_prop
  have hR : Measurable (fun p : (X × Velocity) × (Velocity × Sphere) => f (right p)) := by
    apply hf.comp
    unfold right scatterRight normalComponent
    fun_prop
  have hk : Measurable (fun p : (X × Velocity) × (Velocity × Sphere) =>
      CollisionCutoff.kernel b p.1.2 p.2.1 p.2.2) := by
    unfold CollisionCutoff.kernel
    apply Measurable.ite (measurableSet_lt (by fun_prop) measurable_const)
    · unfold collisionKernel normalComponent
      fun_prop
    · exact measurable_const
  exact ((hk.mul hL).mul hR).stronglyMeasurable.integral_prod_right.measurable

theorem frequency_congr (μ : Measure X) [SFinite μ] {f g : X × Velocity → ℝ}
    (hfg : f =ᵐ[μ.prod volume] g) (b : ℝ) :
    frequency b f =ᵐ[μ.prod volume] frequency b g := by
  have hx := ae_ae_of_ae_prod hfg
  have he : ∀ᵐ x ∂μ, ∀ v, CollisionCutoff.frequency b (fun w => f (x, w)) v =
      CollisionCutoff.frequency b (fun w => g (x, w)) v :=
    hx.mono (fun x hx v => CollisionNullSets.frequency_congr hx b v)
  exact (quasiMeasurePreserving_fst.ae he).mono (fun p hp => hp p.2)

theorem measurable_frequency {f : X × Velocity → ℝ} (hf : Measurable f) (b : ℝ) :
    Measurable (frequency b f) := by
  have hk : Measurable (fun p : (X × Velocity) × Velocity =>
      CollisionCutoff.rate b p.1.2 p.2) := by
    unfold CollisionCutoff.rate
    exact Measurable.ite (measurableSet_lt (by fun_prop) measurable_const)
      (by fun_prop) measurable_const
  have hm : Measurable (fun p : (X × Velocity) × Velocity => f (p.1.1, p.2)) := by
    exact hf.comp (measurable_fst.fst.prodMk measurable_snd)
  exact measurable_const.mul (hk.mul hm).stronglyMeasurable.integral_prod_right.measurable

end BoltzmannNonuniqueness.KineticCollisionNullSets

end

end

end OAI
end

section
-- module Solutions.OAIQ080_BZ.Boltzmann_Branching_ChartPointLift
attribute [-instance] _root_.OAI.BoltzmannNonuniqueness.ChartKernel.coordinateKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ChartKernel.offAxis_sFinite _root_.OAI.BoltzmannNonuniqueness.CollisionCompactness.DoubleGain.incomingBallFinite _root_.OAI.BoltzmannNonuniqueness.CollisionCompactness.DoubleGain.parameterMeasureFinite _root_.OAI.BoltzmannNonuniqueness.EuclideanFlight.sourcePullback_finite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.characteristicGainKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.hotKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.mixedKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.retainedKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.coldCylinderVolume_finite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.copyColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.mainCoreKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.selectedColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCoreSheet.coreKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCoreSheet.dilatedColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCoreSheet.kineticColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.PeriodicApproximation.fiberMeasure_finite _root_.OAI.BoltzmannNonuniqueness.PositiveIteration.awayOriginKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.PositiveIteration.nearOriginKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamNormalCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamNormalRetainedKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.dampedCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.densityScaledCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.eventParameterMeasure_isFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalBeamKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalCollision_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalPhysicalEvent_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalWindowEvent_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.markedEventMeasure_isFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.physicalEventMeasure_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.scaledBeamNormalKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.WeakTime.phaseEndpointKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.WeakTime.phaseIncrement_finite _root_.OAI.BoltzmannNonuniqueness.WeakTime.phaseSeed_sFinite _root_.OAI.BoltzmannNonuniqueness.WeakTime.residenceKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.normalParameters_sFinite _root_.OAI.BoltzmannNonuniqueness.normalPhaseGainKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.Compactness.instSecondCountableTopologyPositivePhaseTest _root_.OAI.BoltzmannNonuniqueness.Compactness.instSecondCountableTopologySupportedTest
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

/-!
# The normalized gain as a measure on chart coordinates

This measure retains the incoming velocity and both plane coordinates. Its
restriction equals the chart gain, so countable shell
estimates concern the full normalized kernel of the manuscript.
-/

noncomputable section

open MeasureTheory Set
open scoped ENNReal
open BoltzmannNonuniqueness.VelocityWeight
open BoltzmannNonuniqueness.PlaneChart

namespace BoltzmannNonuniqueness.ChartKernel

theorem measurable_H (q : ℝ) : Measurable (H q) := by
  unfold H singularity
  fun_prop

end BoltzmannNonuniqueness.ChartKernel

end

end

end OAI
end

section
-- module Solutions.OAIQ080_BZ.Boltzmann_Branching_HotGainReduction
attribute [-instance] _root_.OAI.BoltzmannNonuniqueness.ChartKernel.coordinateKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ChartKernel.offAxis_sFinite _root_.OAI.BoltzmannNonuniqueness.CollisionCompactness.DoubleGain.incomingBallFinite _root_.OAI.BoltzmannNonuniqueness.CollisionCompactness.DoubleGain.parameterMeasureFinite _root_.OAI.BoltzmannNonuniqueness.EuclideanFlight.sourcePullback_finite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.characteristicGainKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.hotKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.mixedKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.retainedKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.copyColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.mainCoreKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.selectedColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCoreSheet.coreKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCoreSheet.dilatedColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCoreSheet.kineticColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.PeriodicApproximation.fiberMeasure_finite _root_.OAI.BoltzmannNonuniqueness.PositiveIteration.awayOriginKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.PositiveIteration.nearOriginKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamNormalCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamNormalRetainedKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.dampedCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.densityScaledCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.eventParameterMeasure_isFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalBeamKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalCollision_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalPhysicalEvent_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalWindowEvent_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.markedEventMeasure_isFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.physicalEventMeasure_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.scaledBeamNormalKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.WeakTime.phaseEndpointKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.WeakTime.phaseIncrement_finite _root_.OAI.BoltzmannNonuniqueness.WeakTime.phaseSeed_sFinite _root_.OAI.BoltzmannNonuniqueness.WeakTime.residenceKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.normalParameters_sFinite _root_.OAI.BoltzmannNonuniqueness.normalPhaseGainKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.Compactness.instSecondCountableTopologyPositivePhaseTest _root_.OAI.BoltzmannNonuniqueness.Compactness.instSecondCountableTopologySupportedTest
attribute [-simp] _root_.OAI.BoltzmannNonuniqueness.EuclideanFlight.phaseEquiv_snd _root_.OAI.BoltzmannNonuniqueness.KineticTest.timeShift_toFun _root_.OAI.BoltzmannNonuniqueness.timeTranslation_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

/-!
# Algebraic reduction of the quadratic hot gain

Symmetry allows the output polynomial weight to be assigned to either
incoming velocity. The resulting mixed gain has only one polynomial factor,
while its two Gaussian factors cancel by collision energy conservation.
-/

noncomputable section

open MeasureTheory
open BoltzmannNonuniqueness.VelocityWeight

namespace BoltzmannNonuniqueness.HotWeight

theorem polynomial_pos (v : Velocity) : 0 < polynomial v := by
  unfold polynomial
  positivity

theorem H_mul_polynomial (q : ℝ) (v : Velocity) : H q v * polynomial v = G q v := by
  unfold H polynomial G
  change Real.exp (-‖v‖ ^ 2) * (1 + ‖v‖ ^ 2) ^ (-50 : ℝ) * W q v *
    (1 + ‖v‖ ^ 2) ^ (50 : ℕ) = _
  rw [show (-50 : ℝ) = -(50 : ℕ) by norm_num,
    Real.rpow_neg (by positivity), Real.rpow_natCast]
  have hp : (1 + ‖v‖ ^ 2) ^ (50 : ℕ) ≠ 0 := by positivity
  field_simp

end BoltzmannNonuniqueness.HotWeight

end

end

end OAI
end

section
-- module Solutions.OAIQ080_BZ.Boltzmann_Branching_HotQuadraticGain
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

/-!
# The quadratic hot-gain bound

The geometric shell estimates and their summation transfer through the
Carleman identity to the original hard-sphere collision variables.
-/

noncomputable section

open MeasureTheory
open scoped ENNReal
open BoltzmannNonuniqueness.VelocityWeight
open BoltzmannNonuniqueness.HotWeight
open BoltzmannNonuniqueness.ChartKernel
open BoltzmannNonuniqueness.HotMixedGain

namespace BoltzmannNonuniqueness.HotApplication

theorem realBound_pos (q : ℝ) : 0 < realBound q := by
  unfold realBound
  positivity

end BoltzmannNonuniqueness.HotApplication

end

end

end OAI
end

section
-- module Solutions.OAIQ080_BZ.Boltzmann_Jets_JetBarriers
attribute [-instance] _root_.OAI.BoltzmannNonuniqueness.ChartKernel.coordinateKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ChartKernel.offAxis_sFinite _root_.OAI.BoltzmannNonuniqueness.CollisionCompactness.DoubleGain.incomingBallFinite _root_.OAI.BoltzmannNonuniqueness.CollisionCompactness.DoubleGain.parameterMeasureFinite _root_.OAI.BoltzmannNonuniqueness.EuclideanFlight.sourcePullback_finite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.characteristicGainKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.hotKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.mixedKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.retainedKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.coldCylinderVolume_finite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.copyColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.mainCoreKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.selectedColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCoreSheet.coreKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCoreSheet.dilatedColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCoreSheet.kineticColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.PeriodicApproximation.fiberMeasure_finite _root_.OAI.BoltzmannNonuniqueness.PositiveIteration.awayOriginKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.PositiveIteration.nearOriginKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamNormalCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamNormalRetainedKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.dampedCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.densityScaledCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.eventParameterMeasure_isFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalBeamKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalCollision_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalPhysicalEvent_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalWindowEvent_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.markedEventMeasure_isFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.physicalEventMeasure_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.scaledBeamNormalKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.WeakTime.phaseEndpointKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.WeakTime.phaseIncrement_finite _root_.OAI.BoltzmannNonuniqueness.WeakTime.phaseSeed_sFinite _root_.OAI.BoltzmannNonuniqueness.WeakTime.residenceKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.normalParameters_sFinite _root_.OAI.BoltzmannNonuniqueness.normalPhaseGainKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.Compactness.instSecondCountableTopologyPositivePhaseTest _root_.OAI.BoltzmannNonuniqueness.Compactness.instSecondCountableTopologySupportedTest
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

/-! # The actual unshifted cold-jet density and its mass bound -/

noncomputable section

open MeasureTheory Set
open BoltzmannNonuniqueness.VelocityWeight
open BoltzmannNonuniqueness.JetGeometry
open BoltzmannNonuniqueness.JetMaskMeasure
open BoltzmannNonuniqueness.JetAxialWeight

namespace BoltzmannNonuniqueness.JetPrototype

theorem axialAmplitude_nonneg {K s : ℝ} (hK : 0 ≤ K) (hs : 0 ≤ s) (γ z : ℝ) :
    0 ≤ axialAmplitude K γ s z := by
  apply indicator_nonneg
  intro z _
  exact mul_nonneg (div_nonneg hK hs) (S_pos _).le

theorem spatial_nonneg {K s : ℝ} (hK : 0 ≤ K) (hs : 0 ≤ s) (η γ : ℝ) (a : Bool) (x : Space) :
    0 ≤ spatial η K γ s a x :=
  mul_nonneg (indicator_nonneg (fun _ _ => zero_le_one) _)
    (axialAmplitude_nonneg hK hs γ _)

theorem density_nonneg {K s d : ℝ} (hK : 0 ≤ K) (hs : 0 ≤ s) (hd : 0 ≤ d)
    (η α γ : ℝ) (a : Bool) (p : Phase) : 0 ≤ density η K α γ s d a p :=
  mul_nonneg (spatial_nonneg hK hs η γ a _)
    (JetThermalLaw.density_nonneg hd _ _)

theorem measurable_spatial (η K γ s : ℝ) (a : Bool) : Measurable (spatial η K γ s a) := by
  unfold spatial axialAmplitude
  exact (((measurable_const.indicator (measurableSet_mask η s a)).comp measurable_fst).mul
    (((continuous_const.mul (continuous_S.comp
      ((continuous_const.mul continuous_id).div_const s))).measurable.indicator measurableSet_Ioo).comp
      measurable_snd))

theorem measurable_center (α γ s : ℝ) (a : Bool) : Measurable (center α γ s a) := by
  change Measurable (fun z => SheetMeasures.join (0, AxialFlow.profile (sign a) α γ s z))
  exact SheetMeasures.join.measurable.comp
    (measurable_const.prodMk (AxialFlow.continuous_profile _ _ _ _).measurable)

theorem measurable_density (η K α γ s d : ℝ) (a : Bool) :
    Measurable (density η K α γ s d a) := by
  unfold density JetThermalLaw.density JetThermalLaw.scaled
  have hc : Measurable (fun p : Phase => center α γ s a p.1.2) :=
    (measurable_center α γ s a).comp (measurable_snd.comp measurable_fst)
  have hv : Measurable (fun p : Phase => d⁻¹ • (p.2 - center α γ s a p.1.2)) :=
    (measurable_const : Measurable (fun _ : Phase => d⁻¹)).smul (measurable_snd.sub hc)
  exact ((measurable_spatial η K γ s a).comp measurable_fst).mul
    (measurable_const.mul (JetThermalKernel.J_smooth.continuous.measurable.comp
      hv))

end BoltzmannNonuniqueness.JetPrototype

end

end

section

/-! # Velocity support and spatial confinement of the free cold cores -/

noncomputable section

open Set Metric
open BoltzmannNonuniqueness.VelocityWeight
open BoltzmannNonuniqueness.JetGeometry
open BoltzmannNonuniqueness.JetPrototype

namespace BoltzmannNonuniqueness.JetSupport

theorem center_norm (α γ s : ℝ) (a : Bool) (z : ℝ) :
    ‖center α γ s a z‖ = |AxialFlow.profile (sign a) α γ s z| := by
  have h := PlaneChart.norm_join_sq (0 : Transverse) (AxialFlow.profile (sign a) α γ s z)
  simp only [norm_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, zero_add] at h
  change ‖center α γ s a z‖ ^ 2 = _ at h
  nlinarith [sq_abs (AxialFlow.profile (sign a) α γ s z), norm_nonneg (center α γ s a z),
    abs_nonneg (AxialFlow.profile (sign a) α γ s z)]

theorem abs_sign (a : Bool) : |sign a| = 1 := by cases a <;> norm_num [sign]

theorem center_norm_bound {α : ℝ} (hα : 0 ≤ α) (γ s : ℝ) (a : Bool) (z : ℝ) :
    ‖center α γ s a z‖ ≤ 1 + α := by
  rw [center_norm]
  have h := AxialFlow.profile_sub_center_le (σ := sign a) (γ := γ) (s := s) (z := z) hα
  have ht := abs_add_le (AxialFlow.profile (sign a) α γ s z - sign a) (sign a)
  rw [sub_add_cancel, abs_sign] at ht
  linarith

theorem density_velocity_bound {d α : ℝ} (hd : 0 < d) (hα : 0 ≤ α)
    (η K γ s : ℝ) (a : Bool) {p : JetPrototype.Phase}
    (hp : JetPrototype.density η K α γ s d a p ≠ 0) : ‖p.2‖ < 1 + α + d := by
  have hthermal : JetThermalLaw.density d (center α γ s a p.1.2) p.2 ≠ 0 :=
    right_ne_zero_of_mul hp
  exact (JetThermalLaw.density_velocity_bound hd hthermal).trans_le
    (add_le_add (center_norm_bound hα γ s a _) le_rfl)

theorem density_support_two {d α : ℝ} (hd : 0 < d) (hdmax : d ≤ 1 / 64)
    (hα : 0 ≤ α) (hαmax : α ≤ 1 / 4) (η K γ s : ℝ) (a : Bool)
    {p : JetPrototype.Phase} (hp : JetPrototype.density η K α γ s d a p ≠ 0) : ‖p.2‖ < 2 := by
  have h := density_velocity_bound hd hα η K γ s a hp
  linarith

theorem initial_spatial_support (η K α γ s d : ℝ) (a : Bool) {p : JetPrototype.Phase}
    (hp : JetPrototype.density η K α γ s d a p ≠ 0) :
    p.1.1 ∈ mask η s a ∧ |p.1.2| < 1 / 8 := by
  have hsp : spatial η K γ s a p.1 ≠ 0 := left_ne_zero_of_mul hp
  have hm : (mask η s a).indicator (fun _ => (1 : ℝ)) p.1.1 ≠ 0 := left_ne_zero_of_mul hsp
  have hz : axialAmplitude K γ s p.1.2 ≠ 0 := right_ne_zero_of_mul hsp
  have hy : p.1.1 ∈ mask η s a := by
    by_contra h
    exact hm (indicator_of_notMem h _)
  have hz' : p.1.2 ∈ Ioo (-(1 / 8 : ℝ)) (1 / 8) := by
    by_contra h
    exact hz (indicator_of_notMem h _)
  exact ⟨hy, abs_lt.mpr hz'⟩

end BoltzmannNonuniqueness.JetSupport

end

end

section

/-! # The actual Gaussian barrier and free-core domination -/

noncomputable section

open MeasureTheory Set Metric
open BoltzmannNonuniqueness.VelocityWeight
open BoltzmannNonuniqueness.JetPrototype
open BoltzmannNonuniqueness.JetAxialWeight
open BoltzmannNonuniqueness.JetCoreFlight

namespace BoltzmannNonuniqueness.JetBarrier

theorem spatial_le {K s : ℝ} (hK : 0 ≤ K) (hs : 0 < s) (η γ : ℝ) (a : Bool) (x : Space) :
    spatial η K γ s a x ≤ K / s := by
  by_cases hy : x.1 ∈ JetGeometry.mask η s a
  · by_cases hz : x.2 ∈ Ioo (-(1 / 8 : ℝ)) (1 / 8)
    · simpa only [spatial, axialAmplitude, indicator_of_mem hy, indicator_of_mem hz, one_mul] using
        mul_le_of_le_one_right (div_nonneg hK hs.le) (S_le_one (γ * x.2 / s))
    · simp only [spatial, axialAmplitude, indicator_of_notMem hz, mul_zero]
      exact div_nonneg hK hs.le
  · simp only [spatial, indicator_of_notMem hy, zero_mul]
    exact div_nonneg hK hs.le

theorem initial_density_bound {K s d : ℝ} (hK : 0 ≤ K) (hs : 0 < s) (hd : 0 ≤ d)
    (η α γ : ℝ) (a : Bool) (p : JetPrototype.Phase) :
    density η K α γ s d a p ≤ (K / s) * (d ^ 3)⁻¹ * JetThermalKernel.bound := by
  calc
    _ ≤ (K / s) * JetThermalLaw.density d (center α γ s a p.1.2) p.2 :=
      mul_le_mul_of_nonneg_right (spatial_le hK hs η γ a p.1) (JetThermalLaw.density_nonneg hd _ _)
    _ ≤ (K / s) * ((d ^ 3)⁻¹ * JetThermalKernel.bound) :=
      mul_le_mul_of_nonneg_left (JetThermalLaw.density_le hd _ _) (div_nonneg hK hs.le)
    _ = _ := by ring

end BoltzmannNonuniqueness.JetBarrier

end

end

section

/-! # Gaussian decay of a cold barrier away from its spatial core -/

noncomputable section

open MeasureTheory
open BoltzmannNonuniqueness.VelocityWeight
open BoltzmannNonuniqueness.JetPrototype
open BoltzmannNonuniqueness.JetBarrier

namespace BoltzmannNonuniqueness.JetGaussianEscape

theorem gaussian_le_hot (q : ℝ) (v : Velocity) :
    Real.exp (-2 * ‖v‖ ^ 2) ≤ tiltConstant * H q v := by
  have hp := polynomial_le_gaussian v
  have hw : 1 ≤ W q v := by unfold W; linarith [singularity_nonneg q (transverse v)]
  have hm := mul_le_mul_of_nonneg_left hp (Real.exp_nonneg (-2 * ‖v‖ ^ 2))
  have hexp : Real.exp (-2 * ‖v‖ ^ 2) * Real.exp (‖v‖ ^ 2) = Real.exp (-‖v‖ ^ 2) := by
    rw [← Real.exp_add]
    congr 1
    ring
  have hprod : Real.exp (-2 * ‖v‖ ^ 2) * HotWeight.polynomial v ≤
      tiltConstant * HotWeight.G q v := by
    calc
      _ ≤ tiltConstant * Real.exp (-‖v‖ ^ 2) := by
        change Real.exp (-2 * ‖v‖ ^ 2) * (1 + ‖v‖ ^ 2) ^ (50 : ℕ) ≤ _
        calc
          _ ≤ Real.exp (-2 * ‖v‖ ^ 2) * (tiltConstant * Real.exp (‖v‖ ^ 2)) := hm
          _ = _ := by rw [mul_left_comm, hexp]
      _ ≤ _ := by
        unfold HotWeight.G
        simpa only [mul_one, mul_assoc] using mul_le_mul_of_nonneg_left hw
          (mul_nonneg tiltConstant_pos.le (Real.exp_nonneg (-‖v‖ ^ 2)))
  rw [← HotWeight.H_mul_polynomial] at hprod
  exact (mul_le_mul_iff_of_pos_right (HotWeight.polynomial_pos v)).mp (by
    simpa only [mul_assoc] using hprod)

end BoltzmannNonuniqueness.JetGaussianEscape

end

end

end OAI
end

section
-- module Solutions.OAIQ080_BZ.Boltzmann_Jets_JetPeriodicDatum
attribute [-instance] _root_.OAI.BoltzmannNonuniqueness.ChartKernel.coordinateKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ChartKernel.offAxis_sFinite _root_.OAI.BoltzmannNonuniqueness.CollisionCompactness.DoubleGain.incomingBallFinite _root_.OAI.BoltzmannNonuniqueness.CollisionCompactness.DoubleGain.parameterMeasureFinite _root_.OAI.BoltzmannNonuniqueness.EuclideanFlight.sourcePullback_finite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.characteristicGainKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.hotKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.mixedKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.retainedKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.coldCylinderVolume_finite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.copyColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.mainCoreKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.selectedColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCoreSheet.coreKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCoreSheet.dilatedColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCoreSheet.kineticColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.PeriodicApproximation.fiberMeasure_finite _root_.OAI.BoltzmannNonuniqueness.PositiveIteration.awayOriginKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.PositiveIteration.nearOriginKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamNormalCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamNormalRetainedKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.dampedCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.densityScaledCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.eventParameterMeasure_isFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalBeamKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalCollision_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalPhysicalEvent_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalWindowEvent_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.markedEventMeasure_isFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.physicalEventMeasure_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.scaledBeamNormalKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.WeakTime.phaseEndpointKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.WeakTime.phaseIncrement_finite _root_.OAI.BoltzmannNonuniqueness.WeakTime.phaseSeed_sFinite _root_.OAI.BoltzmannNonuniqueness.WeakTime.residenceKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.normalParameters_sFinite _root_.OAI.BoltzmannNonuniqueness.normalPhaseGainKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.Compactness.instSecondCountableTopologyPositivePhaseTest _root_.OAI.BoltzmannNonuniqueness.Compactness.instSecondCountableTopologySupportedTest
attribute [-simp] _root_.OAI.BoltzmannNonuniqueness.EuclideanFlight.phaseEquiv_snd
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

/-! # Integration of the nonnegative, disjoint cold-jet series -/

noncomputable section

open MeasureTheory
open BoltzmannNonuniqueness.JetThermalEntropy

namespace BoltzmannNonuniqueness.JetSeries

theorem summable_single_support {ι : Type*} {f : ι → ℝ}
    (hf : ∀ i j, i ≠ j → f i ≠ 0 → f j = 0) : Summable f := by
  classical
  by_cases h : ∃ i, f i ≠ 0
  · obtain ⟨i, hi⟩ := h
    exact summable_of_ne_finset_zero (s := {i}) (fun j hj => hf i j (by simpa [eq_comm] using hj) hi)
  · have he : f = 0 := by ext i; simpa using not_exists.mp h i
    rw [he]
    exact summable_zero

end BoltzmannNonuniqueness.JetSeries

end

end

section

/-! # The full unperiodized cold datum -/

noncomputable section

open MeasureTheory Set
open BoltzmannNonuniqueness.VelocityWeight
open BoltzmannNonuniqueness.JetPrototype
open BoltzmannNonuniqueness.JetGeometry
open BoltzmannNonuniqueness.JetThermalEntropy

namespace BoltzmannNonuniqueness.JetDatum

theorem term_nonneg {s₀ K d₀ : ℝ} (hs₀ : 0 < s₀) (hK : 0 ≤ K) (hd₀ : 0 ≤ d₀)
    (η α γ : ℝ) (i : Index) (p : JetPrototype.Phase) : 0 ≤ term s₀ η K α γ d₀ i p :=
  density_nonneg hK (DatumBounds.scale_pos hs₀ _).le
    (mul_nonneg hd₀ (pow_nonneg (DatumBounds.scale_pos hs₀ _).le _)) η α γ i.2 p

theorem term_measurable (s₀ η K α γ d₀ : ℝ) (i : Index) :
    Measurable (term s₀ η K α γ d₀ i) := measurable_density _ _ _ _ _ _ _

end BoltzmannNonuniqueness.JetDatum

end

end

section

/-! # Mass, energy, and entropy of the full cold datum -/

noncomputable section

open MeasureTheory
open BoltzmannNonuniqueness.JetPrototype
open BoltzmannNonuniqueness.JetGeometry
open BoltzmannNonuniqueness.JetThermalEntropy
open BoltzmannNonuniqueness.JetDatum

namespace BoltzmannNonuniqueness.JetDatumMoments

theorem thermal_width_le {s₀ η d₀ : ℝ} (hs₀ : 0 < s₀) (hsmax : s₀ ≤ 1 / 8)
    (hη : 0 ≤ η) (hd₀ : 0 ≤ d₀) (hwidth : d₀ * (1 / 8 : ℝ) ^ 10 ≤ 1 / 64) (j : ℕ) :
    d₀ * jetScale s₀ η j ^ 10 ≤ 1 / 64 := by
  have hs : jetScale s₀ η j ≤ 1 / 8 := by
    change DatumBounds.scale s₀ η (j + 1) ≤ _
    calc
      _ ≤ DatumBounds.scale s₀ η 0 := scale_antitone hs₀.le hη (Nat.zero_le (j + 1))
      _ = s₀ := by simp [DatumBounds.scale]
      _ ≤ _ := hsmax
  exact (mul_le_mul_of_nonneg_left
    (pow_le_pow_left₀ (DatumBounds.scale_pos hs₀ _).le hs 10) hd₀).trans hwidth

end BoltzmannNonuniqueness.JetDatumMoments

end

end

section

/-! # The free cold core in Eulerian coordinates -/

noncomputable section

open MeasureTheory
open BoltzmannNonuniqueness.JetPrototype
open BoltzmannNonuniqueness.JetBarrier
open BoltzmannNonuniqueness.VelocityWeight

namespace BoltzmannNonuniqueness.JetFreeTransport

theorem flight_add (t r : ℝ) (p : JetPrototype.Phase) :
    flight t (flight r p) = flight (t + r) p := by
  apply Prod.ext
  · apply Prod.ext
    · dsimp only [flight]
      module
    · dsimp only [flight]
      ring
  · rfl

@[simp] theorem flight_neg (t : ℝ) (p : JetPrototype.Phase) : flight t (flight (-t) p) = p := by
  rw [flight_add, add_neg_cancel, flight_zero]

@[simp] theorem neg_flight (t : ℝ) (p : JetPrototype.Phase) : flight (-t) (flight t p) = p := by
  rw [flight_add, neg_add_cancel, flight_zero]

end BoltzmannNonuniqueness.JetFreeTransport

end

end

end OAI
end

section
-- module Solutions.OAIQ080_BZ.Boltzmann_Jets_JetCoreMomentBound
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

/-! # Arbitrary-power bounds for the complete escaped-barrier sum -/

noncomputable section

open MeasureTheory Set
open scoped ENNReal
open BoltzmannNonuniqueness.VelocityWeight
open BoltzmannNonuniqueness.JetGeometry
open BoltzmannNonuniqueness.JetPrototype
open BoltzmannNonuniqueness.JetBarrier
open BoltzmannNonuniqueness.JetLattice
open BoltzmannNonuniqueness.JetSpatialBox
open BoltzmannNonuniqueness.JetLatticeTail

namespace BoltzmannNonuniqueness.JetEscapedTotal

theorem coefficient_nonneg {K d₀ : ℝ} (hK : 0 ≤ K) (hd₀ : 0 < d₀) (α : ℝ) :
    0 ≤ coefficient α K d₀ := by
  have hL : 0 ≤ JetLatticeGaussian.constant := by
    unfold JetLatticeGaussian.constant JetLatticeGaussian.exponential
    positivity
  unfold coefficient JetEscapedBarrier.coefficient JetGaussianEscape.constant
  have := JetThermalKernel.bound_pos
  positivity

theorem powerConstant_nonneg {s₀ K d₀ : ℝ} (hs₀ : 0 < s₀) (hK : 0 ≤ K) (hd₀ : 0 < d₀)
    (η α : ℝ) (m : ℕ) : 0 ≤ powerConstant s₀ η α K d₀ m := by
  have hr : 0 ≤ JetEscapedBarrier.rate η d₀ := by
    unfold JetEscapedBarrier.rate
    positivity
  unfold powerConstant
  apply mul_nonneg (mul_nonneg (coefficient_nonneg hK hd₀ α) (by positivity))
  exact tsum_nonneg (fun j => pow_nonneg (DatumBounds.scale_pos (η := η) hs₀ (j + 1)).le _)

end BoltzmannNonuniqueness.JetEscapedTotal

end

end

section

/-! # Escaped sums for arbitrary retained cold colors

The comparison hypothesis here is a pointwise bound for a color family. It is
kept explicit for application to the solutions of the finite labeled system.
All constants are independent of the retained subset.
-/

noncomputable section

open MeasureTheory Set
open scoped ENNReal
open BoltzmannNonuniqueness.VelocityWeight
open BoltzmannNonuniqueness.JetGeometry
open BoltzmannNonuniqueness.JetLattice
open BoltzmannNonuniqueness.JetSpatialBox
open BoltzmannNonuniqueness.JetLatticeTail

namespace BoltzmannNonuniqueness.JetEscapedEnvelope

theorem constant_nonneg {s₀ K d₀ : ℝ} (hs₀ : 0 < s₀) (hK : 0 ≤ K) (hd₀ : 0 < d₀)
    (η α : ℝ) (m : ℕ) : 0 ≤ constant s₀ η α K d₀ m :=
  mul_nonneg (mul_nonneg (by norm_num) (JetEscapedTotal.powerConstant_nonneg hs₀ hK hd₀ η α m))
    tiltConstant_pos.le

end BoltzmannNonuniqueness.JetEscapedEnvelope

end

end

end OAI
end

section
-- module Solutions.OAIQ080_BZ.Boltzmann_Branching_GainSmoothingError
attribute [-instance] _root_.OAI.BoltzmannNonuniqueness.ChartKernel.offAxis_sFinite _root_.OAI.BoltzmannNonuniqueness.EuclideanFlight.sourcePullback_finite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.characteristicGainKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.hotKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.mixedKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.retainedKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.copyColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.mainCoreKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.selectedColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCoreSheet.dilatedColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCoreSheet.kineticColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.PeriodicApproximation.fiberMeasure_finite _root_.OAI.BoltzmannNonuniqueness.PositiveIteration.awayOriginKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.PositiveIteration.nearOriginKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamNormalCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamNormalRetainedKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.dampedCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.densityScaledCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.eventParameterMeasure_isFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalBeamKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalCollision_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalPhysicalEvent_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalWindowEvent_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.markedEventMeasure_isFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.physicalEventMeasure_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.scaledBeamNormalKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.WeakTime.phaseEndpointKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.WeakTime.phaseIncrement_finite _root_.OAI.BoltzmannNonuniqueness.WeakTime.phaseSeed_sFinite _root_.OAI.BoltzmannNonuniqueness.WeakTime.residenceKernel_sFinite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

/-! # One-sided gain differences for the nonlinear cold comparison -/

noncomputable section

open MeasureTheory
open BoltzmannNonuniqueness.VelocityWeight

namespace BoltzmannNonuniqueness.GainUpperDifference

theorem integrand_bound {f g : Velocity → ℝ} {q A B D : ℝ} (hD : 0 ≤ D)
    (hf : ∀ w, 0 ≤ f w) (hg : ∀ w, 0 ≤ g w)
    (hfB : ∀ w, f w ≤ A * H q w) (hgB : ∀ w, g w ≤ B * H q w)
    (hfg : ∀ w, f w - g w ≤ D * H q w) (v : Velocity) (p : Velocity × Sphere) :
    GainOrder.integrand f v p - GainOrder.integrand g v p ≤
      (D * (A + B)) * GainOrder.integrand (H q) v p := by
  let l := scatterLeft v p.1 p.2
  let r := scatterRight v p.1 p.2
  have h1 : (f l - g l) * f r ≤ (D * H q l) * (A * H q r) :=
    (mul_le_mul_of_nonneg_right (hfg l) (hf r)).trans
      (mul_le_mul_of_nonneg_left (hfB r) (mul_nonneg hD (H_nonneg q l)))
  have h2 : g l * (f r - g r) ≤ (B * H q l) * (D * H q r) :=
    (mul_le_mul_of_nonneg_left (hfg r) (hg l)).trans
      (mul_le_mul_of_nonneg_right (hgB l) (mul_nonneg hD (H_nonneg q r)))
  have he : GainOrder.integrand f v p - GainOrder.integrand g v p =
      collisionKernel v p.1 p.2 * ((f l - g l) * f r + g l * (f r - g r)) := by
    unfold GainOrder.integrand l r
    ring
  rw [he]
  calc
    _ ≤ collisionKernel v p.1 p.2 *
        ((D * H q l) * (A * H q r) + (B * H q l) * (D * H q r)) :=
      mul_le_mul_of_nonneg_left (add_le_add h1 h2) (collisionKernel_nonneg _ _ _)
    _ = _ := by unfold GainOrder.integrand l r; ring

theorem cutoff_integrand_bound {f g : Velocity → ℝ} {q A B D : ℝ}
    (hA : 0 ≤ A) (hB : 0 ≤ B) (hD : 0 ≤ D)
    (hf : ∀ w, 0 ≤ f w) (hg : ∀ w, 0 ≤ g w)
    (hfB : ∀ w, f w ≤ A * H q w) (hgB : ∀ w, g w ≤ B * H q w)
    (hfg : ∀ w, f w - g w ≤ D * H q w) (b : ℝ) (v : Velocity) (p : Velocity × Sphere) :
    CollisionCutoff.integrand b f v p - CollisionCutoff.integrand b g v p ≤
      (D * (A + B)) * GainOrder.integrand (H q) v p := by
  by_cases hp : ‖v - p.1‖ < b
  · simpa only [CollisionCutoff.integrand, CollisionCutoff.kernel, GainOrder.integrand, ite_eq_left hp] using
      integrand_bound hD hf hg hfB hgB hfg v p
  · simp only [CollisionCutoff.integrand, CollisionCutoff.kernel, ite_eq_right hp, zero_mul, sub_self]
    exact mul_nonneg (mul_nonneg hD (add_nonneg hA hB)) (GainOrder.integrand_nonneg (H_nonneg q) v p)

end BoltzmannNonuniqueness.GainUpperDifference

end

end

end OAI
end

section
-- module Solutions.OAIQ080_BZ.Boltzmann_Approximation_CutoffLipschitz
attribute [-instance] _root_.OAI.BoltzmannNonuniqueness.ChartKernel.offAxis_sFinite _root_.OAI.BoltzmannNonuniqueness.EuclideanFlight.sourcePullback_finite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.characteristicGainKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.hotKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.mixedKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.retainedKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.copyColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.mainCoreKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.selectedColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCoreSheet.dilatedColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCoreSheet.kineticColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.PeriodicApproximation.fiberMeasure_finite _root_.OAI.BoltzmannNonuniqueness.PositiveIteration.awayOriginKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.PositiveIteration.nearOriginKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamNormalCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamNormalRetainedKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.dampedCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.densityScaledCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.eventParameterMeasure_isFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalBeamKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalCollision_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalPhysicalEvent_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalWindowEvent_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.markedEventMeasure_isFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.physicalEventMeasure_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.scaledBeamNormalKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.WeakTime.phaseEndpointKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.WeakTime.phaseIncrement_finite _root_.OAI.BoltzmannNonuniqueness.WeakTime.phaseSeed_sFinite _root_.OAI.BoltzmannNonuniqueness.WeakTime.residenceKernel_sFinite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Local weighted Lipschitz bounds for the finite-cutoff equation -/

noncomputable section

open MeasureTheory
open BoltzmannNonuniqueness.VelocityWeight

namespace BoltzmannNonuniqueness.CutoffLipschitz

theorem frequencyConstant_nonneg {b : ℝ} (hb : 0 ≤ b) (q : ℝ) : 0 ≤ frequencyConstant q b := by
  unfold frequencyConstant
  have hi : 0 ≤ ∫ w, H q w := integral_nonneg (H_nonneg q)
  positivity

theorem integrable_dominated {q A : ℝ} (hq : q < 2) {f : Velocity → ℝ}
    (hfm : Measurable f) (hf : ∀ w, 0 ≤ f w) (hfB : ∀ w, f w ≤ A * H q w) : Integrable f := by
  apply ((integrable_H hq).const_mul A).mono' hfm.aestronglyMeasurable
  filter_upwards [] with w
  simpa only [Real.norm_eq_abs, abs_of_nonneg (hf w)] using hfB w

theorem frequency_nonneg {f : Velocity → ℝ} (hf : ∀ w, 0 ≤ f w) (b : ℝ) (v : Velocity) :
    0 ≤ CollisionCutoff.frequency b f v := by
  apply mul_nonneg (by positivity)
  exact integral_nonneg (fun w => mul_nonneg (CollisionCutoff.rate_nonneg b v w) (hf w))

theorem frequency_bound {q A b : ℝ} (hq : q < 2) (hb : 0 ≤ b)
    {f : Velocity → ℝ} (hfm : Measurable f) (hf : ∀ w, 0 ≤ f w)
    (hfB : ∀ w, f w ≤ A * H q w) (v : Velocity) :
    CollisionCutoff.frequency b f v ≤ A * frequencyConstant q b := by
  have hi := integrable_dominated hq hfm hf hfB
  calc
    _ ≤ 2 * Real.pi * b * ∫ w, |f w| :=
      (le_abs_self _).trans (CollisionCutoff.abs_frequency_le hb hi v)
    _ ≤ 2 * Real.pi * b * ∫ w, A * H q w := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      exact integral_mono hi.abs ((integrable_H hq).const_mul A)
        (fun w => by simpa only [abs_of_nonneg (hf w)] using hfB w)
    _ = _ := by rw [integral_const_mul]; unfold frequencyConstant; ring

theorem frequency_difference {q A B D b : ℝ} (hq : q < 2) (hb : 0 ≤ b)
    {f g : Velocity → ℝ} (hfm : Measurable f) (hgm : Measurable g)
    (hf : ∀ w, 0 ≤ f w) (hg : ∀ w, 0 ≤ g w)
    (hfB : ∀ w, f w ≤ A * H q w) (hgB : ∀ w, g w ≤ B * H q w)
    (hfg : ∀ w, |f w - g w| ≤ D * H q w) (v : Velocity) :
    |CollisionCutoff.frequency b f v - CollisionCutoff.frequency b g v| ≤ D * frequencyConstant q b := by
  have hfi := integrable_dominated hq hfm hf hfB
  have hgi := integrable_dominated hq hgm hg hgB
  have he : CollisionCutoff.frequency b f v - CollisionCutoff.frequency b g v =
      CollisionCutoff.frequency b (fun w => f w - g w) v := by
    unfold CollisionCutoff.frequency
    rw [← mul_sub, ← integral_sub (CollisionCutoff.integrable_frequency hb hfi v)
      (CollisionCutoff.integrable_frequency hb hgi v)]
    congr 2
    funext w
    ring
  rw [he]
  calc
    _ ≤ 2 * Real.pi * b * ∫ w, |f w - g w| :=
      CollisionCutoff.abs_frequency_le hb (hfi.sub hgi) v
    _ ≤ 2 * Real.pi * b * ∫ w, D * H q w := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      exact integral_mono (hfi.sub hgi).abs ((integrable_H hq).const_mul D) hfg
    _ = _ := by rw [integral_const_mul]; unfold frequencyConstant; ring

end BoltzmannNonuniqueness.CutoffLipschitz

end

end OAI
end

section
-- module Solutions.OAIQ080_BZ.Boltzmann_Approximation_PositiveIntegralFixedPoint
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

/-! # Positive integral contraction along measurable characteristics

This lemma constructs a fixed point of a bounded positive source map.
The collision source and its quantitative estimates are supplied separately.
-/

noncomputable section

open MeasureTheory Set
open scoped Topology

namespace BoltzmannNonuniqueness.PositiveIntegral

variable {P : Type*} [MeasurableSpace P]

theorem value_difference {T L S D : ℝ} (hT : 0 ≤ T) (hL : 0 ≤ L) (hD : 0 ≤ D)
    {flow : ℝ → P → P} (hflow : Measurable (fun z : ℝ × P => flow z.1 z.2))
    (f₀ : P → ℝ) {g h : Domain P → ℝ} (hgm : Measurable g) (hhm : Measurable h)
    (hg : ∀ z, |g z| ≤ S) (hh : ∀ z, |h z| ≤ S) (hgh : ∀ z, |g z - h z| ≤ D)
    (z : Domain P) : |value T L flow f₀ g z - value T L flow f₀ h z| ≤ T * D := by
  have ht := time_bounds hT z.1
  have hgi := damped_integrable hT hL hflow hgm hg z
  have hhi := damped_integrable hT hL hflow hhm hh z
  unfold value
  rw [add_sub_add_left_eq_sub, ← intervalIntegral.integral_sub hgi hhi]
  have hb := intervalIntegral.norm_integral_le_of_norm_le_const (a := 0) (b := time T z.1)
    (C := D) (f := fun r =>
      Real.exp (-L * (time T z.1 - r)) * g (r, flow (r - time T z.1) z.2) -
      Real.exp (-L * (time T z.1 - r)) * h (r, flow (r - time T z.1) z.2))
    (fun r hr => by
      rw [uIoc_of_le ht.1] at hr
      rw [← mul_sub, Real.norm_eq_abs, abs_mul, abs_of_pos (Real.exp_pos _)]
      have he : Real.exp (-L * (time T z.1 - r)) ≤ 1 :=
        Real.exp_le_one_iff.mpr (by nlinarith [hr.2])
      exact (mul_le_mul_of_nonneg_right he (abs_nonneg _)).trans (by simpa using hgh _))
  rw [Real.norm_eq_abs, sub_zero, abs_of_nonneg ht.1] at hb
  exact hb.trans (by nlinarith)

/-- Positive Picard iteration converges in the complete sup-norm space. -/
theorem exists_fixed_point {T L A R S K : ℝ} (hT : 0 ≤ T) (hL : 0 ≤ L)
    (hA : 0 ≤ A) (hR : 0 ≤ R) (hS : 0 ≤ S) (hK : 0 ≤ K)
    (hball : A + T * S ≤ R) (hsmall : T * K < 1)
    {flow : ℝ → P → P} (hflow : Measurable (fun z : ℝ × P => flow z.1 z.2))
    {f₀ : P → ℝ} (hf₀m : Measurable f₀) (hf₀ : ∀ p, 0 ≤ f₀ p ∧ f₀ p ≤ A)
    (source : BoundedMeasurable.PositiveBall (Domain P) R → Domain P → ℝ)
    (hsm : ∀ f, Measurable (source f))
    (hsb : ∀ f z, 0 ≤ source f z ∧ source f z ≤ S)
    (hsl : ∀ f g z, |source f z - source g z| ≤ K * dist f g) :
    ∃ f : BoundedMeasurable.PositiveBall (Domain P) R,
      ∀ z, f.val z = value T L flow f₀ (source f) z := by
  let step : BoundedMeasurable.PositiveBall (Domain P) R →
      BoundedMeasurable.PositiveBall (Domain P) R := fun f =>
    ⟨BoundedMeasurable.ofBounded (Domain P) (value T L flow f₀ (source f))
      (measurable_value hT hflow hf₀m (hsm f)) (A + T * S)
      (fun z => by
        rw [abs_of_nonneg (value_bounds hT hL hA hS flow hf₀ (hsb f) z).1]
        exact (value_bounds hT hL hA hS flow hf₀ (hsb f) z).2),
      fun z => ⟨(value_bounds hT hL hA hS flow hf₀ (hsb f) z).1,
        (value_bounds hT hL hA hS flow hf₀ (hsb f) z).2.trans hball⟩⟩
  have hc : ContractingWith ⟨T * K, mul_nonneg hT hK⟩ step := by
    constructor
    · exact hsmall
    · apply LipschitzWith.of_dist_le_mul
      intro f g
      change dist (step f).val (step g).val ≤ (T * K) * dist f g
      apply BoundedMeasurable.dist_le (Domain P) (by positivity)
      intro z
      have h := value_difference hT hL (mul_nonneg hK dist_nonneg) hflow f₀
        (hsm f) (hsm g)
        (fun z => by rw [abs_of_nonneg (hsb f z).1]; exact (hsb f z).2)
        (fun z => by rw [abs_of_nonneg (hsb g z).1]; exact (hsb g z).2)
        (hsl f g) z
      simpa only [step, BoundedMeasurable.ofBounded_apply, mul_assoc] using h
  let zero : BoundedMeasurable.PositiveBall (Domain P) R :=
    ⟨BoundedMeasurable.ofBounded (Domain P) (fun _ => 0) measurable_const 0
      (fun _ => by simp), fun _ => ⟨le_rfl, hR⟩⟩
  let : Nonempty (BoundedMeasurable.PositiveBall (Domain P) R) := ⟨zero⟩
  refine ⟨hc.fixedPoint, ?_⟩
  intro z
  have he := congrArg (fun f : BoundedMeasurable.PositiveBall (Domain P) R => f.val z)
    hc.fixedPoint_isFixedPt
  exact he.symm

end BoltzmannNonuniqueness.PositiveIntegral

end

end

section

/-! # Order and dominated convergence for positive characteristic integrals -/

noncomputable section

open MeasureTheory Set Filter
open scoped Topology

namespace BoltzmannNonuniqueness.PositiveIntegral

variable {P : Type*} [MeasurableSpace P]

theorem value_mono {T L S : ℝ} (hT : 0 ≤ T) (hL : 0 ≤ L)
    {flow : ℝ → P → P} (hflow : Measurable (fun z : ℝ × P => flow z.1 z.2))
    {f₀ k₀ : P → ℝ} (hfk : ∀ p, f₀ p ≤ k₀ p)
    {g h : Domain P → ℝ} (hgm : Measurable g) (hhm : Measurable h)
    (hg : ∀ z, |g z| ≤ S) (hh : ∀ z, |h z| ≤ S) (hgh : ∀ z, g z ≤ h z)
    (z : Domain P) : value T L flow f₀ g z ≤ value T L flow k₀ h z := by
  apply add_le_add
  · exact mul_le_mul_of_nonneg_left (hfk _) (Real.exp_pos _).le
  · apply intervalIntegral.integral_mono_on (time_bounds hT z.1).1
      (damped_integrable hT hL hflow hgm hg z) (damped_integrable hT hL hflow hhm hh z)
    intro r _
    exact mul_le_mul_of_nonneg_left (hgh _) (Real.exp_pos _).le

theorem value_tendsto {T L S : ℝ} (hT : 0 ≤ T) (hL : 0 ≤ L)
    {flow : ℝ → P → P} (hflow : Measurable (fun z : ℝ × P => flow z.1 z.2))
    (f₀ : P → ℝ) {g : ℕ → Domain P → ℝ} {h : Domain P → ℝ}
    (hgm : ∀ n, Measurable (g n)) (hg : ∀ n z, |g n z| ≤ S)
    (hlim : ∀ z, Tendsto (fun n => g n z) atTop (𝓝 (h z)))
    (z : Domain P) : Tendsto (fun n => value T L flow f₀ (g n) z) atTop
      (𝓝 (value T L flow f₀ h z)) := by
  apply tendsto_const_nhds.add
  apply intervalIntegral.tendsto_integral_filter_of_dominated_convergence (fun _ => S)
  · exact .of_forall (fun n => (damped_integrable hT hL hflow (hgm n) (hg n) z).def'.aestronglyMeasurable)
  · apply Eventually.of_forall
    intro n
    apply ae_of_all
    intro r hr
    rw [uIoc_of_le (time_bounds hT z.1).1] at hr
    rw [Real.norm_eq_abs, abs_mul, abs_of_pos (Real.exp_pos _)]
    have he : Real.exp (-L * (time T z.1 - r)) ≤ 1 := Real.exp_le_one_iff.mpr (by nlinarith [hr.2])
    exact (mul_le_mul_of_nonneg_right he (abs_nonneg _)).trans (by simpa using hg n _)
  · exact intervalIntegrable_const
  · exact ae_of_all _ (fun r _ => tendsto_const_nhds.mul (hlim _))

end BoltzmannNonuniqueness.PositiveIntegral

end

end

section

/-! # Dependence of the characteristic map on its initial value -/

noncomputable section

open MeasureTheory

namespace BoltzmannNonuniqueness.PositiveIntegral

variable {P : Type*} [MeasurableSpace P]

theorem value_difference_initial {T L S D I : ℝ} (hT : 0 ≤ T) (hL : 0 ≤ L)
    (hD : 0 ≤ D) (_hI : 0 ≤ I)
    {flow : ℝ → P → P} (hflow : Measurable (fun z : ℝ × P => flow z.1 z.2))
    {f₀ k₀ : P → ℝ} (hfk : ∀ p, |f₀ p-k₀ p| ≤ I)
    {g h : Domain P → ℝ} (hgm : Measurable g) (hhm : Measurable h)
    (hg : ∀ z, |g z| ≤ S) (hh : ∀ z, |h z| ≤ S) (hgh : ∀ z, |g z-h z| ≤ D)
    (z : Domain P) : |value T L flow f₀ g z-value T L flow k₀ h z| ≤ I+T*D := by
  have hsource := value_difference hT hL hD hflow f₀ hgm hhm hg hh hgh z
  have hinitial : |value T L flow f₀ h z-value T L flow k₀ h z| ≤ I := by
    have heq : value T L flow f₀ h z-value T L flow k₀ h z =
        Real.exp (-L*time T z.1) * (f₀ (flow (-time T z.1) z.2)-k₀ (flow (-time T z.1) z.2)) := by
      unfold value
      ring
    rw [heq, abs_mul, abs_of_pos (Real.exp_pos _)]
    have he : Real.exp (-L*time T z.1) ≤ 1 := Real.exp_le_one_iff.mpr
      (mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hL) (time_bounds hT z.1).1)
    exact (mul_le_mul he (hfk _) (abs_nonneg _) (by norm_num)).trans_eq (one_mul I)
  exact (abs_sub_le _ _ _).trans ((add_le_add hsource hinitial).trans_eq (add_comm _ _))

end BoltzmannNonuniqueness.PositiveIntegral

end

end

section

/-! # Finite sums of positive characteristic integrals -/

noncomputable section

open MeasureTheory
open scoped BigOperators

namespace BoltzmannNonuniqueness.PositiveIntegral

variable {P I : Type*} [MeasurableSpace P]

theorem value_finsetSum {T L S : ℝ} (hT : 0 ≤ T) (hL : 0 ≤ L)
    {flow : ℝ → P → P} (hflow : Measurable (fun z : ℝ × P => flow z.1 z.2))
    (s : Finset I) (f₀ : I → P → ℝ) (g : I → Domain P → ℝ)
    (hgm : ∀ i ∈ s, Measurable (g i)) (hg : ∀ i ∈ s, ∀ z, |g i z| ≤ S)
    (z : Domain P) :
    ∑ i ∈ s, value T L flow (f₀ i) (g i) z =
      value T L flow (fun p => ∑ i ∈ s, f₀ i p) (fun q => ∑ i ∈ s, g i q) z := by
  unfold value
  rw [Finset.sum_add_distrib, Finset.mul_sum]
  congr 1
  rw [← intervalIntegral.integral_finsetSum
    (fun i hi => damped_integrable hT hL hflow (hgm i hi) (hg i hi) z)]
  apply intervalIntegral.integral_congr
  intro r _
  exact (Finset.mul_sum s _ _).symm

end BoltzmannNonuniqueness.PositiveIntegral

end

end

section

/-! # Countable positive sums in the characteristic equation -/

noncomputable section

open MeasureTheory Set Filter
open scoped Topology

namespace BoltzmannNonuniqueness.PositiveIntegral

variable {P I : Type*} [MeasurableSpace P] [Countable I]

theorem hasSum_value {T L S : ℝ} (hT : 0 ≤ T) (hL : 0 ≤ L)
    {flow : ℝ → P → P} (hflow : Measurable (fun z : ℝ × P => flow z.1 z.2))
    (f₀ : I → P → ℝ) (hf₀ : ∀ p, Summable (fun i => f₀ i p))
    (g : I → Domain P → ℝ) (hgm : ∀ i, Measurable (g i))
    (hg : ∀ i z, 0 ≤ g i z ∧ g i z ≤ S)
    (hgs : ∀ z, Summable (fun i => g i z)) (hgb : ∀ z, (∑' i, g i z) ≤ S)
    (z : Domain P) : HasSum (fun i => value T L flow (f₀ i) (g i) z)
      (value T L flow (fun p => ∑' i, f₀ i p) (fun q => ∑' i, g i q) z) := by
  have hsm : Measurable (fun q => ∑' i, g i q) := Measurable.tsum hgm
  have hsa (q) : |∑' i, g i q| ≤ S := by
    rw [abs_of_nonneg (tsum_nonneg (fun i => (hg i q).1))]
    exact hgb q
  have hgi (i) := damped_integrable hT hL hflow (hgm i)
    (fun q => by rw [abs_of_nonneg (hg i q).1]; exact (hg i q).2) z
  have hi := intervalIntegral.hasSum_integral_of_dominated_convergence
    (a := 0) (b := time T z.1) (μ := volume)
    (F := fun i r => Real.exp (-L * (time T z.1 - r)) * g i (r, flow (r - time T z.1) z.2))
    (f := fun r => Real.exp (-L * (time T z.1 - r)) *
      ∑' i, g i (r, flow (r - time T z.1) z.2))
    (fun i r => Real.exp (-L * (time T z.1 - r)) * g i (r, flow (r - time T z.1) z.2))
    (fun i => (hgi i).def'.aestronglyMeasurable)
    (fun i => ae_of_all _ (fun r _ => by
      rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (Real.exp_pos _).le (hg i _).1)]))
    (ae_of_all _ (fun r _ => (hgs _).mul_left _))
    (by
      simpa only [tsum_mul_left] using damped_integrable hT hL hflow hsm hsa z)
    (ae_of_all _ (fun r _ => (hgs _).hasSum.mul_left _))
  exact ((hf₀ _).hasSum.mul_left (Real.exp (-L * time T z.1))).add hi

end BoltzmannNonuniqueness.PositiveIntegral

end

end

end OAI
end

section
-- module Solutions.OAIQ080_BZ.Boltzmann_Collision_GaussianLocalExistence
attribute [-instance] _root_.OAI.BoltzmannNonuniqueness.ChartKernel.offAxis_sFinite _root_.OAI.BoltzmannNonuniqueness.EuclideanFlight.sourcePullback_finite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.characteristicGainKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.hotKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.mixedKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.retainedKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.coldCylinderVolume_finite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.copyColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.mainCoreKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.selectedColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCoreSheet.dilatedColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCoreSheet.kineticColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.PeriodicApproximation.fiberMeasure_finite _root_.OAI.BoltzmannNonuniqueness.PositiveIteration.awayOriginKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.PositiveIteration.nearOriginKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamNormalCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamNormalRetainedKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.dampedCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.densityScaledCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalBeamKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalCollision_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalPhysicalEvent_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalWindowEvent_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.physicalEventMeasure_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.scaledBeamNormalKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.WeakTime.phaseEndpointKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.WeakTime.phaseIncrement_finite _root_.OAI.BoltzmannNonuniqueness.WeakTime.phaseSeed_sFinite _root_.OAI.BoltzmannNonuniqueness.WeakTime.residenceKernel_sFinite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

/-! # Positive local cutoff iteration along the actual free transport -/

noncomputable section

open MeasureTheory Set
open BoltzmannNonuniqueness.JetPrototype

namespace BoltzmannNonuniqueness.GaussianLocal

theorem measurable_state {f : ℝ × JetPrototype.Phase → ℝ} (hf : Measurable f) :
    Measurable (state f) := hf.comp (by fun_prop)

theorem measurable_flight : Measurable (fun z : ℝ × JetPrototype.Phase => JetBarrier.flight z.1 z.2) := by
  unfold JetBarrier.flight VelocityWeight.transverse VelocityWeight.axial
  fun_prop

end BoltzmannNonuniqueness.GaussianLocal

end

end

end OAI
end

section
-- module Solutions.OAIQ080_BZ.Boltzmann_Approximation_PositiveIntegralTime
attribute [-instance] _root_.OAI.BoltzmannNonuniqueness.ChartKernel.offAxis_sFinite _root_.OAI.BoltzmannNonuniqueness.EuclideanFlight.sourcePullback_finite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.characteristicGainKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.hotKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.mixedKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.retainedKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.coldCylinderVolume_finite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.copyColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.mainCoreKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.selectedColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCoreSheet.dilatedColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCoreSheet.kineticColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.PeriodicApproximation.fiberMeasure_finite _root_.OAI.BoltzmannNonuniqueness.PositiveIteration.awayOriginKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.PositiveIteration.nearOriginKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamNormalCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamNormalRetainedKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.dampedCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.densityScaledCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalBeamKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalCollision_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalPhysicalEvent_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalWindowEvent_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.physicalEventMeasure_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.scaledBeamNormalKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.WeakTime.phaseEndpointKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.WeakTime.phaseIncrement_finite _root_.OAI.BoltzmannNonuniqueness.WeakTime.phaseSeed_sFinite _root_.OAI.BoltzmannNonuniqueness.WeakTime.residenceKernel_sFinite
attribute [-simp] _root_.OAI.BoltzmannNonuniqueness.EuclideanFlight.phaseEquiv_snd _root_.OAI.BoltzmannNonuniqueness.timeTranslation_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

/-! # Restarting the mild equation at an intermediate time -/

noncomputable section

open MeasureTheory Set

namespace BoltzmannNonuniqueness.PositiveIntegral

theorem restart {T L S s t : ℝ} (hT : 0 ≤ T) (hL : 0 ≤ L)
    (hs : 0 ≤ s) (hst : s ≤ t) (ht : t ≤ T)
    (f₀ : JetPrototype.Phase → ℝ) {g : ℝ × JetPrototype.Phase → ℝ}
    (hgm : Measurable g) (hg : ∀ z, |g z| ≤ S) (p : JetPrototype.Phase) :
    value T L JetBarrier.flight f₀ g (t,p) =
      Real.exp (-L*(t-s)) * value T L JetBarrier.flight f₀ g (s,JetBarrier.flight (s-t) p) +
      ∫ r in s..t, Real.exp (-L*(t-r))*g (r,JetBarrier.flight (r-t) p) := by
  have ht0 : 0 ≤ t := hs.trans hst
  have hti : time T t = t := GaussianLocal.time_eq ⟨ht0,ht⟩
  have hsi : time T s = s := GaussianLocal.time_eq ⟨hs,hst.trans ht⟩
  let a (r : ℝ) := Real.exp (-L*(t-r))*g (r,JetBarrier.flight (r-t) p)
  have hi : IntervalIntegrable a volume 0 t := by
    have h := damped_integrable hT hL GaussianLocal.measurable_flight hgm hg (t,p)
    simpa only [hti] using h
  have his : IntervalIntegrable a volume 0 s := by
    apply hi.mono_set
    rw [uIcc_of_le hs,uIcc_of_le ht0]
    exact Icc_subset_Icc le_rfl hst
  have hist : IntervalIntegrable a volume s t := by
    apply hi.mono_set
    rw [uIcc_of_le hst,uIcc_of_le ht0]
    exact Icc_subset_Icc hs le_rfl
  have hinit : Real.exp (-L*(t-s))*value T L JetBarrier.flight f₀ g (s,JetBarrier.flight (s-t) p) =
      Real.exp (-L*t)*f₀ (JetBarrier.flight (-t) p) + ∫ r in 0..s,a r := by
    unfold value
    rw [hsi,mul_add,← intervalIntegral.integral_const_mul]
    congr 1
    · rw [JetFreeTransport.flight_add]
      have he : -s+(s-t) = -t := by ring
      rw [he,← mul_assoc,← Real.exp_add]
      congr 2
      ring
    · apply intervalIntegral.integral_congr
      intro r _
      dsimp only [a]
      rw [JetFreeTransport.flight_add]
      have he : r-s+(s-t) = r-t := by ring
      rw [he,← mul_assoc,← Real.exp_add]
      congr 2
      ring
  rw [hinit]
  change value T L JetBarrier.flight f₀ g (t,p) = _ + ∫ r in s..t,a r
  unfold value
  rw [hti,← intervalIntegral.integral_add_adjacent_intervals his hist]
  ring

end BoltzmannNonuniqueness.PositiveIntegral

end

end

section

/-! # Time regularity along the free paths without continuity of translations -/

noncomputable section

open MeasureTheory Set

namespace BoltzmannNonuniqueness.PositiveIntegral

theorem along_time_bound {T L S R s t : ℝ} (hT : 0 ≤ T) (hL : 0 ≤ L)
    (_hS : 0 ≤ S) (_hR : 0 ≤ R) (hs : 0 ≤ s) (hst : s ≤ t) (ht : t ≤ T)
    {f₀ : JetPrototype.Phase → ℝ} {g f : ℝ × JetPrototype.Phase → ℝ}
    (hgm : Measurable g) (hg : ∀ z, |g z| ≤ S) (hfB : ∀ z, |f z| ≤ R)
    (hf : ∀ z, f z = value T L JetBarrier.flight f₀ g z) (p : JetPrototype.Phase) :
    |f (t,p)-f (s,JetBarrier.flight (s-t) p)| ≤ (L*R+S)*(t-s) := by
  have hr := restart hT hL hs hst ht f₀ hgm hg p
  rw [← hf (t,p),← hf (s,JetBarrier.flight (s-t) p)] at hr
  have he : Real.exp (-L*(t-s)) ≤ 1 := Real.exp_le_one_iff.mpr
    (mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hL) (sub_nonneg.mpr hst))
  have hediff : |Real.exp (-L*(t-s))-1| ≤ L*(t-s) := by
    rw [abs_of_nonpos (sub_nonpos.mpr he)]
    have ha := Real.add_one_le_exp (-L*(t-s))
    linarith
  have hi : |∫ r in s..t, Real.exp (-L*(t-r))*g (r,JetBarrier.flight (r-t) p)| ≤ S*(t-s) := by
    have hh := intervalIntegral.norm_integral_le_of_norm_le_const
      (a := s) (b := t) (C := S)
      (f := fun r => Real.exp (-L*(t-r))*g (r,JetBarrier.flight (r-t) p)) (by
        intro r hrt
        rw [uIoc_of_le hst] at hrt
        rw [Real.norm_eq_abs,abs_mul,abs_of_pos (Real.exp_pos _)]
        have hx : Real.exp (-L*(t-r)) ≤ 1 := Real.exp_le_one_iff.mpr
          (mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hL) (sub_nonneg.mpr hrt.2))
        exact (mul_le_mul hx (hg _) (abs_nonneg _) (by norm_num)).trans_eq (one_mul S))
    simpa only [Real.norm_eq_abs,abs_of_nonneg (sub_nonneg.mpr hst)] using hh
  have hsB := hfB (s,JetBarrier.flight (s-t) p)
  have hiB : |(Real.exp (-L*(t-s))-1)*f (s,JetBarrier.flight (s-t) p)| ≤ L*(t-s)*R := by
    rw [abs_mul]
    exact mul_le_mul hediff hsB (abs_nonneg _) (mul_nonneg hL (sub_nonneg.mpr hst))
  calc
    _ = |(Real.exp (-L*(t-s))-1)*f (s,JetBarrier.flight (s-t) p) +
        ∫ r in s..t, Real.exp (-L*(t-r))*g (r,JetBarrier.flight (r-t) p)| := by
      rw [hr]
      congr 1
      ring
    _ ≤ L*(t-s)*R+S*(t-s) := (abs_add_le _ _).trans (add_le_add hiB hi)
    _ = _ := by ring

end BoltzmannNonuniqueness.PositiveIntegral

end

end

end OAI
end

section
-- module Solutions.OAIQ080_BZ.Boltzmann_Branching_FlightMeasure
attribute [-instance] _root_.OAI.BoltzmannNonuniqueness.ChartKernel.offAxis_sFinite _root_.OAI.BoltzmannNonuniqueness.EuclideanFlight.sourcePullback_finite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.characteristicGainKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.hotKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.mixedKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.retainedKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.coldCylinderVolume_finite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.copyColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.mainCoreKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.selectedColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCoreSheet.dilatedColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCoreSheet.kineticColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.PeriodicApproximation.fiberMeasure_finite _root_.OAI.BoltzmannNonuniqueness.PositiveIteration.awayOriginKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.PositiveIteration.nearOriginKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamNormalCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamNormalRetainedKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.dampedCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.densityScaledCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalBeamKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalCollision_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalPhysicalEvent_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalWindowEvent_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.physicalEventMeasure_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.scaledBeamNormalKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.WeakTime.phaseEndpointKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.WeakTime.phaseIncrement_finite _root_.OAI.BoltzmannNonuniqueness.WeakTime.phaseSeed_sFinite _root_.OAI.BoltzmannNonuniqueness.WeakTime.residenceKernel_sFinite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Free-flight measure preservation and representative invariance -/

noncomputable section

open MeasureTheory MeasureTheory.Measure

namespace BoltzmannNonuniqueness.FlightMeasure

theorem spacetime_measurePreserving (s : ℝ) :
    MeasurePreserving (fun z : ℝ × JetPrototype.Phase => (z.1,JetBarrier.flight (z.1-s) z.2))
      ((volume : Measure ℝ).prod phaseVolume) ((volume : Measure ℝ).prod phaseVolume) := by
  exact (MeasurePreserving.id (volume : Measure ℝ)).skew_product
    (μc := phaseVolume) (μd := phaseVolume)
    (g := fun r p => JetBarrier.flight (r-s) p)
    (GaussianLocal.measurable_flight.comp
      ((measurable_fst.sub measurable_const).prodMk measurable_snd))
    (ae_of_all _ (fun r => (flight_measurePreserving (r-s)).map_eq))

theorem value_congr_at_time {f₀ k₀ : JetPrototype.Phase → ℝ}
    {g h : ℝ × JetPrototype.Phase → ℝ}
    (hinit : f₀ =ᵐ[phaseVolume] k₀) (hsource : g =ᵐ[(volume : Measure ℝ).prod phaseVolume] h)
    (T L t : ℝ) :
    (fun p => PositiveIntegral.value T L JetBarrier.flight f₀ g (t,p)) =ᵐ[phaseVolume]
      (fun p => PositiveIntegral.value T L JetBarrier.flight k₀ h (t,p)) := by
  let τ := PositiveIntegral.time T t
  have hi := (flight_measurePreserving (-τ)).quasiMeasurePreserving.ae hinit
  have hs := (spacetime_measurePreserving τ).quasiMeasurePreserving.ae hsource
  have hsp := (Measure.measurePreserving_swap (μ := phaseVolume) (ν := volume)).quasiMeasurePreserving.ae hs
  have hr := ae_ae_of_ae_prod hsp
  filter_upwards [hi,hr] with p hip hrp
  unfold PositiveIntegral.value
  change Real.exp (-L*τ)*f₀ (JetBarrier.flight (-τ) p) + _ =
    Real.exp (-L*τ)*k₀ (JetBarrier.flight (-τ) p) + _
  rw [hip]
  congr 1
  apply intervalIntegral.integral_congr_ae
  filter_upwards [hrp] with r hr _
  change g (r,JetBarrier.flight (r-PositiveIntegral.time T t) p) =
    h (r,JetBarrier.flight (r-PositiveIntegral.time T t) p) at hr
  rw [hr]

end BoltzmannNonuniqueness.FlightMeasure

end

end OAI
end

section
-- module Solutions.OAIQ080_BZ.Boltzmann_Branching_PhaseDecompositionNorm
attribute [-instance] _root_.OAI.BoltzmannNonuniqueness.ChartKernel.offAxis_sFinite _root_.OAI.BoltzmannNonuniqueness.EuclideanFlight.sourcePullback_finite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.characteristicGainKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.hotKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.mixedKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.retainedKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.coldCylinderVolume_finite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.copyColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.mainCoreKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.selectedColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCoreSheet.dilatedColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCoreSheet.kineticColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.PeriodicApproximation.fiberMeasure_finite _root_.OAI.BoltzmannNonuniqueness.PositiveIteration.awayOriginKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.PositiveIteration.nearOriginKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamNormalCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamNormalRetainedKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.dampedCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.densityScaledCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalBeamKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalCollision_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalPhysicalEvent_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalWindowEvent_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.physicalEventMeasure_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.scaledBeamNormalKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.WeakTime.phaseEndpointKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.WeakTime.phaseIncrement_finite _root_.OAI.BoltzmannNonuniqueness.WeakTime.phaseSeed_sFinite _root_.OAI.BoltzmannNonuniqueness.WeakTime.residenceKernel_sFinite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

/-! # The essential supremum norm along free transport -/

noncomputable section

open MeasureTheory
open scoped ENNReal

namespace BoltzmannNonuniqueness.PhaseEssSup

open FlightMeasure

theorem size_le {f : JetPrototype.Phase → ℝ} {R : ℝ} (hR : 0 ≤ R)
    (hfm : Measurable f) (hf : ∀ p, |f p| ≤ R) : size f ≤ R := by
  have he : eLpNorm f ∞ phaseVolume ≤ ENNReal.ofReal R := by
    rw [eLpNorm_exponent_top]
    exact eLpNormEssSup_le_of_ae_bound (ae_of_all _ (fun p => by simpa only [Real.norm_eq_abs] using hf p))
  simpa only [size,ENNReal.toReal_ofReal hR] using ENNReal.toReal_mono ENNReal.ofReal_ne_top he

theorem size_difference {f g : JetPrototype.Phase → ℝ} {A B D : ℝ}
    (hD : 0 ≤ D) (hfm : Measurable f) (hgm : Measurable g)
    (hf : ∀ p, |f p| ≤ A) (hg : ∀ p, |g p| ≤ B) (hfg : ∀ p, |f p-g p| ≤ D) :
    |size f-size g| ≤ D := by
  have hfp : MemLp f ∞ phaseVolume := memLp_top_of_bound hfm.aestronglyMeasurable A
    (ae_of_all _ (fun p => by simpa only [Real.norm_eq_abs] using hf p))
  have hgp : MemLp g ∞ phaseVolume := memLp_top_of_bound hgm.aestronglyMeasurable B
    (ae_of_all _ (fun p => by simpa only [Real.norm_eq_abs] using hg p))
  calc
    _ = |‖hfp.toLp f‖-‖hgp.toLp g‖| := by rw [Lp.norm_toLp,Lp.norm_toLp]; rfl
    _ ≤ ‖hfp.toLp f-hgp.toLp g‖ := abs_norm_sub_norm_le _ _
    _ = size (fun p => f p-g p) := by rw [← MemLp.toLp_sub,Lp.norm_toLp]; rfl
    _ ≤ D := size_le hD (hfm.sub hgm) hfg

theorem size_flight {f : JetPrototype.Phase → ℝ} (hfm : Measurable f) (t : ℝ) :
    size (fun p => f (JetBarrier.flight t p)) = size f := by
  unfold size
  exact congrArg ENNReal.toReal
    (eLpNorm_comp_measurePreserving hfm.aestronglyMeasurable (flight_measurePreserving t))

theorem time_difference {T L S R s t : ℝ} (hT : 0 ≤ T) (hL : 0 ≤ L)
    (hS : 0 ≤ S) (hR : 0 ≤ R) (hs : 0 ≤ s) (hst : s ≤ t) (ht : t ≤ T)
    {f₀ : JetPrototype.Phase → ℝ} {g f : ℝ × JetPrototype.Phase → ℝ}
    (hgm : Measurable g) (hfm : Measurable f) (hg : ∀ z, |g z| ≤ S) (hfB : ∀ z, |f z| ≤ R)
    (hf : ∀ z, f z = PositiveIntegral.value T L JetBarrier.flight f₀ g z) :
    |size (fun p => f (t,p))-size (fun p => f (s,p))| ≤ (L*R+S)*(t-s) := by
  have hfs : Measurable (fun p => f (s,p)) := hfm.comp (measurable_const.prodMk measurable_id)
  have hh := size_difference (mul_nonneg (add_nonneg (mul_nonneg hL hR) hS) (sub_nonneg.mpr hst))
    (hfm.comp (measurable_const.prodMk measurable_id))
    (hfs.comp (flight_measurePreserving (s-t)).measurable)
    (fun p => hfB (t,p)) (fun p => hfB (s,JetBarrier.flight (s-t) p))
    (PositiveIntegral.along_time_bound hT hL hS hR hs hst ht hgm hg hfB hf)
  change |size (fun p => f (t,p))-size (fun p => f (s,JetBarrier.flight (s-t) p))| ≤ _ at hh
  rw [size_flight hfs] at hh
  exact hh

end BoltzmannNonuniqueness.PhaseEssSup

end

end

section

/-! # Continuity of the cap ratio in the essential weighted norm -/

noncomputable section

open MeasureTheory Set

namespace BoltzmannNonuniqueness.PhaseEssSup

theorem continuousOn_size {T L S R : ℝ} (hT : 0 ≤ T) (hL : 0 ≤ L)
    (hS : 0 ≤ S) (hR : 0 ≤ R)
    {f₀ : JetPrototype.Phase → ℝ} {g f : ℝ × JetPrototype.Phase → ℝ}
    (hgm : Measurable g) (hfm : Measurable f) (hg : ∀ z, |g z| ≤ S) (hfB : ∀ z, |f z| ≤ R)
    (hf : ∀ z, f z = PositiveIntegral.value T L JetBarrier.flight f₀ g z) :
    ContinuousOn (fun t => size (fun p => f (t,p))) (Icc 0 T) := by
  let C : NNReal := ⟨L*R+S,add_nonneg (mul_nonneg hL hR) hS⟩
  have hLip : LipschitzOnWith C (fun t => size (fun p => f (t,p))) (Icc 0 T) := by
    apply lipschitzOnWith_iff_dist_le_mul.mpr
    intro s hs t ht
    simp only [Real.dist_eq]
    change |size (fun p => f (s,p))-size (fun p => f (t,p))| ≤ (L*R+S)*|s-t|
    rcases le_total s t with hst | hts
    · rw [abs_sub_comm (size _),abs_sub_comm s t,abs_of_nonneg (sub_nonneg.mpr hst)]
      exact time_difference hT hL hS hR hs.1 hst ht.2 hgm hfm hg hfB hf
    · rw [abs_of_nonneg (sub_nonneg.mpr hts)]
      exact time_difference hT hL hS hR ht.1 hts hs.2 hgm hfm hg hfB hf
  exact hLip.continuousOn

end BoltzmannNonuniqueness.PhaseEssSup

end

end

section

/-! # Bounded representatives that realize the essential upper bound -/

noncomputable section

open MeasureTheory
open scoped ENNReal

namespace BoltzmannNonuniqueness.PhaseEssSup

theorem ae_abs_le_size {f : JetPrototype.Phase → ℝ} (hfm : Measurable f)
    {R : ℝ} (hf : ∀ p, |f p| ≤ R) : ∀ᵐ p ∂FlightMeasure.phaseVolume, |f p| ≤ size f := by
  have hm : MemLp f ∞ FlightMeasure.phaseVolume :=
    memLp_top_of_bound hfm.aestronglyMeasurable R (ae_of_all _ (fun p => by
      simpa only [Real.norm_eq_abs] using hf p))
  simpa only [Real.norm_eq_abs,← toReal_eLpNorm hm.1,size] using ae_le_lpNorm_exponent_top hm

theorem size_le_ae {f : JetPrototype.Phase → ℝ} (hfm : Measurable f)
    {R : ℝ} (hR : 0 ≤ R) (hf : ∀ᵐ p ∂FlightMeasure.phaseVolume, |f p| ≤ R) : size f ≤ R := by
  have h : eLpNorm f ∞ FlightMeasure.phaseVolume ≤ ENNReal.ofReal R := by
    rw [eLpNorm_exponent_top]
    exact eLpNormEssSup_le_of_ae_bound (hf.mono (fun p hp => by
      simpa only [Real.norm_eq_abs] using hp))
  simpa only [size,ENNReal.toReal_ofReal hR] using ENNReal.toReal_mono ENNReal.ofReal_ne_top h

end BoltzmannNonuniqueness.PhaseEssSup

end

end

section

/-! # Stability of the essential norm under a.e. bounded differences -/

noncomputable section

open MeasureTheory
open scoped ENNReal

namespace BoltzmannNonuniqueness.PhaseEssSup

theorem size_difference_ae {f g : JetPrototype.Phase → ℝ} {A B D : ℝ}
    (hD : 0 ≤ D) (hfm : Measurable f) (hgm : Measurable g)
    (hf : ∀ p, |f p| ≤ A) (hg : ∀ p, |g p| ≤ B)
    (hfg : ∀ᵐ p ∂FlightMeasure.phaseVolume, |f p-g p| ≤ D) :
    |size f-size g| ≤ D := by
  have hfp : MemLp f ∞ FlightMeasure.phaseVolume := memLp_top_of_bound
    hfm.aestronglyMeasurable A (ae_of_all _ (fun p => by simpa only [Real.norm_eq_abs] using hf p))
  have hgp : MemLp g ∞ FlightMeasure.phaseVolume := memLp_top_of_bound
    hgm.aestronglyMeasurable B (ae_of_all _ (fun p => by simpa only [Real.norm_eq_abs] using hg p))
  calc
    _ = |‖hfp.toLp f‖-‖hgp.toLp g‖| := by rw [Lp.norm_toLp,Lp.norm_toLp]; rfl
    _ ≤ ‖hfp.toLp f-hgp.toLp g‖ := abs_norm_sub_norm_le _ _
    _ = size (fun p => f p-g p) := by rw [← MemLp.toLp_sub,Lp.norm_toLp]; rfl
    _ ≤ D := size_le_ae (hfm.sub hgm) hD hfg

theorem hot_difference_ae {I : Type*} [Countable I]
    {F G : JetPrototype.Phase → ℝ} {c d : I → JetPrototype.Phase → ℝ}
    {R D E : ℝ} (hD : 0 ≤ D) (hE : 0 ≤ E)
    (hFm : Measurable F) (hGm : Measurable G)
    (hcm : ∀ i, Measurable (c i)) (hdm : ∀ i, Measurable (d i))
    (hF : ∀ p, 0 ≤ F p ∧ F p ≤ R) (hG : ∀ p, 0 ≤ G p ∧ G p ≤ R)
    (hcn : ∀ i p, 0 ≤ c i p) (hdn : ∀ i p, 0 ≤ d i p)
    (hcSum : ∀ s : Finset I, ∀ p, ∑ i ∈ s, c i p ≤ F p)
    (hdSum : ∀ s : Finset I, ∀ p, ∑ i ∈ s, d i p ≤ G p)
    (hFG : ∀ᵐ p ∂FlightMeasure.phaseVolume, |F p-G p| ≤ D)
    (hcd : ∀ᵐ p ∂FlightMeasure.phaseVolume, (∑' i, |c i p-d i p|) ≤ E) :
    |size (fun p => F p-∑' i, c i p)-size (fun p => G p-∑' i, d i p)| ≤ D+E := by
  have hcs (p) : Summable (fun i => c i p) := summable_of_sum_le
    (fun i => hcn i p) (fun s => hcSum s p)
  have hds (p) : Summable (fun i => d i p) := summable_of_sum_le
    (fun i => hdn i p) (fun s => hdSum s p)
  have hcb (p) : |F p-∑' i, c i p| ≤ R := by
    have hn : 0 ≤ ∑' i, c i p := tsum_nonneg (fun i => hcn i p)
    have hs := Real.tsum_le_of_sum_le (fun i => hcn i p) (fun s => hcSum s p)
    rw [abs_of_nonneg (sub_nonneg.mpr hs)]
    linarith [(hF p).2]
  have hdb (p) : |G p-∑' i, d i p| ≤ R := by
    have hn : 0 ≤ ∑' i, d i p := tsum_nonneg (fun i => hdn i p)
    have hs := Real.tsum_le_of_sum_le (fun i => hdn i p) (fun s => hdSum s p)
    rw [abs_of_nonneg (sub_nonneg.mpr hs)]
    linarith [(hG p).2]
  apply size_difference_ae (add_nonneg hD hE)
    (hFm.sub (Measurable.tsum hcm)) (hGm.sub (Measurable.tsum hdm)) hcb hdb
  filter_upwards [hFG,hcd] with p hp hcp
  have ht : |(∑' i, c i p)-(∑' i, d i p)| ≤ E := by
    rw [← (hcs p).tsum_sub (hds p)]
    have hn : Summable (fun i : I => ‖c i p - d i p‖) := by
      simpa only [Real.norm_eq_abs] using ((hcs p).sub (hds p)).abs
    have ha : |tsum (fun i : I => c i p - d i p)| ≤ tsum (fun i : I => |c i p - d i p|) := by
      simpa only [Real.norm_eq_abs] using norm_tsum_le_tsum_norm hn
    exact ha.trans hcp
  have he : (F p-∑' i, c i p)-(G p-∑' i, d i p) =
      (F p-G p)-((∑' i, c i p)-(∑' i, d i p)) := by ring
  change |(F p-∑' i, c i p)-(G p-∑' i, d i p)| ≤ D+E
  rw [he]
  exact (abs_sub _ _).trans (add_le_add hp ht)

end BoltzmannNonuniqueness.PhaseEssSup

end

end

section

/-! # Scalar upper integral bounds for the essential norm of a mild solution -/

noncomputable section

open MeasureTheory MeasureTheory.Measure Set

namespace BoltzmannNonuniqueness.PhaseEssSup

theorem value_le_ae {T L S a t : ℝ} (hT : 0 ≤ T) (hL : 0 ≤ L) (ht : t ∈ Icc 0 T)
    {f₀ : JetPrototype.Phase → ℝ} {g : ℝ × JetPrototype.Phase → ℝ} {w : ℝ → ℝ}
    (hgm : Measurable g) (hg : ∀ u, |g u| ≤ S) (hw : IntervalIntegrable w volume 0 T)
    (hinit : ∀ᵐ p ∂FlightMeasure.phaseVolume, f₀ p ≤ a)
    (hsource : ∀ᵐ u ∂(volume : Measure ℝ).prod FlightMeasure.phaseVolume,
      u.1 ∈ Ioc 0 T → g u ≤ w u.1) :
    ∀ᵐ p ∂FlightMeasure.phaseVolume,
      PositiveIntegral.value T L JetBarrier.flight f₀ g (t,p) ≤
        Real.exp (-L*t)*a+∫ r in 0..t, Real.exp (-L*(t-r))*w r := by
  have hi := (FlightMeasure.flight_measurePreserving (-t)).quasiMeasurePreserving.ae hinit
  have hs := (FlightMeasure.spacetime_measurePreserving t).quasiMeasurePreserving.ae hsource
  have hsp := (Measure.measurePreserving_swap (μ := FlightMeasure.phaseVolume) (ν := volume)).quasiMeasurePreserving.ae hs
  have hr := ae_ae_of_ae_prod hsp
  have hwt : IntervalIntegrable w volume 0 t := hw.mono_set (by
    rw [uIcc_of_le ht.1,uIcc_of_le hT]
    exact Icc_subset_Icc le_rfl ht.2)
  have hwi : IntervalIntegrable (fun r => Real.exp (-L*(t-r))*w r) volume 0 t :=
    hwt.continuousOn_mul (by fun_prop)
  filter_upwards [hi,hr] with p hip hrp
  unfold PositiveIntegral.value
  rw [GaussianLocal.time_eq ht]
  apply add_le_add (mul_le_mul_of_nonneg_left hip (Real.exp_pos _).le)
  have hgi := PositiveIntegral.damped_integrable hT hL GaussianLocal.measurable_flight hgm hg (t,p)
  rw [GaussianLocal.time_eq ht] at hgi
  apply intervalIntegral.integral_mono_ae_restrict ht.1 hgi hwi
  filter_upwards [ae_restrict_of_ae hrp,ae_restrict_mem measurableSet_Icc,
    ae_restrict_of_ae (Measure.ae_ne (volume : Measure ℝ) 0)] with r hr hrmem hr0
  apply mul_le_mul_of_nonneg_left _ (Real.exp_pos _).le
  exact hr ⟨lt_of_le_of_ne hrmem.1 hr0.symm,hrmem.2.trans ht.2⟩

end BoltzmannNonuniqueness.PhaseEssSup

end

end

section

/-! # Global norm continuity for the clamped local construction -/

noncomputable section

open MeasureTheory MeasureTheory.Measure Set

namespace BoltzmannNonuniqueness.PhaseEssSup

theorem continuous_size {T L S R : ℝ} (hT : 0 ≤ T) (hL : 0 ≤ L)
    (hS : 0 ≤ S) (hR : 0 ≤ R)
    {f₀ : JetPrototype.Phase → ℝ} {g f : ℝ × JetPrototype.Phase → ℝ}
    (hgm : Measurable g) (hfm : Measurable f) (hg : ∀ u, |g u| ≤ S) (hfB : ∀ u, |f u| ≤ R)
    (hf : ∀ u, f u = PositiveIntegral.value T L JetBarrier.flight f₀ g u) :
    Continuous (fun t => size (fun p => f (t,p))) := by
  have he (t : ℝ) (p : JetPrototype.Phase) :
      f (t,p) = f (PositiveIntegral.time T t,p) := by
    rw [hf (t,p),hf (PositiveIntegral.time T t,p)]
    simp only [PositiveIntegral.value,time_idempotent hT]
  have hn : (fun t => size (fun p => f (t,p))) =
      (fun t => size (fun p => f (PositiveIntegral.time T t,p))) := by
    funext t
    exact congrArg size (funext (he t))
  rw [hn]
  exact (continuousOn_size hT hL hS hR hgm hfm hg hfB hf).comp_continuous
    (by unfold PositiveIntegral.time; fun_prop) (PositiveIntegral.time_bounds hT)

end BoltzmannNonuniqueness.PhaseEssSup

end

end

section

/-! # Essential-norm estimates for mild equations holding almost everywhere -/

noncomputable section

open MeasureTheory Set

namespace BoltzmannNonuniqueness.PhaseEssSup

theorem size_congr_ae {f g : JetPrototype.Phase → ℝ}
    (hfg : f =ᵐ[FlightMeasure.phaseVolume] g) : size f = size g :=
  congrArg ENNReal.toReal (eLpNorm_congr_ae hfg)

theorem continuous_size_of_mildAE {T L A S : ℝ} (hT : 0 ≤ T) (hL : 0 ≤ L)
    (hA : 0 ≤ A) (hS : 0 ≤ S) {f₀ : JetPrototype.Phase → ℝ}
    {f g : ℝ × JetPrototype.Phase → ℝ}
    (hf₀m : Measurable f₀) (hgm : Measurable g)
    (hf₀ : ∀ p, 0 ≤ f₀ p ∧ f₀ p ≤ A) (hg : ∀ u, 0 ≤ g u ∧ g u ≤ S)
    (hfix : ∀ t, (fun p => f (t,p)) =ᵐ[FlightMeasure.phaseVolume]
      (fun p => PositiveIntegral.value T L JetBarrier.flight f₀ g (t,p))) :
    Continuous (fun t => size (fun p => f (t,p))) := by
  let v := PositiveIntegral.value T L JetBarrier.flight f₀ g
  have hvm : Measurable v := PositiveIntegral.measurable_value hT GaussianLocal.measurable_flight hf₀m hgm
  have hv (u) := PositiveIntegral.value_bounds hT hL hA hS JetBarrier.flight hf₀ hg u
  have hga (u) : |g u| ≤ S := by rw [abs_of_nonneg (hg u).1]; exact (hg u).2
  have hva (u) : |v u| ≤ A+T*S := by rw [abs_of_nonneg (hv u).1]; exact (hv u).2
  have he : (fun t => size (fun p => f (t,p))) = (fun t => size (fun p => v (t,p))) :=
    funext (fun t => size_congr_ae (hfix t))
  rw [he]
  exact continuous_size hT hL hS (by positivity) hgm hvm hga hva (fun _ => rfl)

end BoltzmannNonuniqueness.PhaseEssSup

end

end

end OAI
end

section
-- module Solutions.OAIQ080_BZ.Boltzmann_Approximation_PositiveIntegralPasting
attribute [-instance] _root_.OAI.BoltzmannNonuniqueness.ChartKernel.offAxis_sFinite _root_.OAI.BoltzmannNonuniqueness.EuclideanFlight.sourcePullback_finite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.characteristicGainKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.hotKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.mixedKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.retainedKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.coldCylinderVolume_finite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.copyColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.mainCoreKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.selectedColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCoreSheet.dilatedColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCoreSheet.kineticColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.PeriodicApproximation.fiberMeasure_finite _root_.OAI.BoltzmannNonuniqueness.PositiveIteration.awayOriginKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.PositiveIteration.nearOriginKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamNormalCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamNormalRetainedKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.dampedCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.densityScaledCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalBeamKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalCollision_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalPhysicalEvent_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalWindowEvent_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.physicalEventMeasure_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.scaledBeamNormalKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.WeakTime.phaseEndpointKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.WeakTime.phaseIncrement_finite _root_.OAI.BoltzmannNonuniqueness.WeakTime.phaseSeed_sFinite _root_.OAI.BoltzmannNonuniqueness.WeakTime.residenceKernel_sFinite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

/-! # Subtracting two bounded characteristic integral equations -/

noncomputable section

open MeasureTheory

namespace BoltzmannNonuniqueness.PositiveIntegral

theorem value_sub {T L S : ℝ} (hT : 0 ≤ T) (hL : 0 ≤ L)
    {g h : ℝ × JetPrototype.Phase → ℝ} (hgm : Measurable g) (hhm : Measurable h)
    (hg : ∀ u, |g u| ≤ S) (hh : ∀ u, |h u| ≤ S)
    (f₀ k₀ : JetPrototype.Phase → ℝ) (u : ℝ × JetPrototype.Phase) :
    value T L JetBarrier.flight f₀ g u-value T L JetBarrier.flight k₀ h u =
      value T L JetBarrier.flight (fun p => f₀ p-k₀ p) (fun z => g z-h z) u := by
  unfold value
  have he (r : ℝ) : Real.exp (-L*(time T u.1-r)) *
      (g (r,JetBarrier.flight (r-time T u.1) u.2)-h (r,JetBarrier.flight (r-time T u.1) u.2)) =
      Real.exp (-L*(time T u.1-r))*g (r,JetBarrier.flight (r-time T u.1) u.2)-
        Real.exp (-L*(time T u.1-r))*h (r,JetBarrier.flight (r-time T u.1) u.2) := mul_sub _ _ _
  simp_rw [he]
  rw [intervalIntegral.integral_sub
    (damped_integrable hT hL GaussianLocal.measurable_flight hgm hg u)
    (damped_integrable hT hL GaussianLocal.measurable_flight hhm hh u)]
  ring

end BoltzmannNonuniqueness.PositiveIntegral

end

end

section

/-! # The positive integral only uses source values on its time interval -/

noncomputable section

open Set

namespace BoltzmannNonuniqueness.PositiveIntegral

theorem value_eq_of_time_eq {T : ℝ} (hT : 0 ≤ T) (L : ℝ)
    (f₀ : JetPrototype.Phase → ℝ) {g h : ℝ × JetPrototype.Phase → ℝ}
    (hgh : ∀ r ∈ Icc 0 T, ∀ p, g (r,p) = h (r,p)) (u : ℝ × JetPrototype.Phase) :
    value T L JetBarrier.flight f₀ g u = value T L JetBarrier.flight f₀ h u := by
  unfold value
  congr 1
  apply intervalIntegral.integral_congr
  intro r hr
  rw [uIcc_of_le (time_bounds hT u.1).1] at hr
  dsimp only
  rw [hgh r ⟨hr.1,hr.2.trans (time_bounds hT u.1).2⟩]

theorem value_time_clamp {T : ℝ} (hT : 0 ≤ T) (L : ℝ)
    (f₀ : JetPrototype.Phase → ℝ) (g : ℝ × JetPrototype.Phase → ℝ) (u : ℝ × JetPrototype.Phase) :
    value T L JetBarrier.flight f₀ g (time T u.1,u.2) = value T L JetBarrier.flight f₀ g u := by
  simp only [value,PhaseEssSup.time_idempotent hT]

end BoltzmannNonuniqueness.PositiveIntegral

end

end

section

/-! # Almost-everywhere difference bounds for the damped characteristic integral -/

noncomputable section

open MeasureTheory Set

namespace BoltzmannNonuniqueness.PositiveIntegral

theorem value_difference_initial_ae {T L S D I t : ℝ}
    (hT : 0 ≤ T) (hL : 0 ≤ L) (hD : 0 ≤ D) (hI : 0 ≤ I) (ht : t ∈ Icc 0 T)
    {f₀ k₀ : JetPrototype.Phase → ℝ} {g h : ℝ × JetPrototype.Phase → ℝ}
    (hinit : ∀ᵐ p ∂FlightMeasure.phaseVolume, |f₀ p-k₀ p| ≤ I)
    (hgm : Measurable g) (hhm : Measurable h)
    (hg : ∀ u, |g u| ≤ S) (hh : ∀ u, |h u| ≤ S)
    (hsource : ∀ᵐ u ∂(volume : Measure ℝ).prod FlightMeasure.phaseVolume, |g u-h u| ≤ D) :
    ∀ᵐ p ∂FlightMeasure.phaseVolume,
      |value T L JetBarrier.flight f₀ g (t,p)-value T L JetBarrier.flight k₀ h (t,p)| ≤ I+T*D := by
  have hdiff (u) : |g u-h u| ≤ 2*S := (abs_sub _ _).trans (by linarith [hg u,hh u])
  have hrev (u) : |h u-g u| ≤ 2*S := by rw [abs_sub_comm]; exact hdiff u
  have hup := PhaseEssSup.value_le_ae (f₀ := fun p => f₀ p-k₀ p) (a := I) hT hL ht (hgm.sub hhm) hdiff
    (intervalIntegrable_const : IntervalIntegrable (fun _ : ℝ => D) volume 0 T)
    (hinit.mono (fun p hp => (le_abs_self _).trans hp))
    (hsource.mono (fun u hu _ => (le_abs_self _).trans hu))
  have hlo := PhaseEssSup.value_le_ae (f₀ := fun p => k₀ p-f₀ p) (a := I) hT hL ht (hhm.sub hgm) hrev
    (intervalIntegrable_const : IntervalIntegrable (fun _ : ℝ => D) volume 0 T)
    (hinit.mono (fun p hp => (abs_sub_le_iff.mp hp).2))
    (hsource.mono (fun u hu _ => (abs_sub_le_iff.mp hu).2))
  have hb : Real.exp (-L*t)*I+(∫ r in 0..t, Real.exp (-L*(t-r))*D) ≤ I+T*D := by
    have h := value_bounds hT hL hI hD JetBarrier.flight
      (fun _ => ⟨hI,le_rfl⟩) (fun _ => ⟨hD,le_rfl⟩) (t,(0 : JetPrototype.Phase))
    simpa only [value,GaussianLocal.time_eq ht] using h.2
  filter_upwards [hup,hlo] with p hp hq
  change value T L JetBarrier.flight (fun p => f₀ p-k₀ p) (fun u => g u-h u) (t,p) ≤ _ at hp
  change value T L JetBarrier.flight (fun p => k₀ p-f₀ p) (fun u => h u-g u) (t,p) ≤ _ at hq
  rw [← value_sub hT hL hgm hhm hg hh f₀ k₀ (t,p)] at hp
  rw [← value_sub hT hL hhm hgm hh hg k₀ f₀ (t,p)] at hq
  exact abs_sub_le_iff.mpr ⟨hp.trans hb,hq.trans hb⟩

theorem value_difference_initial_ae_all {T L S D I : ℝ}
    (hT : 0 ≤ T) (hL : 0 ≤ L) (hD : 0 ≤ D) (hI : 0 ≤ I)
    {f₀ k₀ : JetPrototype.Phase → ℝ} {g h : ℝ × JetPrototype.Phase → ℝ}
    (hinit : ∀ᵐ p ∂FlightMeasure.phaseVolume, |f₀ p-k₀ p| ≤ I)
    (hgm : Measurable g) (hhm : Measurable h)
    (hg : ∀ u, |g u| ≤ S) (hh : ∀ u, |h u| ≤ S)
    (hsource : ∀ᵐ u ∂(volume : Measure ℝ).prod FlightMeasure.phaseVolume, |g u-h u| ≤ D) (t : ℝ) :
    ∀ᵐ p ∂FlightMeasure.phaseVolume,
      |value T L JetBarrier.flight f₀ g (t,p)-value T L JetBarrier.flight k₀ h (t,p)| ≤ I+T*D := by
  filter_upwards [value_difference_initial_ae hT hL hD hI (time_bounds hT t)
    hinit hgm hhm hg hh hsource] with p hp
  rw [value_time_clamp hT L f₀ g (t,p),value_time_clamp hT L k₀ h (t,p)] at hp
  exact hp

end BoltzmannNonuniqueness.PositiveIntegral

end

end

section

/-! # Order of the characteristic integral for almost-everywhere data -/

noncomputable section

open MeasureTheory MeasureTheory.Measure

namespace BoltzmannNonuniqueness.FlightMeasure

theorem value_mono_ae {T L S : ℝ} (hT : 0 ≤ T) (hL : 0 ≤ L)
    {f₀ k₀ : JetPrototype.Phase → ℝ} {g h : ℝ × JetPrototype.Phase → ℝ}
    (hinit : f₀ ≤ᵐ[phaseVolume] k₀) (hsource : g ≤ᵐ[(volume : Measure ℝ).prod phaseVolume] h)
    (hgm : Measurable g) (hhm : Measurable h)
    (hg : ∀ u, |g u| ≤ S) (hh : ∀ u, |h u| ≤ S) (t : ℝ) :
    (fun p => PositiveIntegral.value T L JetBarrier.flight f₀ g (t,p)) ≤ᵐ[phaseVolume]
      (fun p => PositiveIntegral.value T L JetBarrier.flight k₀ h (t,p)) := by
  let τ := PositiveIntegral.time T t
  have hi := (flight_measurePreserving (-τ)).quasiMeasurePreserving.ae hinit
  have hs := (spacetime_measurePreserving τ).quasiMeasurePreserving.ae hsource
  have hr := ae_ae_of_ae_prod
    ((Measure.measurePreserving_swap (μ := phaseVolume) (ν := volume)).quasiMeasurePreserving.ae hs)
  filter_upwards [hi,hr] with p hip hrp
  apply add_le_add (mul_le_mul_of_nonneg_left hip (Real.exp_pos _).le)
  apply intervalIntegral.integral_mono_ae (PositiveIntegral.time_bounds hT t).1
    (PositiveIntegral.damped_integrable hT hL GaussianLocal.measurable_flight hgm hg (t,p))
    (PositiveIntegral.damped_integrable hT hL GaussianLocal.measurable_flight hhm hh (t,p))
  filter_upwards [hrp] with r hrr
  exact mul_le_mul_of_nonneg_left hrr (Real.exp_pos _).le

end BoltzmannNonuniqueness.FlightMeasure

end

end

section

/-! # Absolute values and finite family differences under the positive integral -/

noncomputable section

open MeasureTheory

namespace BoltzmannNonuniqueness.PositiveIntegral

theorem value_abs_le (T L : ℝ) (f₀ : JetPrototype.Phase → ℝ)
    (g : ℝ × JetPrototype.Phase → ℝ) (u : ℝ × JetPrototype.Phase) :
    |value T L JetBarrier.flight f₀ g u| ≤
      value T L JetBarrier.flight (fun p => |f₀ p|) (fun z => |g z|) u := by
  unfold value
  apply (abs_add_le _ _).trans
  apply add_le_add
  · rw [abs_mul,abs_of_pos (Real.exp_pos _)]
  · apply (intervalIntegral.abs_integral_le_integral_abs
      (show 0 ≤ time T u.1 from le_max_left _ _)).trans_eq
    apply intervalIntegral.integral_congr
    intro r _
    dsimp only
    rw [abs_mul,abs_of_pos (Real.exp_pos _)]

theorem finite_difference_le {I : Type*} {T L S : ℝ} (hT : 0 ≤ T) (hL : 0 ≤ L)
    (s : Finset I) (f₀ k₀ : I → JetPrototype.Phase → ℝ)
    (g h : I → ℝ × JetPrototype.Phase → ℝ)
    (hgm : ∀ i ∈ s, Measurable (g i)) (hhm : ∀ i ∈ s, Measurable (h i))
    (hg : ∀ i ∈ s, ∀ u, |g i u| ≤ S) (hh : ∀ i ∈ s, ∀ u, |h i u| ≤ S)
    (u : ℝ × JetPrototype.Phase) :
    (∑ i ∈ s, |value T L JetBarrier.flight (f₀ i) (g i) u-
      value T L JetBarrier.flight (k₀ i) (h i) u|) ≤
      value T L JetBarrier.flight (fun p => ∑ i ∈ s, |f₀ i p-k₀ i p|)
        (fun z => ∑ i ∈ s, |g i z-h i z|) u := by
  calc
    _ ≤ ∑ i ∈ s, value T L JetBarrier.flight
        (fun p => |f₀ i p-k₀ i p|) (fun z => |g i z-h i z|) u := by
      apply Finset.sum_le_sum
      intro i hi
      rw [value_sub hT hL (hgm i hi) (hhm i hi) (hg i hi) (hh i hi)]
      exact value_abs_le T L _ _ u
    _ = _ := value_finsetSum hT hL GaussianLocal.measurable_flight s _ _
      (fun i hi => (hgm i hi |>.sub (hhm i hi)).abs)
      (S := 2*S) (fun i hi z => by
        rw [abs_abs]
        exact (abs_sub _ _).trans (by linarith [hg i hi z,hh i hi z])) u

end BoltzmannNonuniqueness.PositiveIntegral

end

end

section

/-! # A.e. estimates for finite sums of absolute characteristic differences -/

noncomputable section

open MeasureTheory Set

namespace BoltzmannNonuniqueness.PositiveIntegral

theorem value_le_constant_ae {T L S D I t : ℝ}
    (hT : 0 ≤ T) (hL : 0 ≤ L) (hD : 0 ≤ D) (hI : 0 ≤ I) (ht : t ∈ Icc 0 T)
    {f₀ : JetPrototype.Phase → ℝ} {g : ℝ × JetPrototype.Phase → ℝ}
    (hinit : ∀ᵐ p ∂FlightMeasure.phaseVolume, f₀ p ≤ I)
    (hgm : Measurable g) (hg : ∀ u, |g u| ≤ S)
    (hsource : ∀ᵐ u ∂(volume : Measure ℝ).prod FlightMeasure.phaseVolume, g u ≤ D) :
    ∀ᵐ p ∂FlightMeasure.phaseVolume, value T L JetBarrier.flight f₀ g (t,p) ≤ I+T*D := by
  have hp := PhaseEssSup.value_le_ae hT hL ht hgm hg
    (intervalIntegrable_const : IntervalIntegrable (fun _ : ℝ => D) volume 0 T) hinit
    (hsource.mono (fun u hu _ => hu))
  have hb : Real.exp (-L*t)*I+(∫ r in 0..t, Real.exp (-L*(t-r))*D) ≤ I+T*D := by
    have h := value_bounds hT hL hI hD JetBarrier.flight
      (fun _ => ⟨hI,le_rfl⟩) (fun _ => ⟨hD,le_rfl⟩) (t,(0 : JetPrototype.Phase))
    simpa only [value,GaussianLocal.time_eq ht] using h.2
  exact hp.mono (fun p hp => hp.trans hb)

theorem finite_difference_ae {I : Type*} {T L S D A : ℝ}
    (hT : 0 ≤ T) (hL : 0 ≤ L) (hD : 0 ≤ D) (hA : 0 ≤ A)
    (s : Finset I) (f₀ k₀ : I → JetPrototype.Phase → ℝ)
    (g h : I → ℝ × JetPrototype.Phase → ℝ)
    (hgm : ∀ i ∈ s, Measurable (g i)) (hhm : ∀ i ∈ s, Measurable (h i))
    (hg : ∀ i ∈ s, ∀ u, |g i u| ≤ S) (hh : ∀ i ∈ s, ∀ u, |h i u| ≤ S)
    (hinit : ∀ᵐ p ∂FlightMeasure.phaseVolume, (∑ i ∈ s, |f₀ i p-k₀ i p|) ≤ A)
    (hsource : ∀ᵐ u ∂(volume : Measure ℝ).prod FlightMeasure.phaseVolume,
      (∑ i ∈ s, |g i u-h i u|) ≤ D) (t : ℝ) :
    ∀ᵐ p ∂FlightMeasure.phaseVolume,
      (∑ i ∈ s, |value T L JetBarrier.flight (f₀ i) (g i) (t,p)-
        value T L JetBarrier.flight (k₀ i) (h i) (t,p)|) ≤ A+T*D := by
  let G (u : ℝ × JetPrototype.Phase) := ∑ i ∈ s, |g i u-h i u|
  have hGm : Measurable G := Finset.measurable_sum s (fun i hi => (hgm i hi |>.sub (hhm i hi)).abs)
  have hGb (u) : |G u| ≤ (s.card:ℝ)*(2*S) := by
    change |(∑ i ∈ s, |g i u-h i u|)| ≤ _
    rw [abs_of_nonneg (Finset.sum_nonneg (fun i _ => abs_nonneg _))]
    calc
      _ ≤ ∑ i ∈ s, 2*S := Finset.sum_le_sum (fun i hi => (abs_sub _ _).trans
        (by linarith [hg i hi u,hh i hi u]))
      _ = _ := by rw [Finset.sum_const,nsmul_eq_mul]
  have hv := value_le_constant_ae hT hL hD hA (time_bounds hT t) hinit hGm hGb hsource
  filter_upwards [hv] with p hp
  have hval := finite_difference_le hT hL s f₀ k₀ g h hgm hhm hg hh (t,p)
  have he := value_time_clamp hT L (fun p => ∑ i ∈ s, |f₀ i p-k₀ i p|) G (t,p)
  exact hval.trans (he.symm.trans_le hp)

end BoltzmannNonuniqueness.PositiveIntegral

end

end

section

/-! # Restricting and translating the damped mild integral -/

noncomputable section

open MeasureTheory Set

namespace BoltzmannNonuniqueness.PositiveIntegral

theorem shifted_value {U s t : ℝ} (ht : t-s ∈ Icc 0 U) (L : ℝ)
    (f₀ : JetPrototype.Phase → ℝ) (g : ℝ × JetPrototype.Phase → ℝ)
    (p : JetPrototype.Phase) :
    value U L JetBarrier.flight f₀ g (t-s,p) =
      Real.exp (-L*(t-s))*f₀ (JetBarrier.flight (s-t) p) +
      ∫ r in s..t, Real.exp (-L*(t-r))*g (r-s,JetBarrier.flight (r-t) p) := by
  unfold value
  rw [GaussianLocal.time_eq ht]
  have he : -(t-s) = s-t := by ring
  rw [he]
  congr 1
  have hi := intervalIntegral.integral_comp_add_right
    (fun r => Real.exp (-L*(t-r))*g (r-s,JetBarrier.flight (r-t) p)) s
    (a := 0) (b := t-s)
  rw [zero_add,sub_add_cancel] at hi
  rw [← hi]
  apply intervalIntegral.integral_congr
  intro r _
  dsimp only
  have h₁ : t-(r+s) = t-s-r := by ring
  have h₂ : r+s-s = r := by ring
  have h₃ : r+s-t = r-(t-s) := by ring
  rw [h₁,h₂,h₃]

end BoltzmannNonuniqueness.PositiveIntegral

end

end

end OAI
end

section
-- module Solutions.OAIQ080_BZ.Boltzmann_Branching_HotPhysicalSource
attribute [-instance] _root_.OAI.BoltzmannNonuniqueness.ChartKernel.offAxis_sFinite _root_.OAI.BoltzmannNonuniqueness.EuclideanFlight.sourcePullback_finite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.characteristicGainKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.hotKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.mixedKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.retainedKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.coldCylinderVolume_finite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.copyColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.mainCoreKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.selectedColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCoreSheet.dilatedColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCoreSheet.kineticColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.PeriodicApproximation.fiberMeasure_finite _root_.OAI.BoltzmannNonuniqueness.PositiveIteration.awayOriginKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.PositiveIteration.nearOriginKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamNormalCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamNormalRetainedKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.dampedCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.densityScaledCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalBeamKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalCollision_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalPhysicalEvent_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalWindowEvent_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.physicalEventMeasure_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.scaledBeamNormalKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.WeakTime.phaseEndpointKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.WeakTime.phaseIncrement_finite _root_.OAI.BoltzmannNonuniqueness.WeakTime.phaseSeed_sFinite _root_.OAI.BoltzmannNonuniqueness.WeakTime.residenceKernel_sFinite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

/-! # A fixed negligible velocity set for the weighted local construction

The exceptional set depends only on H and its proved quadratic gain bound,
not on a solution or an iterate. Setting the gain to zero there preserves
its almost-everywhere collision meaning and gives pointwise bounded sources.
-/

noncomputable section

open MeasureTheory Set
open scoped ENNReal
open BoltzmannNonuniqueness.VelocityWeight BoltzmannNonuniqueness.ChartKernel

namespace BoltzmannNonuniqueness.HotRepresentative

theorem measurable_nonnegativeGain {f g : Velocity → ℝ≥0∞}
    (hf : Measurable f) (hg : Measurable g) : Measurable (nonnegativeGain f g) := by
  let : SFinite (gainPairMeasure) := Measure.prod.instSFinite
  have hl : Measurable (fun p : Velocity × (Velocity × Sphere) =>
      scatterLeft p.1 p.2.1 p.2.2) := by
    unfold scatterLeft normalComponent
    fun_prop
  have hr : Measurable (fun p : Velocity × (Velocity × Sphere) =>
      scatterRight p.1 p.2.1 p.2.2) := by
    unfold scatterRight normalComponent
    fun_prop
  have hk : Measurable (fun p : Velocity × (Velocity × Sphere) =>
      ENNReal.ofReal (collisionKernel p.1 p.2.1 p.2.2) / 2) := by
    unfold collisionKernel normalComponent
    fun_prop
  exact (hk.mul (((hf.comp hl).mul (hg.comp hr)).add
    ((hg.comp hl).mul (hf.comp hr)))).lintegral_prod_right'

theorem measurableSet_good (q : ℝ) : MeasurableSet (good q) :=
  measurableSet_le (measurable_nonnegativeGain (measurable_H q).ennreal_ofReal
    (measurable_H q).ennreal_ofReal)
    ((measurable_H q).const_mul (HotApplication.realBound q)).ennreal_ofReal

theorem integrable_H_gain {q : ℝ} {v : Velocity} (hv : v ∈ good q) :
    Integrable (GainOrder.integrand (H q) v) ((volume : Measure Velocity).prod sphereArea) :=
  GainNonnegative.integrable_of_bound (measurable_H q) (H_nonneg q) v hv

theorem H_gain_bound {q : ℝ} {v : Velocity} (hv : v ∈ good q) :
    BoltzmannNonuniqueness.gain (fun p => H q p.2) 0 v ≤ HotApplication.realBound q * H q v :=
  GainNonnegative.gain_le_of_bound (measurable_H q) (H_nonneg q)
    (mul_nonneg (HotApplication.realBound_pos q).le (H_nonneg q v)) v 0 hv

variable {X : Type*} [MeasurableSpace X]

theorem measurable_density {f : X × Velocity → ℝ} (hf : Measurable f) (q : ℝ) :
    Measurable (density q f) := ((measurable_H q).comp measurable_snd).mul hf

theorem measurable_gain {f : X × Velocity → ℝ} (hf : Measurable f) (q b : ℝ) :
    Measurable (gain q b f) :=
  Measurable.ite ((measurableSet_good q).preimage measurable_snd)
    ((KineticCollisionNullSets.measurable_gain (measurable_density hf q) b).div
      ((measurable_H q).comp measurable_snd)) measurable_const

theorem measurable_frequency {f : X × Velocity → ℝ} (hf : Measurable f) (q b : ℝ) :
    Measurable (frequency q b f) :=
  KineticCollisionNullSets.measurable_frequency (measurable_density hf q) b

end BoltzmannNonuniqueness.HotRepresentative

end

end

section

/-! # Pointwise weighted gain bounds off the fixed exceptional set -/

noncomputable section

open MeasureTheory
open BoltzmannNonuniqueness.VelocityWeight

namespace BoltzmannNonuniqueness.HotRepresentative

theorem actual_gain_bound {q A : ℝ} {v : Velocity} (hv : v ∈ good q)
    {f : Velocity → ℝ} (hfm : Measurable f) (hf : ∀ w, 0 ≤ f w)
    (hfB : ∀ w, f w ≤ A * H q w) (b : ℝ) :
    CollisionCutoff.gain b f v ≤ A^2 * HotApplication.realBound q * H q v := by
  have hi := GainOrder.integrable_const_mul A v (integrable_H_gain hv)
  calc
    _ ≤ BoltzmannNonuniqueness.gain (fun p => f p.2) 0 v :=
      CollisionCutoff.gain_le b hfm hf v 0 (GainOrder.integrable_of_le hfm hf hfB v hi)
    _ ≤ BoltzmannNonuniqueness.gain (fun p => A * H q p.2) 0 v :=
      GainOrder.gain_mono hfm hf hfB v 0 hi
    _ = A^2 * BoltzmannNonuniqueness.gain (fun p => H q p.2) 0 v :=
      GainOrder.gain_const_mul A (H q) v 0
    _ ≤ A^2 * (HotApplication.realBound q * H q v) :=
      mul_le_mul_of_nonneg_left (H_gain_bound hv) (sq_nonneg A)
    _ = _ := by ring

theorem actual_gain_upper_difference {q A B D : ℝ} {v : Velocity} (hv : v ∈ good q)
    (hA : 0 ≤ A) (hB : 0 ≤ B) (hD : 0 ≤ D)
    {f g : Velocity → ℝ} (hfm : Measurable f) (hgm : Measurable g)
    (hf : ∀ w, 0 ≤ f w) (hg : ∀ w, 0 ≤ g w)
    (hfB : ∀ w, f w ≤ A * H q w) (hgB : ∀ w, g w ≤ B * H q w)
    (hfg : ∀ w, f w - g w ≤ D * H q w) (b : ℝ) :
    CollisionCutoff.gain b f v - CollisionCutoff.gain b g v ≤
      (D * (A+B) * HotApplication.realBound q) * H q v := by
  have hbase := integrable_H_gain hv
  have hfi := GainOrder.integrable_of_le hfm hf hfB v (GainOrder.integrable_const_mul A v hbase)
  have hgi := GainOrder.integrable_of_le hgm hg hgB v (GainOrder.integrable_const_mul B v hbase)
  have hfc := CollisionCutoff.integrable_gain b hfm hf v hfi
  have hgc := CollisionCutoff.integrable_gain b hgm hg v hgi
  calc
    _ = ∫ p, CollisionCutoff.integrand b f v p - CollisionCutoff.integrand b g v p
        ∂((volume : Measure Velocity).prod sphereArea) := (integral_sub hfc hgc).symm
    _ ≤ ∫ p, (D*(A+B)) * GainOrder.integrand (H q) v p
        ∂((volume : Measure Velocity).prod sphereArea) :=
      integral_mono (hfc.sub hgc) (hbase.const_mul _)
        (GainUpperDifference.cutoff_integrand_bound hA hB hD hf hg hfB hgB hfg b v)
    _ = (D*(A+B)) * BoltzmannNonuniqueness.gain (fun p => H q p.2) 0 v := integral_const_mul _ _
    _ ≤ (D*(A+B)) * (HotApplication.realBound q * H q v) :=
      mul_le_mul_of_nonneg_left (H_gain_bound hv) (mul_nonneg hD (add_nonneg hA hB))
    _ = _ := by ring

theorem actual_gain_difference {q A B D : ℝ} {v : Velocity} (hv : v ∈ good q)
    (hA : 0 ≤ A) (hB : 0 ≤ B) (hD : 0 ≤ D)
    {f g : Velocity → ℝ} (hfm : Measurable f) (hgm : Measurable g)
    (hf : ∀ w, 0 ≤ f w) (hg : ∀ w, 0 ≤ g w)
    (hfB : ∀ w, f w ≤ A * H q w) (hgB : ∀ w, g w ≤ B * H q w)
    (hfg : ∀ w, |f w - g w| ≤ D * H q w) (b : ℝ) :
    |CollisionCutoff.gain b f v - CollisionCutoff.gain b g v| ≤
      (D*(A+B)*HotApplication.realBound q) * H q v := by
  have h₁ := actual_gain_upper_difference hv hA hB hD hfm hgm hf hg hfB hgB
    (fun w => (le_abs_self _).trans (hfg w)) b
  have h₂ := actual_gain_upper_difference hv hB hA hD hgm hfm hg hf hgB hfB
    (fun w => (le_abs_self _).trans (by simpa only [abs_sub_comm] using hfg w)) b
  rw [add_comm B A] at h₂
  exact abs_le.mpr ⟨by linarith, h₁⟩

variable {X : Type*} [MeasurableSpace X]

omit [MeasurableSpace X] in
theorem gain_nonneg {f : X × Velocity → ℝ} (hf : ∀ p, 0 ≤ f p) (q b : ℝ) (p : X × Velocity) :
    0 ≤ gain q b f p := by
  unfold gain
  split_ifs
  · apply div_nonneg _ (H_nonneg _ _)
    apply integral_nonneg
    intro w
    exact mul_nonneg (mul_nonneg (CollisionCutoff.kernel_nonneg _ _ _ _)
      (mul_nonneg (H_nonneg _ _) (hf _))) (mul_nonneg (H_nonneg _ _) (hf _))
  · exact le_rfl

theorem gain_bound {q A : ℝ} (_hA : 0 ≤ A) {f : X × Velocity → ℝ}
    (hfm : Measurable f) (hf : ∀ p, 0 ≤ f p ∧ f p ≤ A) (b : ℝ) (p : X × Velocity) :
    gain q b f p ≤ A^2 * HotApplication.realBound q := by
  unfold gain
  split_ifs with hv
  · apply (div_le_iff₀ (H_pos q p.2)).mpr
    apply actual_gain_bound hv
      ((measurable_density hfm q).comp (measurable_const.prodMk measurable_id))
      (fun w => mul_nonneg (H_nonneg _ _) (hf _).1)
    intro w
    exact (mul_le_mul_of_nonneg_left (hf _).2 (H_nonneg _ _)).trans_eq (mul_comm _ _)
  · exact mul_nonneg (sq_nonneg A) (HotApplication.realBound_pos q).le

theorem gain_difference {q A B D : ℝ} (hA : 0 ≤ A) (hB : 0 ≤ B) (hD : 0 ≤ D)
    {f g : X × Velocity → ℝ} (hfm : Measurable f) (hgm : Measurable g)
    (hf : ∀ p, 0 ≤ f p ∧ f p ≤ A) (hg : ∀ p, 0 ≤ g p ∧ g p ≤ B)
    (hfg : ∀ p, |f p-g p| ≤ D) (b : ℝ) (p : X × Velocity) :
    |gain q b f p - gain q b g p| ≤ D*(A+B)*HotApplication.realBound q := by
  unfold gain
  split_ifs with hv
  · rw [← sub_div, abs_div, abs_of_pos (H_pos q p.2)]
    apply (div_le_iff₀ (H_pos q p.2)).mpr
    apply actual_gain_difference hv hA hB hD
      ((measurable_density hfm q).comp (measurable_const.prodMk measurable_id))
      ((measurable_density hgm q).comp (measurable_const.prodMk measurable_id))
      (fun w => mul_nonneg (H_nonneg _ _) (hf _).1)
      (fun w => mul_nonneg (H_nonneg _ _) (hg _).1)
      (fun w => (mul_le_mul_of_nonneg_left (hf _).2 (H_nonneg _ _)).trans_eq (mul_comm _ _))
      (fun w => (mul_le_mul_of_nonneg_left (hg _).2 (H_nonneg _ _)).trans_eq (mul_comm _ _))
    intro w
    change |H q w * f (p.1,w) - H q w * g (p.1,w)| ≤ _
    rw [← mul_sub, abs_mul, abs_of_nonneg (H_nonneg _ _)]
    exact (mul_le_mul_of_nonneg_left (hfg _) (H_nonneg _ _)).trans_eq (mul_comm _ _)
  · simp only [sub_self, abs_zero]
    exact mul_nonneg (mul_nonneg hD (add_nonneg hA hB)) (HotApplication.realBound_pos q).le

end BoltzmannNonuniqueness.HotRepresentative

end

end

section

/-! # Loss estimates and the collision meaning of weighted representatives -/

noncomputable section

open MeasureTheory
open BoltzmannNonuniqueness.VelocityWeight

namespace BoltzmannNonuniqueness.HotRepresentative

variable {X : Type*} [MeasurableSpace X]

omit [MeasurableSpace X] in
theorem density_bounds {q A : ℝ} {f : X × Velocity → ℝ}
    (hf : ∀ p, 0 ≤ f p ∧ f p ≤ A) (p : X × Velocity) :
    0 ≤ density q f p ∧ density q f p ≤ A * H q p.2 :=
  ⟨mul_nonneg (H_nonneg _ _) (hf p).1,
    (mul_le_mul_of_nonneg_left (hf p).2 (H_nonneg _ _)).trans_eq (mul_comm _ _)⟩

omit [MeasurableSpace X] in
theorem density_difference {q D : ℝ} {f g : X × Velocity → ℝ}
    (hfg : ∀ p, |f p-g p| ≤ D) (p : X × Velocity) :
    |density q f p - density q g p| ≤ D * H q p.2 := by
  unfold density
  rw [← mul_sub, abs_mul, abs_of_nonneg (H_nonneg _ _)]
  exact (mul_le_mul_of_nonneg_left (hfg p) (H_nonneg _ _)).trans_eq (mul_comm _ _)

omit [MeasurableSpace X] in
theorem frequency_nonneg {f : X × Velocity → ℝ} (hf : ∀ p, 0 ≤ f p)
    (q b : ℝ) (p : X × Velocity) : 0 ≤ frequency q b f p :=
  CutoffLipschitz.frequency_nonneg (fun _ => mul_nonneg (H_nonneg _ _) (hf _)) b p.2

theorem frequency_bound {q A b : ℝ} (hq : q < 2) (hb : 0 ≤ b)
    {f : X × Velocity → ℝ} (hfm : Measurable f) (hf : ∀ p, 0 ≤ f p ∧ f p ≤ A)
    (p : X × Velocity) : frequency q b f p ≤ A * CutoffLipschitz.frequencyConstant q b :=
  CutoffLipschitz.frequency_bound hq hb
    ((measurable_density hfm q).comp (measurable_const.prodMk measurable_id))
    (fun w => (density_bounds hf (p.1,w)).1) (fun w => (density_bounds hf (p.1,w)).2) p.2

theorem frequency_difference {q A B D b : ℝ} (hq : q < 2) (hb : 0 ≤ b)
    {f g : X × Velocity → ℝ} (hfm : Measurable f) (hgm : Measurable g)
    (hf : ∀ p, 0 ≤ f p ∧ f p ≤ A) (hg : ∀ p, 0 ≤ g p ∧ g p ≤ B)
    (hfg : ∀ p, |f p-g p| ≤ D) (p : X × Velocity) :
    |frequency q b f p - frequency q b g p| ≤ D * CutoffLipschitz.frequencyConstant q b :=
  CutoffLipschitz.frequency_difference hq hb
    ((measurable_density hfm q).comp (measurable_const.prodMk measurable_id))
    ((measurable_density hgm q).comp (measurable_const.prodMk measurable_id))
    (fun w => (density_bounds hf (p.1,w)).1) (fun w => (density_bounds hg (p.1,w)).1)
    (fun w => (density_bounds hf (p.1,w)).2) (fun w => (density_bounds hg (p.1,w)).2)
    (fun w => density_difference hfg (p.1,w)) p.2

end BoltzmannNonuniqueness.HotRepresentative

end

end

section

/-! # Bounded positive source for the H-weighted local equation -/

noncomputable section

open MeasureTheory

namespace BoltzmannNonuniqueness.HotRepresentative

variable {X : Type*} [MeasurableSpace X]

theorem measurable_source {f : X × Velocity → ℝ} (hf : Measurable f) (q b L : ℝ) :
    Measurable (source q b L f) :=
  (measurable_gain hf q b).add ((measurable_const.sub (measurable_frequency hf q b)).mul hf)

theorem source_bounds {q b L R : ℝ} (hq : q < 2) (hb : 0 ≤ b) (hR : 0 ≤ R)
    (hL : R * CutoffLipschitz.frequencyConstant q b ≤ L)
    {f : X × Velocity → ℝ} (hfm : Measurable f) (hf : ∀ p, 0 ≤ f p ∧ f p ≤ R)
    (p : X × Velocity) :
    0 ≤ source q b L f p ∧ source q b L f p ≤ HotApplication.realBound q * R^2 + L*R := by
  have hν := frequency_nonneg (fun p => (hf p).1) q b p
  have hνB := frequency_bound hq hb hfm hf p
  have hLp : 0 ≤ L := (mul_nonneg hR (CutoffLipschitz.frequencyConstant_nonneg hb q)).trans hL
  constructor
  · exact add_nonneg (gain_nonneg (fun p => (hf p).1) q b p)
      (mul_nonneg (sub_nonneg.mpr (hνB.trans hL)) (hf p).1)
  · have hg := gain_bound (q := q) hR hfm hf b p
    have hl : (L - frequency q b f p) * f p ≤ L*R :=
      (mul_le_mul_of_nonneg_right (sub_le_self _ hν) (hf p).1).trans
        (mul_le_mul_of_nonneg_left (hf p).2 hLp)
    unfold source
    nlinarith only [hg,hl]

theorem source_difference {q b L R D : ℝ} (hq : q < 2) (hb : 0 ≤ b)
    (hL : 0 ≤ L) (hR : 0 ≤ R) (hD : 0 ≤ D)
    {f g : X × Velocity → ℝ} (hfm : Measurable f) (hgm : Measurable g)
    (hf : ∀ p, 0 ≤ f p ∧ f p ≤ R) (hg : ∀ p, 0 ≤ g p ∧ g p ≤ R)
    (hfg : ∀ p, |f p-g p| ≤ D) (p : X × Velocity) :
    |source q b L f p - source q b L g p| ≤
      (2*R*(HotApplication.realBound q + CutoffLipschitz.frequencyConstant q b)+L)*D := by
  have hgain := gain_difference (q := q) hR hR hD hfm hgm hf hg hfg b p
  have hνdiff := frequency_difference hq hb hfm hgm hf hg hfg p
  have hνfb : |frequency q b f p| ≤ R * CutoffLipschitz.frequencyConstant q b := by
    rw [abs_of_nonneg (frequency_nonneg (fun p => (hf p).1) q b p)]
    exact frequency_bound hq hb hfm hf p
  have hgabs : |g p| ≤ R := by rw [abs_of_nonneg (hg p).1]; exact (hg p).2
  have hloss : |frequency q b f p * f p - frequency q b g p * g p| ≤
      2 * CutoffLipschitz.frequencyConstant q b * R * D := by
    calc
      _ = |frequency q b f p * (f p-g p) + (frequency q b f p-frequency q b g p)*g p| := by
        congr 1; ring
      _ ≤ |frequency q b f p| * |f p-g p| + |frequency q b f p-frequency q b g p| * |g p| := by
        simpa only [abs_mul] using abs_add_le (frequency q b f p * (f p-g p))
          ((frequency q b f p-frequency q b g p)*g p)
      _ ≤ (R*CutoffLipschitz.frequencyConstant q b)*D + (D*CutoffLipschitz.frequencyConstant q b)*R :=
        add_le_add (mul_le_mul hνfb (hfg p) (abs_nonneg _)
          (mul_nonneg hR (CutoffLipschitz.frequencyConstant_nonneg hb q)))
          (mul_le_mul hνdiff hgabs (abs_nonneg _)
            (mul_nonneg hD (CutoffLipschitz.frequencyConstant_nonneg hb q)))
      _ = _ := by ring
  calc
    _ = |(gain q b f p-gain q b g p)+L*(f p-g p)-
        (frequency q b f p*f p-frequency q b g p*g p)| := by unfold source; congr 1; ring
    _ ≤ |gain q b f p-gain q b g p|+L*|f p-g p|+
        |frequency q b f p*f p-frequency q b g p*g p| := by
      have ha : |(gain q b f p-gain q b g p)+L*(f p-g p)| ≤
          |gain q b f p-gain q b g p|+L*|f p-g p| := by
        simpa only [abs_mul, abs_of_nonneg hL] using
          abs_add_le (gain q b f p-gain q b g p) (L*(f p-g p))
      exact (abs_sub _ _).trans (add_le_add ha le_rfl)
    _ ≤ D*(R+R)*HotApplication.realBound q+L*D+
        2*CutoffLipschitz.frequencyConstant q b*R*D :=
      add_le_add (add_le_add hgain (mul_le_mul_of_nonneg_left (hfg p) hL)) hloss
    _ = _ := by ring

end BoltzmannNonuniqueness.HotRepresentative

end

end

section

/-! # Polynomial control of a hot remainder satisfying the mild equation a.e. -/

noncomputable section

open MeasureTheory Set

namespace BoltzmannNonuniqueness.PhaseEssSup

theorem continuousOn_size_of_mildAE {T L A S : ℝ} (hT : 0 ≤ T) (hL : 0 ≤ L)
    (hA : 0 ≤ A) (hS : 0 ≤ S) {f₀ : JetPrototype.Phase → ℝ}
    {f g : ℝ × JetPrototype.Phase → ℝ}
    (hf₀m : Measurable f₀) (hgm : Measurable g)
    (hf₀ : ∀ p, 0 ≤ f₀ p ∧ f₀ p ≤ A) (hg : ∀ u, 0 ≤ g u ∧ g u ≤ S)
    (hfix : ∀ t ∈ Icc 0 T, (fun p => f (t,p)) =ᵐ[FlightMeasure.phaseVolume]
      (fun p => PositiveIntegral.value T L JetBarrier.flight f₀ g (t,p))) :
    ContinuousOn (fun t => size (fun p => f (t,p))) (Icc 0 T) := by
  have hv : Continuous (fun t => size (fun p =>
      PositiveIntegral.value T L JetBarrier.flight f₀ g (t,p))) :=
    continuous_size_of_mildAE hT hL hA hS hf₀m hgm hf₀ hg (fun _ => ae_of_all _ (fun _ => rfl))
  apply hv.continuousOn.congr
  intro t ht
  exact size_congr_ae (hfix t ht)

end BoltzmannNonuniqueness.PhaseEssSup

end

end

end OAI
end

section
-- module Solutions.OAIQ080_BZ.Boltzmann_Jets_JetColdLimitComparison
attribute [-instance] _root_.OAI.BoltzmannNonuniqueness.ChartKernel.offAxis_sFinite _root_.OAI.BoltzmannNonuniqueness.EuclideanFlight.sourcePullback_finite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.characteristicGainKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.hotKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.mixedKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.retainedKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.coldCylinderVolume_finite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.copyColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.mainCoreKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.selectedColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCoreSheet.dilatedColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCoreSheet.kineticColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.PeriodicApproximation.fiberMeasure_finite _root_.OAI.BoltzmannNonuniqueness.PositiveIteration.awayOriginKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.PositiveIteration.nearOriginKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamNormalCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamNormalRetainedKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.dampedCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.densityScaledCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalBeamKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalCollision_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalPhysicalEvent_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalWindowEvent_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.physicalEventMeasure_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.scaledBeamNormalKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.WeakTime.phaseEndpointKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.WeakTime.phaseIncrement_finite _root_.OAI.BoltzmannNonuniqueness.WeakTime.phaseSeed_sFinite _root_.OAI.BoltzmannNonuniqueness.WeakTime.residenceKernel_sFinite
attribute [-simp] _root_.OAI.BoltzmannNonuniqueness.EuclideanFlight.phaseEquiv_snd _root_.OAI.BoltzmannNonuniqueness.timeTranslation_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

/-! # Gaussian control of the actual finite annular datum -/

noncomputable section

open MeasureTheory
open scoped BigOperators
open BoltzmannNonuniqueness.JetPrototype BoltzmannNonuniqueness.JetGeometry

namespace BoltzmannNonuniqueness.JetFiniteGaussian

theorem coefficient_nonneg {s₀ K d₀ : ℝ} (hs₀ : 0 < s₀) (hK : 0 ≤ K) (hd₀ : 0 ≤ d₀)
    (η : ℝ) (j : ℕ) : 0 ≤ coefficient s₀ η K d₀ j := by
  have hs := DatumBounds.scale_pos (η := η) hs₀ (j+1)
  have hJ := JetThermalKernel.bound_pos
  unfold coefficient jetScale
  positivity

theorem amplitude_pos {s₀ K d₀ : ℝ} (hs₀ : 0 < s₀) (hK : 0 ≤ K) (hd₀ : 0 ≤ d₀)
    (η : ℝ) (N : ℕ) : 0 < amplitude s₀ η K d₀ N := by
  have h := Finset.sum_nonneg (s := indices N)
    (fun i _ => coefficient_nonneg hs₀ hK hd₀ η i.1)
  unfold amplitude
  linarith

theorem term_bound {s₀ η K d₀ α : ℝ} (hs₀ : 0 < s₀) (hsmax : s₀ ≤ 1 / 8)
    (hη : 0 ≤ η) (hK : 0 ≤ K) (hd₀ : 0 < d₀)
    (hwidth : d₀ * (1 / 8 : ℝ) ^ 10 ≤ 1 / 64) (hα : 0 ≤ α) (hαmax : α ≤ 1 / 4)
    (γ : ℝ) (i : JetDatum.Index) (p : JetPrototype.Phase) :
    JetDatum.term s₀ η K α γ d₀ i p ≤ coefficient s₀ η K d₀ i.1 * JetGaussianMoments.kernel 2 p.2 := by
  have hs := DatumBounds.scale_pos (η := η) hs₀ (i.1+1)
  have hd : 0 < d₀ * jetScale s₀ η i.1 ^ 10 := mul_pos hd₀ (pow_pos hs _)
  have hcoef := coefficient_nonneg hs₀ hK hd₀.le η i.1
  by_cases hz : JetDatum.term s₀ η K α γ d₀ i p = 0
  · rw [hz]
    exact mul_nonneg hcoef (Real.exp_pos _).le
  have hv := JetSupport.density_support_two hd
    (JetDatumMoments.thermal_width_le hs₀ hsmax hη hd₀.le hwidth i.1) hα hαmax η K γ _ i.2 hz
  have hW : 1 ≤ Real.exp 8 * JetGaussianMoments.kernel 2 p.2 := by
    unfold JetGaussianMoments.kernel
    rw [← Real.exp_add]
    apply Real.one_le_exp_iff.mpr
    nlinarith [norm_nonneg p.2]
  let A := (K / jetScale s₀ η i.1) * ((d₀ * jetScale s₀ η i.1 ^ 10) ^ 3)⁻¹ * JetThermalKernel.bound
  have hA : 0 ≤ A := by
    have hJ := JetThermalKernel.bound_pos
    dsimp [A]
    positivity
  calc
    _ ≤ A := JetBarrier.initial_density_bound hK hs hd.le η α γ i.2 p
    _ ≤ A * (Real.exp 8 * JetGaussianMoments.kernel 2 p.2) := by
      simpa only [mul_one] using mul_le_mul_of_nonneg_left hW hA
    _ = _ := by unfold coefficient; dsimp [A] <;> ring

end BoltzmannNonuniqueness.JetFiniteGaussian

end

end

end OAI
end

section
-- module Solutions.OAIQ080_BZ.Boltzmann_Branching_WeightedJetSolutions
attribute [-instance] _root_.OAI.BoltzmannNonuniqueness.ChartKernel.offAxis_sFinite _root_.OAI.BoltzmannNonuniqueness.EuclideanFlight.sourcePullback_finite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.characteristicGainKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.hotKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.mixedKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.retainedKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.coldCylinderVolume_finite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.copyColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.mainCoreKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.selectedColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCoreSheet.dilatedColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCoreSheet.kineticColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.PeriodicApproximation.fiberMeasure_finite _root_.OAI.BoltzmannNonuniqueness.PositiveIteration.awayOriginKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.PositiveIteration.nearOriginKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamNormalCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamNormalRetainedKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.dampedCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.densityScaledCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalBeamKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalCollision_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalPhysicalEvent_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalWindowEvent_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.physicalEventMeasure_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.scaledBeamNormalKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.WeakTime.phaseEndpointKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.WeakTime.phaseIncrement_finite _root_.OAI.BoltzmannNonuniqueness.WeakTime.phaseSeed_sFinite _root_.OAI.BoltzmannNonuniqueness.WeakTime.residenceKernel_sFinite
attribute [-simp] _root_.OAI.BoltzmannNonuniqueness.EuclideanFlight.phaseEquiv_snd _root_.OAI.BoltzmannNonuniqueness.timeTranslation_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

/-! # Monotone and dominated limits for the weighted representative gain -/

noncomputable section

open MeasureTheory Filter
open scoped Topology
open BoltzmannNonuniqueness.VelocityWeight

namespace BoltzmannNonuniqueness.HotRepresentative

variable {X : Type*} [MeasurableSpace X]

theorem integrable_cutoff {q R : ℝ} {f : X × Velocity → ℝ}
    (hfm : Measurable f) (hf : ∀ p, 0 ≤ f p ∧ f p ≤ R)
    (b : ℝ) (p : X × Velocity) (hp : p.2 ∈ good q) :
    Integrable (CollisionCutoff.integrand b (fun v => density q f (p.1,v)) p.2)
      ((volume : Measure Velocity).prod sphereArea) := by
  have hm : Measurable (fun v => density q f (p.1,v)) := (measurable_density hfm q).comp (measurable_const.prodMk measurable_id)
  have hn : ∀ v, 0 ≤ density q f (p.1,v) := fun v => (density_bounds (q := q) hf (p.1,v)).1
  exact CollisionCutoff.integrable_gain b hm hn p.2
    (GainOrder.integrable_of_le hm hn (fun v => (density_bounds (q := q) hf (p.1,v)).2) p.2
      (GainOrder.integrable_const_mul R p.2 (integrable_H_gain hp)))

theorem gain_mono {q R : ℝ} {f g : X × Velocity → ℝ}
    (hfm : Measurable f) (hgm : Measurable g)
    (hf : ∀ p, 0 ≤ f p) (hfg : ∀ p, f p ≤ g p) (hg : ∀ p, g p ≤ R)
    (b : ℝ) (p : X × Velocity) : gain q b f p ≤ gain q b g p := by
  have hfn p : 0 ≤ f p ∧ f p ≤ R := ⟨hf p,(hfg p).trans (hg p)⟩
  have hgn p : 0 ≤ g p ∧ g p ≤ R := ⟨(hf p).trans (hfg p),hg p⟩
  unfold gain
  split_ifs with hp
  · apply div_le_div_of_nonneg_right _ (H_nonneg q p.2)
    apply integral_mono (integrable_cutoff hfm hfn b p hp) (integrable_cutoff hgm hgn b p hp)
    intro w
    unfold CollisionCutoff.integrand density
    have hL := mul_le_mul_of_nonneg_left (hfg (p.1,scatterLeft p.2 w.1 w.2)) (H_nonneg q (scatterLeft p.2 w.1 w.2))
    have hR := mul_le_mul_of_nonneg_left (hfg (p.1,scatterRight p.2 w.1 w.2)) (H_nonneg q (scatterRight p.2 w.1 w.2))
    exact mul_le_mul (mul_le_mul_of_nonneg_left hL (CollisionCutoff.kernel_nonneg _ _ _ _)) hR
      (mul_nonneg (H_nonneg _ _) (hf _))
      (mul_nonneg (CollisionCutoff.kernel_nonneg _ _ _ _) (mul_nonneg (H_nonneg _ _) (hgn _).1))
  · exact le_rfl

theorem gain_tendsto {q R : ℝ} (_hR : 0 ≤ R) {f : ℕ → X × Velocity → ℝ} {g : X × Velocity → ℝ}
    (hfm : ∀ n, Measurable (f n)) (hf : ∀ n p, 0 ≤ f n p ∧ f n p ≤ R)
    (hlim : ∀ p, Tendsto (fun n => f n p) atTop (𝓝 (g p))) (b : ℝ) (p : X × Velocity) :
    Tendsto (fun n => gain q b (f n) p) atTop (𝓝 (gain q b g p)) := by
  unfold gain
  split_ifs with hp
  · apply Tendsto.div_const
    apply tendsto_integral_of_dominated_convergence
      (fun w => R^2 * GainOrder.integrand (H q) p.2 w)
    · intro n
      exact (integrable_cutoff (hfm n) (hf n) b p hp).aestronglyMeasurable
    · exact (integrable_H_gain hp).const_mul _
    · intro n
      apply ae_of_all
      intro w
      rw [Real.norm_eq_abs, abs_of_nonneg]
      · apply (CollisionCutoff.integrand_le b (fun v => (density_bounds (q := q) (hf n) (p.1,v)).1) p.2 w).trans
        have h := GainOrder.integrand_mono (fun v => (density_bounds (q := q) (hf n) (p.1,v)).1)
          (fun v => (density_bounds (q := q) (hf n) (p.1,v)).2) p.2 w
        unfold GainOrder.integrand density at h ⊢
        nlinarith only [h]
      · exact mul_nonneg (mul_nonneg (CollisionCutoff.kernel_nonneg _ _ _ _)
          (density_bounds (q := q) (hf n) _).1) (density_bounds (q := q) (hf n) _).1
    · apply ae_of_all
      intro w
      exact ((tendsto_const_nhds.mul (tendsto_const_nhds.mul (hlim _))).mul
        (tendsto_const_nhds.mul (hlim _)))
  · exact tendsto_const_nhds

end BoltzmannNonuniqueness.HotRepresentative

end

end

section

/-! # Positive local iteration in the manuscript's singular weighted norm -/

noncomputable section

open MeasureTheory

namespace BoltzmannNonuniqueness.WeightedLocal

theorem measurable_forcing {f : ℝ × JetPrototype.Phase → ℝ} (hf : Measurable f) (q b L : ℝ) :
    Measurable (forcing q b L f) :=
  (HotRepresentative.measurable_source (GaussianLocal.measurable_state hf) q b L).comp (by fun_prop)

theorem exists_normalized {q b L T A R : ℝ} (hq : q < 2) (hb : 0 ≤ b)
    (hL : 0 ≤ L) (hT : 0 ≤ T) (hA : 0 ≤ A) (hR : 0 ≤ R)
    (hloss : R * CutoffLipschitz.frequencyConstant q b ≤ L)
    (hball : A + T*(HotApplication.realBound q * R^2 + L*R) ≤ R)
    (hsmall : T*(2*R*(HotApplication.realBound q + CutoffLipschitz.frequencyConstant q b)+L) < 1)
    {f₀ : JetPrototype.Phase → ℝ} (hf₀m : Measurable f₀) (hf₀ : ∀ p, 0 ≤ f₀ p ∧ f₀ p ≤ A) :
    ∃ f : ℝ × JetPrototype.Phase → ℝ, Measurable f ∧
      (∀ z, 0 ≤ f z ∧ f z ≤ R) ∧
      ∀ z, f z = PositiveIntegral.value T L JetBarrier.flight f₀ (forcing q b L f) z := by
  let S := HotApplication.realBound q * R^2 + L*R
  let K := 2*R*(HotApplication.realBound q + CutoffLipschitz.frequencyConstant q b)+L
  have hS : 0 ≤ S := by
    have := (HotApplication.realBound_pos q).le
    dsimp [S] <;> positivity
  have hK : 0 ≤ K := by
    have := (HotApplication.realBound_pos q).le
    have := CutoffLipschitz.frequencyConstant_nonneg hb q
    dsimp [K] <;> positivity
  obtain ⟨f,hf⟩ := PositiveIntegral.exists_fixed_point hT hL hA hR hS hK hball hsmall
    GaussianLocal.measurable_flight hf₀m hf₀
    (fun f => forcing q b L (fun z => f.val z))
    (fun f => measurable_forcing (BoundedMeasurable.measurable _ f.val) q b L)
    (fun f z => HotRepresentative.source_bounds hq hb hR hloss
      (GaussianLocal.measurable_state (BoundedMeasurable.measurable _ f.val))
      (fun p => f.property (p.1.1,(p.1.2,p.2))) ((z.1,z.2.1),z.2.2))
    (fun f g z => HotRepresentative.source_difference hq hb hL hR dist_nonneg
      (GaussianLocal.measurable_state (BoundedMeasurable.measurable _ f.val))
      (GaussianLocal.measurable_state (BoundedMeasurable.measurable _ g.val))
      (fun p => f.property (p.1.1,(p.1.2,p.2)))
      (fun p => g.property (p.1.1,(p.1.2,p.2)))
      (fun p => BoundedMeasurable.dist_apply_le _ f.val g.val (p.1.1,(p.1.2,p.2)))
      ((z.1,z.2.1),z.2.2))
  exact ⟨fun z => f.val z, BoundedMeasurable.measurable _ f.val, f.property, hf⟩

end BoltzmannNonuniqueness.WeightedLocal

end

end

section

/-! # The actual finite periodic datum in the singular weighted space -/

noncomputable section

open MeasureTheory
open BoltzmannNonuniqueness.VelocityWeight

namespace BoltzmannNonuniqueness.WeightedFiniteSeed

theorem amplitude_pos {s₀ K d₀ : ℝ} (hs₀ : 0 < s₀) (hK : 0 ≤ K) (hd₀ : 0 ≤ d₀)
    (η : ℝ) (N : ℕ) : 0 < amplitude s₀ η K d₀ N :=
  mul_pos (JetFiniteGaussian.amplitude_pos hs₀ hK hd₀ η N) tiltConstant_pos

end BoltzmannNonuniqueness.WeightedFiniteSeed

end

end

section

/-! # Quantitative dependence in the singular weighted local space -/

noncomputable section

open MeasureTheory

namespace BoltzmannNonuniqueness.WeightedLocal

theorem normalized_difference {q b L T R I : ℝ} (hq : q < 2) (hb : 0 ≤ b)
    (hL : 0 ≤ L) (hT : 0 ≤ T) (hR : 0 ≤ R) (hI : 0 ≤ I)
    (hloss : R*CutoffLipschitz.frequencyConstant q b ≤ L)
    (hsmall : T*(2*R*(HotApplication.realBound q+CutoffLipschitz.frequencyConstant q b)+L) < 1)
    {f₀ g₀ : JetPrototype.Phase → ℝ} (hseed : ∀ p, |f₀ p-g₀ p| ≤ I)
    {f g : ℝ × JetPrototype.Phase → ℝ} (hfm : Measurable f) (hgm : Measurable g)
    (hf : ∀ z, 0 ≤ f z ∧ f z ≤ R) (hg : ∀ z, 0 ≤ g z ∧ g z ≤ R)
    (hfeq : ∀ z, f z = PositiveIntegral.value T L JetBarrier.flight f₀ (forcing q b L f) z)
    (hgeq : ∀ z, g z = PositiveIntegral.value T L JetBarrier.flight g₀ (forcing q b L g) z)
    (z : ℝ × JetPrototype.Phase) :
    |f z-g z| ≤ I / (1-T*(2*R*(HotApplication.realBound q+CutoffLipschitz.frequencyConstant q b)+L)) := by
  let P := ℝ × JetPrototype.Phase
  let f' := BoundedMeasurable.ofBounded P f hfm R
    (fun z => by rw [abs_of_nonneg (hf z).1]; exact (hf z).2)
  let g' := BoundedMeasurable.ofBounded P g hgm R
    (fun z => by rw [abs_of_nonneg (hg z).1]; exact (hg z).2)
  let K := 2*R*(HotApplication.realBound q+CutoffLipschitz.frequencyConstant q b)+L
  let S := HotApplication.realBound q*R^2+L*R
  have hK : 0 ≤ K := by
    have := (HotApplication.realBound_pos q).le
    have := CutoffLipschitz.frequencyConstant_nonneg hb q
    dsimp [K] <;> positivity
  have hsource (u : ℝ × JetPrototype.Phase → ℝ) (hum : Measurable u)
      (hu : ∀ z, 0 ≤ u z ∧ u z ≤ R) (z) : |forcing q b L u z| ≤ S := by
    have h := HotRepresentative.source_bounds hq hb hR hloss (GaussianLocal.measurable_state hum)
      (fun p => hu (p.1.1,(p.1.2,p.2))) ((z.1,z.2.1),z.2.2)
    change 0 ≤ forcing q b L u z ∧ _ at h
    rw [abs_of_nonneg h.1]
    exact h.2
  have hdiff (z) : |forcing q b L f z-forcing q b L g z| ≤ K*dist f' g' :=
    HotRepresentative.source_difference hq hb hL hR dist_nonneg
      (GaussianLocal.measurable_state hfm) (GaussianLocal.measurable_state hgm)
      (fun p => hf (p.1.1,(p.1.2,p.2))) (fun p => hg (p.1.1,(p.1.2,p.2)))
      (fun p => BoundedMeasurable.dist_apply_le P f' g' (p.1.1,(p.1.2,p.2)))
      ((z.1,z.2.1),z.2.2)
  have hd : dist f' g' ≤ I+(T*K)*dist f' g' := by
    apply BoundedMeasurable.dist_le P (by positivity)
    intro z
    change |f z-g z| ≤ _
    rw [hfeq z,hgeq z]
    simpa only [mul_assoc] using PositiveIntegral.value_difference_initial hT hL
      (mul_nonneg hK dist_nonneg) hI GaussianLocal.measurable_flight hseed
      (measurable_forcing hfm q b L) (measurable_forcing hgm q b L)
      (hsource f hfm hf) (hsource g hgm hg) hdiff z
  have hden : 0 < 1-T*K := by dsimp [K] <;> linarith
  have hdist : dist f' g' ≤ I/(1-T*K) := (le_div_iff₀ hden).mpr (by nlinarith [hd])
  exact (BoundedMeasurable.dist_apply_le P f' g' z).trans hdist

end BoltzmannNonuniqueness.WeightedLocal

end

end

section

/-! # Finite-color domination for the H-weighted collision gain -/

noncomputable section

open MeasureTheory

namespace BoltzmannNonuniqueness.HotRepresentative

variable {X I : Type*} [MeasurableSpace X]

theorem finite_sum_gain_le {q R : ℝ} (s : Finset I)
    {c : I → X × Velocity → ℝ} {F : X × Velocity → ℝ}
    (hcm : ∀ i ∈ s, Measurable (c i)) (hFm : Measurable F)
    (hc : ∀ i ∈ s, ∀ p, 0 ≤ c i p ∧ c i p ≤ R)
    (hF : ∀ p, 0 ≤ F p ∧ F p ≤ R)
    (hSum : ∀ p, ∑ i ∈ s, c i p ≤ F p) (b : ℝ) (p : X × Velocity) :
    ∑ i ∈ s, gain q b (c i) p ≤ gain q b F p := by
  classical
  by_cases hp : p.2 ∈ good q
  · have hci (i) (hi : i ∈ s) := integrable_cutoff (hcm i hi) (hc i hi) b p hp
    have hFi := integrable_cutoff hFm hF b p hp
    have hsumD (v : Velocity) : ∑ i ∈ s, density q (c i) (p.1,v) ≤ density q F (p.1,v) := by
      unfold density
      rw [← Finset.mul_sum]
      exact mul_le_mul_of_nonneg_left (hSum _) (VelocityWeight.H_nonneg _ _)
    have hcn (i) (hi : i ∈ s) (v : Velocity) : 0 ≤ density q (c i) (p.1,v) :=
      (density_bounds (q := q) (hc i hi) (p.1,v)).1
    have hFn (v : Velocity) : 0 ≤ density q F (p.1,v) := (density_bounds (q := q) hF (p.1,v)).1
    simp only [gain,ite_eq_left hp]
    rw [← Finset.sum_div]
    apply div_le_div_of_nonneg_right _ (VelocityWeight.H_nonneg q p.2)
    change (∑ i ∈ s, ∫ w, CollisionCutoff.integrand b
      (fun v => density q (c i) (p.1,v)) p.2 w ∂((volume : Measure Velocity).prod sphereArea)) ≤ _
    rw [← integral_finsetSum _ hci]
    apply integral_mono (integrable_finsetSum s hci) hFi
    intro w
    have hdiag : (∑ i ∈ s, density q (c i) (p.1,scatterLeft p.2 w.1 w.2) *
        density q (c i) (p.1,scatterRight p.2 w.1 w.2)) ≤
        density q F (p.1,scatterLeft p.2 w.1 w.2) * density q F (p.1,scatterRight p.2 w.1 w.2) := by
      calc
        _ ≤ ∑ i ∈ s, density q (c i) (p.1,scatterLeft p.2 w.1 w.2) *
            (∑ j ∈ s, density q (c j) (p.1,scatterRight p.2 w.1 w.2)) := by
          apply Finset.sum_le_sum
          intro i hi
          exact mul_le_mul_of_nonneg_left (Finset.single_le_sum (fun j hj => hcn j hj _) hi) (hcn i hi _)
        _ = (∑ i ∈ s, density q (c i) (p.1,scatterLeft p.2 w.1 w.2)) *
            (∑ j ∈ s, density q (c j) (p.1,scatterRight p.2 w.1 w.2)) := by rw [Finset.sum_mul]
        _ ≤ _ := mul_le_mul (hsumD _) (hsumD _) (Finset.sum_nonneg (fun i hi => hcn i hi _)) (hFn _)
    unfold CollisionCutoff.integrand
    simp_rw [mul_assoc]
    rw [← Finset.mul_sum]
    exact mul_le_mul_of_nonneg_left hdiag (CollisionCutoff.kernel_nonneg _ _ _ _)
  · simp only [gain,ite_eq_right hp,Finset.sum_const_zero,le_refl]

end BoltzmannNonuniqueness.HotRepresentative

end

end

section

/-! # Common-loss cold source in the singular weighted space -/

noncomputable section

open MeasureTheory Filter
open scoped Topology

namespace BoltzmannNonuniqueness.HotRepresentative

variable {X : Type*} [MeasurableSpace X]

theorem measurable_coldSource {F c : X × Velocity → ℝ} (hFm : Measurable F) (hcm : Measurable c)
    (q b L : ℝ) : Measurable (coldSource q b L F c) :=
  (measurable_gain hcm q b).add ((measurable_const.sub (measurable_frequency hFm q b)).mul hcm)

theorem coldSource_bounds {q b L R : ℝ} (hq : q < 2) (hb : 0 ≤ b) (hR : 0 ≤ R)
    (hL : R*CutoffLipschitz.frequencyConstant q b ≤ L)
    {F c : X × Velocity → ℝ} (hFm : Measurable F) (hcm : Measurable c)
    (hF : ∀ p, 0 ≤ F p ∧ F p ≤ R) (hc : ∀ p, 0 ≤ c p ∧ c p ≤ R) (p : X × Velocity) :
    0 ≤ coldSource q b L F c p ∧ coldSource q b L F c p ≤ HotApplication.realBound q*R^2+L*R := by
  have hν := frequency_nonneg (fun p => (hF p).1) q b p
  have hνB := frequency_bound hq hb hFm hF p
  have hLp : 0 ≤ L := (mul_nonneg hR (CutoffLipschitz.frequencyConstant_nonneg hb q)).trans hL
  constructor
  · exact add_nonneg (gain_nonneg (fun p => (hc p).1) q b p)
      (mul_nonneg (sub_nonneg.mpr (hνB.trans hL)) (hc p).1)
  · have hg := gain_bound (q := q) hR hcm hc b p
    have hl : (L-frequency q b F p)*c p ≤ L*R :=
      (mul_le_mul_of_nonneg_right (sub_le_self _ hν) (hc p).1).trans
        (mul_le_mul_of_nonneg_left (hc p).2 hLp)
    unfold coldSource
    nlinarith only [hg,hl]

theorem coldSource_mono {q b L R : ℝ} (hq : q < 2) (hb : 0 ≤ b)
    (hL : R*CutoffLipschitz.frequencyConstant q b ≤ L)
    {F c d : X × Velocity → ℝ} (hFm : Measurable F) (hcm : Measurable c) (hdm : Measurable d)
    (hF : ∀ p, 0 ≤ F p ∧ F p ≤ R) (hcn : ∀ p, 0 ≤ c p)
    (hcd : ∀ p, c p ≤ d p) (hdR : ∀ p, d p ≤ R) (p : X × Velocity) :
    coldSource q b L F c p ≤ coldSource q b L F d p := by
  have hν : frequency q b F p ≤ L := (frequency_bound hq hb hFm hF p).trans hL
  exact add_le_add (gain_mono hcm hdm hcn hcd hdR b p)
    (mul_le_mul_of_nonneg_left (hcd p) (sub_nonneg.mpr hν))

theorem coldSource_tendsto {q R : ℝ} (hR : 0 ≤ R) (b L : ℝ) (F : X × Velocity → ℝ)
    {c : ℕ → X × Velocity → ℝ} {d : X × Velocity → ℝ}
    (hcm : ∀ n, Measurable (c n)) (hc : ∀ n p, 0 ≤ c n p ∧ c n p ≤ R)
    (hlim : ∀ p, Tendsto (fun n => c n p) atTop (𝓝 (d p))) (p : X × Velocity) :
    Tendsto (fun n => coldSource q b L F (c n) p) atTop (𝓝 (coldSource q b L F d p)) :=
  (gain_tendsto hR hcm hc hlim b p).add (tendsto_const_nhds.mul (hlim p))

end BoltzmannNonuniqueness.HotRepresentative

end

end

section

/-! # Positive cold iteration beneath the H-weighted total solution -/

noncomputable section

open MeasureTheory

namespace BoltzmannNonuniqueness.WeightedLocal

theorem measurable_coldForcing {F c : ℝ × JetPrototype.Phase → ℝ}
    (hFm : Measurable F) (hcm : Measurable c) (q b L : ℝ) : Measurable (coldForcing q b L F c) :=
  (HotRepresentative.measurable_coldSource (GaussianLocal.measurable_state hFm)
    (GaussianLocal.measurable_state hcm) q b L).comp (by fun_prop)

end BoltzmannNonuniqueness.WeightedLocal

end

end

section

/-! # Weighted collision representatives respect equality almost everywhere -/

noncomputable section

open MeasureTheory

namespace BoltzmannNonuniqueness.HotRepresentative

variable {X : Type*} [MeasurableSpace X]

theorem density_congr (μ : Measure X) {f g : X × Velocity → ℝ}
    (hfg : f =ᵐ[μ.prod volume] g) (q : ℝ) : density q f =ᵐ[μ.prod volume] density q g := by
  filter_upwards [hfg] with p hp
  unfold density
  rw [hp]

theorem gain_congr (μ : Measure X) [SFinite μ] {f g : X × Velocity → ℝ}
    (hfg : f =ᵐ[μ.prod volume] g) (q b : ℝ) : gain q b f =ᵐ[μ.prod volume] gain q b g := by
  have hh := KineticCollisionNullSets.gain_congr μ (density_congr μ hfg q) b
  filter_upwards [hh] with p hp
  unfold gain
  split_ifs <;> simp only [hp]

theorem frequency_congr (μ : Measure X) [SFinite μ] {f g : X × Velocity → ℝ}
    (hfg : f =ᵐ[μ.prod volume] g) (q b : ℝ) : frequency q b f =ᵐ[μ.prod volume] frequency q b g :=
  KineticCollisionNullSets.frequency_congr μ (density_congr μ hfg q) b

theorem source_congr (μ : Measure X) [SFinite μ] {f g : X × Velocity → ℝ}
    (hfg : f =ᵐ[μ.prod volume] g) (q b L : ℝ) : source q b L f =ᵐ[μ.prod volume] source q b L g := by
  filter_upwards [gain_congr μ hfg q b,frequency_congr μ hfg q b,hfg] with p hg hν hp
  unfold source
  rw [hg,hν,hp]

end BoltzmannNonuniqueness.HotRepresentative

end

end

section

/-! # The collision source only depends on its current time slice -/

noncomputable section

namespace BoltzmannNonuniqueness.WeightedLocal

theorem forcing_eq_of_slice {F G : ℝ × JetPrototype.Phase → ℝ} {s t : ℝ}
    (h : ∀ p, F (s,p) = G (t,p)) (q b L : ℝ) (p : JetPrototype.Phase) :
    forcing q b L F (s,p) = forcing q b L G (t,p) := by
  have he : timeSlice F s = timeSlice G t := funext (fun u => h u.2)
  exact congrArg (fun H => forcing q b L H (0,p)) he

theorem forcing_paste_left {s t : ℝ} (ht : t ≤ s) (F G : ℝ × JetPrototype.Phase → ℝ)
    (q b L : ℝ) (p : JetPrototype.Phase) :
    forcing q b L (paste s F G) (t,p) = forcing q b L F (t,p) :=
  forcing_eq_of_slice (fun _ => by simp only [paste,ite_eq_left ht]) q b L p

theorem forcing_paste_right {s t : ℝ} (ht : s < t) (F G : ℝ × JetPrototype.Phase → ℝ)
    (q b L : ℝ) (p : JetPrototype.Phase) :
    forcing q b L (paste s F G) (t,p) = forcing q b L G (t-s,p) :=
  forcing_eq_of_slice (fun _ => by simp only [paste,ite_eq_right (not_le.mpr ht)]) q b L p

end BoltzmannNonuniqueness.WeightedLocal

end

end

section

/-! # Spatial covariance of the constructed weighted cold solutions -/

noncomputable section

open MeasureTheory
open BoltzmannNonuniqueness.JetPrototype

namespace BoltzmannNonuniqueness.WeightedTranslation

theorem measurable_shift (y : Space) : Measurable (shift y) := by
  unfold shift
  fun_prop

theorem measurable_pull {f : ℝ × JetPrototype.Phase → ℝ} (hf : Measurable f) (y : Space) :
    Measurable (pull y f) := hf.comp (measurable_fst.prodMk ((measurable_shift y).comp measurable_snd))

theorem shift_flight (y : Space) (t : ℝ) (p : JetPrototype.Phase) :
    shift y (JetBarrier.flight t p) = JetBarrier.flight t (shift y p) := by
  apply Prod.ext
  · apply Prod.ext <;> dsimp [shift,JetBarrier.flight] <;> abel
  · rfl

theorem forcing_pull (q b L : ℝ) (y : Space) (f : ℝ × JetPrototype.Phase → ℝ) :
    WeightedLocal.forcing q b L (pull y f) = pull y (WeightedLocal.forcing q b L f) := rfl

theorem value_pull (T L : ℝ) (y : Space) (f₀ : JetPrototype.Phase → ℝ)
    (g : ℝ × JetPrototype.Phase → ℝ) :
    PositiveIntegral.value T L JetBarrier.flight (fun p => f₀ (shift y p)) (pull y g) =
      pull y (PositiveIntegral.value T L JetBarrier.flight f₀ g) := by
  funext z
  simp only [PositiveIntegral.value,pull,shift_flight]

theorem fixed_point_pull {q b L T : ℝ} {f₀ : JetPrototype.Phase → ℝ}
    {F : ℝ × JetPrototype.Phase → ℝ}
    (hF : ∀ z, F z = PositiveIntegral.value T L JetBarrier.flight f₀ (WeightedLocal.forcing q b L F) z)
    (y : Space) (z : ℝ × JetPrototype.Phase) :
    pull y F z = PositiveIntegral.value T L JetBarrier.flight
      (fun p => f₀ (shift y p)) (WeightedLocal.forcing q b L (pull y F)) z := by
  rw [forcing_pull,value_pull]
  exact hF _

end BoltzmannNonuniqueness.WeightedTranslation

end

end

end OAI
end

section
-- module Solutions.OAIQ080_BZ.Boltzmann_Branching_WeightedHotRegularity
attribute [-instance] _root_.OAI.BoltzmannNonuniqueness.ChartKernel.offAxis_sFinite _root_.OAI.BoltzmannNonuniqueness.EuclideanFlight.sourcePullback_finite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.characteristicGainKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.hotKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.mixedKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.retainedKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.copyColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.mainCoreKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.selectedColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCoreSheet.dilatedColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCoreSheet.kineticColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.PeriodicApproximation.fiberMeasure_finite _root_.OAI.BoltzmannNonuniqueness.PositiveIteration.awayOriginKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.PositiveIteration.nearOriginKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamNormalCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamNormalRetainedKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.dampedCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.densityScaledCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalBeamKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalCollision_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalPhysicalEvent_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalWindowEvent_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.physicalEventMeasure_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.scaledBeamNormalKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.WeakTime.phaseEndpointKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.WeakTime.phaseIncrement_finite _root_.OAI.BoltzmannNonuniqueness.WeakTime.phaseSeed_sFinite _root_.OAI.BoltzmannNonuniqueness.WeakTime.residenceKernel_sFinite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

/-! # Domination of finite sums of cold sources by the total source -/

noncomputable section

open MeasureTheory

namespace BoltzmannNonuniqueness.HotRepresentative

variable {X I : Type*} [MeasurableSpace X]

theorem finite_sum_coldSource_le {q b L R : ℝ} (hq : q < 2) (hb : 0 ≤ b)
    (hL : R*CutoffLipschitz.frequencyConstant q b ≤ L) (s : Finset I)
    {c : I → X × Velocity → ℝ} {F : X × Velocity → ℝ}
    (hcm : ∀ i ∈ s, Measurable (c i)) (hFm : Measurable F)
    (hc : ∀ i ∈ s, ∀ p, 0 ≤ c i p ∧ c i p ≤ R) (hF : ∀ p, 0 ≤ F p ∧ F p ≤ R)
    (hSum : ∀ p, ∑ i ∈ s, c i p ≤ F p) (p : X × Velocity) :
    ∑ i ∈ s, coldSource q b L F (c i) p ≤ source q b L F p := by
  have hν : frequency q b F p ≤ L := (frequency_bound hq hb hFm hF p).trans hL
  unfold coldSource source
  rw [Finset.sum_add_distrib,← Finset.mul_sum]
  exact add_le_add (finite_sum_gain_le s hcm hFm hc hF hSum b p)
    (mul_le_mul_of_nonneg_left (hSum p) (sub_nonneg.mpr hν))

end BoltzmannNonuniqueness.HotRepresentative

end

end

end OAI
end

section
-- module Solutions.OAIQ080_BZ.Boltzmann_Branching_HotCollisionDecomposition
attribute [-instance] _root_.OAI.BoltzmannNonuniqueness.ChartKernel.offAxis_sFinite _root_.OAI.BoltzmannNonuniqueness.EuclideanFlight.sourcePullback_finite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.characteristicGainKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.hotKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.mixedKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.retainedKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.coldCylinderVolume_finite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.copyColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.mainCoreKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.selectedColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCoreSheet.dilatedColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCoreSheet.kineticColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.PeriodicApproximation.fiberMeasure_finite _root_.OAI.BoltzmannNonuniqueness.PositiveIteration.awayOriginKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.PositiveIteration.nearOriginKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamNormalCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamNormalRetainedKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.dampedCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.densityScaledCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalBeamKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalCollision_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalPhysicalEvent_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalWindowEvent_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.physicalEventMeasure_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.scaledBeamNormalKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.WeakTime.phaseEndpointKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.WeakTime.phaseIncrement_finite _root_.OAI.BoltzmannNonuniqueness.WeakTime.phaseSeed_sFinite _root_.OAI.BoltzmannNonuniqueness.WeakTime.residenceKernel_sFinite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

/-! # Replacing only the hot remainder by an essential-norm representative -/

noncomputable section

open MeasureTheory MeasureTheory.Measure

namespace BoltzmannNonuniqueness.HotCanonical

theorem state_congr {F G : ℝ × JetPrototype.Phase → ℝ}
    (hFG : F =ᵐ[(volume : Measure ℝ).prod FlightMeasure.phaseVolume] G) :
    GaussianLocal.state F =ᵐ[((volume : Measure ℝ).prod JetPrototype.spaceVolume).prod volume]
      GaussianLocal.state G :=
  (measurePreserving_prodAssoc (volume : Measure ℝ) JetPrototype.spaceVolume
    (volume : Measure Velocity)).quasiMeasurePreserving.ae_eq_comp hFG

end BoltzmannNonuniqueness.HotCanonical

namespace BoltzmannNonuniqueness.HotRepresentative

variable {X : Type*} [MeasurableSpace X]

theorem coldSource_congr_total (μ : Measure X) [SFinite μ]
    {F G : X × Velocity → ℝ} (hFG : F =ᵐ[μ.prod volume] G)
    (q b L : ℝ) (c : X × Velocity → ℝ) : coldSource q b L F c =ᵐ[μ.prod volume] coldSource q b L G c := by
  filter_upwards [frequency_congr μ hFG q b] with p hp
  unfold coldSource
  rw [hp]

end BoltzmannNonuniqueness.HotRepresentative

end

end

end OAI
end

section
-- module Solutions.OAIQ080_BZ.Boltzmann_Branching_WeightedNetLoss
attribute [-instance] _root_.OAI.BoltzmannNonuniqueness.ChartKernel.offAxis_sFinite _root_.OAI.BoltzmannNonuniqueness.EuclideanFlight.sourcePullback_finite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.characteristicGainKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.hotKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.mixedKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.retainedKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.coldCylinderVolume_finite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.copyColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.mainCoreKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.selectedColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCoreSheet.dilatedColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCoreSheet.kineticColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.PeriodicApproximation.fiberMeasure_finite _root_.OAI.BoltzmannNonuniqueness.PositiveIteration.awayOriginKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.PositiveIteration.nearOriginKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamNormalCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamNormalRetainedKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.dampedCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.densityScaledCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalBeamKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalCollision_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalPhysicalEvent_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalWindowEvent_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.physicalEventMeasure_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.scaledBeamNormalKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.WeakTime.phaseEndpointKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.WeakTime.phaseIncrement_finite _root_.OAI.BoltzmannNonuniqueness.WeakTime.phaseSeed_sFinite _root_.OAI.BoltzmannNonuniqueness.WeakTime.residenceKernel_sFinite
attribute [-simp] _root_.OAI.BoltzmannNonuniqueness.EuclideanFlight.phaseEquiv_snd _root_.OAI.BoltzmannNonuniqueness.timeTranslation_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

/-! # Almost-everywhere invariance of the colored forcing along spacetime -/

noncomputable section

open MeasureTheory MeasureTheory.Measure

namespace BoltzmannNonuniqueness.WeightedLocal

private theorem unstate_congr {f g : (ℝ × JetPrototype.Space) × Velocity → ℝ}
    (hfg : f =ᵐ[((volume : Measure ℝ).prod JetPrototype.spaceVolume).prod volume] g) :
    (fun u : ℝ × JetPrototype.Phase => f ((u.1,u.2.1),u.2.2)) =ᵐ[spacetimeVolume]
      (fun u : ℝ × JetPrototype.Phase => g ((u.1,u.2.1),u.2.2)) :=
  (MeasurePreserving.symm MeasurableEquiv.prodAssoc
    (measurePreserving_prodAssoc (volume : Measure ℝ) JetPrototype.spaceVolume
      (volume : Measure Velocity))).quasiMeasurePreserving.ae_eq_comp hfg

theorem forcing_congr {F G : ℝ × JetPrototype.Phase → ℝ}
    (hFG : F =ᵐ[spacetimeVolume] G) (q b L : ℝ) :
    forcing q b L F =ᵐ[spacetimeVolume] forcing q b L G :=
  unstate_congr (HotRepresentative.source_congr ((volume : Measure ℝ).prod JetPrototype.spaceVolume)
    (HotCanonical.state_congr hFG) q b L)

theorem coldForcing_congr_total {F G : ℝ × JetPrototype.Phase → ℝ}
    (hFG : F =ᵐ[spacetimeVolume] G) (q b L : ℝ) (c : ℝ × JetPrototype.Phase → ℝ) :
    coldForcing q b L F c =ᵐ[spacetimeVolume] coldForcing q b L G c :=
  unstate_congr (HotRepresentative.coldSource_congr_total
    ((volume : Measure ℝ).prod JetPrototype.spaceVolume) (HotCanonical.state_congr hFG) q b L
    (GaussianLocal.state c))

end BoltzmannNonuniqueness.WeightedLocal

end

end

section

/-! # Mild equations stable under changing spatial representatives -/

noncomputable section

open MeasureTheory MeasureTheory.Measure Set

namespace BoltzmannNonuniqueness.WeightedLocal

theorem mildAE_of_pointwise {q b L T : ℝ} {f₀ : JetPrototype.Phase → ℝ}
    {F : ℝ × JetPrototype.Phase → ℝ}
    (hF : ∀ u, F u = PositiveIntegral.value T L JetBarrier.flight f₀ (forcing q b L F) u) :
    MildAE q b L T f₀ F := fun t _ => ae_of_all _ (fun p => hF (t,p))

theorem slice_congr_spacetime {F G : ℝ × JetPrototype.Phase → ℝ}
    (hFm : Measurable F) (hGm : Measurable G)
    (hFG : ∀ t, (fun p => F (t,p)) =ᵐ[FlightMeasure.phaseVolume] (fun p => G (t,p))) :
    F =ᵐ[spacetimeVolume] G :=
  (ae_prod_iff_ae_ae (measurableSet_eq_fun hFm hGm)).mpr (ae_of_all _ hFG)

end BoltzmannNonuniqueness.WeightedLocal

end

end

section

/-! # Cold-source equality and finite-family domination almost everywhere -/

noncomputable section

open MeasureTheory MeasureTheory.Measure

namespace BoltzmannNonuniqueness.WeightedLocal

theorem coldForcing_congr_cold {c d : ℝ × JetPrototype.Phase → ℝ}
    (hcd : c =ᵐ[spacetimeVolume] d) (q b L : ℝ) (F : ℝ × JetPrototype.Phase → ℝ) :
    coldForcing q b L F c =ᵐ[spacetimeVolume] coldForcing q b L F d := by
  have hs := HotCanonical.state_congr hcd
  have hg := HotRepresentative.gain_congr ((volume : Measure ℝ).prod JetPrototype.spaceVolume) hs q b
  have he : HotRepresentative.coldSource q b L (GaussianLocal.state F) (GaussianLocal.state c) =ᵐ[
      ((volume : Measure ℝ).prod JetPrototype.spaceVolume).prod volume]
      HotRepresentative.coldSource q b L (GaussianLocal.state F) (GaussianLocal.state d) := by
    filter_upwards [hs,hg] with u hu hgu
    unfold HotRepresentative.coldSource
    rw [hu,hgu]
  exact (MeasurePreserving.symm MeasurableEquiv.prodAssoc
    (measurePreserving_prodAssoc (volume : Measure ℝ) JetPrototype.spaceVolume
      (volume : Measure Velocity))).quasiMeasurePreserving.ae_eq_comp he

theorem finite_coldForcing_le_ae {I : Type*} [Countable I] {q b L R : ℝ}
    (hq : q < 2) (hb : 0 ≤ b) (hR : 0 ≤ R)
    (hloss : R*CutoffLipschitz.frequencyConstant q b ≤ L) (s : Finset I)
    {F : ℝ × JetPrototype.Phase → ℝ} {c : I → ℝ × JetPrototype.Phase → ℝ}
    (hFm : Measurable F) (hcm : ∀ i ∈ s, Measurable (c i))
    (hF : ∀ u, 0 ≤ F u ∧ F u ≤ R) (hc : ∀ i ∈ s, ∀ u, 0 ≤ c i u ∧ c i u ≤ R)
    (hSum : ∀ᵐ u ∂spacetimeVolume, ∑ i ∈ s, c i u ≤ F u) :
    ∀ᵐ u ∂spacetimeVolume, ∑ i ∈ s, coldForcing q b L F (c i) u ≤ forcing q b L F u := by
  classical
  let d (i : I) (u : ℝ × JetPrototype.Phase) := if (∑ j ∈ s, c j u) ≤ F u then c i u else 0
  have hm : MeasurableSet {u : ℝ × JetPrototype.Phase | (∑ j ∈ s, c j u) ≤ F u} :=
    measurableSet_le (Finset.measurable_sum s hcm) hFm
  have hdm (i) (hi : i ∈ s) : Measurable (d i) := (hcm i hi).ite hm measurable_const
  have hdb (i) (hi : i ∈ s) (u) : 0 ≤ d i u ∧ d i u ≤ R := by
    dsimp [d]
    split_ifs
    · exact hc i hi u
    · exact ⟨le_rfl,hR⟩
  have hds (u) : (∑ i ∈ s, d i u) ≤ F u := by
    by_cases hu : (∑ i ∈ s, c i u) ≤ F u
    · simpa only [d,ite_eq_left hu] using hu
    · simpa only [d,ite_eq_right hu,Finset.sum_const_zero] using (hF u).1
  have hbound (u) : (∑ i ∈ s, coldForcing q b L F (d i) u) ≤ forcing q b L F u :=
    HotRepresentative.finite_sum_coldSource_le hq hb hloss s
      (fun i hi => GaussianLocal.measurable_state (hdm i hi)) (GaussianLocal.measurable_state hFm)
      (fun i hi p => hdb i hi (p.1.1,(p.1.2,p.2)))
      (fun p => hF (p.1.1,(p.1.2,p.2))) (fun p => hds (p.1.1,(p.1.2,p.2))) _
  have he (i : I) : d i =ᵐ[spacetimeVolume] c i := hSum.mono (fun u hu => ite_eq_left hu)
  have hce : ∀ᵐ u ∂spacetimeVolume, ∀ i, coldForcing q b L F (d i) u = coldForcing q b L F (c i) u :=
    ae_all_iff.mpr (fun i => coldForcing_congr_cold (he i) q b L F)
  filter_upwards [hce] with u hu
  have h := hbound u
  simpa only [hu] using h

end BoltzmannNonuniqueness.WeightedLocal

end

end

section

/-! # Pasting positive local solutions across an a.e. time slice -/

noncomputable section

open MeasureTheory Set

namespace BoltzmannNonuniqueness.WeightedLocal

theorem measurable_paste {s : ℝ} {F G : ℝ × JetPrototype.Phase → ℝ}
    (hF : Measurable F) (hG : Measurable G) : Measurable (paste s F G) :=
  hF.ite (measurableSet_le measurable_fst measurable_const)
    (hG.comp ((measurable_fst.sub measurable_const).prodMk measurable_snd))

theorem paste_bounds {s R : ℝ} {F G : ℝ × JetPrototype.Phase → ℝ}
    (hF : ∀ u, 0 ≤ F u ∧ F u ≤ R) (hG : ∀ u, 0 ≤ G u ∧ G u ≤ R)
    (u : ℝ × JetPrototype.Phase) : 0 ≤ paste s F G u ∧ paste s F G u ≤ R := by
  unfold paste
  split_ifs
  · exact hF u
  · exact hG _

theorem paste_pull (s : ℝ) (F G : ℝ × JetPrototype.Phase → ℝ)
    (y : JetPrototype.Space) :
    WeightedTranslation.pull y (paste s F G) =
      paste s (WeightedTranslation.pull y F) (WeightedTranslation.pull y G) := rfl

theorem paste_mildAE {q b L s U S : ℝ} (hs : 0 ≤ s) (hU : 0 ≤ U) (hL : 0 ≤ L)
    {f₀ g₀ : JetPrototype.Phase → ℝ} {F G : ℝ × JetPrototype.Phase → ℝ}
    (hFm : Measurable F) (hGm : Measurable G)
    (hsource : ∀ u, |forcing q b L (paste s F G) u| ≤ S)
    (hF : MildAE q b L s f₀ F) (hG : MildAE q b L U g₀ G)
    (hinit : g₀ =ᵐ[FlightMeasure.phaseVolume] (fun p => F (s,p))) :
    MildAE q b L (s+U) f₀ (paste s F G) := by
  have hprefix (t : ℝ) (ht : t ∈ Icc 0 s) (p : JetPrototype.Phase) :
      PositiveIntegral.value (s+U) L JetBarrier.flight f₀
          (forcing q b L (paste s F G)) (t,p) =
        PositiveIntegral.value s L JetBarrier.flight f₀ (forcing q b L F) (t,p) := by
    apply PositiveIntegral.value_eq_at_time ⟨ht.1,by linarith [ht.2]⟩ ht.2
    intro r hr p
    exact forcing_paste_left (hr.2.trans ht.2) F G q b L p
  intro t ht
  by_cases hts : t ≤ s
  · filter_upwards [hF t ⟨ht.1,hts⟩] with p hp
    rw [paste,ite_eq_left hts,hprefix t ⟨ht.1,hts⟩ p]
    exact hp
  · have hst : s < t := lt_of_not_ge hts
    have htu : t-s ∈ Icc 0 U := ⟨by linarith,by linarith [ht.2]⟩
    have hi := (FlightMeasure.flight_measurePreserving (s-t)).quasiMeasurePreserving.ae
      ((hF s ⟨hs,le_rfl⟩).symm.trans hinit.symm)
    filter_upwards [hG (t-s) htu,hi] with p hp hip
    have hr := PositiveIntegral.restart (add_nonneg hs hU) hL hs hst.le ht.2 f₀
      (measurable_forcing (measurable_paste hFm hGm) q b L) hsource p
    rw [hprefix s ⟨hs,le_rfl⟩,hip] at hr
    have hrest : (∫ r in s..t, Real.exp (-L*(t-r))*
        forcing q b L (paste s F G) (r,JetBarrier.flight (r-t) p)) =
        ∫ r in s..t, Real.exp (-L*(t-r))*
          forcing q b L G (r-s,JetBarrier.flight (r-t) p) := by
      apply intervalIntegral.integral_congr_ae
      apply ae_of_all
      intro r hr
      rw [uIoc_of_le hst.le] at hr
      rw [forcing_paste_right hr.1]
    rw [hrest,← PositiveIntegral.shifted_value htu] at hr
    rw [paste,ite_eq_right hts,hr]
    exact hp

end BoltzmannNonuniqueness.WeightedLocal

end

end

section

/-! # The cutoff source is Lipschitz for essentially close representatives -/

noncomputable section

open MeasureTheory

namespace BoltzmannNonuniqueness.WeightedLocal

theorem forcing_difference_ae {q b L R D : ℝ} (hq : q < 2) (hb : 0 ≤ b)
    (hL : 0 ≤ L) (hR : 0 ≤ R) (hD : 0 ≤ D)
    {F G : ℝ × JetPrototype.Phase → ℝ} (hFm : Measurable F) (hGm : Measurable G)
    (hF : ∀ u, 0 ≤ F u ∧ F u ≤ R) (hG : ∀ u, 0 ≤ G u ∧ G u ≤ R)
    (hFG : ∀ᵐ u ∂spacetimeVolume, |F u-G u| ≤ D) :
    ∀ᵐ u ∂spacetimeVolume, |forcing q b L F u-forcing q b L G u| ≤
      (2*R*(HotApplication.realBound q+CutoffLipschitz.frequencyConstant q b)+L)*D := by
  let H (u : ℝ × JetPrototype.Phase) := max (G u-D) (min (F u) (G u+D))
  have hHm : Measurable H := (hGm.sub_const D).max (hFm.min (hGm.add_const D))
  have hHb (u) : 0 ≤ H u ∧ H u ≤ R := by
    dsimp [H]
    constructor
    · exact (le_min (hF u).1 (add_nonneg (hG u).1 hD)).trans (le_max_right _ _)
    · exact max_le (by linarith [(hG u).2]) ((min_le_left _ _).trans (hF u).2)
  have hHD (u) : |H u-G u| ≤ D := by
    rw [abs_sub_le_iff]
    dsimp [H]
    have hleft : G u-D ≤ max (G u-D) (min (F u) (G u+D)) := le_max_left _ _
    have hright : max (G u-D) (min (F u) (G u+D)) ≤ G u+D :=
      max_le (by linarith) (min_le_right _ _)
    constructor <;> linarith
  have hHF : H =ᵐ[spacetimeVolume] F := by
    filter_upwards [hFG] with u hu
    obtain ⟨h₁,h₂⟩ := abs_sub_le_iff.mp hu
    dsimp [H]
    rw [min_eq_left (by linarith),max_eq_right (by linarith)]
  have hsrc := forcing_congr hHF q b L
  filter_upwards [hsrc] with u hu
  rw [← hu]
  exact HotRepresentative.source_difference hq hb hL hR hD
    (GaussianLocal.measurable_state hHm) (GaussianLocal.measurable_state hGm)
    (fun p => hHb (p.1.1,(p.1.2,p.2))) (fun p => hG (p.1.1,(p.1.2,p.2)))
    (fun p => hHD (p.1.1,(p.1.2,p.2))) ((u.1,u.2.1),u.2.2)

end BoltzmannNonuniqueness.WeightedLocal

end

end

end OAI
end

section
-- module Solutions.OAIQ080_BZ.Boltzmann_Branching_ClippedColdFiniteLimit
attribute [-instance] _root_.OAI.BoltzmannNonuniqueness.ChartKernel.offAxis_sFinite _root_.OAI.BoltzmannNonuniqueness.EuclideanFlight.sourcePullback_finite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.characteristicGainKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.hotKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.mixedKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.retainedKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.coldCylinderVolume_finite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.copyColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.mainCoreKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.selectedColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCoreSheet.dilatedColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCoreSheet.kineticColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.PeriodicApproximation.fiberMeasure_finite _root_.OAI.BoltzmannNonuniqueness.PositiveIteration.awayOriginKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.PositiveIteration.nearOriginKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamNormalCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamNormalRetainedKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.dampedCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.densityScaledCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalBeamKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalCollision_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalPhysicalEvent_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalWindowEvent_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.physicalEventMeasure_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.scaledBeamNormalKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.WeakTime.phaseEndpointKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.WeakTime.phaseIncrement_finite _root_.OAI.BoltzmannNonuniqueness.WeakTime.phaseSeed_sFinite _root_.OAI.BoltzmannNonuniqueness.WeakTime.residenceKernel_sFinite
attribute [-simp] _root_.OAI.BoltzmannNonuniqueness.EuclideanFlight.phaseEquiv_snd _root_.OAI.BoltzmannNonuniqueness.timeTranslation_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

/-! # Bounded positive cold iteration without a pointwise total fixed point -/

noncomputable section

open MeasureTheory

namespace BoltzmannNonuniqueness.WeightedLocal

theorem clippedCold_properties {q b L T R : ℝ} (hq : q < 2) (hb : 0 ≤ b)
    (hL : 0 ≤ L) (hT : 0 ≤ T) (hR : 0 ≤ R)
    (hloss : R*CutoffLipschitz.frequencyConstant q b ≤ L)
    {F : ℝ × JetPrototype.Phase → ℝ} {c₀ : JetPrototype.Phase → ℝ}
    (hFm : Measurable F) (hc₀m : Measurable c₀)
    (hF : ∀ u, 0 ≤ F u ∧ F u ≤ R) (hc₀ : ∀ p, 0 ≤ c₀ p ∧ c₀ p ≤ R)
    (n : ℕ) : Measurable (clippedColdPicard q b L T F c₀ n) ∧
      ∀ u, 0 ≤ clippedColdPicard q b L T F c₀ n u ∧ clippedColdPicard q b L T F c₀ n u ≤ F u := by
  let S := HotApplication.realBound q*R^2+L*R
  have hS : 0 ≤ S := by
    have h := (HotApplication.realBound_pos q).le
    dsimp [S]
    positivity
  induction n with
  | zero => exact ⟨measurable_const,fun u => ⟨le_rfl,(hF u).1⟩⟩
  | succ n ih =>
    have hcb (u) : 0 ≤ clippedColdPicard q b L T F c₀ n u ∧
        clippedColdPicard q b L T F c₀ n u ≤ R := ⟨(ih.2 u).1,(ih.2 u).2.trans (hF u).2⟩
    have hgm := measurable_coldForcing hFm ih.1 q b L
    have hgb (u) : 0 ≤ coldForcing q b L F (clippedColdPicard q b L T F c₀ n) u ∧
        coldForcing q b L F (clippedColdPicard q b L T F c₀ n) u ≤ S :=
      HotRepresentative.coldSource_bounds hq hb hR hloss (GaussianLocal.measurable_state hFm)
        (GaussianLocal.measurable_state ih.1)
        (fun p => hF (p.1.1,(p.1.2,p.2))) (fun p => hcb (p.1.1,(p.1.2,p.2))) _
    refine ⟨hFm.min (PositiveIntegral.measurable_value hT GaussianLocal.measurable_flight hc₀m hgm),?_⟩
    intro u
    exact ⟨le_min (hF u).1
      (PositiveIntegral.value_bounds hT hL hR hS JetBarrier.flight hc₀ hgb u).1,min_le_left _ _⟩

theorem clippedCold_monotone {q b L T R : ℝ} (hq : q < 2) (hb : 0 ≤ b)
    (hL : 0 ≤ L) (hT : 0 ≤ T) (hR : 0 ≤ R)
    (hloss : R*CutoffLipschitz.frequencyConstant q b ≤ L)
    {F : ℝ × JetPrototype.Phase → ℝ} {c₀ : JetPrototype.Phase → ℝ}
    (hFm : Measurable F) (hc₀m : Measurable c₀)
    (hF : ∀ u, 0 ≤ F u ∧ F u ≤ R) (hc₀ : ∀ p, 0 ≤ c₀ p ∧ c₀ p ≤ R)
    (u : ℝ × JetPrototype.Phase) : Monotone (fun n => clippedColdPicard q b L T F c₀ n u) := by
  have hp := clippedCold_properties hq hb hL hT hR hloss hFm hc₀m hF hc₀
  have hcb (n) (u) : 0 ≤ clippedColdPicard q b L T F c₀ n u ∧
      clippedColdPicard q b L T F c₀ n u ≤ R :=
    ⟨((hp n).2 u).1,((hp n).2 u).2.trans (hF u).2⟩
  have hgb (n) (u) : 0 ≤ coldForcing q b L F (clippedColdPicard q b L T F c₀ n) u ∧
      coldForcing q b L F (clippedColdPicard q b L T F c₀ n) u ≤ HotApplication.realBound q*R^2+L*R :=
    HotRepresentative.coldSource_bounds hq hb hR hloss (GaussianLocal.measurable_state hFm)
      (GaussianLocal.measurable_state (hp n).1)
      (fun p => hF (p.1.1,(p.1.2,p.2))) (fun p => hcb n (p.1.1,(p.1.2,p.2))) _
  have hstep : ∀ n u, clippedColdPicard q b L T F c₀ n u ≤ clippedColdPicard q b L T F c₀ (n+1) u := by
    intro n
    induction n with
    | zero => intro u; exact ((hp 1).2 u).1
    | succ n ih =>
      intro u
      apply min_le_min_left
      apply PositiveIntegral.value_mono hT hL GaussianLocal.measurable_flight (fun _ => le_rfl)
        (measurable_coldForcing hFm (hp n).1 q b L)
        (measurable_coldForcing hFm (hp (n+1)).1 q b L)
        (fun z => by rw [abs_of_nonneg (hgb n z).1]; exact (hgb n z).2)
        (fun z => by rw [abs_of_nonneg (hgb (n+1) z).1]; exact (hgb (n+1) z).2)
      intro p
      exact HotRepresentative.coldSource_mono hq hb hloss (GaussianLocal.measurable_state hFm)
        (GaussianLocal.measurable_state (hp n).1) (GaussianLocal.measurable_state (hp (n+1)).1)
        (fun p => hF (p.1.1,(p.1.2,p.2))) (fun p => (hcb n (p.1.1,(p.1.2,p.2))).1)
        (fun p => ih (p.1.1,(p.1.2,p.2))) (fun p => (hcb (n+1) (p.1.1,(p.1.2,p.2))).2) _
  exact monotone_nat_of_le_succ (fun n => hstep n u)

end BoltzmannNonuniqueness.WeightedLocal

end

end

section

/-! # The bounded monotone cold limit for a measurable total state -/

noncomputable section

open MeasureTheory Filter
open scoped Topology

namespace BoltzmannNonuniqueness.WeightedLocal

theorem clippedCold_solution {q b L T R : ℝ} (hq : q < 2) (hb : 0 ≤ b)
    (hL : 0 ≤ L) (hT : 0 ≤ T) (hR : 0 ≤ R)
    (hloss : R*CutoffLipschitz.frequencyConstant q b ≤ L)
    {F : ℝ × JetPrototype.Phase → ℝ} {c₀ : JetPrototype.Phase → ℝ}
    (hFm : Measurable F) (hc₀m : Measurable c₀)
    (hF : ∀ u, 0 ≤ F u ∧ F u ≤ R) (hc₀ : ∀ p, 0 ≤ c₀ p ∧ c₀ p ≤ R) :
    Measurable (clippedColdLimit q b L T F c₀) ∧
      (∀ u, 0 ≤ clippedColdLimit q b L T F c₀ u ∧ clippedColdLimit q b L T F c₀ u ≤ F u) ∧
      (∀ u, clippedColdLimit q b L T F c₀ u = min (F u)
        (PositiveIntegral.value T L JetBarrier.flight c₀
          (coldForcing q b L F (clippedColdLimit q b L T F c₀)) u)) ∧
      ∀ u, Tendsto (fun n => clippedColdPicard q b L T F c₀ n u) atTop
        (𝓝 (clippedColdLimit q b L T F c₀ u)) := by
  let c := clippedColdLimit q b L T F c₀
  let u := clippedColdPicard q b L T F c₀
  have hp := clippedCold_properties hq hb hL hT hR hloss hFm hc₀m hF hc₀
  have hcb (n) (z) : 0 ≤ u n z ∧ u n z ≤ R :=
    ⟨((hp n).2 z).1,((hp n).2 z).2.trans (hF z).2⟩
  have hgb (n) (z) : 0 ≤ coldForcing q b L F (u n) z ∧
      coldForcing q b L F (u n) z ≤ HotApplication.realBound q*R^2+L*R :=
    HotRepresentative.coldSource_bounds hq hb hR hloss (GaussianLocal.measurable_state hFm)
      (GaussianLocal.measurable_state (hp n).1)
      (fun p => hF (p.1.1,(p.1.2,p.2))) (fun p => hcb n (p.1.1,(p.1.2,p.2))) _
  have hmono (z) : Monotone (fun n => u n z) :=
    clippedCold_monotone hq hb hL hT hR hloss hFm hc₀m hF hc₀ z
  have hbdd (z) : BddAbove (Set.range (fun n => u n z)) :=
    ⟨F z,by rintro _ ⟨n,rfl⟩; exact ((hp n).2 z).2⟩
  have hlim (z) : Tendsto (fun n => u n z) atTop (𝓝 (c z)) :=
    tendsto_atTop_ciSup (hmono z) (hbdd z)
  have hcm : Measurable c := measurable_of_tendsto_metrizable (fun n => (hp n).1)
    (tendsto_pi_nhds.mpr hlim)
  have hbound (z) : 0 ≤ c z ∧ c z ≤ F z :=
    ⟨(le_ciSup (hbdd z) 0 : u 0 z ≤ c z),ciSup_le (fun n => ((hp n).2 z).2)⟩
  refine ⟨hcm,hbound,?_,hlim⟩
  intro z
  have hsource (p) : Tendsto (fun n => coldForcing q b L F (u n) p) atTop
      (𝓝 (coldForcing q b L F c p)) :=
    HotRepresentative.coldSource_tendsto hR b L (GaussianLocal.state F)
      (fun n => GaussianLocal.measurable_state (hp n).1)
      (fun n p => hcb n (p.1.1,(p.1.2,p.2)))
      (fun p => hlim (p.1.1,(p.1.2,p.2))) _
  have hv := PositiveIntegral.value_tendsto hT hL GaussianLocal.measurable_flight c₀
    (fun n => measurable_coldForcing hFm (hp n).1 q b L)
    (fun n p => by rw [abs_of_nonneg (hgb n p).1]; exact (hgb n p).2) hsource z
  have hnext : Tendsto (fun n => u (n+1) z) atTop (𝓝 (c z)) :=
    (hlim z).comp (tendsto_add_atTop_nat 1)
  exact tendsto_nhds_unique hnext (tendsto_const_nhds.min hv)

end BoltzmannNonuniqueness.WeightedLocal

end

end

section

/-! # Finite sums of clipped cold iterates stay below a mild total solution -/

noncomputable section

open MeasureTheory MeasureTheory.Measure

namespace BoltzmannNonuniqueness.WeightedLocal

theorem clippedCold_finite_picard {I : Type*} [Countable I] {q b L T R : ℝ}
    (hq : q < 2) (hb : 0 ≤ b) (hL : 0 ≤ L) (hT : 0 ≤ T) (hR : 0 ≤ R)
    (hloss : R*CutoffLipschitz.frequencyConstant q b ≤ L) (s : Finset I)
    {F : ℝ × JetPrototype.Phase → ℝ} {F₀ : JetPrototype.Phase → ℝ}
    {c₀ : I → JetPrototype.Phase → ℝ}
    (hFm : Measurable F) (hc₀m : ∀ i, Measurable (c₀ i))
    (hF : ∀ u, 0 ≤ F u ∧ F u ≤ R) (hc₀ : ∀ i p, 0 ≤ c₀ i p ∧ c₀ i p ≤ R)
    (hSum₀ : ∀ p, ∑ i ∈ s, c₀ i p ≤ F₀ p)
    (hFeq : ∀ t, (fun p => F (t,p)) =ᵐ[FlightMeasure.phaseVolume]
      (fun p => PositiveIntegral.value T L JetBarrier.flight F₀ (forcing q b L F) (t,p))) :
    ∀ n t, ∀ᵐ p ∂FlightMeasure.phaseVolume, ∑ i ∈ s, clippedColdPicard q b L T F (c₀ i) n (t,p) ≤ F (t,p) := by
  let S := HotApplication.realBound q*R^2+L*R
  have hS : 0 ≤ S := by
    have hg := (HotApplication.realBound_pos q).le
    dsimp [S]
    positivity
  have hp (i) := clippedCold_properties hq hb hL hT hR hloss hFm (hc₀m i) hF (hc₀ i)
  have hcb (i n u) : 0 ≤ clippedColdPicard q b L T F (c₀ i) n u ∧
      clippedColdPicard q b L T F (c₀ i) n u ≤ R :=
    ⟨((hp i n).2 u).1,((hp i n).2 u).2.trans (hF u).2⟩
  have hgb (i n u) : 0 ≤ coldForcing q b L F (clippedColdPicard q b L T F (c₀ i) n) u ∧
      coldForcing q b L F (clippedColdPicard q b L T F (c₀ i) n) u ≤ S :=
    HotRepresentative.coldSource_bounds hq hb hR hloss (GaussianLocal.measurable_state hFm)
      (GaussianLocal.measurable_state (hp i n).1)
      (fun p => hF (p.1.1,(p.1.2,p.2))) (fun p => hcb i n (p.1.1,(p.1.2,p.2))) _
  have hfb (u) : 0 ≤ forcing q b L F u ∧ forcing q b L F u ≤ S :=
    HotRepresentative.source_bounds hq hb hR hloss (GaussianLocal.measurable_state hFm)
      (fun p => hF (p.1.1,(p.1.2,p.2))) _
  intro n
  induction n with
  | zero =>
    intro t
    exact ae_of_all _ (fun p => by simpa only [clippedColdPicard,Finset.sum_const_zero] using (hF (t,p)).1)
  | succ n ih =>
    let g (i : I) := coldForcing q b L F (clippedColdPicard q b L T F (c₀ i) n)
    have hgm (i) : Measurable (g i) := measurable_coldForcing hFm (hp i n).1 q b L
    have hsum : ∀ᵐ u ∂spacetimeVolume, ∑ i ∈ s, clippedColdPicard q b L T F (c₀ i) n u ≤ F u :=
      (ae_prod_iff_ae_ae (measurableSet_le (Finset.measurable_sum s (fun i _ => (hp i n).1)) hFm)).mpr
        (ae_of_all _ ih)
    have hsource := finite_coldForcing_le_ae hq hb hR hloss s hFm (fun i _ => (hp i n).1)
      hF (fun i _ => hcb i n) hsum
    have hsumabs (u) : |∑ i ∈ s, g i u| ≤ (s.card+1 : ℕ)*S := by
      rw [abs_of_nonneg (Finset.sum_nonneg (fun i _ => (hgb i n u).1))]
      calc
        _ ≤ ∑ _i ∈ s, S := Finset.sum_le_sum (fun i _ => (hgb i n u).2)
        _ = (s.card : ℝ)*S := by simp
        _ ≤ (s.card+1 : ℕ)*S := mul_le_mul_of_nonneg_right (by norm_num) hS
    have hfabs (u) : |forcing q b L F u| ≤ (s.card+1 : ℕ)*S := by
      rw [abs_of_nonneg (hfb u).1]
      have hcard : (1:ℝ) ≤ (s.card+1 : ℕ) := by norm_num
      have hmul := mul_le_mul_of_nonneg_right hcard hS
      exact (hfb u).2.trans (by simpa only [one_mul] using hmul)
    intro t
    have hv := FlightMeasure.value_mono_ae hT hL (ae_of_all _ hSum₀) hsource
      (Finset.measurable_sum s (fun i _ => hgm i)) (measurable_forcing hFm q b L) hsumabs hfabs t
    filter_upwards [hv,hFeq t] with p hvp hfp
    have hsumvalue := PositiveIntegral.value_finsetSum hT hL GaussianLocal.measurable_flight s c₀ g
      (fun i _ => hgm i) (fun i _ u => by rw [abs_of_nonneg (hgb i n u).1]; exact (hgb i n u).2) (t,p)
    calc
      _ ≤ ∑ i ∈ s, PositiveIntegral.value T L JetBarrier.flight (c₀ i) (g i) (t,p) :=
        Finset.sum_le_sum (fun i _ => min_le_right _ _)
      _ = _ := hsumvalue
      _ ≤ _ := hvp
      _ = F (t,p) := hfp.symm

end BoltzmannNonuniqueness.WeightedLocal

end

end

section

/-! # The clipping is inactive almost everywhere for a mild total solution -/

noncomputable section

open MeasureTheory Set

namespace BoltzmannNonuniqueness.WeightedLocal

theorem clippedCold_mildAE {q b L T R : ℝ} (hq : q < 2) (hb : 0 ≤ b)
    (hL : 0 ≤ L) (hT : 0 ≤ T) (hR : 0 ≤ R)
    (hloss : R*CutoffLipschitz.frequencyConstant q b ≤ L)
    {F : ℝ × JetPrototype.Phase → ℝ} {F₀ c₀ : JetPrototype.Phase → ℝ}
    (hFm : Measurable F) (hc₀m : Measurable c₀)
    (hF : ∀ u, 0 ≤ F u ∧ F u ≤ R) (hc₀ : ∀ p, 0 ≤ c₀ p ∧ c₀ p ≤ R)
    (hcF₀ : ∀ p, c₀ p ≤ F₀ p) (hFeq : MildAE q b L T F₀ F) :
    ColdMildAE q b L T F c₀ (clippedColdLimit q b L T F c₀) := by
  let c := clippedColdLimit q b L T F c₀
  have hc := clippedCold_solution hq hb hL hT hR hloss hFm hc₀m hF hc₀
  have hcb (u) : 0 ≤ c u ∧ c u ≤ R := ⟨(hc.2.1 u).1,(hc.2.1 u).2.trans (hF u).2⟩
  have hgb (u : ℝ × JetPrototype.Phase) : 0 ≤ coldForcing q b L F c u ∧
      coldForcing q b L F c u ≤ HotApplication.realBound q*R^2+L*R :=
    HotRepresentative.coldSource_bounds hq hb hR hloss
    (GaussianLocal.measurable_state hFm) (GaussianLocal.measurable_state hc.1)
    (fun p => hF (p.1.1,(p.1.2,p.2))) (fun p => hcb (p.1.1,(p.1.2,p.2))) ((u.1,u.2.1),u.2.2)
  have hfb (u : ℝ × JetPrototype.Phase) : 0 ≤ forcing q b L F u ∧
      forcing q b L F u ≤ HotApplication.realBound q*R^2+L*R :=
    HotRepresentative.source_bounds hq hb hR hloss (GaussianLocal.measurable_state hFm)
    (fun p => hF (p.1.1,(p.1.2,p.2))) ((u.1,u.2.1),u.2.2)
  have horder (u) : coldForcing q b L F c u ≤ forcing q b L F u :=
    HotRepresentative.coldSource_mono hq hb hloss
      (GaussianLocal.measurable_state hFm) (GaussianLocal.measurable_state hc.1)
      (GaussianLocal.measurable_state hFm) (fun p => hF (p.1.1,(p.1.2,p.2)))
      (fun p => (hcb (p.1.1,(p.1.2,p.2))).1)
      (fun p => (hc.2.1 (p.1.1,(p.1.2,p.2))).2)
      (fun p => (hF (p.1.1,(p.1.2,p.2))).2) _
  have hvalue (u) := PositiveIntegral.value_mono hT hL GaussianLocal.measurable_flight hcF₀
    (measurable_coldForcing hFm hc.1 q b L) (measurable_forcing hFm q b L)
    (fun u => by rw [abs_of_nonneg (hgb u).1]; exact (hgb u).2)
    (fun u => by rw [abs_of_nonneg (hfb u).1]; exact (hfb u).2) horder u
  intro t ht
  filter_upwards [hFeq t ht] with p hp
  have hv := hvalue (t,p)
  change PositiveIntegral.value T L JetBarrier.flight c₀ (coldForcing q b L F c) (t,p) ≤ _ at hv
  rw [← hp] at hv
  rw [hc.2.2.1 (t,p),min_eq_right hv]

end BoltzmannNonuniqueness.WeightedLocal

end

end

section

/-! # Finite-family domination passes to the cold limits -/

noncomputable section

open MeasureTheory Filter
open scoped Topology

namespace BoltzmannNonuniqueness.WeightedLocal

theorem clippedCold_finite_limit {I : Type*} [Countable I] {q b L T R : ℝ}
    (hq : q < 2) (hb : 0 ≤ b) (hL : 0 ≤ L) (hT : 0 ≤ T) (hR : 0 ≤ R)
    (hloss : R*CutoffLipschitz.frequencyConstant q b ≤ L) (s : Finset I)
    {F : ℝ × JetPrototype.Phase → ℝ} {F₀ : JetPrototype.Phase → ℝ}
    {c₀ : I → JetPrototype.Phase → ℝ}
    (hFm : Measurable F) (hc₀m : ∀ i, Measurable (c₀ i))
    (hF : ∀ u, 0 ≤ F u ∧ F u ≤ R) (hc₀ : ∀ i p, 0 ≤ c₀ i p ∧ c₀ i p ≤ R)
    (hSum₀ : ∀ p, ∑ i ∈ s, c₀ i p ≤ F₀ p)
    (hFeq : ∀ t, (fun p => F (t,p)) =ᵐ[FlightMeasure.phaseVolume]
      (fun p => PositiveIntegral.value T L JetBarrier.flight F₀ (forcing q b L F) (t,p))) :
    ∀ t, ∀ᵐ p ∂FlightMeasure.phaseVolume,
      ∑ i ∈ s, clippedColdLimit q b L T F (c₀ i) (t,p) ≤ F (t,p) := by
  have hn := clippedCold_finite_picard hq hb hL hT hR hloss s hFm hc₀m hF hc₀ hSum₀ hFeq
  intro t
  have hall : ∀ᵐ p ∂FlightMeasure.phaseVolume, ∀ n,
      ∑ i ∈ s, clippedColdPicard q b L T F (c₀ i) n (t,p) ≤ F (t,p) :=
    ae_all_iff.mpr (fun n => hn n t)
  filter_upwards [hall] with p hp
  have hlim (i) := (clippedCold_solution hq hb hL hT hR hloss hFm (hc₀m i) hF (hc₀ i)).2.2.2 (t,p)
  exact le_of_tendsto (tendsto_finsetSum s (fun i _ => hlim i)) (Filter.Eventually.of_forall hp)

end BoltzmannNonuniqueness.WeightedLocal

end

end

end OAI
end

section
-- module Solutions.OAIQ080_BZ.Boltzmann_Approximation_ColoredSourceDifferenceAE
attribute [-instance] _root_.OAI.BoltzmannNonuniqueness.ChartKernel.offAxis_sFinite _root_.OAI.BoltzmannNonuniqueness.EuclideanFlight.sourcePullback_finite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.characteristicGainKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.hotKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.mixedKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.retainedKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.coldCylinderVolume_finite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.copyColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.mainCoreKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.selectedColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCoreSheet.dilatedColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCoreSheet.kineticColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.PeriodicApproximation.fiberMeasure_finite _root_.OAI.BoltzmannNonuniqueness.PositiveIteration.awayOriginKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.PositiveIteration.nearOriginKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamNormalCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamNormalRetainedKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.dampedCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.densityScaledCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalBeamKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalCollision_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalPhysicalEvent_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalWindowEvent_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.physicalEventMeasure_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.scaledBeamNormalKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.WeakTime.phaseEndpointKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.WeakTime.phaseIncrement_finite _root_.OAI.BoltzmannNonuniqueness.WeakTime.phaseSeed_sFinite _root_.OAI.BoltzmannNonuniqueness.WeakTime.residenceKernel_sFinite
attribute [-simp] _root_.OAI.BoltzmannNonuniqueness.EuclideanFlight.phaseEquiv_snd _root_.OAI.BoltzmannNonuniqueness.timeTranslation_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

/-! # Collision integrand differences for a finite family in the sum norm -/

noncomputable section

open MeasureTheory
open BoltzmannNonuniqueness.VelocityWeight

namespace BoltzmannNonuniqueness.HotRepresentative

theorem finite_integrand_abs_difference {X I : Type*} (s : Finset I) {q R E : ℝ}
    (hR : 0 ≤ R) (hE : 0 ≤ E) (c d : I → X × Velocity → ℝ)
    (hc : ∀ i ∈ s, ∀ p, 0 ≤ c i p ∧ c i p ≤ R)
    (hd : ∀ i ∈ s, ∀ p, 0 ≤ d i p ∧ d i p ≤ R)
    (hcd : ∀ p, (∑ i ∈ s, |c i p-d i p|) ≤ E)
    (b : ℝ) (x : X) (v : Velocity) (w : Velocity × Sphere) :
    (∑ i ∈ s, |CollisionCutoff.integrand b (fun u => density q (c i) (x,u)) v w-
      CollisionCutoff.integrand b (fun u => density q (d i) (x,u)) v w|) ≤
      (2*R*E)*GainOrder.integrand (H q) v w := by
  let a := scatterLeft v w.1 w.2
  let z := scatterRight v w.1 w.2
  let C := CollisionCutoff.kernel b v w.1 w.2*H q a*H q z
  have hC : 0 ≤ C := mul_nonneg (mul_nonneg (CollisionCutoff.kernel_nonneg _ _ _ _) (H_nonneg _ _)) (H_nonneg _ _)
  have he (i) : |CollisionCutoff.integrand b (fun u => density q (c i) (x,u)) v w-
      CollisionCutoff.integrand b (fun u => density q (d i) (x,u)) v w| =
      C* |c i (x,a)*c i (x,z)-d i (x,a)*d i (x,z)| := by
    rw [← abs_of_nonneg hC,← abs_mul]
    congr 1
    dsimp [CollisionCutoff.integrand,density,C,a,z]
    ring
  simp_rw [he]
  rw [← Finset.mul_sum]
  have hsum := ColoredAlgebra.sum_abs_product_difference_le s hR
    (fun i => c i (x,a)) (fun i => c i (x,z)) (fun i => d i (x,a)) (fun i => d i (x,z))
    (fun i hi => hc i hi _) (fun i hi => hd i hi _) (hcd _) (hcd _)
  apply (mul_le_mul_of_nonneg_left hsum hC).trans
  have hk : C ≤ GainOrder.integrand (H q) v w := by
    exact mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right (CollisionCutoff.kernel_le b v w.1 w.2) (H_nonneg _ _)) (H_nonneg _ _)
  exact (mul_le_mul_of_nonneg_right hk (by positivity : 0 ≤ 2*R*E)).trans_eq (mul_comm _ _)

end BoltzmannNonuniqueness.HotRepresentative

end

end

section

/-! # A gain estimate in the sum of absolute component differences -/

noncomputable section

open MeasureTheory
open BoltzmannNonuniqueness.VelocityWeight

namespace BoltzmannNonuniqueness.HotRepresentative

theorem finite_gain_difference_sum {X I : Type*} [MeasurableSpace X]
    (s : Finset I) {q R E : ℝ} (hR : 0 ≤ R) (hE : 0 ≤ E)
    {c d : I → X × Velocity → ℝ}
    (hcm : ∀ i ∈ s, Measurable (c i)) (hdm : ∀ i ∈ s, Measurable (d i))
    (hc : ∀ i ∈ s, ∀ p, 0 ≤ c i p ∧ c i p ≤ R)
    (hd : ∀ i ∈ s, ∀ p, 0 ≤ d i p ∧ d i p ≤ R)
    (hcd : ∀ p, (∑ i ∈ s, |c i p-d i p|) ≤ E)
    (b : ℝ) (p : X × Velocity) :
    (∑ i ∈ s, |gain q b (c i) p-gain q b (d i) p|) ≤ 2*R*E*HotApplication.realBound q := by
  classical
  by_cases hp : p.2 ∈ good q
  · let f (i : I) := CollisionCutoff.integrand b (fun v => density q (c i) (p.1,v)) p.2
    let g (i : I) := CollisionCutoff.integrand b (fun v => density q (d i) (p.1,v)) p.2
    let μ := (volume : Measure Velocity).prod sphereArea
    have hfi (i) (hi : i ∈ s) : Integrable (f i) μ := integrable_cutoff (hcm i hi) (hc i hi) b p hp
    have hgi (i) (hi : i ∈ s) : Integrable (g i) μ := integrable_cutoff (hdm i hi) (hd i hi) b p hp
    have hai (i) (hi : i ∈ s) : Integrable (fun w => |f i w-g i w|) μ := (hfi i hi |>.sub (hgi i hi)).abs
    have hterm (i) (hi : i ∈ s) : |gain q b (c i) p-gain q b (d i) p| ≤
        (∫ w, |f i w-g i w| ∂μ)/H q p.2 := by
      simp only [gain,ite_eq_left hp]
      change |(∫ w, f i w ∂μ)/H q p.2-(∫ w, g i w ∂μ)/H q p.2| ≤ _
      rw [← sub_div,abs_div,abs_of_pos (H_pos q p.2),← integral_sub (hfi i hi) (hgi i hi)]
      exact div_le_div_of_nonneg_right abs_integral_le_integral_abs (H_nonneg q p.2)
    calc
      _ ≤ ∑ i ∈ s, (∫ w, |f i w-g i w| ∂μ)/H q p.2 := Finset.sum_le_sum hterm
      _ = (∫ w, ∑ i ∈ s, |f i w-g i w| ∂μ)/H q p.2 := by
        rw [← Finset.sum_div,integral_finsetSum _ hai]
      _ ≤ (∫ w, (2*R*E)*GainOrder.integrand (H q) p.2 w ∂μ)/H q p.2 := by
        apply div_le_div_of_nonneg_right _ (H_nonneg q p.2)
        apply integral_mono (integrable_finsetSum s hai) ((integrable_H_gain hp).const_mul _)
        exact finite_integrand_abs_difference s hR hE c d hc hd hcd b p.1 p.2
      _ = ((2*R*E)*BoltzmannNonuniqueness.gain (fun p => H q p.2) 0 p.2)/H q p.2 := by
        rw [integral_const_mul]
        rfl
      _ ≤ ((2*R*E)*(HotApplication.realBound q*H q p.2))/H q p.2 :=
        div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left (H_gain_bound hp) (by positivity)) (H_nonneg q p.2)
      _ = _ := by field_simp [(H_pos q p.2).ne']
  · simp only [gain,ite_eq_right hp,sub_self,abs_zero,Finset.sum_const_zero]
    exact mul_nonneg (by positivity) (HotApplication.realBound_pos q).le

end BoltzmannNonuniqueness.HotRepresentative

end

end

section

/-! # Difference of the colored collision sources in the sum norm -/

noncomputable section

open MeasureTheory

namespace BoltzmannNonuniqueness.HotRepresentative

theorem finite_coldSource_difference_sum {X I : Type*} [MeasurableSpace X]
    (s : Finset I) {q b L R D E : ℝ} (hq : q < 2) (hb : 0 ≤ b)
    (hL : 0 ≤ L) (hR : 0 ≤ R) (hD : 0 ≤ D) (hE : 0 ≤ E)
    {F G : X × Velocity → ℝ} {c d : I → X × Velocity → ℝ}
    (hFm : Measurable F) (hGm : Measurable G)
    (hcm : ∀ i ∈ s, Measurable (c i)) (hdm : ∀ i ∈ s, Measurable (d i))
    (hF : ∀ p, 0 ≤ F p ∧ F p ≤ R) (hG : ∀ p, 0 ≤ G p ∧ G p ≤ R)
    (hc : ∀ i ∈ s, ∀ p, 0 ≤ c i p ∧ c i p ≤ R)
    (hd : ∀ i ∈ s, ∀ p, 0 ≤ d i p ∧ d i p ≤ R)
    (hFG : ∀ p, |F p-G p| ≤ D)
    (hcd : ∀ p, (∑ i ∈ s, |c i p-d i p|) ≤ E)
    (hdsum : ∀ p, (∑ i ∈ s, d i p) ≤ R) (p : X × Velocity) :
    (∑ i ∈ s, |coldSource q b L F (c i) p-coldSource q b L G (d i) p|) ≤
      2*R*E*HotApplication.realBound q+
        (L+R*CutoffLipschitz.frequencyConstant q b)*E+D*CutoffLipschitz.frequencyConstant q b*R := by
  let B := CutoffLipschitz.frequencyConstant q b
  have hB : 0 ≤ B := CutoffLipschitz.frequencyConstant_nonneg hb q
  have hνF : 0 ≤ frequency q b F p := frequency_nonneg (fun p => (hF p).1) q b p
  have hνFb : frequency q b F p ≤ R*B := frequency_bound hq hb hFm hF p
  have hνdiff : |frequency q b F p-frequency q b G p| ≤ D*B :=
    frequency_difference hq hb hFm hGm hF hG hFG p
  have hLF : |L-frequency q b F p| ≤ L+R*B := by
    apply (abs_sub _ _).trans
    rw [abs_of_nonneg hL,abs_of_nonneg hνF]
    exact add_le_add le_rfl hνFb
  have hLoss (i) (hi : i ∈ s) :
      |(L-frequency q b F p)*c i p-(L-frequency q b G p)*d i p| ≤
        (L+R*B)* |c i p-d i p| + (D*B)*d i p := by
    calc
      _ = |(L-frequency q b F p)*(c i p-d i p)+
          (frequency q b G p-frequency q b F p)*d i p| := by congr 1; ring
      _ ≤ |L-frequency q b F p| * |c i p-d i p| +
          |frequency q b G p-frequency q b F p| * |d i p| := by
        simpa only [abs_mul] using abs_add_le
          ((L-frequency q b F p)*(c i p-d i p)) ((frequency q b G p-frequency q b F p)*d i p)
      _ ≤ _ := by
        rw [abs_sub_comm (frequency q b G p),abs_of_nonneg (hd i hi p).1]
        exact add_le_add (mul_le_mul_of_nonneg_right hLF (abs_nonneg _))
          (mul_le_mul_of_nonneg_right hνdiff (hd i hi p).1)
  calc
    _ ≤ ∑ i ∈ s, (|gain q b (c i) p-gain q b (d i) p| +
        |(L-frequency q b F p)*c i p-(L-frequency q b G p)*d i p|) := by
      apply Finset.sum_le_sum
      intro i _
      have he : coldSource q b L F (c i) p-coldSource q b L G (d i) p =
          (gain q b (c i) p-gain q b (d i) p)+
            ((L-frequency q b F p)*c i p-(L-frequency q b G p)*d i p) := by
        unfold coldSource
        ring
      rw [he]
      exact abs_add_le _ _
    _ ≤ (∑ i ∈ s, |gain q b (c i) p-gain q b (d i) p|)+
        (∑ i ∈ s, ((L+R*B)* |c i p-d i p| + (D*B)*d i p)) := by
      rw [Finset.sum_add_distrib]
      exact add_le_add le_rfl (Finset.sum_le_sum hLoss)
    _ ≤ (2*R*E*HotApplication.realBound q)+(L+R*B)*E+(D*B)*R := by
      rw [Finset.sum_add_distrib,← Finset.mul_sum,← Finset.mul_sum]
      have hgain := finite_gain_difference_sum (q := q) s hR hE hcm hdm hc hd hcd b p
      have hcold := mul_le_mul_of_nonneg_left (hcd p) (add_nonneg hL (mul_nonneg hR hB))
      have hdtotal := mul_le_mul_of_nonneg_left (hdsum p) (mul_nonneg hD hB)
      exact (add_le_add hgain (add_le_add hcold hdtotal)).trans_eq (add_assoc _ _ _).symm
    _ = _ := rfl

end BoltzmannNonuniqueness.HotRepresentative

end

end

section

/-! # The colored sum-norm source estimate for a.e. close representatives -/

noncomputable section

open MeasureTheory

namespace BoltzmannNonuniqueness.WeightedLocal

theorem finite_coldForcing_difference_ae {I : Type*} [Countable I]
    (s : Finset I) {q b L R D E : ℝ} (hq : q < 2) (hb : 0 ≤ b)
    (hL : 0 ≤ L) (hR : 0 ≤ R) (hD : 0 ≤ D) (hE : 0 ≤ E)
    {F G : ℝ × JetPrototype.Phase → ℝ} {c d : I → ℝ × JetPrototype.Phase → ℝ}
    (hFm : Measurable F) (hGm : Measurable G)
    (hcm : ∀ i, Measurable (c i)) (hdm : ∀ i, Measurable (d i))
    (hF : ∀ u, 0 ≤ F u ∧ F u ≤ R) (hG : ∀ u, 0 ≤ G u ∧ G u ≤ R)
    (hc : ∀ i u, 0 ≤ c i u ∧ c i u ≤ R) (hd : ∀ i u, 0 ≤ d i u ∧ d i u ≤ R)
    (hFG : ∀ᵐ u ∂spacetimeVolume, |F u-G u| ≤ D)
    (hcd : ∀ᵐ u ∂spacetimeVolume, (∑ i ∈ s, |c i u-d i u|) ≤ E)
    (hdsum : ∀ u, (∑ i ∈ s, d i u) ≤ R) :
    ∀ᵐ u ∂spacetimeVolume,
      (∑ i ∈ s, |coldForcing q b L F (c i) u-coldForcing q b L G (d i) u|) ≤
        2*R*E*HotApplication.realBound q+
          (L+R*CutoffLipschitz.frequencyConstant q b)*E+D*CutoffLipschitz.frequencyConstant q b*R := by
  classical
  let H (u : ℝ × JetPrototype.Phase) := max (G u-D) (min (F u) (G u+D))
  have hHm : Measurable H := (hGm.sub_const D).max (hFm.min (hGm.add_const D))
  have hHb (u) : 0 ≤ H u ∧ H u ≤ R := by
    dsimp [H]
    exact ⟨(le_min (hF u).1 (add_nonneg (hG u).1 hD)).trans (le_max_right _ _),
      max_le (by linarith [(hG u).2]) ((min_le_left _ _).trans (hF u).2)⟩
  have hHD (u) : |H u-G u| ≤ D := by
    rw [abs_sub_le_iff]
    have hlo : G u-D ≤ H u := le_max_left _ _
    have hhi : H u ≤ G u+D := max_le (by linarith) (min_le_right _ _)
    constructor <;> linarith
  have hHF : H =ᵐ[spacetimeVolume] F := by
    filter_upwards [hFG] with u hu
    obtain ⟨h₁,h₂⟩ := abs_sub_le_iff.mp hu
    dsimp [H]
    rw [min_eq_left (by linarith),max_eq_right (by linarith)]
  let P (u : ℝ × JetPrototype.Phase) := (∑ i ∈ s, |c i u-d i u|) ≤ E
  let c' (i : I) (u : ℝ × JetPrototype.Phase) := if P u then c i u else 0
  let d' (i : I) (u : ℝ × JetPrototype.Phase) := if P u then d i u else 0
  have hPm : MeasurableSet {u | P u} := measurableSet_le
    (Finset.measurable_sum s (fun i _ => (hcm i |>.sub (hdm i)).abs)) measurable_const
  have hc'm (i) : Measurable (c' i) := (hcm i).ite hPm measurable_const
  have hd'm (i) : Measurable (d' i) := (hdm i).ite hPm measurable_const
  have hc'b (i) (u) : 0 ≤ c' i u ∧ c' i u ≤ R := by
    dsimp [c']; split_ifs; exact hc i u; exact ⟨le_rfl,hR⟩
  have hd'b (i) (u) : 0 ≤ d' i u ∧ d' i u ≤ R := by
    dsimp [d']; split_ifs; exact hd i u; exact ⟨le_rfl,hR⟩
  have hcd' (u) : (∑ i ∈ s, |c' i u-d' i u|) ≤ E := by
    by_cases hu : P u
    · simpa only [c',d',ite_eq_left hu] using hu
    · simpa only [c',d',ite_eq_right hu,sub_self,abs_zero,Finset.sum_const_zero] using hE
  have hdsum' (u) : (∑ i ∈ s, d' i u) ≤ R := by
    by_cases hu : P u
    · simpa only [d',ite_eq_left hu] using hdsum u
    · simpa only [d',ite_eq_right hu,Finset.sum_const_zero] using hR
  have hc'e (i) : c' i =ᵐ[spacetimeVolume] c i := by
    filter_upwards [hcd] with u hu
    exact ite_eq_left hu
  have hd'e (i) : d' i =ᵐ[spacetimeVolume] d i := by
    filter_upwards [hcd] with u hu
    exact ite_eq_left hu
  have hec : ∀ᵐ u ∂spacetimeVolume, ∀ i, coldForcing q b L H (c' i) u = coldForcing q b L F (c i) u :=
    ae_all_iff.mpr (fun i => (coldForcing_congr_cold (hc'e i) q b L H).trans
      (coldForcing_congr_total hHF q b L (c i)))
  have hed : ∀ᵐ u ∂spacetimeVolume, ∀ i, coldForcing q b L G (d' i) u = coldForcing q b L G (d i) u :=
    ae_all_iff.mpr (fun i => coldForcing_congr_cold (hd'e i) q b L G)
  filter_upwards [hec,hed] with u hcu hdu
  have h := HotRepresentative.finite_coldSource_difference_sum s hq hb hL hR hD hE
    (GaussianLocal.measurable_state hHm) (GaussianLocal.measurable_state hGm)
    (fun i _ => GaussianLocal.measurable_state (hc'm i)) (fun i _ => GaussianLocal.measurable_state (hd'm i))
    (fun p => hHb (p.1.1,(p.1.2,p.2))) (fun p => hG (p.1.1,(p.1.2,p.2)))
    (fun i _ p => hc'b i (p.1.1,(p.1.2,p.2))) (fun i _ p => hd'b i (p.1.1,(p.1.2,p.2)))
    (fun p => hHD (p.1.1,(p.1.2,p.2))) (fun p => hcd' (p.1.1,(p.1.2,p.2)))
    (fun p => hdsum' (p.1.1,(p.1.2,p.2))) ((u.1,u.2.1),u.2.2)
  change (∑ i ∈ s, |coldForcing q b L H (c' i) u-coldForcing q b L G (d' i) u|) ≤ _ at h
  simpa only [hcu,hdu] using h

end BoltzmannNonuniqueness.WeightedLocal

end

end

end OAI
end

section
-- module Solutions.OAIQ080_BZ.Boltzmann_Branching_SpaceTimeEssSup
attribute [-instance] _root_.OAI.BoltzmannNonuniqueness.ChartKernel.offAxis_sFinite _root_.OAI.BoltzmannNonuniqueness.EuclideanFlight.sourcePullback_finite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.characteristicGainKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.hotKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.mixedKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.retainedKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.coldCylinderVolume_finite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.copyColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.mainCoreKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.selectedColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCoreSheet.dilatedColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCoreSheet.kineticColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.PeriodicApproximation.fiberMeasure_finite _root_.OAI.BoltzmannNonuniqueness.PositiveIteration.awayOriginKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.PositiveIteration.nearOriginKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamNormalCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamNormalRetainedKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.dampedCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.densityScaledCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalBeamKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalCollision_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalPhysicalEvent_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalWindowEvent_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.physicalEventMeasure_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.scaledBeamNormalKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.WeakTime.phaseEndpointKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.WeakTime.phaseIncrement_finite _root_.OAI.BoltzmannNonuniqueness.WeakTime.phaseSeed_sFinite _root_.OAI.BoltzmannNonuniqueness.WeakTime.residenceKernel_sFinite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Essential uniform size for bounded spacetime representatives -/

noncomputable section

open MeasureTheory
open scoped ENNReal

namespace BoltzmannNonuniqueness.SpaceTimeEssSup

theorem nonneg (f : ℝ × JetPrototype.Phase → ℝ) : 0 ≤ size f := ENNReal.toReal_nonneg

theorem ae_abs_le_size {f : ℝ × JetPrototype.Phase → ℝ} (hfm : Measurable f)
    {R : ℝ} (hf : ∀ u, |f u| ≤ R) : ∀ᵐ u ∂WeightedLocal.spacetimeVolume, |f u| ≤ size f := by
  have hm : MemLp f ∞ WeightedLocal.spacetimeVolume :=
    memLp_top_of_bound hfm.aestronglyMeasurable R (ae_of_all _ (fun u => by
      simpa only [Real.norm_eq_abs] using hf u))
  simpa only [Real.norm_eq_abs,← toReal_eLpNorm hm.1,size] using ae_le_lpNorm_exponent_top hm

theorem size_le_ae {f : ℝ × JetPrototype.Phase → ℝ} (hfm : Measurable f)
    {R : ℝ} (hR : 0 ≤ R) (hf : ∀ᵐ u ∂WeightedLocal.spacetimeVolume, |f u| ≤ R) : size f ≤ R := by
  have h : eLpNorm f ∞ WeightedLocal.spacetimeVolume ≤ ENNReal.ofReal R := by
    rw [eLpNorm_exponent_top]
    exact eLpNormEssSup_le_of_ae_bound (hf.mono (fun u hu => by
      simpa only [Real.norm_eq_abs] using hu))
  simpa only [size,ENNReal.toReal_ofReal hR] using ENNReal.toReal_mono ENNReal.ofReal_ne_top h

end BoltzmannNonuniqueness.SpaceTimeEssSup

end

end OAI
end

section
-- module Solutions.OAIQ080_BZ.Boltzmann_Jets_ColdMildRepresentative
attribute [-instance] _root_.OAI.BoltzmannNonuniqueness.ChartKernel.offAxis_sFinite _root_.OAI.BoltzmannNonuniqueness.EuclideanFlight.sourcePullback_finite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.characteristicGainKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.hotKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.mixedKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.retainedKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.coldCylinderVolume_finite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.copyColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.mainCoreKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.selectedColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCoreSheet.dilatedColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCoreSheet.kineticColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.PeriodicApproximation.fiberMeasure_finite _root_.OAI.BoltzmannNonuniqueness.PositiveIteration.awayOriginKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.PositiveIteration.nearOriginKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamNormalCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamNormalRetainedKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.dampedCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.densityScaledCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalBeamKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalCollision_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalPhysicalEvent_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalWindowEvent_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.physicalEventMeasure_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.scaledBeamNormalKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.WeakTime.phaseEndpointKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.WeakTime.phaseIncrement_finite _root_.OAI.BoltzmannNonuniqueness.WeakTime.phaseSeed_sFinite _root_.OAI.BoltzmannNonuniqueness.WeakTime.residenceKernel_sFinite
attribute [-simp] _root_.OAI.BoltzmannNonuniqueness.EuclideanFlight.phaseEquiv_snd _root_.OAI.BoltzmannNonuniqueness.timeTranslation_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

/-! # Pointwise dominated representatives of an almost-everywhere cold family -/

noncomputable section

open MeasureTheory

namespace BoltzmannNonuniqueness.WeightedLocal

variable {I : Type*} [Countable I]

theorem measurable_normalizedFamily {F : ℝ × JetPrototype.Phase → ℝ}
    {c : I → ℝ × JetPrototype.Phase → ℝ} (hFm : Measurable F) (hcm : ∀ i, Measurable (c i)) (i : I) :
    Measurable (normalizedFamily F c i) := by
  classical
  have he : {u : ℝ × JetPrototype.Phase | ∀ s : Finset I, (∑ j ∈ s, c j u) ≤ F u} =
      ⋂ s : Finset I, {u | (∑ j ∈ s, c j u) ≤ F u} := by ext u; simp
  have hm : MeasurableSet {u : ℝ × JetPrototype.Phase | ∀ s : Finset I, (∑ j ∈ s, c j u) ≤ F u} := by
    rw [he]
    exact MeasurableSet.iInter (fun s => measurableSet_le
      (Finset.measurable_sum s (fun j _ => hcm j)) hFm)
  exact (hcm i).ite hm measurable_const

omit [Countable I] in
theorem normalizedFamily_bounds {F : ℝ × JetPrototype.Phase → ℝ}
    {c : I → ℝ × JetPrototype.Phase → ℝ} (hcn : ∀ i u, 0 ≤ c i u) (i : I) (u) :
    0 ≤ normalizedFamily F c i u ∧ normalizedFamily F c i u ≤ c i u := by
  classical
  unfold normalizedFamily
  split_ifs
  · exact ⟨hcn i u,le_rfl⟩
  · exact ⟨le_rfl,hcn i u⟩

omit [Countable I] in
theorem normalizedFamily_sum_le {F : ℝ × JetPrototype.Phase → ℝ}
    (hF : ∀ u, 0 ≤ F u) (c : I → ℝ × JetPrototype.Phase → ℝ) (s : Finset I) (u) :
    (∑ i ∈ s, normalizedFamily F c i u) ≤ F u := by
  classical
  by_cases hu : ∀ r : Finset I, (∑ j ∈ r, c j u) ≤ F u
  · simpa only [normalizedFamily,ite_eq_left hu] using hu s
  · simpa only [normalizedFamily,ite_eq_right hu,Finset.sum_const_zero] using hF u

theorem normalizedFamily_ae_at_time {F : ℝ × JetPrototype.Phase → ℝ}
    {c : I → ℝ × JetPrototype.Phase → ℝ}
    (hfinite : ∀ s : Finset I, ∀ t, ∀ᵐ p ∂FlightMeasure.phaseVolume, (∑ i ∈ s, c i (t,p)) ≤ F (t,p))
    (i : I) (t : ℝ) : (fun p => normalizedFamily F c i (t,p)) =ᵐ[FlightMeasure.phaseVolume]
      (fun p => c i (t,p)) := by
  classical
  have hg : ∀ᵐ p ∂FlightMeasure.phaseVolume, ∀ s : Finset I, (∑ j ∈ s, c j (t,p)) ≤ F (t,p) :=
    ae_all_iff.mpr (fun s => hfinite s t)
  filter_upwards [hg] with p hp
  exact ite_eq_left hp

omit [Countable I] in
theorem normalizedFamily_summable {F : ℝ × JetPrototype.Phase → ℝ}
    {c : I → ℝ × JetPrototype.Phase → ℝ} (hF : ∀ u, 0 ≤ F u) (hcn : ∀ i u, 0 ≤ c i u) (u) :
    Summable (fun i => normalizedFamily F c i u) ∧ (∑' i, normalizedFamily F c i u) ≤ F u := by
  have hn (i) : 0 ≤ normalizedFamily F c i u := (normalizedFamily_bounds hcn i u).1
  have hs (s : Finset I) := normalizedFamily_sum_le hF c s u
  exact ⟨summable_of_sum_le hn hs,Real.tsum_le_of_sum_le hn hs⟩

end BoltzmannNonuniqueness.WeightedLocal

end

end

section

/-! # Local stability of a countable cold family in the sum norm -/

noncomputable section

open MeasureTheory MeasureTheory.Measure

namespace BoltzmannNonuniqueness.WeightedLocal

theorem cold_family_difference_ae {I : Type*} [Countable I] {q b L T R B D : ℝ}
    (hq : q < 2) (hb : 0 ≤ b) (hL : 0 ≤ L) (hT : 0 ≤ T) (hR : 0 ≤ R)
    (hB : 0 ≤ B) (hD : 0 ≤ D) (hloss : R*CutoffLipschitz.frequencyConstant q b ≤ L)
    (hsmall : T*(2*R*HotApplication.realBound q+L+R*CutoffLipschitz.frequencyConstant q b) < 1)
    {F G : ℝ × JetPrototype.Phase → ℝ} {c d : I → ℝ × JetPrototype.Phase → ℝ}
    {c₀ d₀ : I → JetPrototype.Phase → ℝ}
    (hFm : Measurable F) (hGm : Measurable G)
    (hcm : ∀ i, Measurable (c i)) (hdm : ∀ i, Measurable (d i))
    (hF : ∀ u, 0 ≤ F u ∧ F u ≤ R) (hG : ∀ u, 0 ≤ G u ∧ G u ≤ R)
    (hcn : ∀ i u, 0 ≤ c i u) (hdn : ∀ i u, 0 ≤ d i u)
    (hcSum : ∀ s : Finset I, ∀ u, ∑ i ∈ s, c i u ≤ F u)
    (hdSum : ∀ s : Finset I, ∀ u, ∑ i ∈ s, d i u ≤ G u)
    (hFG : ∀ᵐ u ∂spacetimeVolume, |F u-G u| ≤ D)
    (hseed : ∀ s : Finset I, ∀ᵐ p ∂FlightMeasure.phaseVolume, (∑ i ∈ s, |c₀ i p-d₀ i p|) ≤ B)
    (hceq : ∀ i t, (fun p => c i (t,p)) =ᵐ[FlightMeasure.phaseVolume]
      (fun p => PositiveIntegral.value T L JetBarrier.flight (c₀ i) (coldForcing q b L F (c i)) (t,p)))
    (hdeq : ∀ i t, (fun p => d i (t,p)) =ᵐ[FlightMeasure.phaseVolume]
      (fun p => PositiveIntegral.value T L JetBarrier.flight (d₀ i) (coldForcing q b L G (d i)) (t,p))) :
    ∀ t, ∀ᵐ p ∂FlightMeasure.phaseVolume, (∑' i, |c i (t,p)-d i (t,p)|) ≤
      (B+T*(R*CutoffLipschitz.frequencyConstant q b)*D)/
        (1-T*(2*R*HotApplication.realBound q+L+R*CutoffLipschitz.frequencyConstant q b)) := by
  classical
  let J := R*CutoffLipschitz.frequencyConstant q b
  let K := 2*R*HotApplication.realBound q+L+J
  let S := HotApplication.realBound q*R^2+L*R
  let e (u : ℝ × JetPrototype.Phase) := ∑' i, |c i u-d i u|
  let E := SpaceTimeEssSup.size e
  have hJ : 0 ≤ J := mul_nonneg hR (CutoffLipschitz.frequencyConstant_nonneg hb q)
  have hK : 0 ≤ K := by
    have := (HotApplication.realBound_pos q).le
    dsimp [K]
    positivity
  have hE : 0 ≤ E := SpaceTimeEssSup.nonneg _
  have hcb (i) (u) : 0 ≤ c i u ∧ c i u ≤ R := by
    refine ⟨hcn i u,?_⟩
    simpa only [Finset.sum_singleton] using (hcSum {i} u).trans (hF u).2
  have hdb (i) (u) : 0 ≤ d i u ∧ d i u ≤ R := by
    refine ⟨hdn i u,?_⟩
    simpa only [Finset.sum_singleton] using (hdSum {i} u).trans (hG u).2
  have hcs (u) : Summable (fun i => c i u) := summable_of_sum_le (fun i => hcn i u) (fun s => hcSum s u)
  have hds (u) : Summable (fun i => d i u) := summable_of_sum_le (fun i => hdn i u) (fun s => hdSum s u)
  have hes (u) : Summable (fun i => |c i u-d i u|) := (hcs u |>.sub (hds u)).abs
  have hem : Measurable e := Measurable.tsum (fun i => (hcm i |>.sub (hdm i)).abs)
  have hen (u) : 0 ≤ e u := tsum_nonneg (fun i => abs_nonneg _)
  have heb (u) : |e u| ≤ 2*R := by
    rw [abs_of_nonneg (hen u)]
    have hcF : (∑' i, c i u) ≤ F u := Real.tsum_le_of_sum_le (fun i => hcn i u) (fun s => hcSum s u)
    have hdG : (∑' i, d i u) ≤ G u := Real.tsum_le_of_sum_le (fun i => hdn i u) (fun s => hdSum s u)
    have hecd : e u ≤ (∑' i, c i u)+(∑' i, d i u) := by
      rw [← (hcs u).tsum_add (hds u)]
      exact (hes u).tsum_le_tsum (fun i => by
        rw [abs_sub_le_iff]
        constructor <;> linarith [hcn i u,hdn i u]) ((hcs u).add (hds u))
    linarith [(hF u).2,(hG u).2]
  have heAE : ∀ᵐ u ∂spacetimeVolume, e u ≤ E := by
    filter_upwards [SpaceTimeEssSup.ae_abs_le_size hem heb] with u hu
    exact (le_abs_self _).trans hu
  have hsource (s : Finset I) : ∀ᵐ u ∂spacetimeVolume,
      (∑ i ∈ s, |coldForcing q b L F (c i) u-coldForcing q b L G (d i) u|) ≤ K*E+J*D := by
    have hefin : ∀ᵐ u ∂spacetimeVolume, (∑ i ∈ s, |c i u-d i u|) ≤ E :=
      heAE.mono (fun u hu => ((hes u).sum_le_tsum s (fun i _ => abs_nonneg _)).trans hu)
    have h := finite_coldForcing_difference_ae s hq hb hL hR hD hE hFm hGm hcm hdm hF hG hcb hdb
      hFG hefin (fun u => (hdSum s u).trans (hG u).2)
    filter_upwards [h] with u hu
    calc
      _ ≤ 2*R*E*HotApplication.realBound q+
          (L+R*CutoffLipschitz.frequencyConstant q b)*E+
          D*CutoffLipschitz.frequencyConstant q b*R := hu
      _ = K*E+J*D := by dsimp [K,J] <;> ring
  have hsrc (U : ℝ × JetPrototype.Phase → ℝ) (a : I → ℝ × JetPrototype.Phase → ℝ)
      (hUm : Measurable U) (ham : ∀ i, Measurable (a i))
      (hU : ∀ u, 0 ≤ U u ∧ U u ≤ R) (ha : ∀ i u, 0 ≤ a i u ∧ a i u ≤ R)
      (i : I) (u) : |coldForcing q b L U (a i) u| ≤ S := by
    have h := HotRepresentative.coldSource_bounds hq hb hR hloss
      (GaussianLocal.measurable_state hUm) (GaussianLocal.measurable_state (ham i))
      (fun p => hU (p.1.1,(p.1.2,p.2))) (fun p => ha i (p.1.1,(p.1.2,p.2))) ((u.1,u.2.1),u.2.2)
    change 0 ≤ coldForcing q b L U (a i) u ∧ coldForcing q b L U (a i) u ≤ S at h
    rw [abs_of_nonneg h.1]
    exact h.2
  have hbound (t : ℝ) : ∀ᵐ p ∂FlightMeasure.phaseVolume, e (t,p) ≤ B+T*(K*E+J*D) := by
    have hcAll := ae_all_iff.mpr (fun i => hceq i t)
    have hdAll := ae_all_iff.mpr (fun i => hdeq i t)
    have hf (s : Finset I) := PositiveIntegral.finite_difference_ae hT hL
      (show 0 ≤ K*E+J*D by positivity) hB s c₀ d₀
      (fun i => coldForcing q b L F (c i)) (fun i => coldForcing q b L G (d i))
      (fun i _ => measurable_coldForcing hFm (hcm i) q b L)
      (fun i _ => measurable_coldForcing hGm (hdm i) q b L)
      (fun i _ => hsrc F c hFm hcm hF hcb i) (fun i _ => hsrc G d hGm hdm hG hdb i)
      (hseed s) (hsource s) t
    filter_upwards [hcAll,hdAll,ae_all_iff.mpr hf] with p hcp hdp hp
    apply Real.tsum_le_of_sum_le (fun i => abs_nonneg _)
    intro s
    simpa only [← hcp,← hdp] using hp s
  have hspace : ∀ᵐ u ∂spacetimeVolume, e u ≤ B+T*(K*E+J*D) :=
    (ae_prod_iff_ae_ae (measurableSet_le hem measurable_const)).mpr (ae_of_all _ hbound)
  have hineq : E ≤ B+T*(K*E+J*D) := SpaceTimeEssSup.size_le_ae hem (by positivity)
    (hspace.mono (fun u hu => by rwa [abs_of_nonneg (hen u)]))
  have hden : 0 < 1-T*K := by dsimp [K,J] <;> linarith
  have hEQ : E ≤ (B+T*J*D)/(1-T*K) := (le_div_iff₀ hden).mpr (by nlinarith [hineq])
  have hmul := mul_le_mul_of_nonneg_left hEQ (mul_nonneg hT hK)
  have hQ : (B+T*J*D)/(1-T*K)*(1-T*K) = B+T*J*D := div_mul_cancel₀ _ hden.ne'
  have hfinal : B+T*(K*E+J*D) ≤ (B+T*J*D)/(1-T*K) := by nlinarith
  intro t
  exact (hbound t).mono (fun p hp => hp.trans hfinal)

end BoltzmannNonuniqueness.WeightedLocal

end

end

section

/-! # Cold mild equations are independent of spatial representatives -/

noncomputable section

open MeasureTheory

namespace BoltzmannNonuniqueness.WeightedLocal

theorem ColdMildAE.representative {q b L T : ℝ} {c₀ : JetPrototype.Phase → ℝ}
    {F c d : ℝ × JetPrototype.Phase → ℝ} (hc : ColdMildAE q b L T F c₀ c)
    (hcm : Measurable c) (hdm : Measurable d)
    (hcd : ∀ t, (fun p => c (t,p)) =ᵐ[FlightMeasure.phaseVolume] (fun p => d (t,p))) :
    ColdMildAE q b L T F c₀ d := by
  have hsource := coldForcing_congr_cold (slice_congr_spacetime hcm hdm hcd) q b L F
  intro t ht
  exact (hcd t).symm.trans ((hc t ht).trans
    (FlightMeasure.value_congr_at_time (ae_of_all _ (fun _ => rfl)) hsource T L t))

end BoltzmannNonuniqueness.WeightedLocal

end

end

end OAI
end

section
-- module Solutions.OAIQ080_BZ.Boltzmann_Approximation_MildInitialAE
attribute [-instance] _root_.OAI.BoltzmannNonuniqueness.ChartKernel.offAxis_sFinite _root_.OAI.BoltzmannNonuniqueness.EuclideanFlight.sourcePullback_finite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.characteristicGainKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.hotKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.mixedKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.retainedKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.coldCylinderVolume_finite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.copyColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.mainCoreKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.selectedColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCoreSheet.dilatedColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCoreSheet.kineticColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.PeriodicApproximation.fiberMeasure_finite _root_.OAI.BoltzmannNonuniqueness.PositiveIteration.awayOriginKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.PositiveIteration.nearOriginKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamNormalCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamNormalRetainedKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.dampedCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.densityScaledCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalBeamKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalCollision_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalPhysicalEvent_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalWindowEvent_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.physicalEventMeasure_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.scaledBeamNormalKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.WeakTime.phaseEndpointKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.WeakTime.phaseIncrement_finite _root_.OAI.BoltzmannNonuniqueness.WeakTime.phaseSeed_sFinite _root_.OAI.BoltzmannNonuniqueness.WeakTime.residenceKernel_sFinite
attribute [-simp] _root_.OAI.BoltzmannNonuniqueness.EuclideanFlight.phaseEquiv_snd _root_.OAI.BoltzmannNonuniqueness.timeTranslation_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Initial traces of the a.e. characteristic equations -/

noncomputable section

open MeasureTheory Set

namespace BoltzmannNonuniqueness

namespace PositiveIntegral

theorem value_zero {T : ℝ} (_hT : 0 ≤ T) (L : ℝ)
    (f₀ : JetPrototype.Phase → ℝ) (g : ℝ × JetPrototype.Phase → ℝ) (p : JetPrototype.Phase) :
    value T L JetBarrier.flight f₀ g (0,p) = f₀ p := by
  simp [value,time,JetBarrier.flight]

end PositiveIntegral

namespace WeightedLocal

theorem MildAE.initial_ae {q b L T : ℝ} (hT : 0 ≤ T)
    {F : ℝ × JetPrototype.Phase → ℝ} {F₀ : JetPrototype.Phase → ℝ}
    (he : MildAE q b L T F₀ F) :
    (fun p => F (0,p)) =ᵐ[FlightMeasure.phaseVolume] F₀ := by
  simpa only [PositiveIntegral.value_zero hT] using he 0 ⟨le_rfl,hT⟩

theorem ColdMildAE.initial_ae {q b L T : ℝ} (hT : 0 ≤ T)
    {F c : ℝ × JetPrototype.Phase → ℝ} {c₀ : JetPrototype.Phase → ℝ}
    (he : ColdMildAE q b L T F c₀ c) :
    (fun p => c (0,p)) =ᵐ[FlightMeasure.phaseVolume] c₀ := by
  simpa only [PositiveIntegral.value_zero hT] using he 0 ⟨le_rfl,hT⟩

end WeightedLocal
end BoltzmannNonuniqueness

end

end OAI
end

section
-- module Solutions.OAIQ080_BZ.Boltzmann_Branching_RebuiltHotInitial
attribute [-instance] _root_.OAI.BoltzmannNonuniqueness.ChartKernel.offAxis_sFinite _root_.OAI.BoltzmannNonuniqueness.EuclideanFlight.sourcePullback_finite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.characteristicGainKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.hotKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.mixedKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.retainedKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.coldCylinderVolume_finite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.copyColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.mainCoreKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.selectedColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCoreSheet.dilatedColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCoreSheet.kineticColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.PeriodicApproximation.fiberMeasure_finite _root_.OAI.BoltzmannNonuniqueness.PositiveIteration.awayOriginKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.PositiveIteration.nearOriginKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamNormalCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamNormalRetainedKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.dampedCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.densityScaledCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalBeamKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalCollision_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalPhysicalEvent_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalWindowEvent_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.physicalEventMeasure_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.scaledBeamNormalKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.WeakTime.phaseEndpointKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.WeakTime.phaseIncrement_finite _root_.OAI.BoltzmannNonuniqueness.WeakTime.phaseSeed_sFinite _root_.OAI.BoltzmannNonuniqueness.WeakTime.residenceKernel_sFinite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

/-! # A pointwise summable cold family over an almost-everywhere mild total state -/

noncomputable section

open MeasureTheory

namespace BoltzmannNonuniqueness.WeightedLocal

variable {I : Type*} [Countable I]

theorem rebuiltColdFamily_properties {q b L T R : ℝ}
    (hq : q < 2) (hb : 0 ≤ b) (hL : 0 ≤ L) (hT : 0 ≤ T) (hR : 0 ≤ R)
    (hloss : R*CutoffLipschitz.frequencyConstant q b ≤ L)
    {F : ℝ × JetPrototype.Phase → ℝ} {F₀ : JetPrototype.Phase → ℝ}
    {c₀ : I → JetPrototype.Phase → ℝ}
    (hFm : Measurable F) (hc₀m : ∀ i, Measurable (c₀ i))
    (hF : ∀ u, 0 ≤ F u ∧ F u ≤ R) (hc₀ : ∀ i p, 0 ≤ c₀ i p ∧ c₀ i p ≤ R)
    (hSum₀ : ∀ s : Finset I, ∀ p, ∑ i ∈ s, c₀ i p ≤ F₀ p)
    (hFeq : ∀ t, (fun p => F (t,p)) =ᵐ[FlightMeasure.phaseVolume]
      (fun p => PositiveIntegral.value T L JetBarrier.flight F₀ (forcing q b L F) (t,p))) :
    (∀ i, Measurable (rebuiltColdFamily q b L T F c₀ i)) ∧
      (∀ i u, 0 ≤ rebuiltColdFamily q b L T F c₀ i u ∧
        rebuiltColdFamily q b L T F c₀ i u ≤ clippedColdLimit q b L T F (c₀ i) u) ∧
      (∀ s : Finset I, ∀ u, ∑ i ∈ s, rebuiltColdFamily q b L T F c₀ i u ≤ F u) ∧
      (∀ u, Summable (fun i => rebuiltColdFamily q b L T F c₀ i u) ∧
        (∑' i, rebuiltColdFamily q b L T F c₀ i u) ≤ F u) ∧
      ∀ i, ColdMildAE q b L T F (c₀ i) (rebuiltColdFamily q b L T F c₀ i) := by
  classical
  let c (i : I) := clippedColdLimit q b L T F (c₀ i)
  have hc (i) := clippedCold_solution hq hb hL hT hR hloss hFm (hc₀m i) hF (hc₀ i)
  have hcm (i) : Measurable (c i) := (hc i).1
  have hcn (i) (u) : 0 ≤ c i u := ((hc i).2.1 u).1
  have hfin (s : Finset I) := clippedCold_finite_limit hq hb hL hT hR hloss s hFm hc₀m hF hc₀ (hSum₀ s) hFeq
  have hd (i) : Measurable (rebuiltColdFamily q b L T F c₀ i) := measurable_normalizedFamily hFm hcm i
  refine ⟨hd,normalizedFamily_bounds hcn,normalizedFamily_sum_le (fun u => (hF u).1) c,
    normalizedFamily_summable (fun u => (hF u).1) hcn,?_⟩
  intro i
  have hi : ∀ p, c₀ i p ≤ F₀ p := by
    intro p
    simpa only [Finset.sum_singleton] using hSum₀ {i} p
  have hm := clippedCold_mildAE hq hb hL hT hR hloss hFm (hc₀m i) hF (hc₀ i) hi
    (fun t _ => hFeq t)
  exact hm.representative (hcm i) (hd i)
    (fun t => (normalizedFamily_ae_at_time hfin i t).symm)

end BoltzmannNonuniqueness.WeightedLocal

end

end

section

/-! # The initial hot trace of the reconstructed colored solution -/

noncomputable section

open MeasureTheory
open scoped ENNReal

namespace BoltzmannNonuniqueness

namespace PhaseEssSup

theorem size_const_mul (a : ℝ) (f : JetPrototype.Phase → ℝ) :
    size (fun p => a*f p) = |a| * size f := by
  change (eLpNorm (a • f) ∞ FlightMeasure.phaseVolume).toReal = _
  rw [eLpNorm_const_smul,ENNReal.toReal_mul]
  simp only [enorm,ENNReal.coe_toReal]
  rfl

end PhaseEssSup

namespace WeightedLocal

theorem rebuilt_hot_initial_ae {I : Type*} [Countable I] {q b L T R : ℝ}
    (hq : q < 2) (hb : 0 ≤ b) (hL : 0 ≤ L) (hT : 0 ≤ T) (hR : 0 ≤ R)
    (hloss : R*CutoffLipschitz.frequencyConstant q b ≤ L)
    {F : ℝ × JetPrototype.Phase → ℝ} {F₀ : JetPrototype.Phase → ℝ}
    {c₀ : I → JetPrototype.Phase → ℝ}
    (hFm : Measurable F) (hc₀m : ∀ i, Measurable (c₀ i))
    (hF : ∀ u, 0 ≤ F u ∧ F u ≤ R) (hc₀ : ∀ i p, 0 ≤ c₀ i p ∧ c₀ i p ≤ R)
    (hSum₀ : ∀ s : Finset I, ∀ p, ∑ i ∈ s, c₀ i p ≤ F₀ p)
    (hFeq : ∀ t, (fun p => F (t,p)) =ᵐ[FlightMeasure.phaseVolume]
      (fun p => PositiveIntegral.value T L JetBarrier.flight F₀ (forcing q b L F) (t,p))) :
    (fun p => F (0,p)-∑' i, rebuiltColdFamily q b L T F c₀ i (0,p)) =ᵐ[FlightMeasure.phaseVolume]
      (fun p => F₀ p-∑' i, c₀ i p) := by
  have hp := rebuiltColdFamily_properties hq hb hL hT hR hloss hFm hc₀m hF hc₀ hSum₀ hFeq
  have hf : (fun p => F (0,p)) =ᵐ[FlightMeasure.phaseVolume] F₀ := by
    simpa only [PositiveIntegral.value_zero hT] using hFeq 0
  have hc : ∀ᵐ p ∂FlightMeasure.phaseVolume, ∀ i,
      rebuiltColdFamily q b L T F c₀ i (0,p) = c₀ i p :=
    ae_all_iff.mpr (fun i => (hp.2.2.2.2 i).initial_ae hT)
  filter_upwards [hf,hc] with p hfp hcp
  simp only [hfp,hcp]

end WeightedLocal
end BoltzmannNonuniqueness

end

end

end OAI
end

section
-- module Solutions.OAIQ080_BZ.Boltzmann_Branching_ClippedColdTime
attribute [-instance] _root_.OAI.BoltzmannNonuniqueness.ChartKernel.offAxis_sFinite _root_.OAI.BoltzmannNonuniqueness.EuclideanFlight.sourcePullback_finite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.characteristicGainKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.hotKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.mixedKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.retainedKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.coldCylinderVolume_finite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.copyColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.mainCoreKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.selectedColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCoreSheet.dilatedColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCoreSheet.kineticColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.PeriodicApproximation.fiberMeasure_finite _root_.OAI.BoltzmannNonuniqueness.PositiveIteration.awayOriginKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.PositiveIteration.nearOriginKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamNormalCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamNormalRetainedKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.dampedCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.densityScaledCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalBeamKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalCollision_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalPhysicalEvent_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalWindowEvent_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.physicalEventMeasure_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.scaledBeamNormalKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.WeakTime.phaseEndpointKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.WeakTime.phaseIncrement_finite _root_.OAI.BoltzmannNonuniqueness.WeakTime.phaseSeed_sFinite _root_.OAI.BoltzmannNonuniqueness.WeakTime.residenceKernel_sFinite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

/-! # Time clamping of the reconstructed cold family -/

noncomputable section

open MeasureTheory

namespace BoltzmannNonuniqueness.WeightedLocal

theorem mild_all_of_time_clamp {T : ℝ} (hT : 0 ≤ T) (L : ℝ)
    {f : ℝ × JetPrototype.Phase → ℝ} {f₀ : JetPrototype.Phase → ℝ}
    {g : ℝ × JetPrototype.Phase → ℝ}
    (hf : ∀ u, f (PositiveIntegral.time T u.1,u.2) = f u)
    (he : ∀ t ∈ Set.Icc 0 T, (fun p => f (t,p)) =ᵐ[FlightMeasure.phaseVolume]
      (fun p => PositiveIntegral.value T L JetBarrier.flight f₀ g (t,p))) :
    ∀ t, (fun p => f (t,p)) =ᵐ[FlightMeasure.phaseVolume]
      (fun p => PositiveIntegral.value T L JetBarrier.flight f₀ g (t,p)) := by
  intro t
  filter_upwards [he (PositiveIntegral.time T t) (PositiveIntegral.time_bounds hT t)] with p hp
  rw [hf (t,p)] at hp
  exact hp.trans (PositiveIntegral.value_time_clamp hT L f₀ g (t,p))

end BoltzmannNonuniqueness.WeightedLocal

end

end

end OAI
end

section
-- module Solutions.OAIQ080_BZ.Boltzmann_Approximation_PositiveIntegralWindow
attribute [-instance] _root_.OAI.BoltzmannNonuniqueness.ChartKernel.offAxis_sFinite _root_.OAI.BoltzmannNonuniqueness.EuclideanFlight.sourcePullback_finite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.characteristicGainKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.hotKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.mixedKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.retainedKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.coldCylinderVolume_finite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.copyColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.mainCoreKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.selectedColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCoreSheet.dilatedColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCoreSheet.kineticColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.PeriodicApproximation.fiberMeasure_finite _root_.OAI.BoltzmannNonuniqueness.PositiveIteration.awayOriginKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.PositiveIteration.nearOriginKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamNormalCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamNormalRetainedKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.dampedCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.densityScaledCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalBeamKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalCollision_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalPhysicalEvent_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalWindowEvent_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.physicalEventMeasure_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.scaledBeamNormalKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.WeakTime.phaseEndpointKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.WeakTime.phaseIncrement_finite _root_.OAI.BoltzmannNonuniqueness.WeakTime.phaseSeed_sFinite _root_.OAI.BoltzmannNonuniqueness.WeakTime.residenceKernel_sFinite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Restarting an a.e. mild equation on a bounded time window -/

noncomputable section

open MeasureTheory Set

namespace BoltzmannNonuniqueness.PositiveIntegral

theorem measurable_window (s U : ℝ) {f : ℝ × JetPrototype.Phase → ℝ}
    (hfm : Measurable f) : Measurable (window s U f) := by
  apply hfm.comp
  unfold time
  fun_prop

theorem window_clamped {U : ℝ} (hU : 0 ≤ U) (s : ℝ)
    (f : ℝ × JetPrototype.Phase → ℝ) (u : ℝ × JetPrototype.Phase) :
    window s U f (time U u.1,u.2) = window s U f u := by
  change f (s+time U (time U u.1),u.2) = _
  rw [PhaseEssSup.time_idempotent hU]
  rfl

theorem window_mild_ae {T L S s U : ℝ} (hT : 0 ≤ T) (hL : 0 ≤ L)
    (hs : 0 ≤ s) (hU : 0 ≤ U) (hsU : s+U ≤ T)
    {f : ℝ × JetPrototype.Phase → ℝ} {f₀ : JetPrototype.Phase → ℝ}
    {g : ℝ × JetPrototype.Phase → ℝ}
    (hgm : Measurable g) (hg : ∀ u, |g u| ≤ S)
    (he : ∀ t ∈ Icc 0 T, (fun p => f (t,p)) =ᵐ[FlightMeasure.phaseVolume]
      (fun p => value T L JetBarrier.flight f₀ g (t,p))) :
    ∀ t, (fun p => window s U f (t,p)) =ᵐ[FlightMeasure.phaseVolume]
      (fun p => value U L JetBarrier.flight (fun p => f (s,p)) (window s U g) (t,p)) := by
  apply WeightedLocal.mild_all_of_time_clamp hU L (window_clamped hU s f)
  intro t ht
  have hst : s ≤ s+t := by linarith [ht.1]
  have htop : s+t ≤ T := by linarith [ht.2]
  have hi := (FlightMeasure.flight_measurePreserving (-t)).quasiMeasurePreserving.ae
    (he s ⟨hs,by linarith⟩)
  filter_upwards [he (s+t) ⟨by linarith,htop⟩,hi] with p hp hip
  change f (s+time U t,p) = _
  rw [GaussianLocal.time_eq ht,hp]
  have hr := restart hT hL hs hst htop f₀ hgm hg p
  have hsimp : s-(s+t) = -t := by ring
  have hsub : s+t-s = t := by ring
  rw [hsimp,← hip,hsub] at hr
  rw [hr]
  have hv := shifted_value (s := s) (t := s+t)
    (show s+t-s ∈ Icc 0 U by simpa only [hsub] using ht) L
    (fun p => f (s,p)) (window s U g) p
  rw [hsub,hsimp] at hv
  rw [hv]
  congr 1
  apply intervalIntegral.integral_congr
  intro r hrr
  rw [uIcc_of_le hst] at hrr
  change Real.exp (-L*(s+t-r))*g (r,JetBarrier.flight (r-(s+t)) p) =
    Real.exp (-L*(s+t-r))*g (s+time U (r-s),JetBarrier.flight (r-(s+t)) p)
  rw [GaussianLocal.time_eq (show r-s ∈ Icc 0 U by constructor <;> linarith [hrr.1,hrr.2,ht.2])]
  rw [add_sub_cancel]

end BoltzmannNonuniqueness.PositiveIntegral

end

end OAI
end

section
-- module Solutions.OAIQ080_BZ.Boltzmann_Branching_ClampedMildAE
attribute [-instance] _root_.OAI.BoltzmannNonuniqueness.ChartKernel.offAxis_sFinite _root_.OAI.BoltzmannNonuniqueness.EuclideanFlight.sourcePullback_finite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.characteristicGainKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.hotKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.mixedKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.retainedKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.coldCylinderVolume_finite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.copyColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.mainCoreKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.selectedColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCoreSheet.dilatedColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCoreSheet.kineticColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.PeriodicApproximation.fiberMeasure_finite _root_.OAI.BoltzmannNonuniqueness.PositiveIteration.awayOriginKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.PositiveIteration.nearOriginKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamNormalCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamNormalRetainedKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.dampedCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.densityScaledCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalBeamKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalCollision_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalPhysicalEvent_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalWindowEvent_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.physicalEventMeasure_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.scaledBeamNormalKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.WeakTime.phaseEndpointKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.WeakTime.phaseIncrement_finite _root_.OAI.BoltzmannNonuniqueness.WeakTime.phaseSeed_sFinite _root_.OAI.BoltzmannNonuniqueness.WeakTime.residenceKernel_sFinite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Extending a mild representative constantly beyond its time interval -/

noncomputable section

open MeasureTheory Set

namespace BoltzmannNonuniqueness.WeightedLocal

theorem mildAE_all_times {q b L T : ℝ} (hT : 0 ≤ T) {f₀ : JetPrototype.Phase → ℝ}
    {F : ℝ × JetPrototype.Phase → ℝ} (hF : MildAE q b L T f₀ F) :
    ∀ t, (fun p => clampTime T F (t,p)) =ᵐ[FlightMeasure.phaseVolume]
      (fun p => PositiveIntegral.value T L JetBarrier.flight f₀
        (forcing q b L (clampTime T F)) (t,p)) := by
  have hs : ∀ r ∈ Icc 0 T, ∀ p,
      forcing q b L (clampTime T F) (r,p) = forcing q b L F (r,p) := by
    intro r hr p
    rw [forcing_clampTime,GaussianLocal.time_eq hr]
  intro t
  filter_upwards [hF (PositiveIntegral.time T t) (PositiveIntegral.time_bounds hT t)] with p hp
  change F (PositiveIntegral.time T t,p) = _
  rw [PositiveIntegral.value_eq_of_time_eq hT L f₀ hs (t,p)]
  rw [← PositiveIntegral.value_time_clamp hT L f₀ (forcing q b L F) (t,p)]
  exact hp

end BoltzmannNonuniqueness.WeightedLocal

end

end OAI
end

section
-- module Solutions.OAIQ080_BZ.Boltzmann_Branching_SliceUniformLimit
attribute [-instance] _root_.OAI.BoltzmannNonuniqueness.ChartKernel.offAxis_sFinite _root_.OAI.BoltzmannNonuniqueness.EuclideanFlight.sourcePullback_finite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.characteristicGainKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.hotKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.mixedKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.retainedKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.coldCylinderVolume_finite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.copyColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.mainCoreKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.selectedColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCoreSheet.dilatedColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCoreSheet.kineticColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.PeriodicApproximation.fiberMeasure_finite _root_.OAI.BoltzmannNonuniqueness.PositiveIteration.awayOriginKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.PositiveIteration.nearOriginKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamNormalCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamNormalRetainedKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.dampedCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.densityScaledCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalBeamKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalCollision_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalPhysicalEvent_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalWindowEvent_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.physicalEventMeasure_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.scaledBeamNormalKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.WeakTime.phaseEndpointKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.WeakTime.phaseIncrement_finite _root_.OAI.BoltzmannNonuniqueness.WeakTime.phaseSeed_sFinite _root_.OAI.BoltzmannNonuniqueness.WeakTime.residenceKernel_sFinite
attribute [-simp] _root_.OAI.BoltzmannNonuniqueness.EuclideanFlight.phaseEquiv_snd _root_.OAI.BoltzmannNonuniqueness.timeTranslation_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Bounded measurable limits with uniform a.e. control on every time slice -/

noncomputable section

open MeasureTheory Filter
open scoped Topology

namespace BoltzmannNonuniqueness

theorem exists_slice_uniform_limit {R : ℝ} (hR : 0 ≤ R)
    {F : ℕ → ℝ × JetPrototype.Phase → ℝ} {a : ℕ → ℝ}
    (hFm : ∀ n, Measurable (F n)) (hF : ∀ n u, 0 ≤ F n u ∧ F n u ≤ R)
    (ha : ∀ n, 0 ≤ a n) (ha0 : Tendsto a atTop (𝓝 0))
    (hclose : ∀ n m t, ∀ᵐ p ∂FlightMeasure.phaseVolume,
      |F n (t,p)-F m (t,p)| ≤ a n+a m) :
    ∃ G : ℝ × JetPrototype.Phase → ℝ, Measurable G ∧ (∀ u, 0 ≤ G u ∧ G u ≤ R) ∧
      (∀ n t, ∀ᵐ p ∂FlightMeasure.phaseVolume, |F n (t,p)-G (t,p)| ≤ a n) ∧
      ∀ v : (ℝ × JetPrototype.Phase) → ℝ × JetPrototype.Phase,
        (∀ n u, F n (v u) = F n u) → ∀ u, G (v u) = G u := by
  classical
  let P (u : ℝ × JetPrototype.Phase) := ∀ n m, |F n u-F m u| ≤ a n+a m
  let H (n : ℕ) (u : ℝ × JetPrototype.Phase) := if P u then F n u else 0
  have hPm : MeasurableSet {u | P u} := by
    simp only [P,Set.ofPred_forall]
    exact MeasurableSet.iInter (fun n => MeasurableSet.iInter (fun m =>
      measurableSet_le ((hFm n).sub (hFm m)).abs measurable_const))
  have hHm (n) : Measurable (H n) := (hFm n).ite hPm measurable_const
  have hHb (n) (u) : 0 ≤ H n u ∧ H n u ≤ R := by
    dsimp [H]; split_ifs
    · exact hF n u
    · exact ⟨le_rfl,hR⟩
  have hHH (n m) (u) : |H n u-H m u| ≤ a n+a m := by
    by_cases hu : P u
    · simpa only [H,ite_eq_left hu] using hu n m
    · simpa only [H,ite_eq_right hu,sub_self,abs_zero] using add_nonneg (ha n) (ha m)
  have hCauchy (u) : CauchySeq (fun n => H n u) := by
    apply Metric.cauchySeq_iff.mpr
    intro ε hε
    have he : ∀ᶠ n in atTop, a n < ε/2 := (tendsto_order.mp ha0).2 _ (by linarith)
    obtain ⟨N,hN⟩ := eventually_atTop.mp he
    refine ⟨N,fun n hn m hm => ?_⟩
    rw [Real.dist_eq]
    exact (hHH n m u).trans_lt (by linarith [hN n hn,hN m hm])
  have hex (u) : ∃ x : ℝ, Tendsto (fun n => H n u) atTop (𝓝 x) :=
    cauchySeq_tendsto_of_complete (hCauchy u)
  let G (u : ℝ × JetPrototype.Phase) := Classical.choose (hex u)
  have hGlim (u) : Tendsto (fun n => H n u) atTop (𝓝 (G u)) := Classical.choose_spec (hex u)
  have hGm : Measurable G := measurable_of_tendsto_metrizable hHm (tendsto_pi_nhds.mpr hGlim)
  have hGb (u) : 0 ≤ G u ∧ G u ≤ R :=
    ⟨ge_of_tendsto' (hGlim u) (fun n => (hHb n u).1),
      le_of_tendsto' (hGlim u) (fun n => (hHb n u).2)⟩
  have hHG (n) (u) : |H n u-G u| ≤ a n := by
    have h := le_of_tendsto_of_tendsto' ((tendsto_const_nhds.sub (hGlim u)).abs)
      (tendsto_const_nhds.add ha0) (fun m => hHH n m u)
    simpa only [add_zero] using h
  refine ⟨G,hGm,hGb,?_,?_⟩
  · intro n t
    have hPa : ∀ᵐ p ∂FlightMeasure.phaseVolume, P (t,p) :=
      ae_all_iff.mpr (fun k => ae_all_iff.mpr (fun m => hclose k m t))
    filter_upwards [hPa] with p hp
    simpa only [H,ite_eq_left hp] using hHG n (t,p)
  · intro v hv u
    have hPv : P (v u) ↔ P u := by
      simp only [P,hv]
    have hHv (n) : H n (v u) = H n u := by
      by_cases hp : P u
      · simp only [H,ite_eq_left hp,ite_eq_left (hPv.mpr hp),hv]
      · simp only [H,ite_eq_right hp,ite_eq_right (mt hPv.mp hp)]
    exact tendsto_nhds_unique (hGlim (v u)) (by simpa only [hHv] using hGlim u)

end BoltzmannNonuniqueness

end

end OAI
end

section
-- module Solutions.OAIQ080_BZ.Boltzmann_Branching_WeightedJetStability
attribute [-instance] _root_.OAI.BoltzmannNonuniqueness.ChartKernel.offAxis_sFinite _root_.OAI.BoltzmannNonuniqueness.EuclideanFlight.sourcePullback_finite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.characteristicGainKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.hotKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.mixedKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.retainedKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.coldCylinderVolume_finite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.copyColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.mainCoreKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.selectedColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCoreSheet.dilatedColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCoreSheet.kineticColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.PeriodicApproximation.fiberMeasure_finite _root_.OAI.BoltzmannNonuniqueness.PositiveIteration.awayOriginKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.PositiveIteration.nearOriginKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamNormalCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamNormalRetainedKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.dampedCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.densityScaledCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalBeamKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalCollision_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalPhysicalEvent_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalWindowEvent_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.physicalEventMeasure_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.scaledBeamNormalKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.WeakTime.phaseEndpointKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.WeakTime.phaseIncrement_finite _root_.OAI.BoltzmannNonuniqueness.WeakTime.phaseSeed_sFinite _root_.OAI.BoltzmannNonuniqueness.WeakTime.residenceKernel_sFinite
attribute [-simp] _root_.OAI.BoltzmannNonuniqueness.EuclideanFlight.phaseEquiv_snd _root_.OAI.BoltzmannNonuniqueness.timeTranslation_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

/-! # Time windows for total and colored cutoff mild equations -/

noncomputable section

open MeasureTheory Set
open BoltzmannNonuniqueness.PositiveIntegral (window)

namespace BoltzmannNonuniqueness.WeightedLocal

theorem MildAE.window {q b L T R s U : ℝ}
    (hq : q < 2) (hb : 0 ≤ b) (hL : 0 ≤ L) (hT : 0 ≤ T) (hR : 0 ≤ R)
    (hloss : R*CutoffLipschitz.frequencyConstant q b ≤ L)
    (hs : 0 ≤ s) (hU : 0 ≤ U) (hsU : s+U ≤ T)
    {F : ℝ × JetPrototype.Phase → ℝ} {f₀ : JetPrototype.Phase → ℝ}
    (hFm : Measurable F) (hF : ∀ u, 0 ≤ F u ∧ F u ≤ R) (he : MildAE q b L T f₀ F) :
    ∀ t, (fun p => window s U F (t,p)) =ᵐ[FlightMeasure.phaseVolume]
      (fun p => PositiveIntegral.value U L JetBarrier.flight (fun p => F (s,p))
        (forcing q b L (window s U F)) (t,p)) := by
  have hbnd (u) : |forcing q b L F u| ≤ HotApplication.realBound q*R^2+L*R := by
    have h := HotRepresentative.source_bounds hq hb hR hloss
      (GaussianLocal.measurable_state hFm) (fun p => hF (p.1.1,(p.1.2,p.2))) ((u.1,u.2.1),u.2.2)
    change 0 ≤ forcing q b L F u ∧ forcing q b L F u ≤ _ at h
    rw [abs_of_nonneg h.1]
    exact h.2
  exact PositiveIntegral.window_mild_ae hT hL hs hU hsU (measurable_forcing hFm q b L) hbnd he

theorem ColdMildAE.window {q b L T R s U : ℝ}
    (hq : q < 2) (hb : 0 ≤ b) (hL : 0 ≤ L) (hT : 0 ≤ T) (hR : 0 ≤ R)
    (hloss : R*CutoffLipschitz.frequencyConstant q b ≤ L)
    (hs : 0 ≤ s) (hU : 0 ≤ U) (hsU : s+U ≤ T)
    {F c : ℝ × JetPrototype.Phase → ℝ} {c₀ : JetPrototype.Phase → ℝ}
    (hFm : Measurable F) (hcm : Measurable c)
    (hF : ∀ u, 0 ≤ F u ∧ F u ≤ R) (hc : ∀ u, 0 ≤ c u ∧ c u ≤ R)
    (he : ColdMildAE q b L T F c₀ c) :
    ∀ t, (fun p => window s U c (t,p)) =ᵐ[FlightMeasure.phaseVolume]
      (fun p => PositiveIntegral.value U L JetBarrier.flight (fun p => c (s,p))
        (coldForcing q b L (window s U F) (window s U c)) (t,p)) := by
  have hbnd (u) : |coldForcing q b L F c u| ≤ HotApplication.realBound q*R^2+L*R := by
    have h := HotRepresentative.coldSource_bounds hq hb hR hloss
      (GaussianLocal.measurable_state hFm) (GaussianLocal.measurable_state hcm)
      (fun p => hF (p.1.1,(p.1.2,p.2))) (fun p => hc (p.1.1,(p.1.2,p.2))) ((u.1,u.2.1),u.2.2)
    change 0 ≤ coldForcing q b L F c u ∧ coldForcing q b L F c u ≤ _ at h
    rw [abs_of_nonneg h.1]
    exact h.2
  exact PositiveIntegral.window_mild_ae hT hL hs hU hsU (measurable_coldForcing hFm hcm q b L) hbnd he

end BoltzmannNonuniqueness.WeightedLocal

end

end

section

/-! # Quantitative local dependence for a.e. mild representatives -/

noncomputable section

open MeasureTheory MeasureTheory.Measure

namespace BoltzmannNonuniqueness.WeightedLocal

theorem normalized_difference_ae {q b L T R I : ℝ} (hq : q < 2) (hb : 0 ≤ b)
    (hL : 0 ≤ L) (hT : 0 ≤ T) (hR : 0 ≤ R) (hI : 0 ≤ I)
    (hloss : R*CutoffLipschitz.frequencyConstant q b ≤ L)
    (hsmall : T*(2*R*(HotApplication.realBound q+CutoffLipschitz.frequencyConstant q b)+L) < 1)
    {f₀ g₀ : JetPrototype.Phase → ℝ}
    (hseed : ∀ᵐ p ∂FlightMeasure.phaseVolume, |f₀ p-g₀ p| ≤ I)
    {F G : ℝ × JetPrototype.Phase → ℝ} (hFm : Measurable F) (hGm : Measurable G)
    (hF : ∀ u, 0 ≤ F u ∧ F u ≤ R) (hG : ∀ u, 0 ≤ G u ∧ G u ≤ R)
    (hFeq : ∀ t, (fun p => F (t,p)) =ᵐ[FlightMeasure.phaseVolume]
      (fun p => PositiveIntegral.value T L JetBarrier.flight f₀ (forcing q b L F) (t,p)))
    (hGeq : ∀ t, (fun p => G (t,p)) =ᵐ[FlightMeasure.phaseVolume]
      (fun p => PositiveIntegral.value T L JetBarrier.flight g₀ (forcing q b L G) (t,p))) :
    ∀ t, ∀ᵐ p ∂FlightMeasure.phaseVolume, |F (t,p)-G (t,p)| ≤
      I/(1-T*(2*R*(HotApplication.realBound q+CutoffLipschitz.frequencyConstant q b)+L)) := by
  let K := 2*R*(HotApplication.realBound q+CutoffLipschitz.frequencyConstant q b)+L
  let S := HotApplication.realBound q*R^2+L*R
  let D := SpaceTimeEssSup.size (fun u => F u-G u)
  have hK : 0 ≤ K := by
    have := (HotApplication.realBound_pos q).le
    have := CutoffLipschitz.frequencyConstant_nonneg hb q
    dsimp [K]
    positivity
  have hD : 0 ≤ D := SpaceTimeEssSup.nonneg _
  have habs (u) : |F u-G u| ≤ 2*R :=
    (abs_sub _ _).trans (by rw [abs_of_nonneg (hF u).1,abs_of_nonneg (hG u).1]; linarith [(hF u).2,(hG u).2])
  have hFD := SpaceTimeEssSup.ae_abs_le_size (hFm.sub hGm) habs
  have hdiff : ∀ᵐ u ∂spacetimeVolume, |forcing q b L F u-forcing q b L G u| ≤ K*D :=
    forcing_difference_ae hq hb hL hR hD hFm hGm hF hG hFD
  have hsrc (U : ℝ × JetPrototype.Phase → ℝ) (hUm : Measurable U)
      (hU : ∀ u, 0 ≤ U u ∧ U u ≤ R) (u) : |forcing q b L U u| ≤ S := by
    have h := HotRepresentative.source_bounds hq hb hR hloss (GaussianLocal.measurable_state hUm)
      (fun p => hU (p.1.1,(p.1.2,p.2))) ((u.1,u.2.1),u.2.2)
    change 0 ≤ forcing q b L U u ∧ forcing q b L U u ≤ S at h
    rw [abs_of_nonneg h.1]
    exact h.2
  have hbnd (t : ℝ) : ∀ᵐ p ∂FlightMeasure.phaseVolume, |F (t,p)-G (t,p)| ≤ I+T*(K*D) := by
    filter_upwards [hFeq t,hGeq t,
      PositiveIntegral.value_difference_initial_ae_all hT hL (mul_nonneg hK hD) hI hseed
        (measurable_forcing hFm q b L) (measurable_forcing hGm q b L)
        (hsrc F hFm hF) (hsrc G hGm hG) hdiff t] with p hf hg hp
    rwa [hf,hg]
  have hspace : ∀ᵐ u ∂spacetimeVolume, |F u-G u| ≤ I+T*(K*D) :=
    (ae_prod_iff_ae_ae (measurableSet_le (hFm.sub hGm).abs measurable_const)).mpr (ae_of_all _ hbnd)
  have hineq : D ≤ I+T*(K*D) :=
    SpaceTimeEssSup.size_le_ae (hFm.sub hGm) (by positivity) hspace
  have hden : 0 < 1-T*K := by dsimp [K] <;> linarith
  have hDQ : D ≤ I/(1-T*K) := (le_div_iff₀ hden).mpr (by nlinarith [hineq])
  have hmul := mul_le_mul_of_nonneg_left hDQ (mul_nonneg hT hK)
  have hQ : I/(1-T*K)*(1-T*K) = I := div_mul_cancel₀ I hden.ne'
  have hfinal : I+T*(K*D) ≤ I/(1-T*K) := by nlinarith
  intro t
  exact (hbnd t).mono (fun p hp => hp.trans hfinal)

end BoltzmannNonuniqueness.WeightedLocal

end

end

section

/-! # The hot remainder of a countable almost-everywhere mild cold family -/

noncomputable section

open MeasureTheory Set

namespace BoltzmannNonuniqueness.WeightedLocal

variable {I : Type*} [Countable I]

theorem family_hot_mildAE {q b L T R : ℝ} (hq : q < 2) (hb : 0 ≤ b)
    (hL : 0 ≤ L) (hT : 0 ≤ T) (hR : 0 ≤ R)
    (hloss : R*CutoffLipschitz.frequencyConstant q b ≤ L)
    {F : ℝ × JetPrototype.Phase → ℝ} {c : I → ℝ × JetPrototype.Phase → ℝ}
    {F₀ : JetPrototype.Phase → ℝ} {c₀ : I → JetPrototype.Phase → ℝ}
    (hFm : Measurable F) (hcm : ∀ i, Measurable (c i))
    (hF : ∀ u, 0 ≤ F u ∧ F u ≤ R) (hcn : ∀ i u, 0 ≤ c i u)
    (hSum : ∀ s : Finset I, ∀ u, ∑ i ∈ s, c i u ≤ F u)
    (hc₀n : ∀ i p, 0 ≤ c₀ i p)
    (hSum₀ : ∀ s : Finset I, ∀ p, ∑ i ∈ s, c₀ i p ≤ F₀ p)
    (hFeq : MildAE q b L T F₀ F) (hceq : ∀ i, ColdMildAE q b L T F (c₀ i) (c i)) :
    ∀ t ∈ Icc 0 T, (fun p => F (t,p)-∑' i, c i (t,p)) =ᵐ[FlightMeasure.phaseVolume]
      (fun p => PositiveIntegral.value T L JetBarrier.flight
        (fun x => F₀ x-∑' i, c₀ i x) (remainderForcing q b L F c) (t,p)) := by
  classical
  let G (i : I) := coldForcing q b L F (c i)
  let S := HotApplication.realBound q*R^2+L*R
  have hcb (i) (u) : 0 ≤ c i u ∧ c i u ≤ R := by
    refine ⟨hcn i u,?_⟩
    have hs := hSum {i} u
    simpa only [Finset.sum_singleton] using hs.trans (hF u).2
  have hgm (i) : Measurable (G i) := measurable_coldForcing hFm (hcm i) q b L
  have hgb (i) (u) : 0 ≤ G i u ∧ G i u ≤ S :=
    HotRepresentative.coldSource_bounds hq hb hR hloss (GaussianLocal.measurable_state hFm)
      (GaussianLocal.measurable_state (hcm i)) (fun p => hF (p.1.1,(p.1.2,p.2)))
      (fun p => hcb i (p.1.1,(p.1.2,p.2))) _
  have hfb (u) : 0 ≤ forcing q b L F u ∧ forcing q b L F u ≤ S :=
    HotRepresentative.source_bounds hq hb hR hloss (GaussianLocal.measurable_state hFm)
      (fun p => hF (p.1.1,(p.1.2,p.2))) _
  have hgsum (s : Finset I) (u) : (∑ i ∈ s, G i u) ≤ forcing q b L F u :=
    HotRepresentative.finite_sum_coldSource_le hq hb hloss s
      (fun i _ => GaussianLocal.measurable_state (hcm i)) (GaussianLocal.measurable_state hFm)
      (fun i _ p => hcb i (p.1.1,(p.1.2,p.2))) (fun p => hF (p.1.1,(p.1.2,p.2)))
      (fun p => hSum s (p.1.1,(p.1.2,p.2))) _
  have hgs (u) : Summable (fun i => G i u) :=
    summable_of_sum_le (fun i => (hgb i u).1) (fun s => hgsum s u)
  have hgBound (u) : (∑' i, G i u) ≤ forcing q b L F u :=
    Real.tsum_le_of_sum_le (fun i => (hgb i u).1) (fun s => hgsum s u)
  have hga (u) : |∑' i, G i u| ≤ S := by
    rw [abs_of_nonneg (tsum_nonneg (fun i => (hgb i u).1))]
    exact (hgBound u).trans (hfb u).2
  intro t ht
  have hcae : ∀ᵐ p ∂FlightMeasure.phaseVolume, ∀ i, c i (t,p) =
      PositiveIntegral.value T L JetBarrier.flight (c₀ i) (G i) (t,p) :=
    ae_all_iff.mpr (fun i => hceq i t ht)
  filter_upwards [hFeq t ht,hcae] with p hfp hcp
  have hs := PositiveIntegral.hasSum_value hT hL GaussianLocal.measurable_flight c₀
    (fun p => summable_of_sum_le (fun i => hc₀n i p) (fun s => hSum₀ s p)) G hgm hgb hgs
    (fun u => (hgBound u).trans (hfb u).2) (t,p)
  have he : (fun i => PositiveIntegral.value T L JetBarrier.flight (c₀ i) (G i) (t,p)) =
      (fun i => c i (t,p)) := funext (fun i => (hcp i).symm)
  rw [he] at hs
  rw [hfp,hs.tsum_eq]
  exact PositiveIntegral.value_sub hT hL (measurable_forcing hFm q b L) (Measurable.tsum hgm)
    (fun u => by rw [abs_of_nonneg (hfb u).1]; exact (hfb u).2) hga F₀ (fun p => ∑' i, c₀ i p) (t,p)

end BoltzmannNonuniqueness.WeightedLocal

end

end

section

/-! # Uniqueness on each weighted local construction interval -/

noncomputable section

open MeasureTheory

namespace BoltzmannNonuniqueness.WeightedLocal

theorem normalized_unique {q b L T R : ℝ} (hq : q < 2) (hb : 0 ≤ b)
    (hL : 0 ≤ L) (hT : 0 ≤ T) (hR : 0 ≤ R)
    (hloss : R*CutoffLipschitz.frequencyConstant q b ≤ L)
    (hsmall : T*(2*R*(HotApplication.realBound q+CutoffLipschitz.frequencyConstant q b)+L) < 1)
    (f₀ : JetPrototype.Phase → ℝ) {f g : ℝ × JetPrototype.Phase → ℝ}
    (hfm : Measurable f) (hgm : Measurable g)
    (hf : ∀ z, 0 ≤ f z ∧ f z ≤ R) (hg : ∀ z, 0 ≤ g z ∧ g z ≤ R)
    (hfeq : ∀ z, f z = PositiveIntegral.value T L JetBarrier.flight f₀ (forcing q b L f) z)
    (hgeq : ∀ z, g z = PositiveIntegral.value T L JetBarrier.flight f₀ (forcing q b L g) z) : f = g := by
  funext z
  have h := normalized_difference hq hb hL hT hR (le_refl 0) hloss hsmall
    (fun p => by simp only [sub_self,abs_zero,le_refl]) hfm hgm hf hg hfeq hgeq z
  rw [zero_div] at h
  exact sub_eq_zero.mp (abs_nonpos_iff.mp h)

end BoltzmannNonuniqueness.WeightedLocal

end

end

section

/-! # Uniform dependence on all prefixes of a fixed bounded interval -/

noncomputable section

open MeasureTheory Set
open BoltzmannNonuniqueness.PositiveIntegral (window)

namespace BoltzmannNonuniqueness.WeightedLocal

theorem bounded_interval_stability_uniform {q b L T R : ℝ}
    (hq : q < 2) (hb : 0 ≤ b) (hL : 0 ≤ L) (_hT : 0 ≤ T) (hR : 0 ≤ R)
    (hloss : R*CutoffLipschitz.frequencyConstant q b ≤ L) :
    ∃ C : ℝ, 0 < C ∧ ∀ {U : ℝ}, 0 ≤ U → U ≤ T → ∀ {A : ℝ}, 0 ≤ A →
      ∀ {F G : ℝ × JetPrototype.Phase → ℝ} {F₀ G₀ : JetPrototype.Phase → ℝ},
      Measurable F → Measurable G →
      (∀ u, 0 ≤ F u ∧ F u ≤ R) → (∀ u, 0 ≤ G u ∧ G u ≤ R) →
      MildAE q b L U F₀ F → MildAE q b L U G₀ G →
      (∀ᵐ p ∂FlightMeasure.phaseVolume, |F₀ p-G₀ p| ≤ A) →
      ∀ t ∈ Icc 0 U, ∀ᵐ p ∂FlightMeasure.phaseVolume, |F (t,p)-G (t,p)| ≤ C*A := by
  let K := 2*R*(HotApplication.realBound q+CutoffLipschitz.frequencyConstant q b)+L
  have hK : 0 ≤ K := by
    have := (HotApplication.realBound_pos q).le
    have := CutoffLipschitz.frequencyConstant_nonneg hb q
    dsimp [K]
    positivity
  let δ := 1/(2*(K+1))
  have hδ : 0 < δ := div_pos zero_lt_one (by positivity)
  have hδK : δ*K < 1/2 := by
    have hd : 0 < 2*(K+1) := by positivity
    dsimp [δ]
    rw [div_mul_eq_mul_div,div_lt_iff₀ hd]
    nlinarith
  obtain ⟨n,hn⟩ := exists_nat_ge (T/δ)
  have hreach : T ≤ (n:ℝ)*δ := (div_le_iff₀ hδ).mp hn
  refine ⟨2^n,by positivity,?_⟩
  intro U hU hUT A hA F G F₀ G₀ hFm hGm hF hG hFe hGe hseed
  have hreachU : U ≤ (n:ℝ)*δ := hUT.trans hreach
  have hzero : ∀ᵐ p ∂FlightMeasure.phaseVolume, |F (0,p)-G (0,p)| ≤ A := by
    filter_upwards [hFe.initial_ae hU,hGe.initial_ae hU,hseed] with p hf hg hp
    simpa only [hf,hg] using hp
  have hsteps : ∀ j : ℕ, ∀ t ∈ Icc 0 (min ((j:ℝ)*δ) U),
      ∀ᵐ p ∂FlightMeasure.phaseVolume, |F (t,p)-G (t,p)| ≤ (2:ℝ)^j*A := by
    intro j
    induction j with
    | zero =>
      intro t ht
      have htzero : t ≤ 0 := by simpa only [Nat.cast_zero,zero_mul,min_eq_left hU] using ht.2
      have ht0 : t = 0 := le_antisymm htzero ht.1
      subst t
      simpa only [pow_zero,one_mul] using hzero
    | succ j ih =>
      intro t ht
      have htT : t ≤ U := ht.2.trans (min_le_right _ _)
      have htj : t ≤ ((j+1:ℕ):ℝ)*δ := ht.2.trans (min_le_left _ _)
      have hAj : 0 ≤ (2:ℝ)^j*A := mul_nonneg (pow_nonneg (by norm_num) j) hA
      by_cases hprefix : t ≤ min ((j:ℝ)*δ) U
      · exact (ih t ⟨ht.1,hprefix⟩).mono (fun p hp => hp.trans (by
          rw [pow_succ]
          nlinarith))
      · let s : ℝ := (j:ℝ)*δ
        have hs : 0 ≤ s := mul_nonneg (Nat.cast_nonneg j) hδ.le
        have hst : s < t := by
          have hnot : ¬ t ≤ (j:ℝ)*δ := fun h => hprefix (le_min h htT)
          exact lt_of_not_ge hnot
        have hsT : s ≤ U := hst.le.trans htT
        have hinit := ih s ⟨hs,le_min le_rfl hsT⟩
        let V := t-s
        have hV : 0 ≤ V := sub_nonneg.mpr hst.le
        have hUδ : V ≤ δ := by
          dsimp [V,s]
          rw [Nat.cast_add,Nat.cast_one] at htj
          nlinarith
        have hUK : V*K < 1/2 := lt_of_le_of_lt (mul_le_mul_of_nonneg_right hUδ hK) hδK
        have hsmall : V*K < 1 := hUK.trans (by norm_num)
        have hsU : s+V ≤ U := by dsimp [V] <;> linarith
        have hfwin := MildAE.window hq hb hL hU hR hloss hs hV hsU hFm hF hFe
        have hgwin := MildAE.window hq hb hL hU hR hloss hs hV hsU hGm hG hGe
        have he := normalized_difference_ae hq hb hL hV hR hAj hloss hsmall hinit
          (PositiveIntegral.measurable_window s V hFm) (PositiveIntegral.measurable_window s V hGm)
          (fun u => hF _) (fun u => hG _) hfwin hgwin V
        have hfac : ((2:ℝ)^j*A)/(1-V*K) ≤ (2:ℝ)^(j+1)*A := by
          apply (div_le_iff₀ (by linarith : 0 < 1-V*K)).mpr
          rw [pow_succ]
          nlinarith
        filter_upwards [he] with p hp
        have hUtime : PositiveIntegral.time V V = V := GaussianLocal.time_eq ⟨hV,le_rfl⟩
        change |F (s+PositiveIntegral.time V V,p)-G (s+PositiveIntegral.time V V,p)| ≤ _ at hp
        rw [hUtime,show s+V=t by dsimp [V]; ring] at hp
        exact hp.trans hfac
  intro t ht
  exact hsteps n t ⟨ht.1,by simpa only [min_eq_right hreachU] using ht.2⟩

end BoltzmannNonuniqueness.WeightedLocal

end

end

section

/-! # Closure of bounded positive mild solutions under uniform a.e. approximation -/

noncomputable section

open MeasureTheory MeasureTheory.Measure Filter
open scoped Topology

namespace BoltzmannNonuniqueness.WeightedLocal

theorem exists_mild_limit {q b L T R : ℝ} (hq : q < 2) (hb : 0 ≤ b)
    (hL : 0 ≤ L) (hT : 0 ≤ T) (hR : 0 ≤ R)
    (hloss : R*CutoffLipschitz.frequencyConstant q b ≤ L)
    {F : ℕ → ℝ × JetPrototype.Phase → ℝ}
    {f₀ : ℕ → JetPrototype.Phase → ℝ} {g₀ : JetPrototype.Phase → ℝ} {a : ℕ → ℝ}
    (hFm : ∀ n, Measurable (F n)) (hF : ∀ n u, 0 ≤ F n u ∧ F n u ≤ R)
    (ha : ∀ n, 0 ≤ a n) (ha0 : Tendsto a atTop (𝓝 0))
    (hclose : ∀ n m t, ∀ᵐ p ∂FlightMeasure.phaseVolume, |F n (t,p)-F m (t,p)| ≤ a n+a m)
    (hseed : ∀ n, ∀ᵐ p ∂FlightMeasure.phaseVolume, |f₀ n p-g₀ p| ≤ a n)
    (hfix : ∀ n t, (fun p => F n (t,p)) =ᵐ[FlightMeasure.phaseVolume]
      (fun p => PositiveIntegral.value T L JetBarrier.flight (f₀ n) (forcing q b L (F n)) (t,p))) :
    ∃ G : ℝ × JetPrototype.Phase → ℝ, Measurable G ∧ (∀ u, 0 ≤ G u ∧ G u ≤ R) ∧
      (∀ t, (fun p => G (t,p)) =ᵐ[FlightMeasure.phaseVolume]
        (fun p => PositiveIntegral.value T L JetBarrier.flight g₀ (forcing q b L G) (t,p))) ∧
      (∀ n t, ∀ᵐ p ∂FlightMeasure.phaseVolume, |F n (t,p)-G (t,p)| ≤ a n) ∧
      ∀ v : (ℝ × JetPrototype.Phase) → ℝ × JetPrototype.Phase,
        (∀ n u, F n (v u) = F n u) → ∀ u, G (v u) = G u := by
  obtain ⟨G,hGm,hG,hFG,hInv⟩ := exists_slice_uniform_limit hR hFm hF ha ha0 hclose
  let K := 2*R*(HotApplication.realBound q+CutoffLipschitz.frequencyConstant q b)+L
  let S := HotApplication.realBound q*R^2+L*R
  have hK : 0 ≤ K := by
    have := (HotApplication.realBound_pos q).le
    have := CutoffLipschitz.frequencyConstant_nonneg hb q
    dsimp [K]
    positivity
  have hsrc (U : ℝ × JetPrototype.Phase → ℝ) (hUm : Measurable U)
      (hU : ∀ u, 0 ≤ U u ∧ U u ≤ R) (u) : |forcing q b L U u| ≤ S := by
    have h := HotRepresentative.source_bounds hq hb hR hloss
      (GaussianLocal.measurable_state hUm) (fun p => hU (p.1.1,(p.1.2,p.2))) ((u.1,u.2.1),u.2.2)
    change 0 ≤ forcing q b L U u ∧ forcing q b L U u ≤ S at h
    rw [abs_of_nonneg h.1]
    exact h.2
  have hsource (n) : ∀ᵐ u ∂spacetimeVolume,
      |forcing q b L (F n) u-forcing q b L G u| ≤ K*a n :=
    forcing_difference_ae hq hb hL hR (ha n) (hFm n) hGm (hF n) hG
      ((ae_prod_iff_ae_ae (measurableSet_le ((hFm n).sub hGm).abs measurable_const)).mpr
        (ae_of_all _ (hFG n)))
  have hval (n t) := PositiveIntegral.value_difference_initial_ae_all hT hL
    (mul_nonneg hK (ha n)) (ha n) (hseed n)
    (measurable_forcing (hFm n) q b L) (measurable_forcing hGm q b L)
    (hsrc (F n) (hFm n) (hF n)) (hsrc G hGm hG) (hsource n) t
  refine ⟨G,hGm,hG,?_,hFG,hInv⟩
  intro t
  have hbnd (n) : ∀ᵐ p ∂FlightMeasure.phaseVolume,
      |G (t,p)-PositiveIntegral.value T L JetBarrier.flight g₀ (forcing q b L G) (t,p)| ≤
        (2+T*K)*a n := by
    filter_upwards [hFG n t,hfix n t,hval n t] with p hp he hv
    calc
      _ ≤ |G (t,p)-F n (t,p)|+
          |F n (t,p)-PositiveIntegral.value T L JetBarrier.flight g₀ (forcing q b L G) (t,p)| :=
        abs_sub_le _ _ _
      _ ≤ a n+(a n+T*(K*a n)) := by
        rw [abs_sub_comm] at hp
        rw [← he] at hv
        exact add_le_add hp hv
      _ = (2+T*K)*a n := by ring
  filter_upwards [ae_all_iff.mpr hbnd] with p hp
  have hz : Tendsto (fun n => (2+T*K)*a n) atTop (𝓝 0) := by
    simpa only [mul_zero] using tendsto_const_nhds.mul ha0
  have hle := le_of_tendsto_of_tendsto' tendsto_const_nhds hz hp
  exact sub_eq_zero.mp (abs_nonpos_iff.mp hle)

end BoltzmannNonuniqueness.WeightedLocal

end

end

section

/-! # A common positive local time for bounded weighted data -/

noncomputable section

open MeasureTheory

namespace BoltzmannNonuniqueness.WeightedLocalControl

theorem bounds {q b A : ℝ} (hb : 0 ≤ b) (hA : 0 < A) :
    0 ≤ damping q b A ∧ 0 ≤ sourceBound q b A ∧ 0 ≤ lipschitz q b A := by
  have hC := CutoffLipschitz.frequencyConstant_nonneg hb q
  have hG := (HotApplication.realBound_pos q).le
  have hL : 0 ≤ damping q b A := by unfold damping; positivity
  exact ⟨hL, by unfold sourceBound; positivity, by unfold lipschitz; positivity⟩

theorem lifespan_pos {q b A : ℝ} (hb : 0 ≤ b) (hA : 0 < A) : 0 < lifespan q b A := by
  obtain ⟨_,hS,hK⟩ := bounds (q := q) hb hA
  exact lt_min (div_pos hA (by positivity)) (div_pos (by norm_num) (by positivity))

theorem small {q b A : ℝ} (hb : 0 ≤ b) (hA : 0 < A) :
    lifespan q b A*lipschitz q b A < 1 := by
  obtain ⟨_,_,hK⟩ := bounds (q := q) hb hA
  have hT := lifespan_pos (q := q) hb hA
  have h := (le_div_iff₀ (by positivity : 0 < lipschitz q b A+1)).mp
    (min_le_right (A/(sourceBound q b A+1)) ((1/2)/(lipschitz q b A+1)))
  change lifespan q b A*(lipschitz q b A+1) ≤ 1/2 at h
  nlinarith

theorem exists_solution {q b A : ℝ} (hq : q < 2) (hb : 0 ≤ b) (hA : 0 < A)
    {f₀ : JetPrototype.Phase → ℝ} (hf₀m : Measurable f₀)
    (hf₀ : ∀ p, 0 ≤ f₀ p ∧ f₀ p ≤ A) :
    ∃ F : ℝ × JetPrototype.Phase → ℝ, Measurable F ∧
      (∀ z, 0 ≤ F z ∧ F z ≤ 2*A) ∧
      ∀ z, F z = PositiveIntegral.value (lifespan q b A) (damping q b A)
        JetBarrier.flight f₀ (WeightedLocal.forcing q b (damping q b A) F) z := by
  obtain ⟨hL,hS,_⟩ := bounds (q := q) hb hA
  have hT := lifespan_pos (q := q) hb hA
  have h := (le_div_iff₀ (by positivity : 0 < sourceBound q b A+1)).mp
    (min_le_left (A/(sourceBound q b A+1)) ((1/2)/(lipschitz q b A+1)))
  change lifespan q b A*(sourceBound q b A+1) ≤ A at h
  have hball : A+lifespan q b A*sourceBound q b A ≤ 2*A := by nlinarith
  exact WeightedLocal.exists_normalized hq hb hL hT.le hA.le (by positivity) le_rfl hball
    (small hb hA) hf₀m hf₀

end BoltzmannNonuniqueness.WeightedLocalControl

end

end

section

/-! # Uniform dependence on a fixed bounded solution interval -/

noncomputable section

open MeasureTheory Set
open BoltzmannNonuniqueness.PositiveIntegral (window)

namespace BoltzmannNonuniqueness.WeightedLocal

theorem bounded_interval_stability {q b L T R : ℝ}
    (hq : q < 2) (hb : 0 ≤ b) (hL : 0 ≤ L) (hT : 0 ≤ T) (hR : 0 ≤ R)
    (hloss : R*CutoffLipschitz.frequencyConstant q b ≤ L) :
    ∃ C : ℝ, 0 < C ∧ ∀ {A : ℝ}, 0 ≤ A →
      ∀ {F G : ℝ × JetPrototype.Phase → ℝ} {F₀ G₀ : JetPrototype.Phase → ℝ},
      Measurable F → Measurable G →
      (∀ u, 0 ≤ F u ∧ F u ≤ R) → (∀ u, 0 ≤ G u ∧ G u ≤ R) →
      MildAE q b L T F₀ F → MildAE q b L T G₀ G →
      (∀ᵐ p ∂FlightMeasure.phaseVolume, |F₀ p-G₀ p| ≤ A) →
      ∀ t ∈ Icc 0 T, ∀ᵐ p ∂FlightMeasure.phaseVolume, |F (t,p)-G (t,p)| ≤ C*A := by
  let K := 2*R*(HotApplication.realBound q+CutoffLipschitz.frequencyConstant q b)+L
  have hK : 0 ≤ K := by
    have := (HotApplication.realBound_pos q).le
    have := CutoffLipschitz.frequencyConstant_nonneg hb q
    dsimp [K]
    positivity
  let δ := 1/(2*(K+1))
  have hδ : 0 < δ := div_pos zero_lt_one (by positivity)
  have hδK : δ*K < 1/2 := by
    have hd : 0 < 2*(K+1) := by positivity
    dsimp [δ]
    rw [div_mul_eq_mul_div,div_lt_iff₀ hd]
    nlinarith
  obtain ⟨n,hn⟩ := exists_nat_ge (T/δ)
  have hreach : T ≤ (n:ℝ)*δ := (div_le_iff₀ hδ).mp hn
  refine ⟨2^n,by positivity,?_⟩
  intro A hA F G F₀ G₀ hFm hGm hF hG hFe hGe hseed
  have hzero : ∀ᵐ p ∂FlightMeasure.phaseVolume, |F (0,p)-G (0,p)| ≤ A := by
    filter_upwards [hFe.initial_ae hT,hGe.initial_ae hT,hseed] with p hf hg hp
    simpa only [hf,hg] using hp
  have hsteps : ∀ j : ℕ, ∀ t ∈ Icc 0 (min ((j:ℝ)*δ) T),
      ∀ᵐ p ∂FlightMeasure.phaseVolume, |F (t,p)-G (t,p)| ≤ (2:ℝ)^j*A := by
    intro j
    induction j with
    | zero =>
      intro t ht
      have htzero : t ≤ 0 := by simpa only [Nat.cast_zero,zero_mul,min_eq_left hT] using ht.2
      have ht0 : t = 0 := le_antisymm htzero ht.1
      subst t
      simpa only [pow_zero,one_mul] using hzero
    | succ j ih =>
      intro t ht
      have htT : t ≤ T := ht.2.trans (min_le_right _ _)
      have htj : t ≤ ((j+1:ℕ):ℝ)*δ := ht.2.trans (min_le_left _ _)
      have hAj : 0 ≤ (2:ℝ)^j*A := mul_nonneg (pow_nonneg (by norm_num) j) hA
      by_cases hprefix : t ≤ min ((j:ℝ)*δ) T
      · exact (ih t ⟨ht.1,hprefix⟩).mono (fun p hp => hp.trans (by
          rw [pow_succ]
          nlinarith))
      · let s : ℝ := (j:ℝ)*δ
        have hs : 0 ≤ s := mul_nonneg (Nat.cast_nonneg j) hδ.le
        have hst : s < t := by
          have hnot : ¬ t ≤ (j:ℝ)*δ := fun h => hprefix (le_min h htT)
          exact lt_of_not_ge hnot
        have hsT : s ≤ T := hst.le.trans htT
        have hinit := ih s ⟨hs,le_min le_rfl hsT⟩
        let U := t-s
        have hU : 0 ≤ U := sub_nonneg.mpr hst.le
        have hUδ : U ≤ δ := by
          dsimp [U,s]
          rw [Nat.cast_add,Nat.cast_one] at htj
          nlinarith
        have hUK : U*K < 1/2 := lt_of_le_of_lt (mul_le_mul_of_nonneg_right hUδ hK) hδK
        have hsmall : U*K < 1 := hUK.trans (by norm_num)
        have hsU : s+U ≤ T := by dsimp [U] <;> linarith
        have hfwin := MildAE.window hq hb hL hT hR hloss hs hU hsU hFm hF hFe
        have hgwin := MildAE.window hq hb hL hT hR hloss hs hU hsU hGm hG hGe
        have he := normalized_difference_ae hq hb hL hU hR hAj hloss hsmall hinit
          (PositiveIntegral.measurable_window s U hFm) (PositiveIntegral.measurable_window s U hGm)
          (fun u => hF _) (fun u => hG _) hfwin hgwin U
        have hfac : ((2:ℝ)^j*A)/(1-U*K) ≤ (2:ℝ)^(j+1)*A := by
          apply (div_le_iff₀ (by linarith : 0 < 1-U*K)).mpr
          rw [pow_succ]
          nlinarith
        filter_upwards [he] with p hp
        have hUtime : PositiveIntegral.time U U = U := GaussianLocal.time_eq ⟨hU,le_rfl⟩
        change |F (s+PositiveIntegral.time U U,p)-G (s+PositiveIntegral.time U U,p)| ≤ _ at hp
        rw [hUtime,show s+U=t by dsimp [U]; ring] at hp
        exact hp.trans hfac
  intro t ht
  exact hsteps n t ⟨ht.1,by simpa only [min_eq_right hreach] using ht.2⟩

end BoltzmannNonuniqueness.WeightedLocal

end

end

section

/-! # Periodic covariance follows from the constructed local uniqueness -/

noncomputable section

open MeasureTheory
open BoltzmannNonuniqueness.JetPrototype

namespace BoltzmannNonuniqueness.WeightedTranslation

theorem solution_covariance {q b L T R : ℝ} (hq : q < 2) (hb : 0 ≤ b)
    (hL : 0 ≤ L) (hT : 0 ≤ T) (hR : 0 ≤ R)
    (hloss : R*CutoffLipschitz.frequencyConstant q b ≤ L)
    (hsmall : T*(2*R*(HotApplication.realBound q+CutoffLipschitz.frequencyConstant q b)+L) < 1)
    {f₀ : JetPrototype.Phase → ℝ} {F : ℝ × JetPrototype.Phase → ℝ}
    (hFm : Measurable F) (hF : ∀ z, 0 ≤ F z ∧ F z ≤ R)
    (hFeq : ∀ z, F z = PositiveIntegral.value T L JetBarrier.flight f₀ (WeightedLocal.forcing q b L F) z)
    (y : Space) (hseed : ∀ p, f₀ (shift y p) = f₀ p) : pull y F = F := by
  have hseed' : (fun p => f₀ (shift y p)) = f₀ := funext hseed
  have hfix (z) := fixed_point_pull hFeq y z
  rw [hseed'] at hfix
  exact WeightedLocal.normalized_unique hq hb hL hT hR hloss hsmall f₀
    (measurable_pull hFm y) hFm (fun z => hF (z.1,shift y z.2)) hF hfix hFeq

end BoltzmannNonuniqueness.WeightedTranslation

end

end

end OAI
end

section
-- module Solutions.OAIQ080_BZ.Boltzmann_Branching_FamilyHotBounds
attribute [-instance] _root_.OAI.BoltzmannNonuniqueness.ChartKernel.offAxis_sFinite _root_.OAI.BoltzmannNonuniqueness.EuclideanFlight.sourcePullback_finite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.characteristicGainKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.hotKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.mixedKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.retainedKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.coldCylinderVolume_finite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.copyColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.mainCoreKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.selectedColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCoreSheet.dilatedColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCoreSheet.kineticColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.PeriodicApproximation.fiberMeasure_finite _root_.OAI.BoltzmannNonuniqueness.PositiveIteration.awayOriginKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.PositiveIteration.nearOriginKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamNormalCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamNormalRetainedKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.dampedCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.densityScaledCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalBeamKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalCollision_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalPhysicalEvent_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalWindowEvent_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.physicalEventMeasure_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.scaledBeamNormalKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.WeakTime.phaseEndpointKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.WeakTime.phaseIncrement_finite _root_.OAI.BoltzmannNonuniqueness.WeakTime.phaseSeed_sFinite _root_.OAI.BoltzmannNonuniqueness.WeakTime.residenceKernel_sFinite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Pointwise bounds for a dominated family's hot remainder and source -/

noncomputable section

open MeasureTheory

namespace BoltzmannNonuniqueness.WeightedLocal

theorem family_hot_bounds {I : Type*} [Countable I] {q b L R : ℝ}
    (hq : q < 2) (hb : 0 ≤ b) (hR : 0 ≤ R)
    (hloss : R*CutoffLipschitz.frequencyConstant q b ≤ L)
    {F : ℝ × JetPrototype.Phase → ℝ} {c : I → ℝ × JetPrototype.Phase → ℝ}
    (hFm : Measurable F) (hcm : ∀ i, Measurable (c i))
    (hF : ∀ u, 0 ≤ F u ∧ F u ≤ R) (hcn : ∀ i u, 0 ≤ c i u)
    (hSum : ∀ s : Finset I, ∀ u, ∑ i ∈ s, c i u ≤ F u) :
    Measurable (fun u => F u-∑' i, c i u) ∧
      (∀ u, 0 ≤ F u-∑' i, c i u ∧ F u-∑' i, c i u ≤ R) ∧
      Measurable (remainderForcing q b L F c) ∧
      ∀ u, 0 ≤ remainderForcing q b L F c u ∧
        remainderForcing q b L F c u ≤ HotApplication.realBound q*R^2+L*R := by
  classical
  let G (i : I) := coldForcing q b L F (c i)
  let S := HotApplication.realBound q*R^2+L*R
  have hcb (i) (u) : 0 ≤ c i u ∧ c i u ≤ R := by
    refine ⟨hcn i u,?_⟩
    simpa only [Finset.sum_singleton] using (hSum {i} u).trans (hF u).2
  have hgm (i) : Measurable (G i) := measurable_coldForcing hFm (hcm i) q b L
  have hgb (i) (u) : 0 ≤ G i u ∧ G i u ≤ S :=
    HotRepresentative.coldSource_bounds hq hb hR hloss (GaussianLocal.measurable_state hFm)
      (GaussianLocal.measurable_state (hcm i)) (fun p => hF (p.1.1,(p.1.2,p.2)))
      (fun p => hcb i (p.1.1,(p.1.2,p.2))) _
  have hfb (u) : 0 ≤ forcing q b L F u ∧ forcing q b L F u ≤ S :=
    HotRepresentative.source_bounds hq hb hR hloss (GaussianLocal.measurable_state hFm)
      (fun p => hF (p.1.1,(p.1.2,p.2))) _
  have hgsum (s : Finset I) (u) : (∑ i ∈ s, G i u) ≤ forcing q b L F u :=
    HotRepresentative.finite_sum_coldSource_le hq hb hloss s
      (fun i _ => GaussianLocal.measurable_state (hcm i)) (GaussianLocal.measurable_state hFm)
      (fun i _ p => hcb i (p.1.1,(p.1.2,p.2))) (fun p => hF (p.1.1,(p.1.2,p.2)))
      (fun p => hSum s (p.1.1,(p.1.2,p.2))) _
  have hgBound (u) : (∑' i, G i u) ≤ forcing q b L F u :=
    Real.tsum_le_of_sum_le (fun i => (hgb i u).1) (fun s => hgsum s u)
  refine ⟨hFm.sub (Measurable.tsum hcm),?_,
    (measurable_forcing hFm q b L).sub (Measurable.tsum hgm),?_⟩
  · intro u
    exact ⟨sub_nonneg.mpr (Real.tsum_le_of_sum_le (fun i => hcn i u) (fun s => hSum s u)),
      (sub_le_self _ (tsum_nonneg (fun i => hcn i u))).trans (hF u).2⟩
  · intro u
    exact ⟨sub_nonneg.mpr (hgBound u),
      (sub_le_self _ (tsum_nonneg (fun i => (hgb i u).1))).trans (hfb u).2⟩

end BoltzmannNonuniqueness.WeightedLocal

end

end OAI
end

section
-- module Solutions.OAIQ080_BZ.Boltzmann_Jets_PeriodicJetFamilies
attribute [-instance] _root_.OAI.BoltzmannNonuniqueness.ChartKernel.offAxis_sFinite _root_.OAI.BoltzmannNonuniqueness.EuclideanFlight.sourcePullback_finite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.characteristicGainKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.hotKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.mixedKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.retainedKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.coldCylinderVolume_finite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.copyColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.mainCoreKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.selectedColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCoreSheet.dilatedColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCoreSheet.kineticColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.PeriodicApproximation.fiberMeasure_finite _root_.OAI.BoltzmannNonuniqueness.PositiveIteration.awayOriginKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.PositiveIteration.nearOriginKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamNormalCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamNormalRetainedKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.dampedCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.densityScaledCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalBeamKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalCollision_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalPhysicalEvent_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalWindowEvent_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.physicalEventMeasure_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.scaledBeamNormalKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.WeakTime.phaseEndpointKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.WeakTime.phaseIncrement_finite _root_.OAI.BoltzmannNonuniqueness.WeakTime.phaseSeed_sFinite _root_.OAI.BoltzmannNonuniqueness.WeakTime.residenceKernel_sFinite
attribute [-simp] _root_.OAI.BoltzmannNonuniqueness.EuclideanFlight.phaseEquiv_snd _root_.OAI.BoltzmannNonuniqueness.timeTranslation_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

/-! # Countably labeled periodic copies of the finite cold datum -/

noncomputable section

open MeasureTheory Set
open BoltzmannNonuniqueness.VelocityWeight BoltzmannNonuniqueness.JetPrototype
open BoltzmannNonuniqueness.JetGeometry BoltzmannNonuniqueness.WeightedTranslation

namespace BoltzmannNonuniqueness.JetCopyDatum

theorem measurable_color (s₀ η K α γ d₀ q : ℝ) (N : ℕ) (i : JetLattice.Label) :
    Measurable (color s₀ η K α γ d₀ q N i) := by
  unfold color
  split_ifs
  · exact ((JetDatum.term_measurable s₀ η K α γ d₀ _).comp (measurable_shift _)).div
      ((ChartKernel.measurable_H q).comp measurable_snd)
  · exact measurable_const

theorem measurable_seed (s₀ η K α γ d₀ q : ℝ) (N : ℕ) : Measurable (seed s₀ η K α γ d₀ q N) :=
  Measurable.tsum (measurable_color s₀ η K α γ d₀ q N)

theorem color_nonneg {s₀ K d₀ : ℝ} (hs₀ : 0 < s₀) (hK : 0 ≤ K) (hd₀ : 0 ≤ d₀)
    (η α γ q : ℝ) (N : ℕ) (i : JetLattice.Label) (p : JetPrototype.Phase) :
    0 ≤ color s₀ η K α γ d₀ q N i p := by
  unfold color
  split_ifs
  · exact div_nonneg (JetDatum.term_nonneg hs₀ hK hd₀ η α γ _ _) (H_nonneg _ _)
  · exact le_rfl

private theorem in_enlargement {s₀ η K α γ d₀ q : ℝ} {N : ℕ}
    (hs₀ : 0 < s₀) (hη : 0 < η) {i : JetLattice.Label} {p : JetPrototype.Phase}
    (hp : color s₀ η K α γ d₀ q N i p ≠ 0) :
    PlaneChart.join p.1.1 p.1.2 ∈ JetLattice.spatialEnlargement s₀ η 0 i := by
  have hi : i.annulus < N := by
    by_contra h
    exact hp (by simp only [color,ite_eq_right h])
  have hn : JetDatum.term s₀ η K α γ d₀ (i.annulus,i.positive)
      (shift (displacement i.lattice) p) ≠ 0 := by
    intro h
    exact hp (by simp only [color,ite_eq_left hi,h,zero_div])
  have hsp := JetSupport.initial_spatial_support η K α γ
    (jetScale s₀ η i.annulus) (d₀*jetScale s₀ η i.annulus^10) i.positive hn
  constructor
  · rw [PlaneChart.transverse_join]
    apply Metric.mem_cthickening_of_dist_le _ _ _ _ hsp.1
    simpa [shift,displacement,jetScale] using (enlargementWidth_pos hη
      (DatumBounds.scale_pos (η := η) hs₀ (i.annulus+1))).le
  · have hax : |p.1.2-JetLattice.axialShift i.lattice| < 1/8 := hsp.2
    change |axial (PlaneChart.join p.1.1 p.1.2)-JetLattice.axialShift i.lattice| ≤ _
    rw [PlaneChart.axial_join]
    linarith

theorem color_disjoint {s₀ η : ℝ} (hs₀ : 0 < s₀) (hsmax : s₀ ≤ 1/8)
    (hη : 0 < η) (hηmax : η ≤ Real.log 2) (K α γ d₀ q : ℝ) (N : ℕ)
    (p : JetPrototype.Phase) (i j : JetLattice.Label) (hij : i ≠ j)
    (hi : color s₀ η K α γ d₀ q N i p ≠ 0) : color s₀ η K α γ d₀ q N j p = 0 := by
  by_contra hj
  exact hij (JetLattice.common_point_label hs₀ hsmax hη hηmax (by norm_num : (0:ℝ) ≤ 1/32)
    (in_enlargement hs₀ hη hi) (in_enlargement hs₀ hη hj))

theorem color_summable {s₀ η : ℝ} (hs₀ : 0 < s₀) (hsmax : s₀ ≤ 1/8)
    (hη : 0 < η) (hηmax : η ≤ Real.log 2) (K α γ d₀ q : ℝ) (N : ℕ) (p : JetPrototype.Phase) :
    Summable (fun i => color s₀ η K α γ d₀ q N i p) :=
  JetSeries.summable_single_support (color_disjoint hs₀ hsmax hη hηmax K α γ d₀ q N p)

end BoltzmannNonuniqueness.JetCopyDatum

end

end

section

/-! # Finite weighted bounds for the countably labeled periodic seed -/

noncomputable section

open MeasureTheory
open BoltzmannNonuniqueness.VelocityWeight BoltzmannNonuniqueness.JetPrototype

namespace BoltzmannNonuniqueness.JetCopyDatum

theorem coefficient_le_amplitude {s₀ K d₀ : ℝ} (hs₀ : 0 < s₀) (hK : 0 ≤ K)
    (hd₀ : 0 ≤ d₀) (η : ℝ) {N : ℕ} (i : JetDatum.Index)
    (hi : i ∈ JetFiniteGaussian.indices N) :
    JetFiniteGaussian.coefficient s₀ η K d₀ i.1 ≤ JetFiniteGaussian.amplitude s₀ η K d₀ N := by
  classical
  have h : JetFiniteGaussian.coefficient s₀ η K d₀ i.1 ≤
      ∑ j ∈ JetFiniteGaussian.indices N, JetFiniteGaussian.coefficient s₀ η K d₀ j.1 :=
    Finset.single_le_sum (fun (j : JetDatum.Index) _ =>
      JetFiniteGaussian.coefficient_nonneg hs₀ hK hd₀ η j.1) hi
  exact h.trans (le_add_of_nonneg_left zero_le_one)

theorem color_bound {s₀ η K d₀ α : ℝ} (hs₀ : 0 < s₀) (hsmax : s₀ ≤ 1/8)
    (hη : 0 ≤ η) (hK : 0 ≤ K) (hd₀ : 0 < d₀)
    (hwidth : d₀*(1/8:ℝ)^10 ≤ 1/64) (hα : 0 ≤ α) (hαmax : α ≤ 1/4)
    (γ q : ℝ) (N : ℕ) (i : JetLattice.Label) (p : JetPrototype.Phase) :
    color s₀ η K α γ d₀ q N i p ≤ WeightedFiniteSeed.amplitude s₀ η K d₀ N := by
  classical
  unfold color
  split_ifs with hi
  · apply (div_le_iff₀ (H_pos q p.2)).mpr
    have hmem : (i.annulus,i.positive) ∈ JetFiniteGaussian.indices N := by
      simp [JetFiniteGaussian.indices,hi]
    have hcoef := coefficient_le_amplitude hs₀ hK hd₀.le η (i.annulus,i.positive) hmem
    calc
      _ ≤ JetFiniteGaussian.coefficient s₀ η K d₀ i.annulus * JetGaussianMoments.kernel 2 p.2 :=
        JetFiniteGaussian.term_bound hs₀ hsmax hη hK hd₀ hwidth hα hαmax γ
          (i.annulus,i.positive) (WeightedTranslation.shift (displacement i.lattice) p)
      _ ≤ JetFiniteGaussian.amplitude s₀ η K d₀ N * JetGaussianMoments.kernel 2 p.2 :=
        mul_le_mul_of_nonneg_right hcoef (Real.exp_pos _).le
      _ ≤ JetFiniteGaussian.amplitude s₀ η K d₀ N * (tiltConstant*H q p.2) :=
        mul_le_mul_of_nonneg_left (JetGaussianEscape.gaussian_le_hot q p.2)
          (JetFiniteGaussian.amplitude_pos hs₀ hK hd₀.le η N).le
      _ = _ := by unfold WeightedFiniteSeed.amplitude; ring
  · exact (WeightedFiniteSeed.amplitude_pos hs₀ hK hd₀.le η N).le

theorem seed_bounds {s₀ η K d₀ α : ℝ} (hs₀ : 0 < s₀) (hsmax : s₀ ≤ 1/8)
    (hη : 0 < η) (hηmax : η ≤ Real.log 2) (hK : 0 ≤ K) (hd₀ : 0 < d₀)
    (hwidth : d₀*(1/8:ℝ)^10 ≤ 1/64) (hα : 0 ≤ α) (hαmax : α ≤ 1/4)
    (γ q : ℝ) (N : ℕ) (p : JetPrototype.Phase) :
    0 ≤ seed s₀ η K α γ d₀ q N p ∧
      seed s₀ η K α γ d₀ q N p ≤ WeightedFiniteSeed.amplitude s₀ η K d₀ N := by
  classical
  refine ⟨tsum_nonneg (fun i => color_nonneg hs₀ hK hd₀.le η α γ q N i p),?_⟩
  by_cases h : ∃ i, color s₀ η K α γ d₀ q N i p ≠ 0
  · obtain ⟨i,hi⟩ := h
    unfold seed
    rw [tsum_eq_single i (fun j hj => color_disjoint hs₀ hsmax hη hηmax K α γ d₀ q N p i j hj.symm hi)]
    exact color_bound hs₀ hsmax hη.le hK hd₀ hwidth hα hαmax γ q N i p
  · have hz (i) : color s₀ η K α γ d₀ q N i p = 0 := not_ne_iff.mp (not_exists.mp h i)
    simp only [seed,hz,tsum_zero]
    exact (WeightedFiniteSeed.amplitude_pos hs₀ hK hd₀.le η N).le

theorem finite_sum_le_seed {s₀ η K d₀ : ℝ} (hs₀ : 0 < s₀) (hsmax : s₀ ≤ 1/8)
    (hη : 0 < η) (hηmax : η ≤ Real.log 2) (hK : 0 ≤ K) (hd₀ : 0 ≤ d₀)
    (α γ q : ℝ) (N : ℕ) (u : Finset JetLattice.Label) (p : JetPrototype.Phase) :
    ∑ i ∈ u, color s₀ η K α γ d₀ q N i p ≤ seed s₀ η K α γ d₀ q N p :=
  (color_summable hs₀ hsmax hη hηmax K α γ d₀ q N p).sum_le_tsum u
    (fun i _ => color_nonneg hs₀ hK hd₀ η α γ q N i p)

end BoltzmannNonuniqueness.JetCopyDatum

end

end

section

/-! # Exact periodicity of the labeled initial datum -/

noncomputable section

open BoltzmannNonuniqueness.JetPrototype BoltzmannNonuniqueness.WeightedTranslation

namespace BoltzmannNonuniqueness.JetCopyDatum

theorem displacement_add (m n : JetLattice.Lattice) :
    displacement (m+n) = displacement m+displacement n := by
  apply Prod.ext
  · ext k
    simp [displacement,JetLattice.transverseShift]
  · simp [displacement,JetLattice.axialShift]

theorem shift_shift (y z : Space) (p : JetPrototype.Phase) :
    shift y (shift z p) = shift (y+z) p := by
  apply Prod.ext
  · dsimp [shift]
    abel
  · rfl

theorem color_shift (s₀ η K α γ d₀ q : ℝ) (N : ℕ) (n : JetLattice.Lattice)
    (i : JetLattice.Label) (p : JetPrototype.Phase) :
    color s₀ η K α γ d₀ q N i (shift (displacement n) p) =
      color s₀ η K α γ d₀ q N (relabel n i) p := by
  change (if i.annulus < N then
    JetDatum.term s₀ η K α γ d₀ (i.annulus,i.positive)
      (shift (displacement i.lattice) (shift (displacement n) p)) / VelocityWeight.H q p.2 else 0) =
    (if i.annulus < N then
    JetDatum.term s₀ η K α γ d₀ (i.annulus,i.positive)
      (shift (displacement (i.lattice+n)) p) / VelocityWeight.H q p.2 else 0)
  rw [displacement_add,shift_shift]

theorem seed_periodic (s₀ η K α γ d₀ q : ℝ) (N : ℕ) (n : JetLattice.Lattice)
    (p : JetPrototype.Phase) :
    seed s₀ η K α γ d₀ q N (shift (displacement n) p) = seed s₀ η K α γ d₀ q N p := by
  unfold seed
  simp_rw [color_shift]
  exact (relabel n).tsum_eq (fun i => color s₀ η K α γ d₀ q N i p)

end BoltzmannNonuniqueness.JetCopyDatum

end

end

section

/-! # The actual labeled periodic approximation on a common local interval -/

noncomputable section

open MeasureTheory
open BoltzmannNonuniqueness.JetPrototype BoltzmannNonuniqueness.WeightedTranslation

namespace BoltzmannNonuniqueness.JetCopyDatum

theorem initial_color_bounds {s₀ η K d₀ : ℝ} (hs₀ : 0 < s₀) (hsmax : s₀ ≤ 1/8)
    (hη : 0 < η) (hηmax : η ≤ Real.log 2) (hK : 0 ≤ K) (hd₀ : 0 ≤ d₀)
    (α γ q : ℝ) (N : ℕ) {h₀ : JetPrototype.Phase → ℝ} (hh₀ : ∀ p, 0 ≤ h₀ p) :
    (∀ i p, 0 ≤ color s₀ η K α γ d₀ q N i p ∧
      color s₀ η K α γ d₀ q N i p ≤ initial s₀ η K α γ d₀ q N h₀ p) ∧
    (∀ u : Finset JetLattice.Label, ∀ p,
      ∑ i ∈ u, color s₀ η K α γ d₀ q N i p ≤ initial s₀ η K α γ d₀ q N h₀ p) := by
  have hf (u : Finset JetLattice.Label) (p) : ∑ i ∈ u, color s₀ η K α γ d₀ q N i p ≤
      initial s₀ η K α γ d₀ q N h₀ p :=
    (finite_sum_le_seed hs₀ hsmax hη hηmax hK hd₀ α γ q N u p).trans (le_add_of_nonneg_right (hh₀ p))
  refine ⟨?_,hf⟩
  intro i p
  classical
  exact ⟨color_nonneg hs₀ hK hd₀ η α γ q N i p,by simpa using hf {i} p⟩

end BoltzmannNonuniqueness.JetCopyDatum

end

end

end OAI
end

section
-- module Solutions.OAIQ080_BZ.Boltzmann_Branching_HotSeedCoreLower
attribute [-instance] _root_.OAI.BoltzmannNonuniqueness.ChartKernel.offAxis_sFinite _root_.OAI.BoltzmannNonuniqueness.EuclideanFlight.sourcePullback_finite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.characteristicGainKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.hotKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.mixedKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.retainedKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.coldCylinderVolume_finite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.copyColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.mainCoreKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.selectedColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCoreSheet.dilatedColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCoreSheet.kineticColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.PeriodicApproximation.fiberMeasure_finite _root_.OAI.BoltzmannNonuniqueness.PositiveIteration.awayOriginKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.PositiveIteration.nearOriginKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamNormalCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamNormalRetainedKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.dampedCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.densityScaledCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalBeamKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalCollision_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalPhysicalEvent_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalWindowEvent_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.physicalEventMeasure_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.scaledBeamNormalKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.WeakTime.phaseEndpointKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.WeakTime.phaseIncrement_finite _root_.OAI.BoltzmannNonuniqueness.WeakTime.phaseSeed_sFinite _root_.OAI.BoltzmannNonuniqueness.WeakTime.residenceKernel_sFinite
attribute [-simp] _root_.OAI.BoltzmannNonuniqueness.EuclideanFlight.phaseEquiv_snd _root_.OAI.BoltzmannNonuniqueness.timeTranslation_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

/-! # A localized periodic thermal seed, normalized in the singular weighted norm -/

noncomputable section

open MeasureTheory
open BoltzmannNonuniqueness.VelocityWeight BoltzmannNonuniqueness.JetPrototype

namespace BoltzmannNonuniqueness.HotSeedProfile

theorem bound_pos : 0 < bound := by
  unfold bound
  exact mul_pos (mul_pos (sq_pos_of_pos JetThermalKernel.bound_pos) (Real.exp_pos _)) tiltConstant_pos

theorem centered_sub_int (x : ℝ) (n : ℤ) : centered (x-n) = centered x := by
  unfold centered
  rw [show x-(n:ℝ)+1/2=x+1/2-n by ring,Int.fract_sub_intCast]

theorem centeredSpace_shift (n : JetLattice.Lattice) (p : JetPrototype.Phase) :
    centeredSpace (WeightedTranslation.shift (JetCopyDatum.displacement n) p).1 = centeredSpace p.1 := by
  apply Prod.ext
  · ext i
    exact centered_sub_int (p.1.1 i) (n i.castSucc)
  · exact centered_sub_int p.1.2 (n (Fin.last 2))

theorem raw_periodic (q δ : ℝ) (n : JetLattice.Lattice) (p : JetPrototype.Phase) :
    raw q δ (WeightedTranslation.shift (JetCopyDatum.displacement n) p) = raw q δ p := by
  unfold raw
  rw [centeredSpace_shift]
  rfl

theorem measurable_centered : Measurable centered :=
  ((measurable_id.add_const (1/2)).fract).sub_const (1/2)

theorem measurable_centeredSpace : Measurable centeredSpace := by
  apply Measurable.prodMk
  · apply (MeasurableEquiv.toLp 2 (Fin 2 → ℝ)).measurable.comp
    exact Measurable.of_eval (fun i => measurable_centered.comp
      (show Measurable (fun x : Space => x.1 i) from by fun_prop))
  · exact measurable_centered.comp measurable_snd

theorem measurable_raw (q δ : ℝ) : Measurable (raw q δ) := by
  have hjoin : Measurable (fun x : Space => PlaneChart.join x.1 x.2) :=
    split.symm.measurable.comp (measurable_snd.prodMk measurable_fst)
  exact (JetThermalKernel.J_smooth.continuous.measurable.comp
    ((hjoin.comp (measurable_centeredSpace.comp measurable_fst)).const_smul δ⁻¹)).mul
    ((JetThermalKernel.J_smooth.continuous.measurable.comp measurable_snd).div
      ((ChartKernel.measurable_H q).comp measurable_snd))

theorem raw_nonneg (q δ : ℝ) (p : JetPrototype.Phase) : 0 ≤ raw q δ p :=
  mul_nonneg (JetThermalKernel.J_nonneg _) (div_nonneg (JetThermalKernel.J_nonneg _) (H_nonneg _ _))

theorem velocity_bound (q : ℝ) (v : Velocity) :
    JetThermalKernel.J v/H q v ≤ JetThermalKernel.bound*Real.exp 2*tiltConstant := by
  by_cases hv : 1 ≤ ‖v‖
  · rw [JetThermalKernel.J_zero hv,zero_div]
    exact mul_nonneg (mul_nonneg JetThermalKernel.bound_pos.le (Real.exp_pos _).le) tiltConstant_pos.le
  · have hv2 : ‖v‖^2 ≤ 1 := by nlinarith [norm_nonneg v,lt_of_not_ge hv]
    have he : 1 ≤ Real.exp 2*Real.exp (-2*‖v‖^2) := by
      rw [← Real.exp_add,← Real.exp_zero]
      exact Real.exp_le_exp.mpr (by linarith)
    apply (div_le_iff₀ (H_pos q v)).mpr
    calc
      _ ≤ JetThermalKernel.bound := JetThermalKernel.J_le v
      _ ≤ JetThermalKernel.bound*(Real.exp 2*Real.exp (-2*‖v‖^2)) :=
        by simpa only [mul_one] using mul_le_mul_of_nonneg_left he JetThermalKernel.bound_pos.le
      _ ≤ JetThermalKernel.bound*(Real.exp 2*(tiltConstant*H q v)) :=
        mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_left (JetGaussianEscape.gaussian_le_hot q v) (Real.exp_pos _).le)
          JetThermalKernel.bound_pos.le
      _ = _ := by ring

theorem raw_le (q δ : ℝ) (p : JetPrototype.Phase) : raw q δ p ≤ bound := by
  unfold raw bound
  have h := mul_le_mul
    (JetThermalKernel.J_le (δ⁻¹ • PlaneChart.join (centeredSpace p.1).1 (centeredSpace p.1).2))
    (velocity_bound q p.2)
    (div_nonneg (JetThermalKernel.J_nonneg _) (H_nonneg _ _)) JetThermalKernel.bound_pos.le
  exact h.trans_eq (by ring)

theorem normalized_size {q δ : ℝ} (hδ : 0 ≤ δ) (hp : 0 < PhaseEssSup.size (raw q δ)) :
    PhaseEssSup.size (normalized q δ) = δ := by
  change PhaseEssSup.size (fun p => (δ/PhaseEssSup.size (raw q δ))*raw q δ p) = δ
  rw [PhaseEssSup.size_const_mul,abs_of_nonneg (div_nonneg hδ hp.le)]
  exact div_mul_cancel₀ δ hp.ne'

end BoltzmannNonuniqueness.HotSeedProfile

end

end

section

/-! # The localized thermal seed has positive essential weighted norm -/

noncomputable section

open MeasureTheory MeasureTheory.Measure Set Metric
open BoltzmannNonuniqueness.VelocityWeight BoltzmannNonuniqueness.JetPrototype

namespace BoltzmannNonuniqueness.PhaseEssSup

theorem size_pos_of_positive_set {f : JetPrototype.Phase → ℝ} {R : ℝ}
    (hfm : Measurable f) (hb : ∀ p, |f p| ≤ R) {s : Set JetPrototype.Phase}
    (hs : FlightMeasure.phaseVolume s ≠ 0) (hf : ∀ p ∈ s, 0 < f p) : 0 < size f := by
  obtain ⟨p,hp,hbound⟩ := exists_mem_of_measure_ne_zero_of_ae hs
    (ae_restrict_of_ae (ae_abs_le_size hfm hb))
  exact (hf p hp).trans_le ((le_abs_self _).trans hbound)

end BoltzmannNonuniqueness.PhaseEssSup

namespace BoltzmannNonuniqueness.HotSeedProfile

theorem centered_eq {x : ℝ} (hx : |x| < 1/2) : centered x = x := by
  have h := abs_lt.mp hx
  unfold centered
  rw [Int.fract_eq_self.mpr ⟨by linarith [h.1],by linarith [h.2]⟩]
  ring

theorem centeredSpace_eq {x : Space} (hx : ‖x‖ < 1/2) : centeredSpace x = x := by
  apply Prod.ext
  · ext i
    apply centered_eq
    exact (show |x.1 i| ≤ ‖x.1‖ from by simpa only [Real.norm_eq_abs] using PiLp.norm_apply_le x.1 i).trans_lt
      ((norm_fst_le x).trans_lt hx)
  · apply centered_eq
    exact (show |x.2| ≤ ‖x‖ from by simpa only [Real.norm_eq_abs] using norm_snd_le x).trans_lt hx

theorem J_pos {v : Velocity} (hv : ‖v‖ < 1) : 0 < JetThermalKernel.J v := by
  have hn : JetThermalKernel.J v ≠ 0 := by
    change v ∈ Function.support JetThermalKernel.J
    rw [JetThermalKernel.J_support]
    simpa only [mem_ball,dist_zero_right] using hv
  exact lt_of_le_of_ne (JetThermalKernel.J_nonneg v) hn.symm

theorem raw_pos {δ : ℝ} (hδ : 0 < δ) (hδmax : δ ≤ 1) (q : ℝ)
    {p : JetPrototype.Phase} (hx : ‖p.1‖ < δ/4) (hv : ‖p.2‖ < 1/2) : 0 < raw q δ p := by
  have hc : centeredSpace p.1 = p.1 := centeredSpace_eq (by linarith)
  have hu : ‖p.1.1‖ < δ/4 := (norm_fst_le p.1).trans_lt hx
  have hz : |p.1.2| < δ/4 := by simpa only [Real.norm_eq_abs] using (norm_snd_le p.1).trans_lt hx
  have hj : ‖PlaneChart.join p.1.1 p.1.2‖ < δ := by
    have he := PlaneChart.norm_join_sq p.1.1 p.1.2
    have hsq := sq_abs p.1.2
    nlinarith [norm_nonneg p.1.1,norm_nonneg (PlaneChart.join p.1.1 p.1.2),abs_nonneg p.1.2]
  have harg : ‖δ⁻¹ • PlaneChart.join p.1.1 p.1.2‖ < 1 := by
    rw [norm_smul,Real.norm_eq_abs,abs_of_pos (inv_pos.mpr hδ)]
    exact (inv_mul_lt_one₀ hδ).mpr hj
  unfold raw
  rw [hc]
  exact mul_pos (J_pos harg) (div_pos (J_pos (by linarith)) (H_pos q p.2))

theorem raw_size_pos {δ : ℝ} (hδ : 0 < δ) (hδmax : δ ≤ 1) (q : ℝ) :
    0 < PhaseEssSup.size (raw q δ) := by
  let s : Set JetPrototype.Phase := ball (0 : Space) (δ/4) ×ˢ ball (0 : Velocity) (1/2)
  have hs : FlightMeasure.phaseVolume s ≠ 0 := by
    change ((volume : Measure Space).prod (volume : Measure Velocity))
      (ball (0 : Space) (δ/4) ×ˢ ball (0 : Velocity) (1/2)) ≠ 0
    rw [Measure.prod_prod]
    exact mul_ne_zero (measure_ball_pos volume (0 : Space) (by linarith)).ne'
      (measure_ball_pos volume (0 : Velocity) (by norm_num : (0:ℝ) < 1/2)).ne'
  apply PhaseEssSup.size_pos_of_positive_set (measurable_raw q δ)
    (fun p => by rw [abs_of_nonneg (raw_nonneg q δ p)]; exact raw_le q δ p) hs
  intro p hp
  exact raw_pos hδ hδmax q (by simpa only [mem_ball,dist_zero_right] using hp.1)
    (by simpa only [mem_ball,dist_zero_right] using hp.2)

end BoltzmannNonuniqueness.HotSeedProfile

end

end

section

/-! # The normalized periodic hot seed has the data required by cap selection -/

noncomputable section

open MeasureTheory
open BoltzmannNonuniqueness.JetPrototype

namespace BoltzmannNonuniqueness.HotSeedProfile

theorem normalized_measurable (q δ : ℝ) : Measurable (normalized q δ) :=
  (measurable_raw q δ).const_mul _

theorem normalized_periodic (q δ : ℝ) (n : JetLattice.Lattice) (p : JetPrototype.Phase) :
    normalized q δ (WeightedTranslation.shift (JetCopyDatum.displacement n) p) = normalized q δ p := by
  unfold normalized
  rw [raw_periodic]

theorem normalized_bounds {δ : ℝ} (hδ : 0 < δ) (hδmax : δ ≤ 1) (q : ℝ) :
    ∃ M : ℝ, 0 < M ∧ ∀ p, 0 ≤ normalized q δ p ∧ normalized q δ p ≤ M := by
  have hs := raw_size_pos hδ hδmax q
  let c := δ/PhaseEssSup.size (raw q δ)
  have hc : 0 < c := div_pos hδ hs
  refine ⟨c*bound,mul_pos hc bound_pos,?_⟩
  intro p
  exact ⟨mul_nonneg hc.le (raw_nonneg q δ p),mul_le_mul_of_nonneg_left (raw_le q δ p) hc.le⟩

theorem normalized_norm {δ : ℝ} (hδ : 0 < δ) (hδmax : δ ≤ 1) (q : ℝ) :
    PhaseEssSup.size (normalized q δ) = δ :=
  normalized_size hδ.le (raw_size_pos hδ hδmax q)

end BoltzmannNonuniqueness.HotSeedProfile

end

end

end OAI
end

section
-- module Solutions.OAIQ080_BZ.Boltzmann_Branching_WeightedHotGain
attribute [-instance] _root_.OAI.BoltzmannNonuniqueness.ChartKernel.offAxis_sFinite _root_.OAI.BoltzmannNonuniqueness.EuclideanFlight.sourcePullback_finite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.characteristicGainKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.hotKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.mixedKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.retainedKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.coldCylinderVolume_finite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.copyColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.mainCoreKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.selectedColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCoreSheet.dilatedColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCoreSheet.kineticColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.PeriodicApproximation.fiberMeasure_finite _root_.OAI.BoltzmannNonuniqueness.PositiveIteration.awayOriginKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.PositiveIteration.nearOriginKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamNormalCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamNormalRetainedKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.dampedCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.densityScaledCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalBeamKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalCollision_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalPhysicalEvent_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalWindowEvent_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.physicalEventMeasure_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.scaledBeamNormalKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.WeakTime.phaseEndpointKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.WeakTime.phaseIncrement_finite _root_.OAI.BoltzmannNonuniqueness.WeakTime.phaseSeed_sFinite _root_.OAI.BoltzmannNonuniqueness.WeakTime.residenceKernel_sFinite
attribute [-simp] _root_.OAI.BoltzmannNonuniqueness.EuclideanFlight.phaseEquiv_snd _root_.OAI.BoltzmannNonuniqueness.timeTranslation_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

/-! # A uniform positive local interval from an essentially bounded time slice -/

noncomputable section

open MeasureTheory
open BoltzmannNonuniqueness.WeightedTranslation

namespace BoltzmannNonuniqueness.WeightedLocalControl

theorem exists_extension {q b A s : ℝ} (hq : q < 2) (hb : 0 ≤ b) (hA : 0 < A)
    {F : ℝ × JetPrototype.Phase → ℝ} (hFm : Measurable F)
    (hFn : ∀ p, 0 ≤ F (s,p))
    (hFA : ∀ᵐ p ∂FlightMeasure.phaseVolume, F (s,p) ≤ A)
    (hper : ∀ n, pull (JetCopyDatum.displacement n) F = F) :
    ∃ G : ℝ × JetPrototype.Phase → ℝ, Measurable G ∧
      (∀ u, 0 ≤ G u ∧ G u ≤ 2*A) ∧
      (∀ u, G u = PositiveIntegral.value (lifespan q b A) (damping q b A)
        JetBarrier.flight (clippedSlice A F s) (WeightedLocal.forcing q b (damping q b A) G) u) ∧
      ((fun p => G (0,p)) =ᵐ[FlightMeasure.phaseVolume] (fun p => F (s,p))) ∧
      ∀ n, pull (JetCopyDatum.displacement n) G = G := by
  have hsm : Measurable (clippedSlice A F s) :=
    (hFm.comp (measurable_const.prodMk measurable_id)).min measurable_const
  have hsb (p) : 0 ≤ clippedSlice A F s p ∧ clippedSlice A F s p ≤ A :=
    ⟨le_min (hFn p) hA.le,min_le_right _ _⟩
  obtain ⟨G,hGm,hG,hGeq⟩ := exists_solution hq hb hA hsm hsb
  have hT : 0 ≤ lifespan q b A := (lifespan_pos hb hA).le
  have hL : 0 ≤ damping q b A := (bounds hb hA).1
  refine ⟨G,hGm,hG,hGeq,?_,?_⟩
  · filter_upwards [hFA] with p hp
    rw [hGeq (0,p)]
    have ht : PositiveIntegral.time (lifespan q b A) 0 = 0 := GaussianLocal.time_eq ⟨le_rfl,hT⟩
    simp [PositiveIntegral.value,ht,JetBarrier.flight,clippedSlice,min_eq_left hp]
  · intro n
    apply solution_covariance hq hb hL hT (by positivity)
      (show (2*A)*CutoffLipschitz.frequencyConstant q b ≤ damping q b A from le_rfl)
      (small hb hA) hGm hG hGeq
    intro p
    have hp := congrFun (hper n) (s,p)
    change F (s,shift (JetCopyDatum.displacement n) p) = F (s,p) at hp
    unfold clippedSlice
    rw [hp]

end BoltzmannNonuniqueness.WeightedLocalControl

end

end

section

/-! # Extending a bounded positive periodic solution from a bounded time slice -/

noncomputable section

open MeasureTheory Set
open BoltzmannNonuniqueness.WeightedLocal BoltzmannNonuniqueness.WeightedTranslation

namespace BoltzmannNonuniqueness.WeightedLocalControl

theorem exists_continuation_step {q b A s : ℝ} (hq : q < 2) (hb : 0 ≤ b)
    (hA : 0 < A) (hs : 0 ≤ s) {f₀ : JetPrototype.Phase → ℝ}
    {F : ℝ × JetPrototype.Phase → ℝ} (hFm : Measurable F)
    (hF : ∀ u, 0 ≤ F u ∧ F u ≤ 2*A)
    (hFA : ∀ᵐ p ∂FlightMeasure.phaseVolume, F (s,p) ≤ A)
    (hfix : MildAE q b (damping q b A) s f₀ F)
    (hper : ∀ n, pull (JetCopyDatum.displacement n) F = F) :
    ∃ H : ℝ × JetPrototype.Phase → ℝ, Measurable H ∧
      (∀ u, 0 ≤ H u ∧ H u ≤ 2*A) ∧
      (∀ t, (fun p => H (t,p)) =ᵐ[FlightMeasure.phaseVolume]
        (fun p => PositiveIntegral.value (s+lifespan q b A) (damping q b A)
          JetBarrier.flight f₀ (forcing q b (damping q b A) H) (t,p))) ∧
      (∀ n, pull (JetCopyDatum.displacement n) H = H) ∧
      ∀ t ∈ Icc 0 s, ∀ p, H (t,p) = F (t,p) := by
  obtain ⟨G,hGm,hG,hGeq,_,hGper⟩ := exists_extension hq hb hA hFm
    (fun p => (hF (s,p)).1) hFA hper
  let P := paste s F G
  have hPm : Measurable P := measurable_paste hFm hGm
  have hPb (u) : 0 ≤ P u ∧ P u ≤ 2*A := paste_bounds hF hG u
  have hδ : 0 ≤ lifespan q b A := (lifespan_pos hb hA).le
  have hL : 0 ≤ damping q b A := (bounds hb hA).1
  have hsrc (u) : |forcing q b (damping q b A) P u| ≤ sourceBound q b A := by
    have h := HotRepresentative.source_bounds hq hb (by positivity : 0 ≤ 2*A)
      (show (2*A)*CutoffLipschitz.frequencyConstant q b ≤ damping q b A from le_rfl)
      (GaussianLocal.measurable_state hPm) (fun v => hPb (v.1.1,(v.1.2,v.2)))
      ((u.1,u.2.1),u.2.2)
    exact (abs_of_nonneg h.1).trans_le h.2
  have hclip : clippedSlice A F s =ᵐ[FlightMeasure.phaseVolume] (fun p => F (s,p)) := by
    filter_upwards [hFA] with p hp
    exact min_eq_left hp
  have hPeq : MildAE q b (damping q b A) (s+lifespan q b A) f₀ P :=
    paste_mildAE hs hδ hL hFm hGm hsrc hfix (mildAE_of_pointwise hGeq) hclip
  have hPper (n) : pull (JetCopyDatum.displacement n) P = P := by
    dsimp only [P]
    rw [paste_pull,hper n,hGper n]
  let H := clampTime (s+lifespan q b A) P
  have htot := add_nonneg hs hδ
  refine ⟨H,measurable_clampTime hPm _,fun u => hPb _,mildAE_all_times htot hPeq,?_,?_⟩
  · intro n
    funext u
    exact congrFun (hPper n) (PositiveIntegral.time (s+lifespan q b A) u.1,u.2)
  · intro t ht p
    change P (PositiveIntegral.time (s+lifespan q b A) t,p) = F (t,p)
    rw [GaussianLocal.time_eq ⟨ht.1,by linarith [ht.2]⟩]
    exact ite_eq_left ht.2

end BoltzmannNonuniqueness.WeightedLocalControl

end

end

end OAI
end

section
-- module Solutions.OAIQ080_BZ.Boltzmann_Jets_JetFamilyBounds
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

/-! # A finite cold-norm bound from one core and the escaped tail -/

noncomputable section

open BoltzmannNonuniqueness.JetPrototype

namespace BoltzmannNonuniqueness.JetCopyDatum

theorem colorAmplitude_nonneg {K s d : ℝ} (hK : 0 ≤ K) (hs : 0 < s) (hd : 0 < d)
    (α : ℝ) : 0 ≤ colorAmplitude K α s d := by
  unfold colorAmplitude JetGaussianEscape.constant VelocityWeight.tiltConstant
  have := JetThermalKernel.bound_pos
  positivity

end BoltzmannNonuniqueness.JetCopyDatum

end

end

section

/-! # A finite uniform-in-time norm bound for the retained cold family -/

noncomputable section

open BoltzmannNonuniqueness.JetPrototype

namespace BoltzmannNonuniqueness.JetCopyDatum

theorem finiteAmplitude_nonneg {s₀ K d₀ : ℝ} (hs₀ : 0 < s₀) (hK : 0 ≤ K)
    (hd₀ : 0 < d₀) (η α : ℝ) (N : ℕ) : 0 ≤ finiteAmplitude s₀ η K α d₀ N := by
  apply Finset.sum_nonneg
  intro j _
  have hs : 0 < JetGeometry.jetScale s₀ η j := DatumBounds.scale_pos hs₀ _
  exact colorAmplitude_nonneg hK hs (by positivity) α

end BoltzmannNonuniqueness.JetCopyDatum

end

end

section

/-! # A fixed-truncation bound for the full periodic cold sum -/

noncomputable section

open MeasureTheory Set
open BoltzmannNonuniqueness.WeightedLocal BoltzmannNonuniqueness.WeightedTranslation

namespace BoltzmannNonuniqueness.JetCopyDatum

theorem coldNormBound_nonneg {s₀ K d₀ : ℝ} (hs₀ : 0 < s₀) (hK : 0 ≤ K)
    (hd₀ : 0 < d₀) (η α : ℝ) (N : ℕ) : 0 ≤ coldNormBound s₀ η K α d₀ N :=
  add_nonneg (finiteAmplitude_nonneg hs₀ hK hd₀ η α N)
    (JetEscapedEnvelope.constant_nonneg hs₀ hK hd₀ η α _)

end BoltzmannNonuniqueness.JetCopyDatum

end

end

end OAI
end

section
-- module Solutions.OAIQ080_BZ.Boltzmann_Approximation_CapDilationScales
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

/-! # The attained cap ratio and its uniform perturbation bound -/

noncomputable section

open Set

namespace BoltzmannNonuniqueness.Cap

theorem peak_eq_of_max {T δ t : ℝ} {z : ℝ → ℝ} (ht : t ∈ Icc 0 T)
    (hmax : ∀ s ∈ Icc 0 T, z s/(s+δ) ≤ z t/(t+δ)) :
    peak T δ z = z t/(t+δ) := by
  have hmem : z t/(t+δ) ∈ (fun t => z t/(t+δ)) '' Icc 0 T := mem_image_of_mem _ ht
  have hbd : BddAbove ((fun t => z t/(t+δ)) '' Icc 0 T) :=
    ⟨z t/(t+δ),by rintro y ⟨s,hs,rfl⟩; exact hmax s hs⟩
  exact le_antisymm (csSup_le ⟨_,hmem⟩ (by rintro y ⟨s,hs,rfl⟩; exact hmax s hs)) (le_csSup hbd hmem)

theorem peak_attained {T δ : ℝ} {z : ℝ → ℝ} (hT : 0 ≤ T) (hδ : 0 < δ)
    (hz : ContinuousOn z (Icc 0 T)) :
    ∃ t ∈ Icc 0 T, peak T δ z = z t/(t+δ) ∧ ∀ s ∈ Icc 0 T, z s/(s+δ) ≤ peak T δ z := by
  have hc : ContinuousOn (fun t => z t/(t+δ)) (Icc 0 T) :=
    hz.div (by fun_prop) (fun t ht => ne_of_gt (by linarith [ht.1]))
  obtain ⟨t,ht,hm⟩ := isCompact_Icc.exists_isMaxOn (nonempty_Icc.mpr hT) hc
  have he := peak_eq_of_max ht hm
  exact ⟨t,ht,he,fun s hs => (hm hs).trans_eq he.symm⟩

theorem peak_difference {T δ E : ℝ} {z w : ℝ → ℝ} (hT : 0 ≤ T) (hδ : 0 < δ)
    (hE : 0 ≤ E) (hz : ContinuousOn z (Icc 0 T)) (hw : ContinuousOn w (Icc 0 T))
    (hzw : ∀ t ∈ Icc 0 T, |z t-w t| ≤ E) : |peak T δ z-peak T δ w| ≤ E/δ := by
  obtain ⟨s,hs,hsp,hsm⟩ := peak_attained hT hδ hz
  obtain ⟨t,ht,htp,htm⟩ := peak_attained hT hδ hw
  have hrat (r : ℝ) (hr : r ∈ Icc 0 T) : |z r/(r+δ)-w r/(r+δ)| ≤ E/δ := by
    rw [← sub_div,abs_div,abs_of_pos (by linarith [hr.1] : 0 < r+δ)]
    exact (div_le_div_of_nonneg_right (hzw r hr) (by linarith [hr.1])).trans
      (div_le_div_of_nonneg_left hE hδ (by linarith [hr.1]))
  apply abs_sub_le_iff.mpr
  constructor
  · have h := (abs_sub_le_iff.mp (hrat s hs)).1
    rw [hsp]
    linarith [htm s hs]
  · have h := (abs_sub_le_iff.mp (hrat t ht)).2
    rw [htp]
    linarith [hsm t ht]

end BoltzmannNonuniqueness.Cap

end

end

end OAI
end

section
-- module Solutions.OAIQ080_BZ.Boltzmann_Jets_ColdFamilyGlobalStabilityAE
attribute [-instance] _root_.OAI.BoltzmannNonuniqueness.ChartKernel.offAxis_sFinite _root_.OAI.BoltzmannNonuniqueness.EuclideanFlight.sourcePullback_finite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.characteristicGainKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.hotKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.mixedKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.retainedKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.coldCylinderVolume_finite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.copyColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.mainCoreKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.selectedColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCoreSheet.dilatedColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCoreSheet.kineticColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.PeriodicApproximation.fiberMeasure_finite _root_.OAI.BoltzmannNonuniqueness.PositiveIteration.awayOriginKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.PositiveIteration.nearOriginKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamNormalCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamNormalRetainedKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.dampedCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.densityScaledCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalBeamKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalCollision_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalPhysicalEvent_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalWindowEvent_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.physicalEventMeasure_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.scaledBeamNormalKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.WeakTime.phaseEndpointKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.WeakTime.phaseIncrement_finite _root_.OAI.BoltzmannNonuniqueness.WeakTime.phaseSeed_sFinite _root_.OAI.BoltzmannNonuniqueness.WeakTime.residenceKernel_sFinite
attribute [-simp] _root_.OAI.BoltzmannNonuniqueness.EuclideanFlight.phaseEquiv_snd _root_.OAI.BoltzmannNonuniqueness.timeTranslation_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Fixed-interval stability of the countable cold system -/

noncomputable section

open MeasureTheory MeasureTheory.Measure Set
open BoltzmannNonuniqueness.PositiveIntegral (window)

namespace BoltzmannNonuniqueness.WeightedLocal

theorem cold_bounded_interval_stability {I : Type*} [Countable I] {q b L T R : ℝ}
    (hq : q < 2) (hb : 0 ≤ b) (hL : 0 ≤ L) (hT : 0 ≤ T) (hR : 0 ≤ R)
    (hloss : R*CutoffLipschitz.frequencyConstant q b ≤ L) :
    ∃ C : ℝ, 0 < C ∧ ∀ {B D : ℝ}, 0 ≤ B → 0 ≤ D →
      ∀ {F G : ℝ × JetPrototype.Phase → ℝ} {c d : I → ℝ × JetPrototype.Phase → ℝ}
        {c₀ d₀ : I → JetPrototype.Phase → ℝ},
      Measurable F → Measurable G → (∀ i, Measurable (c i)) → (∀ i, Measurable (d i)) →
      (∀ u, 0 ≤ F u ∧ F u ≤ R) → (∀ u, 0 ≤ G u ∧ G u ≤ R) →
      (∀ i u, 0 ≤ c i u) → (∀ i u, 0 ≤ d i u) →
      (∀ s : Finset I, ∀ u, ∑ i ∈ s, c i u ≤ F u) →
      (∀ s : Finset I, ∀ u, ∑ i ∈ s, d i u ≤ G u) →
      (∀ i, ColdMildAE q b L T F (c₀ i) (c i)) →
      (∀ i, ColdMildAE q b L T G (d₀ i) (d i)) →
      (∀ t ∈ Icc 0 T, ∀ᵐ p ∂FlightMeasure.phaseVolume, |F (t,p)-G (t,p)| ≤ D) →
      (∀ᵐ p ∂FlightMeasure.phaseVolume, (∑' i, |c₀ i p-d₀ i p|) ≤ B) →
      ∀ t ∈ Icc 0 T, ∀ᵐ p ∂FlightMeasure.phaseVolume, (∑' i, |c i (t,p)-d i (t,p)|) ≤
        C*(B+T*(R*CutoffLipschitz.frequencyConstant q b)*D) := by
  classical
  let J := R*CutoffLipschitz.frequencyConstant q b
  let K := 2*R*HotApplication.realBound q+L+J
  have hJ : 0 ≤ J := mul_nonneg hR (CutoffLipschitz.frequencyConstant_nonneg hb q)
  have hK : 0 ≤ K := by
    have := (HotApplication.realBound_pos q).le
    dsimp [K]
    positivity
  let δ := 1/(2*(K+1))
  have hδ : 0 < δ := div_pos zero_lt_one (by positivity)
  have hδK : δ*K < 1/2 := by
    have hd : 0 < 2*(K+1) := by positivity
    dsimp [δ]
    rw [div_mul_eq_mul_div,div_lt_iff₀ hd]
    nlinarith
  obtain ⟨n,hn⟩ := exists_nat_ge (T/δ)
  have hreach : T ≤ (n:ℝ)*δ := (div_le_iff₀ hδ).mp hn
  refine ⟨4^n,by positivity,?_⟩
  intro B D hB hD F G c d c₀ d₀ hFm hGm hcm hdm hF hG hcn hdn hcSum hdSum hce hde hFG hseed
  let Z := B+T*J*D
  have hZ : 0 ≤ Z := by dsimp [Z] <;> positivity
  have hes (u) : Summable (fun i => |c i u-d i u|) :=
    ((summable_of_sum_le (fun i => hcn i u) (fun s => hcSum s u)).sub
      (summable_of_sum_le (fun i => hdn i u) (fun s => hdSum s u))).abs
  have hcb (i) (u) : 0 ≤ c i u ∧ c i u ≤ R := by
    refine ⟨hcn i u,?_⟩
    simpa only [Finset.sum_singleton] using (hcSum {i} u).trans (hF u).2
  have hdb (i) (u) : 0 ≤ d i u ∧ d i u ≤ R := by
    refine ⟨hdn i u,?_⟩
    simpa only [Finset.sum_singleton] using (hdSum {i} u).trans (hG u).2
  have hzero : ∀ᵐ p ∂FlightMeasure.phaseVolume, (∑' i, |c i (0,p)-d i (0,p)|) ≤ Z := by
    filter_upwards [ae_all_iff.mpr (fun i => (hce i).initial_ae hT),
      ae_all_iff.mpr (fun i => (hde i).initial_ae hT),hseed] with p hc hd hp
    simpa only [hc,hd] using hp.trans (show B ≤ Z from le_add_of_nonneg_right (by positivity))
  have hsteps : ∀ j : ℕ, ∀ t ∈ Icc 0 (min ((j:ℝ)*δ) T),
      ∀ᵐ p ∂FlightMeasure.phaseVolume, (∑' i, |c i (t,p)-d i (t,p)|) ≤ (4:ℝ)^j*Z := by
    intro j
    induction j with
    | zero =>
      intro t ht
      have htzero : t ≤ 0 := by simpa only [Nat.cast_zero,zero_mul,min_eq_left hT] using ht.2
      have ht0 : t = 0 := le_antisymm htzero ht.1
      subst t
      simpa only [pow_zero,one_mul] using hzero
    | succ j ih =>
      intro t ht
      have htT : t ≤ T := ht.2.trans (min_le_right _ _)
      have htj : t ≤ ((j+1:ℕ):ℝ)*δ := ht.2.trans (min_le_left _ _)
      have hBj : 0 ≤ (4:ℝ)^j*Z := mul_nonneg (pow_nonneg (by norm_num) j) hZ
      by_cases hprefix : t ≤ min ((j:ℝ)*δ) T
      · exact (ih t ⟨ht.1,hprefix⟩).mono (fun p hp => hp.trans (by rw [pow_succ]; nlinarith))
      · let s : ℝ := (j:ℝ)*δ
        have hs : 0 ≤ s := mul_nonneg (Nat.cast_nonneg j) hδ.le
        have hst : s < t := lt_of_not_ge (fun h => hprefix (le_min h htT))
        have hsT : s ≤ T := hst.le.trans htT
        have hinit := ih s ⟨hs,le_min le_rfl hsT⟩
        let U := t-s
        have hU : 0 ≤ U := sub_nonneg.mpr hst.le
        have hUδ : U ≤ δ := by
          dsimp [U,s]
          rw [Nat.cast_add,Nat.cast_one] at htj
          nlinarith
        have hUK : U*K < 1/2 := lt_of_le_of_lt (mul_le_mul_of_nonneg_right hUδ hK) hδK
        have hsU : s+U ≤ T := by dsimp [U] <;> linarith
        have hsmall : U*K < 1 := hUK.trans (by norm_num)
        have hwinFG : ∀ᵐ u ∂spacetimeVolume, |window s U F u-window s U G u| ≤ D := by
          apply (ae_prod_iff_ae_ae (measurableSet_le
            ((PositiveIntegral.measurable_window s U hFm).sub
              (PositiveIntegral.measurable_window s U hGm)).abs measurable_const)).mpr
          apply ae_of_all
          intro r
          change ∀ᵐ p ∂FlightMeasure.phaseVolume,
            |F (s+PositiveIntegral.time U r,p)-G (s+PositiveIntegral.time U r,p)| ≤ D
          have hr := PositiveIntegral.time_bounds hU r
          exact hFG (s+PositiveIntegral.time U r) ⟨by linarith [hr.1],by linarith [hr.2]⟩
        have hseedW (a : Finset I) : ∀ᵐ p ∂FlightMeasure.phaseVolume,
            (∑ i ∈ a, |c i (s,p)-d i (s,p)|) ≤ (4:ℝ)^j*Z :=
          hinit.mono (fun p hp => ((hes (s,p)).sum_le_tsum a (fun i _ => abs_nonneg _)).trans hp)
        have hw := cold_family_difference_ae hq hb hL hU hR hBj hD hloss hsmall
          (PositiveIntegral.measurable_window s U hFm) (PositiveIntegral.measurable_window s U hGm)
          (fun i => PositiveIntegral.measurable_window s U (hcm i))
          (fun i => PositiveIntegral.measurable_window s U (hdm i))
          (fun u => hF _) (fun u => hG _) (fun i u => hcn i _) (fun i u => hdn i _)
          (fun a u => hcSum a _) (fun a u => hdSum a _) hwinFG hseedW
          (fun i => (hce i).window hq hb hL hT hR hloss hs hU hsU hFm (hcm i) hF (hcb i))
          (fun i => (hde i).window hq hb hL hT hR hloss hs hU hsU hGm (hdm i) hG (hdb i)) U
        have hUJD : U*J*D ≤ (4:ℝ)^j*Z := by
          have hUT : U ≤ T := by dsimp [U] <;> linarith
          have hzle : Z ≤ (4:ℝ)^j*Z := le_mul_of_one_le_left hZ (one_le_pow₀ (by norm_num))
          have hbound : U*J*D ≤ T*J*D := mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_right hUT hJ) hD
          exact hbound.trans ((le_add_of_nonneg_left hB).trans hzle)
        have hfac : ((4:ℝ)^j*Z+U*J*D)/(1-U*K) ≤ (4:ℝ)^(j+1)*Z := by
          apply (div_le_iff₀ (by linarith : 0 < 1-U*K)).mpr
          rw [pow_succ]
          nlinarith
        filter_upwards [hw] with p hp
        change (∑' i, |c i (s+PositiveIntegral.time U U,p)-d i (s+PositiveIntegral.time U U,p)|) ≤ _ at hp
        rw [GaussianLocal.time_eq (show U ∈ Icc 0 U from ⟨hU,le_rfl⟩),
          show s+U=t by dsimp [U]; ring] at hp
        exact hp.trans hfac
  intro t ht
  exact hsteps n t ⟨ht.1,by simpa only [min_eq_right hreach] using ht.2⟩

end BoltzmannNonuniqueness.WeightedLocal

end

end OAI
end

section
-- module Solutions.OAIQ080_BZ.Boltzmann_Branching_RebuiltHotRegularity
attribute [-instance] _root_.OAI.BoltzmannNonuniqueness.ChartKernel.offAxis_sFinite _root_.OAI.BoltzmannNonuniqueness.EuclideanFlight.sourcePullback_finite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.characteristicGainKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.hotKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.mixedKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.retainedKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.coldCylinderVolume_finite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.copyColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.mainCoreKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.selectedColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCoreSheet.dilatedColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCoreSheet.kineticColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.PeriodicApproximation.fiberMeasure_finite _root_.OAI.BoltzmannNonuniqueness.PositiveIteration.awayOriginKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.PositiveIteration.nearOriginKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamNormalCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamNormalRetainedKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.dampedCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.densityScaledCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalBeamKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalCollision_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalPhysicalEvent_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalWindowEvent_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.physicalEventMeasure_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.scaledBeamNormalKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.WeakTime.phaseEndpointKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.WeakTime.phaseIncrement_finite _root_.OAI.BoltzmannNonuniqueness.WeakTime.phaseSeed_sFinite _root_.OAI.BoltzmannNonuniqueness.WeakTime.residenceKernel_sFinite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

/-! # Uniform seed dependence for the reconstructed hot norm on a fixed interval -/

noncomputable section

open MeasureTheory Set

namespace BoltzmannNonuniqueness.WeightedLocal

theorem exists_rebuilt_hot_stability_constant {I : Type*} [Countable I] {q b L T R : ℝ}
    (hq : q < 2) (hb : 0 ≤ b) (hL : 0 ≤ L) (hT : 0 ≤ T) (hR : 0 ≤ R)
    (hloss : R*CutoffLipschitz.frequencyConstant q b ≤ L) :
    ∃ C : ℝ, 0 < C ∧ ∀ {A : ℝ}, 0 ≤ A →
      ∀ {F G : ℝ × JetPrototype.Phase → ℝ} {F₀ G₀ : JetPrototype.Phase → ℝ}
        {c₀ : I → JetPrototype.Phase → ℝ},
      Measurable F → Measurable G → (∀ i, Measurable (c₀ i)) →
      (∀ u, 0 ≤ F u ∧ F u ≤ R) → (∀ u, 0 ≤ G u ∧ G u ≤ R) →
      (∀ i p, 0 ≤ c₀ i p ∧ c₀ i p ≤ R) →
      (∀ s : Finset I, ∀ p, ∑ i ∈ s, c₀ i p ≤ F₀ p) →
      (∀ s : Finset I, ∀ p, ∑ i ∈ s, c₀ i p ≤ G₀ p) →
      (∀ᵐ p ∂FlightMeasure.phaseVolume, |F₀ p-G₀ p| ≤ A) →
      (∀ t, (fun p => F (t,p)) =ᵐ[FlightMeasure.phaseVolume]
        (fun p => PositiveIntegral.value T L JetBarrier.flight F₀ (forcing q b L F) (t,p))) →
      (∀ t, (fun p => G (t,p)) =ᵐ[FlightMeasure.phaseVolume]
        (fun p => PositiveIntegral.value T L JetBarrier.flight G₀ (forcing q b L G) (t,p))) →
      ∀ t ∈ Icc 0 T,
        |PhaseEssSup.size (fun p => F (t,p)-∑' i, rebuiltColdFamily q b L T F c₀ i (t,p))-
          PhaseEssSup.size (fun p => G (t,p)-∑' i, rebuiltColdFamily q b L T G c₀ i (t,p))| ≤ C*A := by
  obtain ⟨C,hC,hTotal⟩ := bounded_interval_stability hq hb hL hT hR hloss
  obtain ⟨E,hE,hCold⟩ := cold_bounded_interval_stability (I := I) hq hb hL hT hR hloss
  let J := R*CutoffLipschitz.frequencyConstant q b
  have hJ : 0 ≤ J := mul_nonneg hR (CutoffLipschitz.frequencyConstant_nonneg hb q)
  refine ⟨C+E*T*J*C,by positivity,?_⟩
  intro A hA F G F₀ G₀ c₀ hFm hGm hc₀m hF hG hc₀ hcF₀ hcG₀ hseed hFeq hGeq
  obtain ⟨hcm,hcb,hcs,_,hce⟩ := rebuiltColdFamily_properties hq hb hL hT hR hloss
    hFm hc₀m hF hc₀ hcF₀ hFeq
  obtain ⟨hdm,hdb,hds,_,hde⟩ := rebuiltColdFamily_properties hq hb hL hT hR hloss
    hGm hc₀m hG hc₀ hcG₀ hGeq
  have hcn (i) (u) : 0 ≤ rebuiltColdFamily q b L T F c₀ i u := (hcb i u).1
  have hdn (i) (u) : 0 ≤ rebuiltColdFamily q b L T G c₀ i u := (hdb i u).1
  have hFG := hTotal hA hFm hGm hF hG (fun t _ => hFeq t) (fun t _ => hGeq t) hseed
  have hseedC : ∀ᵐ p ∂FlightMeasure.phaseVolume, (∑' i, |c₀ i p-c₀ i p|) ≤ (0:ℝ) := by
    exact ae_of_all _ (fun p => by simp only [sub_self,abs_zero,tsum_zero,le_refl])
  have hcd := hCold (le_refl 0) (mul_nonneg hC.le hA) hFm hGm hcm hdm hF hG
    hcn hdn hcs hds hce hde hFG hseedC
  intro t ht
  have hn := PhaseEssSup.hot_difference_ae (mul_nonneg hC.le hA)
    (show 0 ≤ E*(T*J*(C*A)) by positivity)
    (hFm.comp (measurable_const.prodMk measurable_id)) (hGm.comp (measurable_const.prodMk measurable_id))
    (fun i => (hcm i).comp (measurable_const.prodMk measurable_id))
    (fun i => (hdm i).comp (measurable_const.prodMk measurable_id))
    (fun p => hF (t,p)) (fun p => hG (t,p)) (fun i p => hcn i (t,p)) (fun i p => hdn i (t,p))
    (fun s p => hcs s (t,p)) (fun s p => hds s (t,p)) (hFG t ht)
    (by simpa only [zero_add,Function.comp_apply,id_eq,J] using hcd t ht)
  calc
    _ ≤ C*A+E*(T*J*(C*A)) := hn
    _ = (C+E*T*J*C)*A := by ring

end BoltzmannNonuniqueness.WeightedLocal

end

end

section

/-! # Time regularity of the reconstructed hot remainder -/

noncomputable section

open MeasureTheory Set

namespace BoltzmannNonuniqueness.WeightedLocal

theorem rebuilt_hot_continuous {I : Type*} [Countable I] {q b L T R : ℝ}
    (hq : q < 2) (hb : 0 ≤ b) (hL : 0 ≤ L) (hT : 0 ≤ T) (hR : 0 ≤ R)
    (hloss : R*CutoffLipschitz.frequencyConstant q b ≤ L)
    {F : ℝ × JetPrototype.Phase → ℝ} {F₀ : JetPrototype.Phase → ℝ}
    {c₀ : I → JetPrototype.Phase → ℝ}
    (hFm : Measurable F) (hF₀m : Measurable F₀) (hc₀m : ∀ i, Measurable (c₀ i))
    (hF : ∀ u, 0 ≤ F u ∧ F u ≤ R) (hF₀ : ∀ p, F₀ p ≤ R)
    (hc₀ : ∀ i p, 0 ≤ c₀ i p ∧ c₀ i p ≤ R)
    (hSum₀ : ∀ s : Finset I, ∀ p, ∑ i ∈ s, c₀ i p ≤ F₀ p)
    (hFeq : ∀ t, (fun p => F (t,p)) =ᵐ[FlightMeasure.phaseVolume]
      (fun p => PositiveIntegral.value T L JetBarrier.flight F₀ (forcing q b L F) (t,p))) :
    ContinuousOn (fun t => PhaseEssSup.size (fun p =>
      F (t,p)-∑' i, rebuiltColdFamily q b L T F c₀ i (t,p))) (Icc 0 T) := by
  obtain ⟨hcm,hcb,hSum,_,hceq⟩ := rebuiltColdFamily_properties hq hb hL hT hR hloss
    hFm hc₀m hF hc₀ hSum₀ hFeq
  have hcn (i) (u) : 0 ≤ rebuiltColdFamily q b L T F c₀ i u := (hcb i u).1
  have hhb := family_hot_bounds hq hb hR hloss hFm hcm hF hcn hSum
  have hhm := family_hot_mildAE hq hb hL hT hR hloss hFm hcm hF hcn hSum
    (fun i p => (hc₀ i p).1) hSum₀ (fun t _ => hFeq t) hceq
  have hinit (p) : 0 ≤ F₀ p-∑' i, c₀ i p ∧ F₀ p-∑' i, c₀ i p ≤ R := by
    have hn : 0 ≤ ∑' i, c₀ i p := tsum_nonneg (fun i => (hc₀ i p).1)
    have hs : (∑' i, c₀ i p) ≤ F₀ p := Real.tsum_le_of_sum_le
      (fun i => (hc₀ i p).1) (fun s => hSum₀ s p)
    exact ⟨sub_nonneg.mpr hs,(sub_le_self _ hn).trans (hF₀ p)⟩
  exact PhaseEssSup.continuousOn_size_of_mildAE
    (f₀ := fun p => F₀ p-∑' i, c₀ i p)
    (g := remainderForcing q b L F (rebuiltColdFamily q b L T F c₀))
    (f := fun u => F u-∑' i, rebuiltColdFamily q b L T F c₀ i u) hT hL hR
    (show 0 ≤ HotApplication.realBound q*R^2+L*R by have := (HotApplication.realBound_pos q).le; positivity)
    (hF₀m.sub (Measurable.tsum hc₀m)) hhb.2.2.1 hinit hhb.2.2.2 hhm

end BoltzmannNonuniqueness.WeightedLocal

end

end

end OAI
end

section
-- module Solutions.OAIQ080_BZ.Boltzmann_Compactness_PeriodicMildApproximation
attribute [-instance] _root_.OAI.BoltzmannNonuniqueness.ChartKernel.offAxis_sFinite _root_.OAI.BoltzmannNonuniqueness.EuclideanFlight.sourcePullback_finite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.characteristicGainKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.hotKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.mixedKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.retainedKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.coldCylinderVolume_finite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.copyColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.mainCoreKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.selectedColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCoreSheet.dilatedColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCoreSheet.kineticColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.PositiveIteration.awayOriginKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.PositiveIteration.nearOriginKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamNormalCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamNormalRetainedKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.dampedCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.densityScaledCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalBeamKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalCollision_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalPhysicalEvent_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalWindowEvent_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.physicalEventMeasure_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.scaledBeamNormalKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.WeakTime.phaseEndpointKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.WeakTime.phaseIncrement_finite _root_.OAI.BoltzmannNonuniqueness.WeakTime.phaseSeed_sFinite _root_.OAI.BoltzmannNonuniqueness.WeakTime.residenceKernel_sFinite
attribute [-simp] _root_.OAI.BoltzmannNonuniqueness.EuclideanFlight.phaseEquiv_snd _root_.OAI.BoltzmannNonuniqueness.timeTranslation_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

/-! # Bounded positive periodic mild states and finite-step continuation -/

noncomputable section

open MeasureTheory Set
open BoltzmannNonuniqueness.WeightedLocal BoltzmannNonuniqueness.WeightedTranslation

namespace BoltzmannNonuniqueness.WeightedLocalControl

namespace PeriodicMildState

theorem all_mild {q b L T R : ℝ} {f₀ : JetPrototype.Phase → ℝ}
    (F : PeriodicMildState q b L T R f₀) (hT : 0 ≤ T) :
    ∀ t, (fun p => F.value (t,p)) =ᵐ[FlightMeasure.phaseVolume]
      (fun p => PositiveIntegral.value T L JetBarrier.flight f₀ (forcing q b L F.value) (t,p)) :=
  mild_all_of_time_clamp hT L F.clamped F.mild

theorem exists_extension {q b A T : ℝ} {f₀ : JetPrototype.Phase → ℝ}
    (F : PeriodicMildState q b (damping q b A) T (2*A) f₀)
    (hq : q < 2) (hb : 0 ≤ b) (hA : 0 < A) (hT : 0 ≤ T)
    (hFA : ∀ᵐ p ∂FlightMeasure.phaseVolume, F.value (T,p) ≤ A) :
    Nonempty (PeriodicMildState q b (damping q b A) (T+lifespan q b A) (2*A) f₀) := by
  obtain ⟨G,hGm,hG,hGeq,hGper,_⟩ := exists_continuation_step hq hb hA hT
    F.measurable_value F.value_bounds hFA F.mild F.periodic
  have htotal : 0 ≤ T+lifespan q b A := add_nonneg hT (lifespan_pos (q := q) hb hA).le
  refine ⟨⟨clampTime (T+lifespan q b A) G,measurable_clampTime hGm _,
    fun u => hG _,?_,clampTime_idempotent htotal G,?_⟩⟩
  · exact fun t _ => mildAE_all_times htotal (fun r _ => hGeq r) t
  · intro n
    funext u
    exact congrFun (hGper n) (PositiveIntegral.time (T+lifespan q b A) u.1,u.2)

end PeriodicMildState

theorem exists_to_time_of_apriori {q b A τ : ℝ} (hq : q < 2) (hb : 0 ≤ b)
    (hA : 0 < A) (hτ : 0 ≤ τ) {f₀ : JetPrototype.Phase → ℝ}
    (hf₀m : Measurable f₀) (hf₀ : ∀ p, 0 ≤ f₀ p ∧ f₀ p ≤ A)
    (hper : ∀ n p, f₀ (shift (JetCopyDatum.displacement n) p) = f₀ p)
    (hapriori : ∀ T, 0 ≤ T → T ≤ τ →
      ∀ F : PeriodicMildState q b (damping q b A) T (2*A) f₀,
        ∀ᵐ p ∂FlightMeasure.phaseVolume, F.value (T,p) ≤ A) :
    Nonempty (PeriodicMildState q b (damping q b A) τ (2*A) f₀) := by
  let δ := lifespan q b A
  have hδ : 0 < δ := lifespan_pos hb hA
  have hex : ∀ n : ℕ, Nonempty (PeriodicMildState q b (damping q b A)
      (min ((n:ℝ)*δ) τ) (2*A) f₀) := by
    intro n
    induction n with
    | zero =>
      simpa only [Nat.cast_zero,zero_mul,min_eq_left hτ] using
        (show Nonempty (PeriodicMildState q b (damping q b A) 0 (2*A) f₀) from
          ⟨PeriodicMildState.initial hA.le hf₀m hf₀ hper⟩)
    | succ n ih =>
      have hn : 0 ≤ (n:ℝ)*δ := mul_nonneg (Nat.cast_nonneg n) hδ.le
      by_cases hstop : τ ≤ (n:ℝ)*δ
      · have hnext : τ ≤ ((n+1:ℕ):ℝ)*δ := by
          rw [Nat.cast_add,Nat.cast_one]
          nlinarith
        rw [min_eq_right hnext,min_eq_right hstop] at *
        exact ih
      · obtain ⟨F⟩ := ih
        have hS : 0 ≤ min ((n:ℝ)*δ) τ := le_min hn hτ
        obtain ⟨G⟩ := F.exists_extension hq hb hA hS
          (hapriori _ hS (min_le_right _ _) F)
        have hnew : 0 ≤ min (((n+1:ℕ):ℝ)*δ) τ :=
          le_min (mul_nonneg (Nat.cast_nonneg _) hδ.le) hτ
        have hle : min (((n+1:ℕ):ℝ)*δ) τ ≤ min ((n:ℝ)*δ) τ+δ := by
          rw [min_eq_left (le_of_not_ge hstop)]
          calc
            _ ≤ (((n+1:ℕ):ℝ)*δ) := min_le_left _ _
            _ = (n:ℝ)*δ+δ := by rw [Nat.cast_add,Nat.cast_one]; ring
        exact ⟨G.restrict hnew hle⟩
  obtain ⟨n,hn⟩ := exists_nat_ge (τ/δ)
  have hreach : τ ≤ (n:ℝ)*δ := (div_le_iff₀ hδ).mp hn
  simpa only [min_eq_right hreach] using hex n

end BoltzmannNonuniqueness.WeightedLocalControl

end

end

section

/-! # A bounded sequence of periodic mild states closes at its limiting seed -/

noncomputable section

open MeasureTheory Filter
open scoped Topology
open BoltzmannNonuniqueness.WeightedLocal

namespace BoltzmannNonuniqueness.WeightedLocalControl.PeriodicMildState

theorem exists_seed_limit {q b L T R : ℝ}
    (hq : q < 2) (hb : 0 ≤ b) (hL : 0 ≤ L) (hT : 0 ≤ T) (hR : 0 ≤ R)
    (hloss : R*CutoffLipschitz.frequencyConstant q b ≤ L)
    {f₀ : ℕ → JetPrototype.Phase → ℝ} {g₀ : JetPrototype.Phase → ℝ}
    (F : ∀ n, PeriodicMildState q b L T R (f₀ n))
    {a : ℕ → ℝ} (ha : ∀ n, 0 ≤ a n) (ha0 : Tendsto a atTop (𝓝 0))
    (hseed : ∀ n, ∀ᵐ p ∂FlightMeasure.phaseVolume, |f₀ n p-g₀ p| ≤ a n) :
    ∃ C : ℝ, 0 < C ∧ ∃ G : PeriodicMildState q b L T R g₀,
      ∀ n t, ∀ᵐ p ∂FlightMeasure.phaseVolume, |(F n).value (t,p)-G.value (t,p)| ≤ C*a n := by
  obtain ⟨C,hC,hstable⟩ := bounded_interval_stability hq hb hL hT hR hloss
  let D := C+1
  have hD : 0 < D := by dsimp [D] <;> linarith
  have hpair (n m) : ∀ᵐ p ∂FlightMeasure.phaseVolume, |f₀ n p-f₀ m p| ≤ a n+a m := by
    filter_upwards [hseed n,hseed m] with p hn hm
    exact (abs_sub_le (f₀ n p) (g₀ p) (f₀ m p)).trans
      (add_le_add hn (by simpa only [abs_sub_comm] using hm))
  have hclose (n m t) : ∀ᵐ p ∂FlightMeasure.phaseVolume,
      |(F n).value (t,p)-(F m).value (t,p)| ≤ D*a n+D*a m := by
    have hs := hstable (add_nonneg (ha n) (ha m)) (F n).measurable_value (F m).measurable_value
      (F n).value_bounds (F m).value_bounds (F n).mild (F m).mild (hpair n m)
      (PositiveIntegral.time T t) (PositiveIntegral.time_bounds hT t)
    filter_upwards [hs] with p hp
    rw [(F n).clamped (t,p),(F m).clamped (t,p)] at hp
    exact hp.trans (by dsimp [D] <;> nlinarith [ha n,ha m])
  have hseedD (n) : ∀ᵐ p ∂FlightMeasure.phaseVolume, |f₀ n p-g₀ p| ≤ D*a n :=
    (hseed n).mono (fun p hp => hp.trans (by dsimp [D] <;> nlinarith [ha n]))
  have haD : Tendsto (fun n => D*a n) atTop (𝓝 0) := by
    simpa only [mul_zero] using tendsto_const_nhds.mul ha0
  obtain ⟨G,hGm,hGb,hGe,hFG,hInv⟩ := exists_mild_limit hq hb hL hT hR hloss
    (fun n => (F n).measurable_value) (fun n => (F n).value_bounds)
    (fun n => mul_nonneg hD.le (ha n)) haD hclose hseedD (fun n => (F n).all_mild hT)
  have hclamp : ∀ u, G (PositiveIntegral.time T u.1,u.2) = G u :=
    hInv (fun u => (PositiveIntegral.time T u.1,u.2)) (fun n => (F n).clamped)
  have hper (n) : WeightedTranslation.pull (JetCopyDatum.displacement n) G = G := by
    funext u
    exact hInv (fun u => (u.1,WeightedTranslation.shift (JetCopyDatum.displacement n) u.2))
      (fun k u => congrFun ((F k).periodic n) u) u
  exact ⟨D,hD,⟨G,hGm,hGb,fun t _ => hGe t,hclamp,hper⟩,hFG⟩

end BoltzmannNonuniqueness.WeightedLocalControl.PeriodicMildState

end

end

section

/-! # Persistence of bounded periodic solutions under perturbing the initial seed -/

noncomputable section

open MeasureTheory Set
open BoltzmannNonuniqueness.WeightedLocal BoltzmannNonuniqueness.WeightedTranslation

namespace BoltzmannNonuniqueness.WeightedLocalControl.PeriodicMildState

theorem nearby_seed_exists {q b A B T : ℝ} {f₀ : JetPrototype.Phase → ℝ}
    (hq : q < 2) (hb : 0 ≤ b) (hA : 0 < A) (hT : 0 ≤ T) (hBA : B < A)
    (F : PeriodicMildState q b (damping q b A) T (2*A) f₀)
    (hsmall : ∀ t ∈ Icc 0 T, ∀ᵐ p ∂FlightMeasure.phaseVolume, F.value (t,p) ≤ B) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ {g₀ : JetPrototype.Phase → ℝ}, Measurable g₀ →
      (∀ p, 0 ≤ g₀ p ∧ g₀ p ≤ A) →
      (∀ n p, g₀ (shift (JetCopyDatum.displacement n) p) = g₀ p) →
      (∀ᵐ p ∂FlightMeasure.phaseVolume, |g₀ p-f₀ p| ≤ ε) →
      Nonempty (PeriodicMildState q b (damping q b A) T (2*A) g₀) := by
  have hR : 0 ≤ 2*A := by positivity
  have hL : 0 ≤ damping q b A := (bounds hb hA).1
  have hloss : (2*A)*CutoffLipschitz.frequencyConstant q b ≤ damping q b A := le_rfl
  obtain ⟨C,hC,hstable⟩ := bounded_interval_stability_uniform hq hb hL hT hR hloss
  let ε := (A-B)/(C+1)
  have hε : 0 < ε := div_pos (sub_pos.mpr hBA) (by linarith)
  have heq : ε*(C+1) = A-B := div_mul_cancel₀ _ (by linarith : C+1 ≠ 0)
  have hbound : B+C*ε ≤ A := by nlinarith [hε.le]
  refine ⟨ε,hε,?_⟩
  intro g₀ hgm hgb hgp hseed
  apply exists_to_time_of_apriori hq hb hA hT hgm hgb hgp
  intro S hS hST G
  let F' := F.restrict hS hST
  have hd := hstable hS hST hε.le G.measurable_value F'.measurable_value
    G.value_bounds F'.value_bounds G.mild F'.mild hseed S ⟨hS,le_rfl⟩
  filter_upwards [hd,hsmall S ⟨hS,hST⟩] with p hp hFp
  have he : F'.value (S,p) = F.value (S,p) := by
    change F.value (PositiveIntegral.time S S,p) = _
    rw [GaussianLocal.time_eq (show S ∈ Icc 0 S from ⟨hS,le_rfl⟩)]
  rw [he] at hp
  have h := (abs_sub_le_iff.mp hp).1
  linarith

end BoltzmannNonuniqueness.WeightedLocalControl.PeriodicMildState

end

end

section

/-! # Closedness of the cap under convergence of bounded seed parameters -/

noncomputable section

open MeasureTheory Filter
open scoped Topology
open BoltzmannNonuniqueness.WeightedLocal

namespace BoltzmannNonuniqueness.WeightedLocalControl.PeriodicMildState

theorem affineSeed_difference {f ψ : JetPrototype.Phase → ℝ} {M : ℝ}
    (hψ : ∀ p, |ψ p| ≤ M) (a b : ℝ) (p : JetPrototype.Phase) :
    |affineSeed f ψ a p-affineSeed f ψ b p| ≤ |a-b| * M := by
  have he : affineSeed f ψ a p-affineSeed f ψ b p = (a-b)*ψ p := by unfold affineSeed; ring
  rw [he,abs_mul]
  exact mul_le_mul_of_nonneg_left (hψ p) (abs_nonneg _)

theorem exists_cap_limit {I : Type*} [Countable I] {q b L T R δ M ell : ℝ}
    (hq : q < 2) (hb : 0 ≤ b) (hL : 0 ≤ L) (hT : 0 ≤ T) (hR : 0 ≤ R)
    (hδ : 0 < δ) (hM : 0 ≤ M) (hloss : R*CutoffLipschitz.frequencyConstant q b ≤ L)
    {f ψ : JetPrototype.Phase → ℝ} (hfm : Measurable f) (hψm : Measurable ψ)
    (hψ : ∀ p, |ψ p| ≤ M)
    {c₀ : I → JetPrototype.Phase → ℝ} (hc₀m : ∀ i, Measurable (c₀ i))
    (hc₀ : ∀ i p, 0 ≤ c₀ i p ∧ c₀ i p ≤ R)
    {elln : ℕ → ℝ} (hell : Tendsto elln atTop (𝓝 ell))
    (hinit : ∀ p, affineSeed f ψ ell p ≤ R)
    (hinitn : ∀ n p, affineSeed f ψ (elln n) p ≤ R)
    (hdom : ∀ s : Finset I, ∀ p, ∑ i ∈ s, c₀ i p ≤ affineSeed f ψ ell p)
    (hdomn : ∀ n (s : Finset I), ∀ p, ∑ i ∈ s, c₀ i p ≤ affineSeed f ψ (elln n) p)
    (F : ∀ n, PeriodicMildState q b L T R (affineSeed f ψ (elln n)))
    (hcap : ∀ n, hotPeak δ c₀ (F n) ≤ 1) :
    ∃ G : PeriodicMildState q b L T R (affineSeed f ψ ell), hotPeak δ c₀ G ≤ 1 := by
  let a (n : ℕ) := |elln n-ell| * M
  have ha (n) : 0 ≤ a n := mul_nonneg (abs_nonneg _) hM
  have ha0 : Tendsto a atTop (𝓝 0) := by
    have h := (hell.sub_const ell).abs.mul_const M
    simpa only [sub_self,abs_zero,zero_mul] using h
  have hseed (n) : ∀ᵐ p ∂FlightMeasure.phaseVolume,
      |affineSeed f ψ (elln n) p-affineSeed f ψ ell p| ≤ a n :=
    ae_of_all _ (affineSeed_difference hψ (elln n) ell)
  obtain ⟨_,_,G,_⟩ := exists_seed_limit hq hb hL hT hR hloss F ha ha0 hseed
  obtain ⟨C,hC,hst⟩ := exists_rebuilt_hot_stability_constant (I := I) hq hb hL hT hR hloss
  have hgm : Measurable (affineSeed f ψ ell) := hfm.add (hψm.const_mul ell)
  have hnm (n) : Measurable (affineSeed f ψ (elln n)) := hfm.add (hψm.const_mul (elln n))
  have hGreg := rebuilt_hot_continuous hq hb hL hT hR hloss G.measurable_value hgm hc₀m
    G.value_bounds hinit hc₀ hdom (G.all_mild hT)
  have hdiff (n) : |hotPeak δ c₀ (F n)-hotPeak δ c₀ G| ≤ C*a n/δ := by
    have hreg := rebuilt_hot_continuous hq hb hL hT hR hloss (F n).measurable_value (hnm n) hc₀m
      (F n).value_bounds (hinitn n) hc₀ (hdomn n) ((F n).all_mild hT)
    exact Cap.peak_difference hT hδ (mul_nonneg hC.le (ha n)) hreg hGreg
      (hst (ha n) (F n).measurable_value G.measurable_value hc₀m (F n).value_bounds G.value_bounds
        hc₀ (hdomn n) hdom (hseed n) ((F n).all_mild hT) (G.all_mild hT))
  refine ⟨G,?_⟩
  have hupper (n) : hotPeak δ c₀ G ≤ 1+C*a n/δ := by
    have h := (abs_sub_le_iff.mp (hdiff n)).2
    linarith [hcap n]
  have hlim : Tendsto (fun n => 1+C*a n/δ) atTop (𝓝 1) := by
    have h := ((ha0.const_mul C).div_const δ).const_add 1
    simpa only [mul_zero,zero_div,add_zero] using h
  exact le_of_tendsto_of_tendsto' tendsto_const_nhds hlim hupper

end BoltzmannNonuniqueness.WeightedLocalControl.PeriodicMildState

end

end

section

/-! # Strict caps persist for nearby affine seed parameters -/

noncomputable section

open MeasureTheory Set
open BoltzmannNonuniqueness.WeightedLocal BoltzmannNonuniqueness.WeightedTranslation

namespace BoltzmannNonuniqueness.WeightedLocalControl.PeriodicMildState

theorem strict_cap_open {I : Type*} [Countable I] {q b A B T δ M L₀ ell : ℝ}
    (hq : q < 2) (hb : 0 ≤ b) (hA : 0 < A) (hT : 0 ≤ T) (hδ : 0 < δ)
    (hM : 0 ≤ M) (hBA : B < A) (hell : ell ∈ Icc 0 L₀)
    {f ψ : JetPrototype.Phase → ℝ} (hfm : Measurable f) (hψm : Measurable ψ)
    (hψ : ∀ p, |ψ p| ≤ M)
    {c₀ : I → JetPrototype.Phase → ℝ} (hc₀m : ∀ i, Measurable (c₀ i))
    (hc₀ : ∀ i p, 0 ≤ c₀ i p ∧ c₀ i p ≤ 2*A)
    (hseedB : ∀ μ ∈ Icc 0 L₀, ∀ p, 0 ≤ affineSeed f ψ μ p ∧ affineSeed f ψ μ p ≤ A)
    (hdom : ∀ μ ∈ Icc 0 L₀, ∀ s : Finset I, ∀ p, ∑ i ∈ s, c₀ i p ≤ affineSeed f ψ μ p)
    (hper : ∀ μ ∈ Icc 0 L₀, ∀ n p,
      affineSeed f ψ μ (shift (JetCopyDatum.displacement n) p) = affineSeed f ψ μ p)
    (F : PeriodicMildState q b (damping q b A) T (2*A) (affineSeed f ψ ell))
    (hsmall : ∀ t ∈ Icc 0 T, ∀ᵐ p ∂FlightMeasure.phaseVolume, F.value (t,p) ≤ B)
    (hcap : hotPeak δ c₀ F < 1) :
    ∃ r : ℝ, 0 < r ∧ ∀ μ ∈ Icc 0 L₀, |μ-ell| < r →
      ∃ G : PeriodicMildState q b (damping q b A) T (2*A) (affineSeed f ψ μ), hotPeak δ c₀ G < 1 := by
  have hR : 0 ≤ 2*A := by positivity
  have hL : 0 ≤ damping q b A := (bounds hb hA).1
  have hloss : (2*A)*CutoffLipschitz.frequencyConstant q b ≤ damping q b A := le_rfl
  obtain ⟨ε,hε,hnear⟩ := nearby_seed_exists hq hb hA hT hBA F hsmall
  obtain ⟨C,hC,hst⟩ := exists_rebuilt_hot_stability_constant (I := I) hq hb hL hT hR hloss
  let gap := 1-hotPeak δ c₀ F
  have hg : 0 < gap := sub_pos.mpr hcap
  let r := min (ε/(M+1)) (δ*gap/((C+1)*(M+1)))
  have hr : 0 < r := lt_min (div_pos hε (by positivity))
    (div_pos (mul_pos hδ hg) (by positivity))
  refine ⟨r,hr,?_⟩
  intro μ hμ hdist
  let d := |μ-ell|
  let e := d*M
  have hd : 0 ≤ d := abs_nonneg _
  have he : 0 ≤ e := mul_nonneg hd hM
  have hde : d*(M+1) < ε := (lt_div_iff₀ (by positivity : 0 < M+1)).mp
    (lt_of_lt_of_le hdist (min_le_left _ _))
  have heε : e ≤ ε := by dsimp [e] <;> nlinarith
  have hde' : d*((C+1)*(M+1)) < δ*gap :=
    (lt_div_iff₀ (by positivity : 0 < (C+1)*(M+1))).mp
      (lt_of_lt_of_le hdist (min_le_right _ _))
  have hce : C*e < δ*gap := by
    have hm : C*M ≤ (C+1)*(M+1) := by nlinarith
    have hh := mul_le_mul_of_nonneg_left hm hd
    calc
      C*e = d*(C*M) := by dsimp [e] <;> ring
      _ ≤ d*((C+1)*(M+1)) := hh
      _ < δ*gap := hde'
  have hdata (μ) (hμ : μ ∈ Icc 0 L₀) : Measurable (affineSeed f ψ μ) := hfm.add (hψm.const_mul μ)
  have hseed : ∀ᵐ p ∂FlightMeasure.phaseVolume, |affineSeed f ψ μ p-affineSeed f ψ ell p| ≤ e :=
    ae_of_all _ (affineSeed_difference hψ μ ell)
  obtain ⟨G⟩ := hnear (hdata μ hμ) (hseedB μ hμ) (hper μ hμ)
    (hseed.mono (fun p hp => hp.trans heε))
  have hupper (a) (ha : a ∈ Icc 0 L₀) (p) : affineSeed f ψ a p ≤ 2*A :=
    ((hseedB a ha p).2).trans (by linarith)
  have hregF := rebuilt_hot_continuous hq hb hL hT hR hloss F.measurable_value (hdata ell hell) hc₀m
    F.value_bounds (hupper ell hell) hc₀ (hdom ell hell) (F.all_mild hT)
  have hregG := rebuilt_hot_continuous hq hb hL hT hR hloss G.measurable_value (hdata μ hμ) hc₀m
    G.value_bounds (hupper μ hμ) hc₀ (hdom μ hμ) (G.all_mild hT)
  have hdiff : |hotPeak δ c₀ G-hotPeak δ c₀ F| ≤ C*e/δ :=
    Cap.peak_difference hT hδ (mul_nonneg hC.le he) hregG hregF
      (hst he G.measurable_value F.measurable_value hc₀m G.value_bounds F.value_bounds hc₀
        (hdom μ hμ) (hdom ell hell) hseed (G.all_mild hT) (F.all_mild hT))
  have hratio : C*e/δ < gap := (div_lt_iff₀ hδ).mpr (by nlinarith [hce])
  refine ⟨G,?_⟩
  have hh := (abs_sub_le_iff.mp hdiff).1
  dsimp [gap] at hratio
  linarith

end BoltzmannNonuniqueness.WeightedLocalControl.PeriodicMildState

end

end

section

/-! # Selecting a seed whose periodic solution attains the cap -/

noncomputable section

open MeasureTheory Filter Set
open scoped Topology

namespace BoltzmannNonuniqueness.WeightedLocalControl.PeriodicMildState

theorem select_seed_at_cap {I : Type*} [Countable I] {q b A B T δ M L₀ : ℝ}
    (hq : q < 2) (hb : 0 ≤ b) (hA : 0 < A) (hT : 0 ≤ T) (hδ : 0 < δ)
    (hM : 0 ≤ M) (hBA : B < A) (hL₀ : 0 < L₀)
    {f ψ : JetPrototype.Phase → ℝ} (hfm : Measurable f) (hψm : Measurable ψ)
    (hψ : ∀ p, |ψ p| ≤ M)
    {c₀ : I → JetPrototype.Phase → ℝ} (hc₀m : ∀ i, Measurable (c₀ i))
    (hc₀ : ∀ i p, 0 ≤ c₀ i p ∧ c₀ i p ≤ 2*A)
    (hseedB : ∀ ell ∈ Icc 0 L₀, ∀ p, 0 ≤ affineSeed f ψ ell p ∧ affineSeed f ψ ell p ≤ A)
    (hdom : ∀ ell ∈ Icc 0 L₀, ∀ s : Finset I, ∀ p, ∑ i ∈ s, c₀ i p ≤ affineSeed f ψ ell p)
    (hper : ∀ ell ∈ Icc 0 L₀, ∀ n p,
      affineSeed f ψ ell (WeightedTranslation.shift (JetCopyDatum.displacement n) p) = affineSeed f ψ ell p)
    (hzero : ∃ F : PeriodicMildState q b (damping q b A) T (2*A) (affineSeed f ψ 0),
      hotPeak δ c₀ F < 1)
    (hlarge : ∀ F : PeriodicMildState q b (damping q b A) T (2*A) (affineSeed f ψ L₀),
      1 < hotPeak δ c₀ F)
    (hbound : ∀ ell ∈ Icc 0 L₀,
      ∀ F : PeriodicMildState q b (damping q b A) T (2*A) (affineSeed f ψ ell),
      hotPeak δ c₀ F ≤ 1 →
      ∀ t ∈ Icc 0 T, ∀ᵐ p ∂FlightMeasure.phaseVolume, F.value (t,p) ≤ B) :
    ∃ ell ∈ Icc 0 L₀,
      ∃ F : PeriodicMildState q b (damping q b A) T (2*A) (affineSeed f ψ ell), hotPeak δ c₀ F = 1 := by
  classical
  let D : Set ℝ := {ell | ell ∈ Icc 0 L₀ ∧
    ∃ F : PeriodicMildState q b (damping q b A) T (2*A) (affineSeed f ψ ell), hotPeak δ c₀ F ≤ 1}
  have hR : 0 ≤ 2*A := by positivity
  have hL : 0 ≤ damping q b A := (bounds hb hA).1
  have hloss : (2*A)*CutoffLipschitz.frequencyConstant q b ≤ damping q b A := le_rfl
  have hupper (ell) (hell : ell ∈ Icc 0 L₀) (p) : affineSeed f ψ ell p ≤ 2*A :=
    ((hseedB ell hell p).2).trans (by linarith)
  have hclosed : IsClosed D := by
    apply isSeqClosed_iff_isClosed.mp
    intro u ell hu hulim
    have hell : ell ∈ Icc 0 L₀ := isClosed_Icc.mem_of_tendsto hulim
      (Eventually.of_forall (fun n => (hu n).1))
    choose F hFc using fun n => (hu n).2
    obtain ⟨G,hG⟩ := exists_cap_limit hq hb hL hT hR hδ hM hloss hfm hψm hψ hc₀m hc₀ hulim
      (hupper ell hell) (fun n => hupper (u n) (hu n).1)
      (hdom ell hell) (fun n => hdom (u n) (hu n).1) F hFc
    exact ⟨hell,G,hG⟩
  have hnonempty : D.Nonempty := by
    obtain ⟨F,hF⟩ := hzero
    exact ⟨0,⟨⟨le_rfl,hL₀.le⟩,F,hF.le⟩⟩
  have hbdd : BddAbove D := ⟨L₀,fun ell hell => hell.1.2⟩
  let x := sSup D
  have hx : x ∈ D := hclosed.csSup_mem hnonempty hbdd
  have hxL : x < L₀ := by
    apply lt_of_le_of_ne hx.1.2
    intro he
    have hex := hx.2
    rw [he] at hex
    obtain ⟨F,hF⟩ := hex
    exact (not_lt_of_ge hF) (hlarge F)
  obtain ⟨F,hF⟩ := hx.2
  refine ⟨x,hx.1,F,?_⟩
  by_contra hne
  have hstrict : hotPeak δ c₀ F < 1 := lt_of_le_of_ne hF hne
  obtain ⟨r,hr,hopen⟩ := strict_cap_open hq hb hA hT hδ hM hBA hx.1 hfm hψm hψ hc₀m hc₀
    hseedB hdom hper F (hbound x hx.1 F hF) hstrict
  let d := min (r/2) ((L₀-x)/2)
  have hd : 0 < d := lt_min (by linarith) (by linarith)
  have hdr : d < r := (min_le_left _ _).trans_lt (by linarith)
  have hdx : d ≤ (L₀-x)/2 := min_le_right _ _
  have hm : x+d ∈ Icc 0 L₀ := ⟨by linarith [hx.1.1],by linarith⟩
  have hdist : |x+d-x| < r := by rw [add_sub_cancel_left,abs_of_pos hd]; exact hdr
  obtain ⟨G,hG⟩ := hopen (x+d) hm hdist
  have hmD : x+d ∈ D := ⟨hm,G,hG.le⟩
  have hle : x+d ≤ x := le_csSup hbdd hmD
  linarith

end BoltzmannNonuniqueness.WeightedLocalControl.PeriodicMildState

end

end

end OAI
end

section
-- module Solutions.OAIQ080_BZ.Boltzmann_Approximation_CapMomentBound
attribute [-instance] _root_.OAI.BoltzmannNonuniqueness.ChartKernel.offAxis_sFinite _root_.OAI.BoltzmannNonuniqueness.EuclideanFlight.sourcePullback_finite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.characteristicGainKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.hotKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.mixedKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.retainedKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.coldCylinderVolume_finite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.copyColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.mainCoreKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.selectedColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCoreSheet.dilatedColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCoreSheet.kineticColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.PositiveIteration.awayOriginKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.PositiveIteration.nearOriginKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamNormalCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamNormalRetainedKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.dampedCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.densityScaledCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalBeamKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalCollision_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalPhysicalEvent_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalWindowEvent_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.physicalEventMeasure_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.scaledBeamNormalKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.WeakTime.phaseEndpointKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.WeakTime.phaseIncrement_finite _root_.OAI.BoltzmannNonuniqueness.WeakTime.phaseSeed_sFinite _root_.OAI.BoltzmannNonuniqueness.WeakTime.residenceKernel_sFinite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

/-! # Initial lower bounds and zero-seed strict upper bounds for the cap peak -/

noncomputable section

open MeasureTheory Set

namespace BoltzmannNonuniqueness.Cap

theorem peak_le_of_bound {T δ C : ℝ} {z : ℝ → ℝ} (hT : 0 ≤ T) (hδ : 0 < δ)
    (hz : ContinuousOn z (Icc 0 T)) (hbound : ∀ t ∈ Icc 0 T, z t ≤ C*(t+δ)) :
    peak T δ z ≤ C := by
  obtain ⟨t,ht,he,_⟩ := peak_attained hT hδ hz
  rw [he]
  exact (div_le_iff₀ (by linarith [ht.1] : 0 < t+δ)).mpr (hbound t ht)

theorem peak_le_of_square {T δ : ℝ} {z : ℝ → ℝ} (hT : 0 ≤ T) (hδ : 0 < δ)
    (hz : ContinuousOn z (Icc 0 T)) (hbound : ∀ t ∈ Icc 0 T, z t ≤ t^2) :
    peak T δ z ≤ T := by
  apply peak_le_of_bound hT hδ hz
  intro t ht
  have hp : t^2 ≤ T*(t+δ) := by
    nlinarith [mul_nonneg hT hδ.le,mul_nonneg ht.1 (sub_nonneg.mpr ht.2)]
  exact (hbound t ht).trans hp

end BoltzmannNonuniqueness.Cap

namespace BoltzmannNonuniqueness.WeightedLocalControl.PeriodicMildState

open WeightedLocal

theorem hotPeak_ge_initial {I : Type*} [Countable I] {q b L T R δ : ℝ}
    (hq : q < 2) (hb : 0 ≤ b) (hL : 0 ≤ L) (hT : 0 ≤ T) (hR : 0 ≤ R) (hδ : 0 < δ)
    (hloss : R*CutoffLipschitz.frequencyConstant q b ≤ L)
    {F₀ : JetPrototype.Phase → ℝ} (hF₀m : Measurable F₀) (hF₀ : ∀ p, F₀ p ≤ R)
    {c₀ : I → JetPrototype.Phase → ℝ} (hc₀m : ∀ i, Measurable (c₀ i))
    (hc₀ : ∀ i p, 0 ≤ c₀ i p ∧ c₀ i p ≤ R)
    (hdom : ∀ s : Finset I, ∀ p, ∑ i ∈ s, c₀ i p ≤ F₀ p)
    (F : PeriodicMildState q b L T R F₀) :
    PhaseEssSup.size (fun p => F₀ p-∑' i, c₀ i p)/δ ≤ hotPeak δ c₀ F := by
  have hi := rebuilt_hot_initial_ae hq hb hL hT hR hloss F.measurable_value hc₀m F.value_bounds hc₀ hdom
    (F.all_mild hT)
  have he := PhaseEssSup.size_congr_ae hi
  have hreg := rebuilt_hot_continuous hq hb hL hT hR hloss F.measurable_value hF₀m hc₀m
    F.value_bounds hF₀ hc₀ hdom (F.all_mild hT)
  obtain ⟨_,_,_,hpeak⟩ := Cap.peak_attained hT hδ hreg
  have h := hpeak 0 ⟨le_rfl,hT⟩
  simpa only [zero_add,he,hotPeak] using h

end BoltzmannNonuniqueness.WeightedLocalControl.PeriodicMildState

end

end

end OAI
end

section
-- module Solutions.OAIQ080_BZ.Boltzmann_Jets_JetFiniteCap
attribute [-instance] _root_.OAI.BoltzmannNonuniqueness.ChartKernel.offAxis_sFinite _root_.OAI.BoltzmannNonuniqueness.EuclideanFlight.sourcePullback_finite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.characteristicGainKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.hotKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.mixedKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.retainedKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.coldCylinderVolume_finite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.copyColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.mainCoreKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.selectedColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCoreSheet.dilatedColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCoreSheet.kineticColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.PositiveIteration.awayOriginKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.PositiveIteration.nearOriginKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamNormalCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamNormalRetainedKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.dampedCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.densityScaledCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalBeamKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalCollision_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalPhysicalEvent_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalWindowEvent_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.physicalEventMeasure_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.scaledBeamNormalKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.WeakTime.phaseEndpointKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.WeakTime.phaseIncrement_finite _root_.OAI.BoltzmannNonuniqueness.WeakTime.phaseSeed_sFinite _root_.OAI.BoltzmannNonuniqueness.WeakTime.residenceKernel_sFinite
attribute [-simp] _root_.OAI.BoltzmannNonuniqueness.timeTranslation_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

/-! # Actual finite periodic approximations attaining the hot cap -/

noncomputable section

open MeasureTheory Set
open BoltzmannNonuniqueness.WeightedLocal BoltzmannNonuniqueness.WeightedLocalControl
open BoltzmannNonuniqueness.WeightedLocalControl.PeriodicMildState
open BoltzmannNonuniqueness.WeightedTranslation

namespace BoltzmannNonuniqueness.JetCopyDatum

theorem exists_uniform_cap_solution_q80_oai (hcarleman : Published.GPV2009CarlemanInput)
    {s₀ η K α γ d₀ q : ℝ}
    (hs₀ : 0 < s₀) (hsmax : s₀ ≤ 1/8) (hη : 0 < η) (hηmax : η ≤ Real.log 2)
    (hK : 0 ≤ K) (hα : 0 < α) (hαmax : α ≤ 1/4) (hγ : 0 < γ)
    (hd₀ : 0 < d₀) (hd₀max : d₀ ≤ 1) (hwidth : d₀*(1/8:ℝ)^10 ≤ 1/64)
    (hsmall : JetComparisonCoefficient.coefficient K*d₀*s₀^9 ≤ 1)
    (hq₁ : 1 < q) (hq₂ : q < 2) :
    ∃ τ : ℝ, 0 < τ ∧ τ ≤ 1/32 ∧ ∀ (N : ℕ) (b T : ℝ), 0 ≤ b → 0 ≤ T → T ≤ τ →
      ∃ (A ell : ℝ), 0 < A ∧ ell ∈ Icc 0 2 ∧
        (∀ p, initial s₀ η K α γ d₀ q N
          (fun p => ell*HotSeedProfile.normalized q (DatumBounds.scale s₀ η (N+1)) p) p ≤ 2*A) ∧
        ∃ F : PeriodicMildState q b (damping q b A) T (2*A)
          (initial s₀ η K α γ d₀ q N
            (fun p => ell*HotSeedProfile.normalized q (DatumBounds.scale s₀ η (N+1)) p)),
          F.hotPeak (DatumBounds.scale s₀ η (N+1)) (color s₀ η K α γ d₀ q N) = 1 := by
  obtain ⟨τ,hτ,hτmax,hzero⟩ := exists_uniform_zero_solution_large_q80 hcarleman hs₀ hsmax hη hηmax
    hK hα hαmax hγ hd₀ hd₀max hwidth hsmall hq₁ hq₂
  refine ⟨τ,hτ,hτmax,?_⟩
  intro N b T hb hT hTτ
  let δ := DatumBounds.scale s₀ η (N+1)
  have hδ : 0 < δ := DatumBounds.scale_pos hs₀ (N+1)
  have hδone : δ ≤ 1 := by
    have he : Real.exp (-((N+1:ℕ):ℝ)*η) ≤ 1 := Real.exp_le_one_iff.mpr (mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr (by positivity)) hη.le)
    have hs := mul_le_mul_of_nonneg_left he hs₀.le
    dsimp [δ,DatumBounds.scale]
    nlinarith
  let ψ := HotSeedProfile.normalized q δ
  obtain ⟨M,hM,hψb⟩ := HotSeedProfile.normalized_bounds hδ hδone q
  have hψm : Measurable ψ := HotSeedProfile.normalized_measurable q δ
  have hψnorm : PhaseEssSup.size ψ = δ := HotSeedProfile.normalized_norm hδ hδone q
  let f := seed s₀ η K α γ d₀ q N
  let c₀ := color s₀ η K α γ d₀ q N
  let B := WeightedFiniteSeed.amplitude s₀ η K d₀ N+coldNormBound s₀ η K α d₀ N+T+δ
  let A := B+2*M+1
  have hamp : 0 < WeightedFiniteSeed.amplitude s₀ η K d₀ N :=
    WeightedFiniteSeed.amplitude_pos hs₀ hK hd₀.le η N
  have hcold : 0 ≤ coldNormBound s₀ η K α d₀ N := coldNormBound_nonneg hs₀ hK hd₀ η α N
  have hB : 0 < B := by dsimp [B] <;> positivity
  have hA : 0 < A := by dsimp [A] <;> positivity
  have hBA : B < A := by dsimp [A] <;> linarith
  have hA0 : continuationAmplitude s₀ η K α d₀ N ≤ A := by
    dsimp [continuationAmplitude,A,B]
    linarith [hM.le,hδ.le]
  have hR : 0 ≤ 2*A := by positivity
  have hL : 0 ≤ damping q b A := (bounds hb hA).1
  have hloss : (2*A)*CutoffLipschitz.frequencyConstant q b ≤ damping q b A := le_rfl
  have hseedB (ell) (hell : ell ∈ Icc (0:ℝ) 2) (p) :
      0 ≤ affineSeed f ψ ell p ∧ affineSeed f ψ ell p ≤ A := by
    have hf := seed_bounds hs₀ hsmax hη hηmax hK hd₀ hwidth hα.le hαmax γ q N p
    have hm := mul_le_mul hell.2 (hψb p).2 (hψb p).1 (by norm_num : (0:ℝ) ≤ 2)
    change 0 ≤ f p+ell*ψ p ∧ f p+ell*ψ p ≤ A
    exact ⟨add_nonneg hf.1 (mul_nonneg hell.1 (hψb p).1),by dsimp [A,B,f] <;> nlinarith [hf.2]⟩
  have hseedR (ell) (hell : ell ∈ Icc (0:ℝ) 2) (p) : affineSeed f ψ ell p ≤ 2*A :=
    (hseedB ell hell p).2.trans (by linarith)
  have hdom (ell) (hell : ell ∈ Icc (0:ℝ) 2) (s : Finset JetLattice.Label) (p) :
      ∑ i ∈ s, c₀ i p ≤ affineSeed f ψ ell p :=
    (initial_color_bounds hs₀ hsmax hη hηmax hK hd₀.le α γ q N
      (fun p => mul_nonneg hell.1 (hψb p).1)).2 s p
  have hc₀ (i) (p) : 0 ≤ c₀ i p ∧ c₀ i p ≤ 2*A := by
    refine ⟨color_nonneg hs₀ hK hd₀.le η α γ q N i p,?_⟩
    simpa only [Finset.sum_singleton] using (hdom 0 ⟨le_rfl,by norm_num⟩ {i} p).trans
      (hseedR 0 ⟨le_rfl,by norm_num⟩ p)
  have hper (ell) (_hell : ell ∈ Icc (0:ℝ) 2) (n) (p) :
      affineSeed f ψ ell (shift (displacement n) p) = affineSeed f ψ ell p := by
    simp only [affineSeed,f,seed_periodic,ψ,HotSeedProfile.normalized_periodic]
  have hzeroCap : ∃ F : PeriodicMildState q b (damping q b A) T (2*A) (affineSeed f ψ 0),
      hotPeak δ c₀ F < 1 := by
    have hz := hzero N b A T hb hA0 hT hTτ
    have he : (fun _ : JetPrototype.Phase => (0:ℝ)) = (fun p => (0:ℝ)*ψ p) := by funext p; simp
    rw [he] at hz
    obtain ⟨F,hF⟩ := hz
    have hreg := rebuilt_hot_continuous hq₂ hb hL hT hR hloss F.measurable_value
      ((measurable_seed s₀ η K α γ d₀ q N).add (hψm.const_mul 0))
      (measurable_color s₀ η K α γ d₀ q N) F.value_bounds
      (hseedR 0 ⟨le_rfl,by norm_num⟩) hc₀ (hdom 0 ⟨le_rfl,by norm_num⟩) (F.all_mild hT)
    have hp := Cap.peak_le_of_square hT hδ hreg hF
    refine ⟨F,hp.trans_lt ?_⟩
    exact (hTτ.trans hτmax).trans_lt (by norm_num)
  have hlarge (F : PeriodicMildState q b (damping q b A) T (2*A) (affineSeed f ψ 2)) :
      1 < hotPeak δ c₀ F := by
    have hi := hotPeak_ge_initial hq₂ hb hL hT hR hδ hloss
      ((measurable_seed s₀ η K α γ d₀ q N).add (hψm.const_mul 2))
      (hseedR 2 ⟨by norm_num,le_rfl⟩) (measurable_color s₀ η K α γ d₀ q N)
      hc₀ (hdom 2 ⟨by norm_num,le_rfl⟩) F
    have he : (fun p => affineSeed f ψ 2 p-∑' i, c₀ i p) = (fun p => 2*ψ p) := by
      funext p
      change (∑' i, c₀ i p)+2*ψ p-(∑' i, c₀ i p) = _
      ring
    change PhaseEssSup.size (fun p => affineSeed f ψ 2 p-∑' i, c₀ i p)/δ ≤ hotPeak δ c₀ F at hi
    rw [he,PhaseEssSup.size_const_mul,hψnorm,abs_of_pos (by norm_num : (0:ℝ) < 2)] at hi
    have htwo : (2*δ)/δ = 2 := mul_div_cancel_right₀ _ hδ.ne'
    rw [htwo] at hi
    linarith
  have hbound (ell) (hell : ell ∈ Icc (0:ℝ) 2)
      (F : PeriodicMildState q b (damping q b A) T (2*A) (affineSeed f ψ ell))
      (hcap : hotPeak δ c₀ F ≤ 1) :
      ∀ t ∈ Icc 0 T, ∀ᵐ p ∂FlightMeasure.phaseVolume, F.value (t,p) ≤ B :=
    capped_total_bound_q80 hs₀ hsmax hη hηmax hK hα.le hαmax hγ.le hd₀ hd₀max hwidth hsmall
      hq₂ hb hL hT hR (hTτ.trans hτmax) hδ hloss N (hψm.const_mul ell)
      (fun p => mul_nonneg hell.1 (hψb p).1) (hseedR ell hell) F hcap
  obtain ⟨ell,hell,F,hF⟩ := select_seed_at_cap hq₂ hb hA hT hδ hM.le hBA (by norm_num : (0:ℝ) < 2)
    (measurable_seed s₀ η K α γ d₀ q N) hψm (fun p => by rw [abs_of_nonneg (hψb p).1]; exact (hψb p).2)
    (measurable_color s₀ η K α γ d₀ q N) hc₀ hseedB hdom hper hzeroCap hlarge hbound
  exact ⟨A,ell,hA,hell,hseedR ell hell,F,hF⟩

end BoltzmannNonuniqueness.JetCopyDatum

end

end

end OAI
end

theorem solution : type_of% @OAI.BoltzmannNonuniqueness.JetCopyDatum.exists_uniform_cap_solution_q80_oai := @OAI.BoltzmannNonuniqueness.JetCopyDatum.exists_uniform_cap_solution_q80_oai
