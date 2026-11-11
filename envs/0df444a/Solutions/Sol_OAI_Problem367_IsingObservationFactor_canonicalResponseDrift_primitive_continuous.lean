-- Prove2me | solution 1 for OAI.Problem367.IsingObservationFactor.canonicalResponseDrift_primitive_continuous
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-11T01:46:17.146682+00:00
-- url     : https://prove2.me/submissions/7f7adfdf-c8e2-4d8e-a542-ce196c6367b2

import Mathlib
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.MeasureTheory.Integral.Marginal
import Mathlib.Probability.Martingale.Basic
import Mathlib.Probability.Process.Stopping
import Definitions.Def_FreeIsing
import Definitions.Def_Q243FI005

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Gibbs_Weights
attribute [-instance] _root_.OAI.Problem367.IsingConditionalCopyBounds.graphLaw_isProbabilityMeasure _root_.OAI.Problem367.IsingObservationFactor.copies_probability _root_.OAI.Problem367.IsingObservationFactor.kernel_markov _root_.OAI.Problem367.IsingObservationInnovation.innovationMap_observationLaw_probability _root_.OAI.Problem367.IsingObservationInnovation.observationLaw_probability _root_.OAI.Problem367.TreeKoopman.labelProbability _root_.OAI.Problem367.freeIsingMeasure_probability _root_.OAI.Problem367.reducedTailFintype _root_.OAI.Problem367.treeBallFintype _root_.OAI.Problem367.treeShellFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace Problem367

theorem finiteIsing_partitionFunction
    {d : ℕ} (beta : ℝ) (D : Finset (TreeVertex d)) (hD : ConnectedFinset D) :
    (∑ eta : D → IsingSpin, Real.exp (beta * ∑ e ∈ inducedEdges D,
      spinSign (extendFiniteSpin D eta e.1) * spinSign (extendFiniteSpin D eta e.2))) =
      2 * (2 * Real.cosh beta) ^ (inducedEdges D).card := by
  classical
  have hden : 0 < 2 * (2 * Real.cosh beta) ^ (inducedEdges D).card := by
    positivity
  have hn := sum_freeCylinderWeight_eq_one (Real.neg_one_lt_tanh beta).le
    (Real.tanh_lt_one beta).le D hD
  simp_rw [freeCylinderWeight_tanh_eq_exp] at hn
  rw [← ENNReal.ofReal_sum_of_nonneg (fun eta _ =>
    div_nonneg (Real.exp_pos _).le hden.le)] at hn
  have hreal := ENNReal.ofReal_eq_one.mp hn
  rw [← Finset.sum_div] at hreal
  exact (div_eq_one_iff_eq (ne_of_gt hden)).mp hreal

end Problem367

end

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Posterior_FinitePosterior
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open scoped BigOperators

namespace Problem367.FinitePosterior

variable {ι : Type*} [Fintype ι]

lemma partition_ne_zero [Nonempty ι] (energy signal : ι → ℝ) (t : ℝ) :
    partition energy signal t ≠ 0 := ne_of_gt (partition_pos energy signal t)

lemma mass_pos [Nonempty ι] (energy signal : ι → ℝ) (t : ℝ) (s : ι) :
    0 < mass energy signal t s :=
  div_pos (weight_pos energy signal t s) (partition_pos energy signal t)

lemma sum_mass [Nonempty ι] (energy signal : ι → ℝ) (t : ℝ) :
    ∑ s, mass energy signal t s = 1 := by
  simp only [mass, ← Finset.sum_div]
  change partition energy signal t / partition energy signal t = 1
  exact div_self (partition_ne_zero energy signal t)

lemma mean_eq_sum_mass (energy signal observable : ι → ℝ) (t : ℝ) :
    mean energy signal observable t = ∑ s, observable s * mass energy signal t s := by
  simp only [mean, mass, ← mul_div_assoc, ← Finset.sum_div]

lemma mean_const [Nonempty ι] (energy signal : ι → ℝ) (t c : ℝ) :
    mean energy signal (fun _ => c) t = c := by
  rw [mean_eq_sum_mass, ← Finset.mul_sum, sum_mass, mul_one]

omit [Fintype ι] in
lemma hasDerivAt_weight (energy signal : ι → ℝ) (t : ℝ) (s : ι) :
    HasDerivAt (fun x => weight energy signal x s)
      (signal s * weight energy signal t s) t := by
  simpa [weight, mul_comm] using
    (((hasDerivAt_id t).mul_const (signal s)).const_add (energy s)).exp

lemma hasDerivAt_partition (energy signal : ι → ℝ) (t : ℝ) :
    HasDerivAt (partition energy signal)
      (∑ s, signal s * weight energy signal t s) t := by
  exact HasDerivAt.fun_sum (fun s _ => hasDerivAt_weight energy signal t s)

theorem hasDerivAt_mean [Nonempty ι] (energy signal observable : ι → ℝ) (t : ℝ) :
    HasDerivAt (mean energy signal observable)
      (mean energy signal (fun s => observable s * signal s) t -
        mean energy signal observable t * mean energy signal signal t) t := by
  have hn : HasDerivAt (fun x => ∑ s, observable s * weight energy signal x s)
      (∑ s, (observable s * signal s) * weight energy signal t s) t := by
    simpa only [mul_assoc] using HasDerivAt.fun_sum
      (fun s (_ : s ∈ Finset.univ) =>
        (hasDerivAt_weight energy signal t s).const_mul (observable s))
  convert! hn.div (hasDerivAt_partition energy signal t)
    (partition_ne_zero energy signal t) using 1
  all_goals try with_reducible_and_instances rfl
  dsimp [mean]
  field_simp

theorem hasDerivAt_spin_mean [Nonempty ι] (energy spin : ι → ℝ) (t : ℝ)
    (hspin : ∀ s, spin s = -1 ∨ spin s = 1) :
    HasDerivAt (mean energy spin spin)
      (1 - (mean energy spin spin t) ^ 2) t := by
  have heq : (fun s => spin s * spin s) = (fun _ : ι => (1 : ℝ)) := by
    funext s
    rcases hspin s with hs | hs <;> simp [hs]
  have hd := hasDerivAt_mean energy spin spin t
  rw [heq, mean_const] at hd
  simpa only [← sq] using hd

end Problem367.FinitePosterior

end

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Posterior_Fields
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open scoped BigOperators

namespace Problem367.FinitePosterior

variable {S V : Type*} [Fintype S] [Fintype V]

lemma fieldMean_along_line (energy : S → ℝ) (spin : S → V → ℝ)
    (observable : S → ℝ) (x direction : V → ℝ) (t : ℝ) :
    fieldMean energy spin observable (fun v => x v + t * direction v) =
      mean (fieldEnergy energy spin x) (fun s => ∑ v, direction v * spin s v)
        observable t := by
  have heq (s : S) :
      fieldEnergy energy spin (fun v => x v + t * direction v) s =
        fieldEnergy energy spin x s + t * ∑ v, direction v * spin s v := by
    simp only [fieldEnergy, add_mul, Finset.sum_add_distrib,
      Finset.mul_sum, mul_assoc]
    ring
  simp only [fieldMean, heq, mean, partition, weight]

theorem hasDerivAt_fieldMean [Nonempty S] (energy : S → ℝ) (spin : S → V → ℝ)
    (observable : S → ℝ) (x direction : V → ℝ) :
    HasDerivAt (fun t => fieldMean energy spin observable (fun v => x v + t * direction v))
      (fieldMean energy spin (fun s => observable s * ∑ v, direction v * spin s v) x -
        fieldMean energy spin observable x *
          fieldMean energy spin (fun s => ∑ v, direction v * spin s v) x) 0 := by
  simp_rw [fieldMean_along_line]
  simpa only [mean_fieldEnergy_zero] using
    hasDerivAt_mean (fieldEnergy energy spin x)
      (fun s => ∑ v, direction v * spin s v) observable 0

end Problem367.FinitePosterior

end

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Posterior_Smooth
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open scoped BigOperators ContDiff

namespace Problem367.FinitePosterior

variable {S V : Type*} [Fintype S] [Fintype V]

omit [Fintype S] in

theorem contDiff_fieldEnergy (energy : S → ℝ) (spin : S → V → ℝ)
    (s : S) (n : ℕ∞ω) : ContDiff ℝ n (fun x => fieldEnergy energy spin x s) := by
  unfold fieldEnergy
  fun_prop

theorem contDiff_fieldPartition (energy : S → ℝ) (spin : S → V → ℝ)
    (n : ℕ∞ω) : ContDiff ℝ n (fun x => ∑ s, Real.exp (fieldEnergy energy spin x s)) := by
  apply ContDiff.sum
  intro s _
  exact (contDiff_fieldEnergy energy spin s n).exp

theorem contDiff_fieldMean_all [Nonempty S] (energy : S → ℝ) (spin : S → V → ℝ)
    (observable : S → ℝ) (n : ℕ∞ω) : ContDiff ℝ n (fieldMean energy spin observable) := by
  unfold fieldMean
  apply ContDiff.div
  · apply ContDiff.sum
    intro s _
    exact contDiff_const.mul (contDiff_fieldEnergy energy spin s n).exp
  · exact contDiff_fieldPartition energy spin n
  · intro x
    exact ne_of_gt (fieldPartition_pos energy spin x)

theorem fderiv_fieldMean_apply [Nonempty S] (energy : S → ℝ) (spin : S → V → ℝ)
    (observable : S → ℝ) (x direction : V → ℝ) :
    fderiv ℝ (fieldMean energy spin observable) x direction =
      fieldMean energy spin (fun s => observable s * ∑ v, direction v * spin s v) x -
        fieldMean energy spin observable x *
          fieldMean energy spin (fun s => ∑ v, direction v * spin s v) x := by
  have hd := ((contDiff_fieldMean_all energy spin observable 1).differentiable (by norm_num) x).hasFDerivAt
  have hl : HasDerivAt (fun t : ℝ => x + t • direction) direction 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).smul_const direction).const_add x
  have hc := hd.comp_hasDerivAt_of_eq 0 hl (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)
  have he := hasDerivAt_fieldMean energy spin observable x direction
  exact (show HasDerivAt
    (fun t => fieldMean energy spin observable (fun v => x v + t * direction v))
      (fderiv ℝ (fieldMean energy spin observable) x direction) 0 from hc).unique he

end Problem367.FinitePosterior

end

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Estimates_FiniteIsingZeroField
attribute [-instance] _root_.OAI.Problem367.IsingConditionalCopyBounds.graphLaw_isProbabilityMeasure _root_.OAI.Problem367.IsingObservationFactor.copies_probability _root_.OAI.Problem367.IsingObservationFactor.kernel_markov _root_.OAI.Problem367.IsingObservationInnovation.innovationMap_observationLaw_probability _root_.OAI.Problem367.IsingObservationInnovation.observationLaw_probability _root_.OAI.Problem367.TreeKoopman.labelProbability _root_.OAI.Problem367.WienerSampler.pathMeasurableSpace _root_.OAI.Problem367.freeIsingMeasure_probability _root_.OAI.Problem367.reducedTailFintype _root_.OAI.Problem367.treeBallFintype _root_.OAI.Problem367.treeShellFintype
attribute [-simp] _root_.OAI.Problem367.ConnectedHull.pathAssignment_path _root_.OAI.Problem367.CutContinuationChannels.averageChannel_globalCone _root_.OAI.Problem367.CutContinuationChannels.continuationChannel_globalCone _root_.OAI.Problem367.FactorObservable.centeredSpinLp_coe _root_.OAI.Problem367.FiniteIsingSplit.splitEquiv_fst _root_.OAI.Problem367.FiniteIsingSplit.splitEquiv_snd _root_.OAI.Problem367.FinitePathGibbs.tailPartition_zero _root_.OAI.Problem367.IsingObservationInnovation.uniformObservation_relabel _root_.OAI.Problem367.PathSideBranches.restrictNoisyRegion_array _root_.OAI.Problem367.PosteriorChain.transition_spinMean _root_.OAI.Problem367.PosteriorChain.transition_sum _root_.OAI.Problem367.RootedBroadcast.pos_spinMul _root_.OAI.Problem367.RootedBroadcast.spinMul_pos _root_.OAI.Problem367.RootedBroadcast.spinMul_self _root_.OAI.Problem367.TreeGibbsAut.spinEquiv_apply_image _root_.OAI.Problem367.connectedSpinEncode_apply_root _root_.OAI.Problem367.connectedSpinEquiv_apply _root_.OAI.Problem367.spinAgreementCode_eq_neg_iff _root_.OAI.Problem367.spinAgreementCode_eq_pos_iff _root_.OAI.Problem367.spinSign_flip
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace Problem367

private lemma spinSign_global_flip (s : IsingSpin) :
    spinSign s.flip = -spinSign s := by
  cases s <;> norm_num [IsingSpin.flip, spinSign]

theorem finiteIsingEnergy_flipConfig {d : ℕ} (beta : ℝ)
    (D : Finset (TreeVertex d)) (eta : D → IsingSpin) :
    finiteIsingEnergy beta D (flipConfig eta) = finiteIsingEnergy beta D eta := by
  classical
  unfold finiteIsingEnergy
  congr 1
  apply Finset.sum_congr rfl
  intro e he
  have hm := Finset.mem_product.mp (Finset.mem_filter.mp he).1
  have hsign (v : TreeVertex d) (hv : v ∈ D) :
      spinSign (extendFiniteSpin D (flipConfig eta) v) =
        -spinSign (extendFiniteSpin D eta v) := by
    simp only [extendFiniteSpin, dite_eq_left hv, flipConfig_apply, spinSign_global_flip]
  rw [hsign e.1 hm.1, hsign e.2 hm.2, neg_mul_neg]

theorem finiteIsingPosterior_zero_of_odd {d : ℕ} (beta : ℝ)
    (D : Finset (TreeVertex d)) (q : (D → IsingSpin) → ℝ)
    (hq : ∀ eta, q (flipConfig eta) = -q eta) :
    FinitePosterior.fieldMean (finiteIsingEnergy beta D)
      (fun (eta : D → IsingSpin) v => spinSign (eta v)) q (fun _ => 0) = 0 := by
  classical
  have hsum := (flipConfigMeasurableEquiv D).toEquiv.sum_comp
    (fun eta : D → IsingSpin => q eta * Real.exp (finiteIsingEnergy beta D eta))
  change (∑ eta : D → IsingSpin, q (flipConfig eta) *
    Real.exp (finiteIsingEnergy beta D (flipConfig eta))) =
      ∑ eta : D → IsingSpin, q eta * Real.exp (finiteIsingEnergy beta D eta) at hsum
  simp only [hq, finiteIsingEnergy_flipConfig, neg_mul, Finset.sum_neg_distrib] at hsum
  have hzero : (∑ eta : D → IsingSpin,
      q eta * Real.exp (finiteIsingEnergy beta D eta)) = 0 := by linarith
  simp only [FinitePosterior.fieldMean, FinitePosterior.fieldEnergy,
    zero_mul, Finset.sum_const_zero, add_zero, hzero, zero_div]

theorem finiteIsingPosterior_spin_zero {d : ℕ} (beta : ℝ)
    (D : Finset (TreeVertex d)) (v : D) :
    FinitePosterior.fieldMean (finiteIsingEnergy beta D)
      (fun (eta : D → IsingSpin) w => spinSign (eta w))
      (fun eta => spinSign (eta v)) (fun _ => 0) = 0 := by
  apply finiteIsingPosterior_zero_of_odd
  intro eta
  exact spinSign_global_flip (eta v)

end Problem367

end

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Posterior_GaussianTesting
attribute [-instance] _root_.OAI.Problem367.WienerSampler.pathMeasurableSpace _root_.OAI.Problem367.reducedTailFinite _root_.OAI.Problem367.treeBallFinite _root_.OAI.Problem367.treeShellFinite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal ProbabilityTheory

namespace Problem367

theorem gaussianPi_map_sqrt {I : Type*} [Fintype I]
    (t : ℝ) (ht : 0 ≤ t) :
    (Measure.pi (fun _ : I => gaussianReal 0 1)).map
      (fun x i => Real.sqrt t * x i) =
        Measure.pi (fun _ : I => gaussianReal 0 ⟨t, ht⟩) := by
  rw [Measure.pi_map_pi (μ := fun _ : I => gaussianReal 0 1)
    (f := fun _ (x : ℝ) => Real.sqrt t * x) (fun _ => by fun_prop)]
  congr 1
  funext i
  rw [gaussianReal_map_const_mul]
  congr 1
  · simp
  · apply NNReal.coe_injective
    change (Real.sqrt t) ^ 2 * 1 = t
    rw [mul_one, Real.sq_sqrt ht]

theorem finiteStandardGaussianPlanted_joint_law
    {S I : Type*} [Fintype S] [MeasurableSpace S] [MeasurableSingletonClass S]
    [Fintype I] (μ : Measure S) [IsProbabilityMeasure μ]
    (t : ℝ) (ht : 0 ≤ t) (spin : S → I → ℝ) :
    (μ.prod (Measure.pi (fun _ : I => gaussianReal 0 1))).map
      (fun z : S × (I → ℝ) =>
        (z.1, fun i => t * spin z.1 i + Real.sqrt t * z.2 i)) =
      μ ⊗ₘ finiteGaussianObservationKernel ⟨t, ht⟩ spin := by
  have : IsMarkovKernel (finiteGaussianObservationKernel ⟨t, ht⟩ spin) :=
    finiteGaussianObservationKernel_isMarkov ⟨t, ht⟩ spin
  apply map_planted_eq_compProd μ (Measure.pi (fun _ : I => gaussianReal 0 1))
    (finiteGaussianObservationKernel ⟨t, ht⟩ spin)
    (fun s x i => t * spin s i + Real.sqrt t * x i)
  · exact Measurable.of_eval (fun index =>
      (measurable_const.mul ((measurable_of_finite (fun state => spin state index)).comp
        measurable_fst)).add (measurable_const.mul
          ((measurable_pi_apply index).comp measurable_snd)))
  · intro s
    have hscale : Measurable (fun x : I → ℝ => fun i => Real.sqrt t * x i) := by
      fun_prop
    have hshift : Measurable (fun x : I → ℝ => fun i => t * spin s i + x i) := by
      fun_prop
    rw [show (fun x : I → ℝ => fun i => t * spin s i + Real.sqrt t * x i) =
      (fun x : I → ℝ => fun i => t * spin s i + x i) ∘
        (fun x : I → ℝ => fun i => Real.sqrt t * x i) from rfl,
      ← Measure.map_map hshift hscale, gaussianPi_map_sqrt t ht]
    exact gaussianPi_map_signal ⟨t, ht⟩ (spin s)

namespace FinitePosterior

theorem exponential_posterior_eq_fieldMean
    {S I : Type*} [Fintype S] [Nonempty S] [Fintype I]
    [MeasurableSpace S] (μ : Measure S) (energy : S → ℝ)
    (hprior : ∀ s, μ.real {s} = Real.exp (energy s) / ∑ a, Real.exp (energy a))
    (spin : S → I → ℝ) (q : S → ℝ) (x : I → ℝ) :
    (∑ s, μ.real {s} * Real.exp (∑ i, spin s i * x i) * q s) /
      (∑ s, μ.real {s} * Real.exp (∑ i, spin s i * x i)) =
      fieldMean energy spin q x := by
  let Z := ∑ s, Real.exp (energy s)
  have hZ : Z ≠ 0 := ne_of_gt (Finset.sum_pos
    (fun s _ => Real.exp_pos (energy s)) Finset.univ_nonempty)
  have hw (s : S) :
      μ.real {s} * Real.exp (∑ i, spin s i * x i) =
        Real.exp (fieldEnergy energy spin x s) / Z := by
    rw [hprior s]
    have hsum : (∑ i, spin s i * x i) = ∑ i, x i * spin s i := by
      apply Finset.sum_congr rfl
      intro i _
      ring
    rw [hsum]
    simp only [fieldEnergy, Real.exp_add, Z]
    ring
  simp_rw [hw, div_mul_eq_mul_div, ← Finset.sum_div]
  rw [div_div_div_cancel_right₀ hZ]
  unfold fieldMean
  congr 1
  apply Finset.sum_congr rfl
  intro s _
  ring

end FinitePosterior

theorem finiteStandardGaussianPlanted_condExp_fieldMean
    {S I : Type*} [Fintype S] [MeasurableSpace S] [MeasurableSingletonClass S]
    [StandardBorelSpace S] [Nonempty S] [Fintype I]
    (μ : Measure S) [IsProbabilityMeasure μ] (energy : S → ℝ)
    (hprior : ∀ s, μ.real {s} = Real.exp (energy s) / ∑ a, Real.exp (energy a))
    (t : ℝ) (ht : 0 ≤ t) (spin : S → I → ℝ)
    (hspin : ∀ s i, spin s i ^ 2 = 1) (q : S → ℝ) :
    let ρ := μ.prod (Measure.pi (fun _ : I => gaussianReal 0 1))
    let Y : S × (I → ℝ) → I → ℝ :=
      fun z i => t * spin z.1 i + Real.sqrt t * z.2 i
    ρ[fun z => q z.1 | (inferInstance : MeasurableSpace (I → ℝ)).comap Y] =ᵐ[ρ]
      fun z => FinitePosterior.fieldMean energy spin q (Y z) := by
  dsimp only
  have : IsMarkovKernel (finiteGaussianObservationKernel ⟨t, ht⟩ spin) :=
    finiteGaussianObservationKernel_isMarkov ⟨t, ht⟩ spin
  apply FiniteBayes.condExp_state_eq_of_posterior_integral
    (μ.prod (Measure.pi (fun _ : I => gaussianReal 0 1))) μ
    (finiteGaussianObservationKernel ⟨t, ht⟩ spin) Prod.fst
    (fun z i => t * spin z.1 i + Real.sqrt t * z.2 i) measurable_fst
    (by exact Measurable.of_eval (fun index =>
      (measurable_const.mul ((measurable_of_finite (fun state => spin state index)).comp
        measurable_fst)).add (measurable_const.mul
          ((measurable_pi_apply index).comp measurable_snd))))
    (finiteStandardGaussianPlanted_joint_law μ t ht spin) q
  filter_upwards [finiteGaussianObservation_posterior_mean μ ⟨t, ht⟩ spin hspin q]
    with x hx
  exact hx.trans (FinitePosterior.exponential_posterior_eq_fieldMean
    μ energy hprior spin q x)

theorem finiteStandardGaussianPlanted_integral_test_fieldMean
    {S I : Type*} [Fintype S] [MeasurableSpace S] [MeasurableSingletonClass S]
    [StandardBorelSpace S] [Nonempty S] [Fintype I]
    (μ : Measure S) [IsProbabilityMeasure μ] (energy : S → ℝ)
    (hprior : ∀ s, μ.real {s} = Real.exp (energy s) / ∑ a, Real.exp (energy a))
    (t : ℝ) (ht : 0 ≤ t) (spin : S → I → ℝ)
    (hspin : ∀ s i, spin s i ^ 2 = 1) (q : S → ℝ)
    (h : (I → ℝ) → ℝ) (hh : Measurable h) (C : ℝ)
    (hbound : ∀ x, ‖h x‖ ≤ C) :
    let ρ := μ.prod (Measure.pi (fun _ : I => gaussianReal 0 1))
    let Y : S × (I → ℝ) → I → ℝ :=
      fun z i => t * spin z.1 i + Real.sqrt t * z.2 i
    (∫ z, h (Y z) * q z.1 ∂ρ) =
      ∫ z, h (Y z) * FinitePosterior.fieldMean energy spin q (Y z) ∂ρ := by
  let ρ := μ.prod (Measure.pi (fun _ : I => gaussianReal 0 1))
  let Y : S × (I → ℝ) → I → ℝ :=
    fun z i => t * spin z.1 i + Real.sqrt t * z.2 i
  change (∫ z, h (Y z) * q z.1 ∂ρ) = _
  have hY : Measurable Y := by
    exact Measurable.of_eval (fun index =>
      (measurable_const.mul ((measurable_of_finite (fun state => spin state index)).comp
        measurable_fst)).add (measurable_const.mul
          ((measurable_pi_apply index).comp measurable_snd)))
  have hm : (inferInstance : MeasurableSpace (I → ℝ)).comap Y ≤
      (inferInstance : MeasurableSpace (S × (I → ℝ))) := hY.comap_le
  have htest : StronglyMeasurable[(inferInstance : MeasurableSpace (I → ℝ)).comap Y]
      (fun z => h (Y z)) :=
    (hh.comp (comap_measurable Y)).stronglyMeasurable
  have hq : Integrable (fun z : S × (I → ℝ) => q z.1) ρ := by
    apply (integrable_const (∑ s, |q s|)).mono'
    · exact ((measurable_of_finite q).comp measurable_fst).aestronglyMeasurable
    · filter_upwards [] with z
      rw [Real.norm_eq_abs]
      exact Finset.single_le_sum (fun s _ => abs_nonneg (q s)) (Finset.mem_univ z.1)
  have hpull := condExp_stronglyMeasurable_mul_of_bound hm htest hq C
    (Filter.Eventually.of_forall (fun z => hbound (Y z)))
  have hposterior := finiteStandardGaussianPlanted_condExp_fieldMean
    μ energy hprior t ht spin hspin q
  calc
    (∫ z, h (Y z) * q z.1 ∂ρ) =
        ∫ z, ρ[(fun z => h (Y z)) * (fun z => q z.1) | (inferInstance : MeasurableSpace (I → ℝ)).comap Y] z ∂ρ :=
      (integral_condExp hm).symm
    _ = ∫ z, h (Y z) * ρ[(fun z => q z.1) | (inferInstance : MeasurableSpace (I → ℝ)).comap Y] z ∂ρ :=
      integral_congr_ae hpull
    _ = ∫ z, h (Y z) * FinitePosterior.fieldMean energy spin q (Y z) ∂ρ := by
      apply integral_congr_ae
      filter_upwards [hposterior] with z hz
      rw [hz]

end Problem367

end

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Gaussian_FiniteIsingGaussianTesting
attribute [-instance] _root_.OAI.Problem367.IsingConditionalCopyBounds.graphLaw_isProbabilityMeasure _root_.OAI.Problem367.IsingObservationFactor.copies_probability _root_.OAI.Problem367.IsingObservationFactor.kernel_markov _root_.OAI.Problem367.IsingObservationInnovation.innovationMap_observationLaw_probability _root_.OAI.Problem367.IsingObservationInnovation.observationLaw_probability _root_.OAI.Problem367.TreeKoopman.labelProbability _root_.OAI.Problem367.WienerSampler.pathMeasurableSpace _root_.OAI.Problem367.freeIsingMeasure_probability _root_.OAI.Problem367.reducedTailFintype _root_.OAI.Problem367.treeBallFintype _root_.OAI.Problem367.treeShellFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

namespace Problem367

local instance instNonemptyIsingSpin_raa325a_1 : Nonempty IsingSpin := ⟨.neg⟩
theorem HasFreeIsingLaw.restrict_real_eq_normalized_exp
    {d : ℕ} {beta : ℝ} {μ : Measure (TreeVertex d → IsingSpin)}
    (hμ : HasFreeIsingLaw (Real.tanh beta) μ)
    (D : Finset (TreeVertex d)) (hD : ConnectedFinset D)
    (eta : D → IsingSpin) :
    (μ.map D.restrict).real {eta} =
      Real.exp (finiteIsingEnergy beta D eta) /
        ∑ xi, Real.exp (finiteIsingEnergy beta D xi) := by
  rw [Measure.real, hμ.restrict_atom D hD eta, freeCylinderWeight_tanh_eq_exp]
  rw [ENNReal.toReal_ofReal (by positivity)]
  rw [show (∑ xi, Real.exp (finiteIsingEnergy beta D xi)) =
    2 * (2 * Real.cosh beta) ^ (inducedEdges D).card from
      finiteIsing_partitionFunction beta D hD]
  rfl

end Problem367

end

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Gaussian_IntegrationByParts
attribute [-instance] _root_.OAI.Problem367.WienerSampler.pathMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory ProbabilityTheory
open scoped NNReal

namespace Problem367

theorem hasDerivAt_gaussianPDFReal (m : ℝ) {v : ℝ≥0} (hv : v ≠ 0) (x : ℝ) :
    HasDerivAt (gaussianPDFReal m v)
      (-(x - m) / (v : ℝ) * gaussianPDFReal m v x) x := by
  have hv' : (v : ℝ) ≠ 0 := by exact_mod_cast hv
  have h := (((((hasDerivAt_id x).sub_const m).pow 2).neg.div_const
    (2 * (v : ℝ))).exp).const_mul ((Real.sqrt (2 * Real.pi * v))⁻¹)
  convert! h using 1
  all_goals try with_reducible_and_instances rfl
  simp only [gaussianPDFReal, Pi.neg_apply, Pi.pow_apply, id_eq,
    Nat.cast_ofNat, Nat.reduceSub, pow_one, mul_one]
  field_simp

theorem integrable_gaussian_iff_density {m : ℝ} {v : ℝ≥0} (hv : v ≠ 0)
    {f : ℝ → ℝ} :
    Integrable f (gaussianReal m v) ↔
      Integrable (fun x => gaussianPDFReal m v x * f x) := by
  rw [gaussianReal_of_var_ne_zero _ hv]
  simpa only [toReal_gaussianPDF, smul_eq_mul] using
    (integrable_withDensity_iff_integrable_smul'
      (measurable_gaussianPDF m v)
      (Filter.Eventually.of_forall (fun _ => gaussianPDF_lt_top)) (g := f))

theorem gaussian_integral_centered_mul_eq_variance_mul_deriv
    (m : ℝ) (v : ℝ≥0) {f f' : ℝ → ℝ}
    (hf : ∀ x, HasDerivAt f (f' x) x)
    (hfi : Integrable f (gaussianReal m v))
    (hf'i : Integrable f' (gaussianReal m v))
    (hxfi : Integrable (fun x => (x - m) * f x) (gaussianReal m v)) :
    (∫ x, (x - m) * f x ∂gaussianReal m v) =
      (v : ℝ) * ∫ x, f' x ∂gaussianReal m v := by
  by_cases hv : v = 0
  · subst v
    simp
  have hv' : (v : ℝ) ≠ 0 := by exact_mod_cast hv
  have huf := (integrable_gaussian_iff_density hv).mp hfi
  have huf' := (integrable_gaussian_iff_density hv).mp hf'i
  have hxuf := (integrable_gaussian_iff_density hv).mp hxfi
  have hfirst : Integrable (fun x => f x *
      (-(x - m) / (v : ℝ) * gaussianPDFReal m v x)) := by
    convert hxuf.const_mul (-(v : ℝ)⁻¹) using 1
    all_goals try with_reducible_and_instances rfl
    ext x
    ring
  have hsecond : Integrable (fun x => f' x * gaussianPDFReal m v x) := by
    simpa only [mul_comm] using huf'
  have hproduct : Integrable (fun x => f x * gaussianPDFReal m v x) := by
    simpa only [mul_comm] using huf
  have hibp := integral_mul_deriv_eq_deriv_mul_of_integrable
    (u := f) (v := gaussianPDFReal m v)
    (u' := f') (v' := fun x => -(x - m) / (v : ℝ) * gaussianPDFReal m v x)
    (fun x _ => hf x) (fun x _ => hasDerivAt_gaussianPDFReal m hv x)
    hfirst hsecond hproduct
  have hfun : (fun x => f x * (-(x - m) / (v : ℝ) * gaussianPDFReal m v x)) =
      (fun x => -(v : ℝ)⁻¹ * (gaussianPDFReal m v x * ((x - m) * f x))) := by
    funext x
    ring
  rw [hfun, integral_const_mul] at hibp
  simp_rw [mul_comm (f' _) (gaussianPDFReal m v _)] at hibp
  rw [integral_gaussianReal_eq_integral_smul hv,
    integral_gaussianReal_eq_integral_smul hv]
  simp only [smul_eq_mul]
  have hmul := congrArg (fun z : ℝ => -(v : ℝ) * z) hibp
  field_simp at hmul
  simpa only [mul_assoc] using hmul

theorem gaussian_integral_centered_mul_of_bounded
    (m : ℝ) (v : ℝ≥0) {f f' : ℝ → ℝ} {C : ℝ}
    (hf : ∀ x, HasDerivAt f (f' x) x) (hbound : ∀ x, |f x| ≤ C)
    (hf'i : Integrable f' (gaussianReal m v)) :
    (∫ x, (x - m) * f x ∂gaussianReal m v) =
      (v : ℝ) * ∫ x, f' x ∂gaussianReal m v := by
  have hfm : AEStronglyMeasurable f (gaussianReal m v) :=
    (continuous_iff_continuousAt.mpr (fun x => (hf x).continuousAt)).aestronglyMeasurable
  have hb : ∀ᵐ x ∂gaussianReal m v, ‖f x‖ ≤ C :=
    Filter.Eventually.of_forall (fun x => by simpa only [Real.norm_eq_abs] using hbound x)
  have hfi := Integrable.of_bound hfm C hb
  have hxi : Integrable (fun x : ℝ => x - m) (gaussianReal m v) :=
    ((memLp_id_gaussianReal 1).integrable (by norm_num)).sub (integrable_const m)
  exact gaussian_integral_centered_mul_eq_variance_mul_deriv m v hf hfi hf'i
    (hxi.mul_bdd hfm hb)

theorem gaussian_integral_centered_mul_of_bounded_deriv
    (m : ℝ) (v : ℝ≥0) {f f' : ℝ → ℝ} {C D : ℝ}
    (hf : ∀ x, HasDerivAt f (f' x) x)
    (hbound : ∀ x, |f x| ≤ C) (hbound' : ∀ x, |f' x| ≤ D) :
    (∫ x, (x - m) * f x ∂gaussianReal m v) =
      (v : ℝ) * ∫ x, f' x ∂gaussianReal m v := by
  apply gaussian_integral_centered_mul_of_bounded m v hf hbound
  have heq : f' = deriv f := funext (fun x => (hf x).deriv.symm)
  have hfm : AEStronglyMeasurable f' (gaussianReal m v) := by
    rw [heq]
    exact aestronglyMeasurable_deriv f _
  exact Integrable.of_bound hfm D
    (Filter.Eventually.of_forall (fun x => by simpa only [Real.norm_eq_abs] using hbound' x))

end Problem367

end

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Gaussian_PiIntegrationByParts
attribute [-instance] _root_.OAI.Problem367.WienerSampler.pathMeasurableSpace _root_.OAI.Problem367.reducedTailFinite _root_.OAI.Problem367.reducedTailFintype _root_.OAI.Problem367.treeBallFinite _root_.OAI.Problem367.treeBallFintype _root_.OAI.Problem367.treeShellFinite _root_.OAI.Problem367.treeShellFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory ProbabilityTheory
open scoped NNReal

namespace Problem367

section CoordinateSplit

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem measurePreserving_funSplitAt (μ : ι → Measure ℝ)
    [∀ j, SigmaFinite (μ j)] (i : ι) :
    MeasurePreserving (Homeomorph.funSplitAt ℝ i) (Measure.pi μ)
      ((μ i).prod (Measure.pi fun j : {j // j ≠ i} => μ j)) := by
  let e := (Homeomorph.funSplitAt ℝ i).toMeasurableEquiv.symm
  apply MeasurePreserving.symm e
  refine ⟨e.measurable, (Measure.pi_eq fun s hs => ?_).symm⟩
  rw [e.map_apply]
  have hpre : e ⁻¹' Set.pi Set.univ s =
      s i ×ˢ Set.pi Set.univ (fun j : {j // j ≠ i} => s j) := by
    ext x
    simp only [Set.mem_preimage, Set.mem_pi, Set.mem_univ, forall_true_left,
      Set.mem_prod]
    constructor
    · intro h
      constructor
      · simpa [e, Homeomorph.funSplitAt, Homeomorph.piSplitAt,
          Equiv.piSplitAt] using h i
      · intro j
        simpa [e, Homeomorph.funSplitAt, Homeomorph.piSplitAt,
          Equiv.piSplitAt, j.property] using h j
    · rintro ⟨hi, hj⟩ j
      by_cases hji : j = i
      · subst j
        simpa [e, Homeomorph.funSplitAt, Homeomorph.piSplitAt,
          Equiv.piSplitAt] using hi
      · simpa [e, Homeomorph.funSplitAt, Homeomorph.piSplitAt,
          Equiv.piSplitAt, hji] using hj ⟨j, hji⟩
  rw [hpre, Measure.prod_prod, Measure.pi_pi]
  simpa using (Fintype.prod_eq_mul_prod_subtype_ne (fun j => μ j (s j)) i).symm

theorem gaussian_pi_integral_centered_mul_of_bounded_deriv
    (m : ι → ℝ) (v : ι → ℝ≥0) (i : ι)
    {f f' : (ι → ℝ) → ℝ} {C D : ℝ}
    (hfc : Continuous f) (hf'c : Continuous f')
    (hf : ∀ z t, HasDerivAt (fun r => f (Function.update z i r))
      (f' (Function.update z i t)) t)
    (hbound : ∀ z, |f z| ≤ C) (hbound' : ∀ z, |f' z| ≤ D) :
    (∫ z, (z i - m i) * f z ∂Measure.pi (fun j => gaussianReal (m j) (v j))) =
      (v i : ℝ) * ∫ z, f' z ∂Measure.pi (fun j => gaussianReal (m j) (v j)) := by
  let μ : ι → Measure ℝ := fun j => gaussianReal (m j) (v j)
  let ν := Measure.pi (fun j : {j // j ≠ i} => μ j)
  let e := (Homeomorph.funSplitAt ℝ i).toMeasurableEquiv.symm
  have hmp : MeasurePreserving e ((μ i).prod ν) (Measure.pi μ) :=
    (measurePreserving_funSplitAt μ i).symm
  have heval (x : ℝ × ({j // j ≠ i} → ℝ)) : e x i = x.1 := by
    simp [e, Homeomorph.funSplitAt, Homeomorph.piSplitAt, Equiv.piSplitAt]
  have hupdate (x : ℝ × ({j // j ≠ i} → ℝ)) (t : ℝ) :
      Function.update (e x) i t = e (t, x.2) := by
    ext j
    by_cases hji : j = i
    · subst j
      simp [heval]
    · simp [e, Homeomorph.funSplitAt,
        Homeomorph.piSplitAt, Equiv.piSplitAt, hji]
  have hxi : Integrable (fun z : ι → ℝ => z i - m i) (Measure.pi μ) := by
    have hi : Integrable (fun r : ℝ => r - m i) (μ i) :=
      ((memLp_id_gaussianReal 1).integrable (by norm_num)).sub (integrable_const _)
    exact (measurePreserving_eval μ i).integrable_comp_of_integrable hi
  have hxfi : Integrable (fun z : ι → ℝ => (z i - m i) * f z) (Measure.pi μ) :=
    hxi.mul_bdd hfc.aestronglyMeasurable (Filter.Eventually.of_forall fun z => by
      simpa only [Real.norm_eq_abs] using hbound z)
  have hf'i : Integrable f' (Measure.pi μ) :=
    Integrable.of_bound hf'c.aestronglyMeasurable D
      (Filter.Eventually.of_forall fun z => by
        simpa only [Real.norm_eq_abs] using hbound' z)
  have hprod := (hmp.integrable_comp_emb e.measurableEmbedding).2 hxfi
  have hprod' := (hmp.integrable_comp_emb e.measurableEmbedding).2 hf'i
  have hstein (y : {j // j ≠ i} → ℝ) :
      (∫ r, (r - m i) * f (e (r, y)) ∂μ i) =
        (v i : ℝ) * ∫ r, f' (e (r, y)) ∂μ i := by
    apply gaussian_integral_centered_mul_of_bounded_deriv (m i) (v i)
    · intro r
      simpa only [hupdate] using hf (e (0, y)) r
    · exact fun r => hbound _
    · exact fun r => hbound' _
  calc
    _ = ∫ x, (e x i - m i) * f (e x) ∂(μ i).prod ν :=
      (hmp.integral_comp e.measurableEmbedding _).symm
    _ = ∫ y, ∫ r, (r - m i) * f (e (r, y)) ∂μ i ∂ν := by
      simpa only [Function.comp_def, heval] using integral_prod_symm _ hprod
    _ = ∫ y, (v i : ℝ) * ∫ r, f' (e (r, y)) ∂μ i ∂ν := by
      congr 1
      funext y
      exact hstein y
    _ = (v i : ℝ) * ∫ x, f' (e x) ∂(μ i).prod ν := by
      rw [integral_const_mul]
      congr 1
      exact (integral_prod_symm _ hprod').symm
    _ = _ := by rw [hmp.integral_comp e.measurableEmbedding]

theorem gaussian_pi_integral_mul_affine_of_bounded_deriv
    (a b : ι → ℝ) (i : ι)
    {f f' : (ι → ℝ) → ℝ} {C D : ℝ}
    (hfc : Continuous f) (hf'c : Continuous f')
    (hf : ∀ z t, HasDerivAt (fun r => f (Function.update z i r))
      (f' (Function.update z i t)) t)
    (hbound : ∀ z, |f z| ≤ C) (hbound' : ∀ z, |f' z| ≤ D) :
    (∫ z, z i * f (fun j => a j + b j * z j)
      ∂Measure.pi (fun _ : ι => gaussianReal 0 1)) =
      b i * ∫ z, f' (fun j => a j + b j * z j)
        ∂Measure.pi (fun _ : ι => gaussianReal 0 1) := by
  let A : (ι → ℝ) → (ι → ℝ) := fun z j => a j + b j * z j
  have hAc : Continuous A := continuous_pi fun j =>
    continuous_const.add (continuous_const.mul (continuous_apply j))
  have hupdate (z : ι → ℝ) (t : ℝ) :
      A (Function.update z i t) = Function.update (A z) i (a i + b i * t) := by
    ext j
    by_cases hji : j = i
    · subst j
      simp [A]
    · simp [A, hji]
  have hd (z : ι → ℝ) (t : ℝ) :
      HasDerivAt (fun r => f (A (Function.update z i r)))
        (b i * f' (A (Function.update z i t))) t := by
    simp only [hupdate]
    simpa only [Function.comp_def, id_eq, mul_one, mul_comm] using
      (hf (A z) (a i + b i * t)).comp t
        (((hasDerivAt_id t).const_mul (b i)).const_add (a i))
  have hb' (z : ι → ℝ) : |b i * f' (A z)| ≤ |b i| * D := by
    rw [abs_mul]
    exact mul_le_mul_of_nonneg_left (hbound' _) (abs_nonneg _)
  have h := gaussian_pi_integral_centered_mul_of_bounded_deriv
    (fun _ => 0) (fun _ => 1) i (hfc.comp hAc)
    (continuous_const.mul (hf'c.comp hAc)) hd
    (fun z => hbound (A z)) hb'
  simpa only [Function.comp_def, Pi.mul_apply, A, sub_zero, NNReal.coe_one,
    one_mul, integral_const_mul] using h

end CoordinateSplit

end Problem367

end

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Posterior_FieldCalculus
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open scoped BigOperators ContDiff

namespace Problem367.FinitePosterior

variable {S : Type*} [Fintype S] [Nonempty S]

lemma spin_mean_variance_pos (energy signal observable : S → ℝ) (t : ℝ)
    (hspin : ∀ s, observable s = -1 ∨ observable s = 1)
    (hneg : ∃ s, observable s = -1) (hpos : ∃ s, observable s = 1) :
    0 < 1 - mean energy signal observable t ^ 2 := by
  have h := spin_mean_mem_Ioo energy signal observable t hspin hneg hpos
  nlinarith [h.1, h.2]

theorem hasDerivAt_mean_covariance (energy signal observable : S → ℝ) (t : ℝ) :
    HasDerivAt (mean energy signal observable)
      (tiltCovariance energy signal observable t) t :=
  hasDerivAt_mean energy signal observable t

theorem hasDerivAt_tiltCovariance (energy signal observable : S → ℝ) (t : ℝ)
    (hsignal : ∀ s, signal s = -1 ∨ signal s = 1) :
    HasDerivAt (tiltCovariance energy signal observable)
      (-2 * mean energy signal signal t * tiltCovariance energy signal observable t) t := by
  have hprod : (fun s => (observable s * signal s) * signal s) = observable := by
    funext s
    rcases hsignal s with hs | hs <;> simp [hs]
  have hc := hasDerivAt_mean energy signal (fun s => observable s * signal s) t
  rw [hprod] at hc
  have hm := hasDerivAt_mean energy signal observable t
  have hn := hasDerivAt_spin_mean energy signal t hsignal
  have hd := hc.sub (hm.mul hn)
  change HasDerivAt (tiltCovariance energy signal observable) _ t at hd
  apply hd.congr_deriv
  unfold tiltCovariance
  ring

theorem hasDerivAt_tiltResponse (energy signal observable : S → ℝ) (t : ℝ)
    (hsignal : ∀ s, signal s = -1 ∨ signal s = 1)
    (hspin : ∀ s, observable s = -1 ∨ observable s = 1)
    (hneg : ∃ s, observable s = -1) (hpos : ∃ s, observable s = 1) :
    HasDerivAt (tiltResponse energy signal observable)
      (-2 * mean energy signal signal t * tiltResponse energy signal observable t +
        2 * mean energy signal observable t * tiltResponse energy signal observable t ^ 2) t := by
  have hden := ne_of_gt (spin_mean_variance_pos energy signal observable t hspin hneg hpos)
  have hd := (hasDerivAt_tiltCovariance energy signal observable t hsignal).div
    (((hasDerivAt_mean_covariance energy signal observable t).pow 2).const_sub 1) hden
  change HasDerivAt (tiltResponse energy signal observable) _ t at hd
  apply hd.congr_deriv
  unfold tiltResponse
  simp only [Pi.pow_apply, Nat.cast_ofNat, Nat.reduceSub, pow_one]
  field_simp [hden]
  ring

section Fields

variable {V : Type*} [Fintype V]

omit [Nonempty S] in
lemma fieldMean_sum_mul (energy : S → ℝ) (spin : S → V → ℝ)
    (observable : V → S → ℝ) (a : V → ℝ) (x : V → ℝ) :
    fieldMean energy spin (fun s => ∑ v, a v * observable v s) x =
      ∑ v, a v * fieldMean energy spin (observable v) x := by
  unfold fieldMean
  simp_rw [Finset.sum_mul]
  rw [Finset.sum_comm]
  simp only [Finset.sum_div, Finset.mul_sum, mul_div_assoc, mul_assoc]

theorem differentiable_fieldMean (energy : S → ℝ) (spin : S → V → ℝ)
    (observable : S → ℝ) : Differentiable ℝ (fieldMean energy spin observable) :=
  (contDiff_fieldMean_all energy spin observable 1).differentiable (by norm_num)

theorem fderiv_fieldMean_covariance_apply (energy : S → ℝ) (spin : S → V → ℝ)
    (observable : S → ℝ) (x direction : V → ℝ) :
    fderiv ℝ (fieldMean energy spin observable) x direction =
      ∑ v, direction v * fieldCovariance energy spin observable x v := by
  rw [fderiv_fieldMean_apply]
  have hobs : (fun s => observable s * ∑ v, direction v * spin s v) =
      (fun s => ∑ v, direction v * (observable s * spin s v)) := by
    funext s
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro v _
    ring
  rw [hobs, fieldMean_sum_mul, fieldMean_sum_mul]
  simp only [fieldCovariance, Finset.mul_sum, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro v _
  ring

theorem hasFDerivAt_fieldMean (energy : S → ℝ) (spin : S → V → ℝ)
    (observable : S → ℝ) (x : V → ℝ) :
    HasFDerivAt (fieldMean energy spin observable)
      (fieldMeanDerivative energy spin observable x) x := by
  have heq : fderiv ℝ (fieldMean energy spin observable) x =
      fieldMeanDerivative energy spin observable x := by
    ext direction
    rw [fderiv_fieldMean_covariance_apply]
    simp only [fieldMeanDerivative, sum_apply,
      smul_apply, ContinuousLinearMap.proj_apply, smul_eq_mul]
    apply Finset.sum_congr rfl
    intro v _
    ring
  rw [← heq]
  exact (differentiable_fieldMean energy spin observable x).hasFDerivAt

variable [DecidableEq V]

omit [Nonempty S] in
lemma fieldMean_coordinate_tilt (energy : S → ℝ) (spin : S → V → ℝ)
    (observable : S → ℝ) (x : V → ℝ) (u : V) (t : ℝ) :
    fieldMean energy spin observable (fun v => x v + if v = u then t else 0) =
      mean (fieldEnergy energy spin x) (fun s => spin s u) observable t := by
  simpa only [mul_ite, mul_one, mul_zero, ite_mul, one_mul, zero_mul,
    Finset.sum_ite_eq', Finset.mem_univ, ite_true, if_true] using
    fieldMean_along_line energy spin observable x (fun v => if v = u then 1 else 0) t

omit [Nonempty S] [DecidableEq V] in
lemma tiltResponse_fieldEnergy_zero (energy : S → ℝ) (spin : S → V → ℝ)
    (observable : S → ℝ) (x : V → ℝ) (u : V) :
    tiltResponse (fieldEnergy energy spin x) (fun s => spin s u) observable 0 =
      normalizedFieldCovariance energy spin observable x u := by
  simp only [tiltResponse, tiltCovariance, mean_fieldEnergy_zero,
    normalizedFieldCovariance, fieldCovariance]

end Fields

end Problem367.FinitePosterior

end

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Posterior_DerivativeBounds
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open scoped BigOperators

namespace Problem367.FinitePosterior

variable {S : Type*} [Fintype S] [Nonempty S]

theorem abs_mean_le (energy signal observable : S → ℝ) (t A : ℝ)
    (hbound : ∀ s, |observable s| ≤ A) :
    |mean energy signal observable t| ≤ A := by
  rw [mean_eq_sum_mass]
  calc
    |∑ s, observable s * mass energy signal t s| ≤
        ∑ s, |observable s * mass energy signal t s| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ s, A * mass energy signal t s := by
      apply Finset.sum_le_sum
      intro s _
      rw [abs_mul, abs_of_pos (mass_pos energy signal t s)]
      exact mul_le_mul_of_nonneg_right (hbound s) (mass_pos energy signal t s).le
    _ = A := by rw [← Finset.mul_sum, sum_mass, mul_one]

omit [Fintype S] [Nonempty S] in
lemma abs_spin_eq_one (signal : S → ℝ)
    (hsignal : ∀ s, signal s = -1 ∨ signal s = 1) (s : S) : |signal s| = 1 := by
  rcases hsignal s with hs | hs <;> simp [hs]

section Fields

variable {V : Type*} [Fintype V]

theorem abs_fieldMean_le (energy : S → ℝ) (spin : S → V → ℝ)
    (observable : S → ℝ) (x : V → ℝ) (A : ℝ)
    (hbound : ∀ s, |observable s| ≤ A) :
    |fieldMean energy spin observable x| ≤ A := by
  rw [← mean_fieldEnergy_zero energy spin (fun _ => 0)]
  exact abs_mean_le _ _ _ _ _ hbound

end Fields

end Problem367.FinitePosterior

end

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Posterior_SqrtObservationDerivative
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory Filter Set
open scoped Topology

namespace Problem367

theorem continuous_integral_sqrt_observation
    {Ω E : Type*} [MeasurableSpace Ω] [NormedAddCommGroup E] [NormedSpace ℝ E]
    {P : Measure Ω} [IsFiniteMeasure P] {S G : Ω → E}
    (hS : AEStronglyMeasurable S P) (hG : AEStronglyMeasurable G P)
    {f : E → ℝ} (hf : Continuous f) {C : ℝ} (hbound : ∀ x, |f x| ≤ C) :
    Continuous (fun t : ℝ => ∫ ω, f (t • S ω + Real.sqrt t • G ω) ∂P) := by
  apply continuous_of_dominated (bound := fun _ => C)
  · intro t
    exact hf.comp_aestronglyMeasurable
      ((hS.const_smul t).add (hG.const_smul (Real.sqrt t)))
  · intro t
    exact Eventually.of_forall fun ω => by
      simpa only [Real.norm_eq_abs] using hbound (t • S ω + Real.sqrt t • G ω)
  · exact integrable_const C
  · exact Eventually.of_forall fun ω => hf.comp
      ((continuous_id.smul continuous_const).add
        (Real.continuous_sqrt.smul continuous_const))

end Problem367

end

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Posterior_GaussianTimeDerivative
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory Filter
open scoped BigOperators Topology

namespace Problem367.FinitePosterior

variable {V : Type*} [Fintype V]

section Posterior

variable {S : Type*} [Fintype S] [Nonempty S]

theorem continuous_fieldCovariance (energy : S → ℝ) (spin : S → V → ℝ)
    (observable : S → ℝ) (v : V) :
    Continuous (fun x => fieldCovariance energy spin observable x v) := by
  exact (continuous_fieldMean energy spin (fun s => observable s * spin s v)).sub
    ((continuous_fieldMean energy spin observable).mul
      (continuous_fieldMean energy spin (fun s => spin s v)))

end Posterior

end Problem367.FinitePosterior

end

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Posterior_GaussianGradient
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace Problem367.FinitePosterior

variable {S V : Type*} [Fintype S] [Nonempty S] [Fintype V]

variable [DecidableEq V]

omit [Nonempty S] in
lemma fieldCovariance_coordinate_tilt (energy : S → ℝ) (spin : S → V → ℝ)
    (observable : S → ℝ) (x : V → ℝ) (v : V) (t : ℝ) :
    fieldCovariance energy spin observable (fun u => x u + if u = v then t else 0) v =
      tiltCovariance (fieldEnergy energy spin x) (fun s => spin s v) observable t := by
  simp only [fieldCovariance, fieldMean_coordinate_tilt, tiltCovariance]

omit [Fintype V] in
lemma update_eq_zero_shift (x : V → ℝ) (v : V) (t : ℝ) :
    Function.update x v t =
      (fun u => Function.update x v 0 u + if u = v then t else 0) := by
  funext u
  by_cases hu : u = v
  · subst u
    simp
  · simp [hu]

end Problem367.FinitePosterior

end

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Posterior_GaussianEnergy
attribute [-instance] _root_.OAI.Problem367.WienerSampler.pathMeasurableSpace _root_.OAI.Problem367.reducedTailFinite _root_.OAI.Problem367.treeBallFinite _root_.OAI.Problem367.treeShellFinite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory
open scoped NNReal

namespace Problem367.FinitePosterior

variable {S V : Type*} [Fintype S] [Nonempty S] [Fintype V] [DecidableEq V]

section Planted

variable [MeasurableSpace S] [MeasurableSingletonClass S]

omit [Nonempty S] [Fintype V] [DecidableEq V] in
lemma measurable_finiteStandardObservation (spin : S → V → ℝ) (t : ℝ) :
    Measurable (finiteStandardObservation spin t) := by
  unfold finiteStandardObservation gaussianObservationCurve
  exact ((measurable_of_finite spin).comp measurable_fst).const_smul t |>.add
    (measurable_snd.const_smul (Real.sqrt t))

omit [Fintype S] [Nonempty S] [DecidableEq V] [MeasurableSingletonClass S] in

theorem integrable_finiteStandardNoise (μ : Measure S) [IsFiniteMeasure μ] (v : V) :
    Integrable (fun x : S × (V → ℝ) => x.2 v)
      (μ.prod (Measure.pi (fun _ : V => gaussianReal 0 1))) := by
  have h := (measurePreserving_eval (fun _ : V => gaussianReal 0 1) v).integrable_comp_of_integrable ((memLp_id_gaussianReal 1).integrable (by norm_num))
  exact h.comp_snd μ

end Planted
end Problem367.FinitePosterior

end

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Gaussian_FiniteFieldGaussianEnergy
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open scoped BigOperators NNReal

namespace Problem367.FinitePosterior

variable {S : Type*} [Fintype S] [Nonempty S]

omit [Nonempty S] in
lemma covariance_eq_centered_sum_entropy (energy signal a b : S → ℝ) (t : ℝ) :
    mean energy signal (fun s => a s * b s) t -
      mean energy signal a t * mean energy signal b t =
      ∑ s, (a s - mean energy signal a t) * b s * mass energy signal t s := by
  simp only [sub_mul, Finset.sum_sub_distrib]
  simp only [mul_assoc, ← Finset.mul_sum, ← mean_eq_sum_mass]
  rw [mean_eq_sum_mass energy signal (fun s => a s * b s) t]
  simp only [mul_assoc]

theorem abs_covariance_le_spin_variance_entropy (energy signal a b : S → ℝ) (t : ℝ)
    (ha : ∀ s, a s = -1 ∨ a s = 1)
    (han : ∃ s, a s = -1) (hap : ∃ s, a s = 1)
    (hb : ∀ s, |b s| ≤ 1) :
    |mean energy signal (fun s => a s * b s) t -
      mean energy signal a t * mean energy signal b t| ≤
      1 - mean energy signal a t ^ 2 := by
  let m := mean energy signal a t
  have hm := spin_mean_mem_Ioo energy signal a t ha han hap
  have habs (s : S) : |a s - m| = 1 - a s * m := by
    rcases ha s with hs | hs
    · rw [hs, abs_of_neg (by dsimp [m] <;> linarith [hm.1])]
      ring
    · rw [hs, abs_of_pos (by dsimp [m] <;> linarith [hm.2])]
      ring
  rw [covariance_eq_centered_sum_entropy]
  calc
    |∑ s, (a s - mean energy signal a t) * b s * mass energy signal t s| ≤
        ∑ s, |(a s - m) * b s * mass energy signal t s| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ s, (1 - a s * m) * mass energy signal t s := by
      apply Finset.sum_le_sum
      intro s _
      rw [abs_mul, abs_mul, abs_of_pos (mass_pos energy signal t s)]
      calc
        |a s - m| * |b s| * mass energy signal t s ≤
            |a s - m| * 1 * mass energy signal t s := by
              exact mul_le_mul_of_nonneg_right
                (mul_le_mul_of_nonneg_left (hb s) (abs_nonneg _))
                (mass_pos energy signal t s).le
        _ = _ := by rw [habs]; ring
    _ = 1 - mean energy signal a t ^ 2 := by
      simp only [sub_mul, one_mul, Finset.sum_sub_distrib, sum_mass]
      have heq (s : S) : a s * m * mass energy signal t s =
          m * (a s * mass energy signal t s) := by ring
      simp_rw [heq]
      rw [← Finset.mul_sum, ← mean_eq_sum_mass]
      dsimp [m]
      ring

theorem abs_tiltResponse_le_one_entropy (energy signal observable : S → ℝ) (t : ℝ)
    (hspin : ∀ s, observable s = -1 ∨ observable s = 1)
    (hneg : ∃ s, observable s = -1) (hpos : ∃ s, observable s = 1)
    (hsignal : ∀ s, |signal s| ≤ 1) :
    |tiltResponse energy signal observable t| ≤ 1 := by
  have hden := spin_mean_variance_pos energy signal observable t hspin hneg hpos
  rw [tiltResponse, abs_div, abs_of_pos hden, div_le_one hden]
  exact abs_covariance_le_spin_variance_entropy energy signal observable signal t
    hspin hneg hpos hsignal

variable {V : Type*} [Fintype V]

lemma fieldVariance_pos_entropy (energy : S → ℝ) (spin : S → V → ℝ)
    (observable : S → ℝ) (x : V → ℝ)
    (hspin : ∀ s, observable s = -1 ∨ observable s = 1)
    (hneg : ∃ s, observable s = -1) (hpos : ∃ s, observable s = 1) :
    0 < 1 - fieldMean energy spin observable x ^ 2 := by
  have h := fieldMean_spin_mem_Ioo energy spin observable x hspin hneg hpos
  nlinarith [h.1, h.2]

theorem abs_normalizedFieldCovariance_le_one_entropy (energy : S → ℝ)
    (spin : S → V → ℝ) (observable : S → ℝ) (x : V → ℝ) (v : V)
    (hspin : ∀ s, observable s = -1 ∨ observable s = 1)
    (hneg : ∃ s, observable s = -1) (hpos : ∃ s, observable s = 1)
    (hsignal : ∀ s, |spin s v| ≤ 1) :
    |normalizedFieldCovariance energy spin observable x v| ≤ 1 := by
  rw [← tiltResponse_fieldEnergy_zero]
  exact abs_tiltResponse_le_one_entropy _ _ _ _ hspin hneg hpos hsignal

theorem continuous_normalizedFieldCovariance_entropy (energy : S → ℝ)
    (spin : S → V → ℝ) (observable : S → ℝ) (v : V)
    (hspin : ∀ s, observable s = -1 ∨ observable s = 1)
    (hneg : ∃ s, observable s = -1) (hpos : ∃ s, observable s = 1) :
    Continuous (fun x => normalizedFieldCovariance energy spin observable x v) := by
  exact (continuous_fieldCovariance energy spin observable v).div
    (continuous_const.sub ((continuous_fieldMean energy spin observable).pow 2))
    (fun x => (fieldVariance_pos_entropy energy spin observable x hspin hneg hpos).ne')

theorem continuous_fieldEntropy (energy : S → ℝ) (spin : S → V → ℝ)
    (observable : S → ℝ)
    (hspin : ∀ s, observable s = -1 ∨ observable s = 1)
    (hneg : ∃ s, observable s = -1) (hpos : ∃ s, observable s = 1) :
    Continuous (fieldEntropy energy spin observable) := by
  exact ((continuous_const.sub ((continuous_fieldMean energy spin observable).pow 2)).log
    (fun x => (fieldVariance_pos_entropy energy spin observable x hspin hneg hpos).ne')).neg

theorem hasFDerivAt_fieldEntropy (energy : S → ℝ) (spin : S → V → ℝ)
    (observable : S → ℝ) (x : V → ℝ)
    (hspin : ∀ s, observable s = -1 ∨ observable s = 1)
    (hneg : ∃ s, observable s = -1) (hpos : ∃ s, observable s = 1) :
    HasFDerivAt (fieldEntropy energy spin observable)
      (∑ v, fieldEntropyGradient energy spin observable x v •
        (ContinuousLinearMap.proj v : (V → ℝ) →L[ℝ] ℝ)) x := by
  have hden := (fieldVariance_pos_entropy energy spin observable x hspin hneg hpos).ne'
  have hd := ((((hasFDerivAt_fieldMean energy spin observable x).pow 2).const_sub 1).log hden).neg
  change HasFDerivAt (fieldEntropy energy spin observable) _ x at hd
  apply hd.congr_fderiv
  ext y
  simp only [fieldMeanDerivative, fieldEntropyGradient, normalizedFieldCovariance,
    Nat.reduceSub, pow_one, neg_apply,
    sum_apply, smul_apply, ContinuousLinearMap.proj_apply, smul_eq_mul,
    Finset.mul_sum]
  ring_nf
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro v _
  ring

theorem continuous_fieldEntropyGradient (energy : S → ℝ) (spin : S → V → ℝ)
    (observable : S → ℝ) (v : V)
    (hspin : ∀ s, observable s = -1 ∨ observable s = 1)
    (hneg : ∃ s, observable s = -1) (hpos : ∃ s, observable s = 1) :
    Continuous (fun x => fieldEntropyGradient energy spin observable x v) :=
  ((continuous_fieldMean energy spin observable).const_mul 2).mul
    (continuous_normalizedFieldCovariance_entropy energy spin observable v hspin hneg hpos)

theorem continuous_fieldEntropyHessianDiagonal (energy : S → ℝ) (spin : S → V → ℝ)
    (observable : S → ℝ) (v : V)
    (hspin : ∀ s, observable s = -1 ∨ observable s = 1)
    (hneg : ∃ s, observable s = -1) (hpos : ∃ s, observable s = 1) :
    Continuous (fun x => fieldEntropyHessianDiagonal energy spin observable x v) := by
  have hm := continuous_fieldMean energy spin observable
  have hc := continuous_normalizedFieldCovariance_entropy energy spin observable v hspin hneg hpos
  exact (((continuous_const.add (hm.pow 2)).const_mul 2).mul (hc.pow 2)).sub
    ((((hm.const_mul 4).mul (continuous_fieldMean energy spin (fun s => spin s v))).mul hc))

theorem abs_fieldEntropyGradient_le (energy : S → ℝ) (spin : S → V → ℝ)
    (observable : S → ℝ) (x : V → ℝ) (v : V)
    (hspin : ∀ s, observable s = -1 ∨ observable s = 1)
    (hneg : ∃ s, observable s = -1) (hpos : ∃ s, observable s = 1)
    (hsignal : ∀ s, |spin s v| ≤ 1) :
    |fieldEntropyGradient energy spin observable x v| ≤ 2 := by
  have hm := abs_fieldMean_le energy spin observable x 1
    (fun s => (abs_spin_eq_one observable hspin s).le)
  have hc := abs_normalizedFieldCovariance_le_one_entropy energy spin observable x v
    hspin hneg hpos hsignal
  unfold fieldEntropyGradient
  rw [abs_mul, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
  calc
    2 * |fieldMean energy spin observable x| * |normalizedFieldCovariance energy spin observable x v|
        ≤ 2 * 1 * 1 := by gcongr
    _ = 2 := by ring

theorem abs_fieldEntropyHessianDiagonal_le (energy : S → ℝ) (spin : S → V → ℝ)
    (observable : S → ℝ) (x : V → ℝ) (v : V)
    (hspin : ∀ s, observable s = -1 ∨ observable s = 1)
    (hneg : ∃ s, observable s = -1) (hpos : ∃ s, observable s = 1)
    (hsignal : ∀ s, |spin s v| ≤ 1) :
    |fieldEntropyHessianDiagonal energy spin observable x v| ≤ 8 := by
  have hm := abs_fieldMean_le energy spin observable x 1
    (fun s => (abs_spin_eq_one observable hspin s).le)
  have hn := abs_fieldMean_le energy spin (fun s => spin s v) x 1 hsignal
  have hc := abs_normalizedFieldCovariance_le_one_entropy energy spin observable x v
    hspin hneg hpos hsignal
  have hm2 : fieldMean energy spin observable x ^ 2 ≤ 1 := by
    exact (sq_le_one_iff_abs_le_one _).mpr hm
  have hc2 : normalizedFieldCovariance energy spin observable x v ^ 2 ≤ 1 := by
    exact (sq_le_one_iff_abs_le_one _).mpr hc
  unfold fieldEntropyHessianDiagonal
  calc
    _ ≤ |2 * (1 + fieldMean energy spin observable x ^ 2) *
        normalizedFieldCovariance energy spin observable x v ^ 2| +
        |4 * fieldMean energy spin observable x * fieldMean energy spin (fun s => spin s v) x *
          normalizedFieldCovariance energy spin observable x v| := by simpa only [sub_eq_add_neg, abs_neg] using abs_add_le (2 * (1 + fieldMean energy spin observable x ^ 2) * normalizedFieldCovariance energy spin observable x v ^ 2) (-(4 * fieldMean energy spin observable x * fieldMean energy spin (fun s => spin s v) x * normalizedFieldCovariance energy spin observable x v))
    _ ≤ 2 * (1 + 1) * 1 + 4 * 1 * 1 * 1 := by
      rw [abs_of_nonneg (by positivity : 0 ≤ 2 * (1 + fieldMean energy spin observable x ^ 2) *
        normalizedFieldCovariance energy spin observable x v ^ 2)]
      simp only [abs_mul]
      rw [abs_of_pos (by norm_num : (0 : ℝ) < 4)]
      gcongr
    _ = 8 := by ring

section

variable [DecidableEq V]

omit [Nonempty S] in
lemma normalizedFieldCovariance_coordinate_tilt_entropy (energy : S → ℝ)
    (spin : S → V → ℝ) (observable : S → ℝ) (x : V → ℝ) (v : V) (t : ℝ) :
    normalizedFieldCovariance energy spin observable (fun u => x u + if u = v then t else 0) v =
      tiltResponse (fieldEnergy energy spin x) (fun s => spin s v) observable t := by
  simp only [normalizedFieldCovariance, fieldCovariance_coordinate_tilt,
    fieldMean_coordinate_tilt, tiltResponse]

theorem hasDerivAt_fieldEntropyGradient_coordinate (energy : S → ℝ)
    (spin : S → V → ℝ) (observable : S → ℝ) (x : V → ℝ) (v : V) (t : ℝ)
    (hcoord : ∀ s, spin s v = -1 ∨ spin s v = 1)
    (hspin : ∀ s, observable s = -1 ∨ observable s = 1)
    (hneg : ∃ s, observable s = -1) (hpos : ∃ s, observable s = 1) :
    HasDerivAt (fun r => fieldEntropyGradient energy spin observable
        (fun u => x u + if u = v then r else 0) v)
      (fieldEntropyHessianDiagonal energy spin observable
        (fun u => x u + if u = v then t else 0) v) t := by
  have hd := ((hasDerivAt_mean_covariance (fieldEnergy energy spin x)
    (fun s => spin s v) observable t).const_mul 2).mul
      (hasDerivAt_tiltResponse (fieldEnergy energy spin x) (fun s => spin s v)
        observable t hcoord hspin hneg hpos)
  simp only [fieldEntropyGradient, fieldEntropyHessianDiagonal,
    fieldMean_coordinate_tilt, normalizedFieldCovariance_coordinate_tilt_entropy]
  change HasDerivAt (fun r => 2 * mean (fieldEnergy energy spin x)
    (fun s => spin s v) observable r *
      tiltResponse (fieldEnergy energy spin x) (fun s => spin s v) observable r) _ t at hd
  apply hd.congr_deriv
  have hden := (spin_mean_variance_pos (fieldEnergy energy spin x)
    (fun s => spin s v) observable t hspin hneg hpos).ne'
  unfold tiltResponse
  field_simp [hden]
  ring

theorem hasDerivAt_fieldEntropyGradient_update (energy : S → ℝ)
    (spin : S → V → ℝ) (observable : S → ℝ) (x : V → ℝ) (v : V) (t : ℝ)
    (hcoord : ∀ s, spin s v = -1 ∨ spin s v = 1)
    (hspin : ∀ s, observable s = -1 ∨ observable s = 1)
    (hneg : ∃ s, observable s = -1) (hpos : ∃ s, observable s = 1) :
    HasDerivAt (fun r => fieldEntropyGradient energy spin observable (Function.update x v r) v)
      (fieldEntropyHessianDiagonal energy spin observable (Function.update x v t) v) t := by
  simpa only [← update_eq_zero_shift] using
    hasDerivAt_fieldEntropyGradient_coordinate energy spin observable
      (Function.update x v 0) v t hcoord hspin hneg hpos

end

theorem fieldEntropy_eq_log_cosh (energy : S → ℝ) (spin : S → V → ℝ)
    (observable : S → ℝ) (x : V → ℝ)
    (hspin : ∀ s, observable s = -1 ∨ observable s = 1)
    (hneg : ∃ s, observable s = -1) (hpos : ∃ s, observable s = 1) :
    fieldEntropy energy spin observable x =
      2 * Real.log (Real.cosh (fieldField energy spin observable x)) := by
  have hm := fieldMean_spin_mem_Ioo energy spin observable x hspin hneg hpos
  have hden := fieldVariance_pos_entropy energy spin observable x hspin hneg hpos
  unfold fieldEntropy fieldField
  rw [Real.cosh_artanh hm, Real.log_div one_ne_zero (Real.sqrt_ne_zero'.mpr hden),
    Real.log_one, Real.log_sqrt hden.le]
  ring

theorem fieldEntropy_nonneg (energy : S → ℝ) (spin : S → V → ℝ)
    (observable : S → ℝ) (x : V → ℝ)
    (hspin : ∀ s, observable s = -1 ∨ observable s = 1)
    (hneg : ∃ s, observable s = -1) (hpos : ∃ s, observable s = 1) :
    0 ≤ fieldEntropy energy spin observable x := by
  apply neg_nonneg.mpr
  exact Real.log_nonpos
    (fieldVariance_pos_entropy energy spin observable x hspin hneg hpos).le
    (sub_le_self _ (sq_nonneg _))

theorem fieldEntropy_le_abs_field (energy : S → ℝ) (spin : S → V → ℝ)
    (observable : S → ℝ) (x : V → ℝ)
    (hspin : ∀ s, observable s = -1 ∨ observable s = 1)
    (hneg : ∃ s, observable s = -1) (hpos : ∃ s, observable s = 1) :
    fieldEntropy energy spin observable x ≤ 2 * |fieldField energy spin observable x| := by
  rw [fieldEntropy_eq_log_cosh energy spin observable x hspin hneg hpos]
  have hcosh (z : ℝ) : Real.cosh z ≤ Real.exp |z| := by
    rw [Real.cosh_eq]
    have hp := Real.exp_le_exp.mpr (le_abs_self z)
    have hn := Real.exp_le_exp.mpr (neg_le_abs z)
    linarith
  have hlog := Real.log_le_log (Real.cosh_pos (fieldField energy spin observable x))
    (hcosh (fieldField energy spin observable x))
  rw [Real.log_exp] at hlog
  linarith

theorem norm_fderiv_fieldEntropy_le (energy : S → ℝ) (spin : S → V → ℝ)
    (observable : S → ℝ) (x : V → ℝ)
    (hspin : ∀ s, observable s = -1 ∨ observable s = 1)
    (hneg : ∃ s, observable s = -1) (hpos : ∃ s, observable s = 1)
    (hsignal : ∀ s v, |spin s v| ≤ 1) :
    ‖fderiv ℝ (fieldEntropy energy spin observable) x‖ ≤ (Fintype.card V : ℝ) * 2 := by
  rw [(hasFDerivAt_fieldEntropy energy spin observable x hspin hneg hpos).fderiv]
  apply ContinuousLinearMap.opNorm_le_bound _ (by positivity)
  intro y
  simp only [sum_apply, smul_apply, ContinuousLinearMap.proj_apply, smul_eq_mul]
  calc
    ‖∑ v, fieldEntropyGradient energy spin observable x v * y v‖ ≤
        ∑ v, ‖fieldEntropyGradient energy spin observable x v * y v‖ := norm_sum_le _ _
    _ ≤ ∑ _v : V, 2 * ‖y‖ := by
      apply Finset.sum_le_sum
      intro v _
      rw [norm_mul, Real.norm_eq_abs (fieldEntropyGradient energy spin observable x v)]
      exact mul_le_mul
        (abs_fieldEntropyGradient_le energy spin observable x v hspin hneg hpos (fun s => hsignal s v))
        (norm_le_pi_norm y v) (norm_nonneg _) (by norm_num)
    _ = _ := by simp [Finset.sum_const, nsmul_eq_mul, mul_assoc]

theorem lipschitzWith_fieldEntropy (energy : S → ℝ) (spin : S → V → ℝ)
    (observable : S → ℝ)
    (hspin : ∀ s, observable s = -1 ∨ observable s = 1)
    (hneg : ∃ s, observable s = -1) (hpos : ∃ s, observable s = 1)
    (hsignal : ∀ s v, |spin s v| ≤ 1) :
    LipschitzWith ((Fintype.card V : ℝ≥0) * 2) (fieldEntropy energy spin observable) := by
  apply lipschitzWith_of_nnnorm_fderiv_le
    (fun x => (hasFDerivAt_fieldEntropy energy spin observable x hspin hneg hpos).differentiableAt)
  intro x
  exact_mod_cast norm_fderiv_fieldEntropy_le energy spin observable x hspin hneg hpos hsignal

open MeasureTheory

theorem integrable_fieldEntropy_comp {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsFiniteMeasure μ] (energy : S → ℝ) (spin : S → V → ℝ)
    (observable : S → ℝ)
    (hspin : ∀ s, observable s = -1 ∨ observable s = 1)
    (hneg : ∃ s, observable s = -1) (hpos : ∃ s, observable s = 1)
    (hsignal : ∀ s v, |spin s v| ≤ 1) {X : Ω → V → ℝ} (hX : Integrable X μ) :
    Integrable (fun ω => fieldEntropy energy spin observable (X ω)) μ := by
  have hL := lipschitzWith_fieldEntropy energy spin observable hspin hneg hpos hsignal
  have hdom := (hX.norm.const_mul ((Fintype.card V : ℝ) * 2)).add
    (integrable_const ‖fieldEntropy energy spin observable 0‖ : Integrable
      (fun _ : Ω => ‖fieldEntropy energy spin observable 0‖) μ)
  apply hdom.mono' (hL.continuous.comp_aestronglyMeasurable hX.aestronglyMeasurable)
  filter_upwards [] with ω
  have hb := hL.norm_sub_le (X ω) 0
  simp only [sub_zero, NNReal.coe_mul, NNReal.coe_natCast, NNReal.coe_ofNat] at hb
  calc
    ‖fieldEntropy energy spin observable (X ω)‖ ≤
        ‖fieldEntropy energy spin observable (X ω) - fieldEntropy energy spin observable 0‖ +
          ‖fieldEntropy energy spin observable 0‖ := norm_le_norm_sub_add _ _
    _ ≤ _ := add_le_add hb le_rfl

end Problem367.FinitePosterior

end

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Conditioning_FiniteFieldEntropyExpectation
attribute [-instance] _root_.OAI.Problem367.WienerSampler.pathMeasurableSpace _root_.OAI.Problem367.reducedTailFinite _root_.OAI.Problem367.treeBallFinite _root_.OAI.Problem367.treeShellFinite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory
open scoped NNReal

namespace Problem367.FinitePosterior

variable {S V : Type*} [Fintype S] [Nonempty S] [Fintype V] [DecidableEq V]

theorem integral_fieldEntropyGradient_mul_noise
    (energy : S → ℝ) (spin : S → V → ℝ) (observable : S → ℝ)
    (hspin : ∀ s, observable s = -1 ∨ observable s = 1)
    (hneg : ∃ s, observable s = -1) (hpos : ∃ s, observable s = 1)
    (hcoords : ∀ s v, spin s v = -1 ∨ spin s v = 1)
    (signal : V → ℝ) (t : ℝ) (v : V) :
    (∫ z, fieldEntropyGradient energy spin observable
      (gaussianObservationCurve signal z t) v * z v
      ∂Measure.pi (fun _ : V => gaussianReal 0 1)) =
    Real.sqrt t * ∫ z, fieldEntropyHessianDiagonal energy spin observable
      (gaussianObservationCurve signal z t) v
      ∂Measure.pi (fun _ : V => gaussianReal 0 1) := by
  have h := Problem367.gaussian_pi_integral_mul_affine_of_bounded_deriv
    (fun j => t * signal j) (fun _ => Real.sqrt t) v
    (continuous_fieldEntropyGradient energy spin observable v hspin hneg hpos)
    (continuous_fieldEntropyHessianDiagonal energy spin observable v hspin hneg hpos)
    (fun z r => hasDerivAt_fieldEntropyGradient_update energy spin observable z v r
      (fun s => hcoords s v) hspin hneg hpos)
    (fun z => abs_fieldEntropyGradient_le energy spin observable z v hspin hneg hpos
      (fun s => (abs_spin_eq_one (fun s => spin s v) (fun s => hcoords s v) s).le))
    (fun z => abs_fieldEntropyHessianDiagonal_le energy spin observable z v hspin hneg hpos
      (fun s => (abs_spin_eq_one (fun s => spin s v) (fun s => hcoords s v) s).le))
  simpa only [gaussianObservationCurve, Pi.add_def, Pi.smul_def, smul_eq_mul,
    mul_comm] using h

section Planted

variable [MeasurableSpace S] [MeasurableSingletonClass S]

omit [DecidableEq V] in
private theorem integrable_bounded_entropy_test
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsFiniteMeasure μ]
    (X : Ω → V → ℝ) (hX : Measurable X) (f : (V → ℝ) → ℝ)
    (hf : Continuous f) (C : ℝ) (hbound : ∀ z, |f z| ≤ C) :
    Integrable (fun x => f (X x)) μ := by
  apply Integrable.of_bound (hf.measurable.comp hX).aestronglyMeasurable C
  exact Filter.Eventually.of_forall fun x => by
    simpa only [Real.norm_eq_abs, Function.comp_def] using hbound (X x)

omit [DecidableEq V] in
theorem integrable_finiteStandardEntropyGradient (μ : Measure S) [IsFiniteMeasure μ]
    (energy : S → ℝ) (spin : S → V → ℝ) (observable : S → ℝ)
    (hspin : ∀ s, observable s = -1 ∨ observable s = 1)
    (hneg : ∃ s, observable s = -1) (hpos : ∃ s, observable s = 1)
    (hcoords : ∀ s v, spin s v = -1 ∨ spin s v = 1) (t : ℝ) (v : V) :
    Integrable (fun x => fieldEntropyGradient energy spin observable
      (finiteStandardObservation spin t x) v)
      (μ.prod (Measure.pi (fun _ : V => gaussianReal 0 1))) :=
  integrable_bounded_entropy_test _ _ (measurable_finiteStandardObservation spin t) _
    (continuous_fieldEntropyGradient energy spin observable v hspin hneg hpos) 2
    (fun z => abs_fieldEntropyGradient_le energy spin observable z v hspin hneg hpos
      (fun s => (abs_spin_eq_one (fun s => spin s v) (fun s => hcoords s v) s).le))

omit [DecidableEq V] in
theorem integrable_finiteStandardEntropyHessian (μ : Measure S) [IsFiniteMeasure μ]
    (energy : S → ℝ) (spin : S → V → ℝ) (observable : S → ℝ)
    (hspin : ∀ s, observable s = -1 ∨ observable s = 1)
    (hneg : ∃ s, observable s = -1) (hpos : ∃ s, observable s = 1)
    (hcoords : ∀ s v, spin s v = -1 ∨ spin s v = 1) (t : ℝ) (v : V) :
    Integrable (fun x => fieldEntropyHessianDiagonal energy spin observable
      (finiteStandardObservation spin t x) v)
      (μ.prod (Measure.pi (fun _ : V => gaussianReal 0 1))) :=
  integrable_bounded_entropy_test _ _ (measurable_finiteStandardObservation spin t) _
    (continuous_fieldEntropyHessianDiagonal energy spin observable v hspin hneg hpos) 8
    (fun z => abs_fieldEntropyHessianDiagonal_le energy spin observable z v hspin hneg hpos
      (fun s => (abs_spin_eq_one (fun s => spin s v) (fun s => hcoords s v) s).le))

omit [DecidableEq V] in
theorem integrable_finiteStandardEntropyGradient_mul_noise
    (μ : Measure S) [IsFiniteMeasure μ]
    (energy : S → ℝ) (spin : S → V → ℝ) (observable : S → ℝ)
    (hspin : ∀ s, observable s = -1 ∨ observable s = 1)
    (hneg : ∃ s, observable s = -1) (hpos : ∃ s, observable s = 1)
    (hcoords : ∀ s v, spin s v = -1 ∨ spin s v = 1) (t : ℝ) (v : V) :
    Integrable (fun x => fieldEntropyGradient energy spin observable
      (finiteStandardObservation spin t x) v * x.2 v)
      (μ.prod (Measure.pi (fun _ : V => gaussianReal 0 1))) := by
  have hg := integrable_finiteStandardEntropyGradient μ energy spin observable hspin hneg hpos hcoords t v
  have h := (integrable_finiteStandardNoise μ v).mul_bdd hg.aestronglyMeasurable
    (Filter.Eventually.of_forall fun x => by
      simpa only [Real.norm_eq_abs, Function.comp_def] using abs_fieldEntropyGradient_le energy spin observable
        (finiteStandardObservation spin t x) v hspin hneg hpos
        (fun s => (abs_spin_eq_one (fun s => spin s v) (fun s => hcoords s v) s).le))
  simpa only [mul_comm] using h

theorem integral_finiteStandardEntropyGradient_mul_noise
    (μ : Measure S) [IsFiniteMeasure μ]
    (energy : S → ℝ) (spin : S → V → ℝ) (observable : S → ℝ)
    (hspin : ∀ s, observable s = -1 ∨ observable s = 1)
    (hneg : ∃ s, observable s = -1) (hpos : ∃ s, observable s = 1)
    (hcoords : ∀ s v, spin s v = -1 ∨ spin s v = 1) (t : ℝ) (v : V) :
    (∫ x, fieldEntropyGradient energy spin observable
      (finiteStandardObservation spin t x) v * x.2 v
      ∂μ.prod (Measure.pi (fun _ : V => gaussianReal 0 1))) =
    Real.sqrt t * ∫ x, fieldEntropyHessianDiagonal energy spin observable
      (finiteStandardObservation spin t x) v
      ∂μ.prod (Measure.pi (fun _ : V => gaussianReal 0 1)) := by
  rw [integral_prod _ (integrable_finiteStandardEntropyGradient_mul_noise
    μ energy spin observable hspin hneg hpos hcoords t v),
    integral_prod _ (integrable_finiteStandardEntropyHessian
    μ energy spin observable hspin hneg hpos hcoords t v), ← integral_const_mul]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall fun s =>
    integral_fieldEntropyGradient_mul_noise energy spin observable hspin hneg hpos hcoords (spin s) t v

theorem integral_finiteStandardEntropyVelocity [StandardBorelSpace S]
    (μ : Measure S) [IsProbabilityMeasure μ] (energy : S → ℝ)
    (hprior : ∀ s, μ.real {s} = Real.exp (energy s) / ∑ a, Real.exp (energy a))
    (spin : S → V → ℝ) (observable : S → ℝ)
    (hspin : ∀ s, observable s = -1 ∨ observable s = 1)
    (hneg : ∃ s, observable s = -1) (hpos : ∃ s, observable s = 1)
    (hcoords : ∀ s v, spin s v = -1 ∨ spin s v = 1)
    {t : ℝ} (ht : 0 < t) :
    (∫ x, ∑ v, fieldEntropyGradient energy spin observable
      (finiteStandardObservation spin t x) v *
        gaussianObservationVelocity (spin x.1) x.2 t v
      ∂μ.prod (Measure.pi (fun _ : V => gaussianReal 0 1))) =
    ∫ x, (1 + fieldMean energy spin observable (finiteStandardObservation spin t x) ^ 2) *
        ∑ v, normalizedFieldCovariance energy spin observable
          (finiteStandardObservation spin t x) v ^ 2
      ∂μ.prod (Measure.pi (fun _ : V => gaussianReal 0 1)) := by
  have hposterior (v : V) :
      (∫ x, fieldEntropyGradient energy spin observable
        (finiteStandardObservation spin t x) v * spin x.1 v
        ∂μ.prod (Measure.pi (fun _ : V => gaussianReal 0 1))) =
      ∫ x, fieldEntropyGradient energy spin observable
        (finiteStandardObservation spin t x) v *
          fieldMean energy spin (fun s => spin s v) (finiteStandardObservation spin t x)
        ∂μ.prod (Measure.pi (fun _ : V => gaussianReal 0 1)) := by
    have hsq : ∀ s i, spin s i ^ 2 = 1 := by
      intro s i
      rcases hcoords s i with h | h <;> simp [h]
    have htest (z : V → ℝ) : ‖fieldEntropyGradient energy spin observable z v‖ ≤ 2 := by
      rw [Real.norm_eq_abs]
      exact abs_fieldEntropyGradient_le energy spin observable z v hspin hneg hpos
        (fun s => (abs_spin_eq_one (fun s => spin s v) (fun s => hcoords s v) s).le)
    exact Problem367.finiteStandardGaussianPlanted_integral_test_fieldMean μ energy hprior t ht.le
      spin hsq (fun s => spin s v) (fun z => fieldEntropyGradient energy spin observable z v)
      (continuous_fieldEntropyGradient energy spin observable v hspin hneg hpos).measurable 2 htest
  let ρ := μ.prod (Measure.pi (fun _ : V => gaussianReal 0 1))
  let Y := finiteStandardObservation spin t
  let g := fun x v => fieldEntropyGradient energy spin observable (Y x) v
  let H := fun x v => fieldEntropyHessianDiagonal energy spin observable (Y x) v
  let p := fun x v => fieldMean energy spin (fun s => spin s v) (Y x)
  let c := 1 / (2 * Real.sqrt t)
  have hy : Measurable Y := measurable_finiteStandardObservation spin t
  have hg (v : V) : Integrable (fun x => g x v) ρ :=
    integrable_finiteStandardEntropyGradient μ energy spin observable hspin hneg hpos hcoords t v
  have hH (v : V) : Integrable (fun x => H x v) ρ :=
    integrable_finiteStandardEntropyHessian μ energy spin observable hspin hneg hpos hcoords t v
  have hn (v : V) : Integrable (fun x => g x v * x.2 v) ρ :=
    integrable_finiteStandardEntropyGradient_mul_noise μ energy spin observable hspin hneg hpos hcoords t v
  have hs (v : V) : Integrable (fun x => g x v * spin x.1 v) ρ := by
    apply (hg v).mul_bdd
      (((measurable_of_finite (fun s => spin s v)).comp measurable_fst).aestronglyMeasurable)
    exact Filter.Eventually.of_forall fun x => by
      simpa only [Real.norm_eq_abs, Function.comp_def] using
        (abs_spin_eq_one (fun s => spin s v) (fun s => hcoords s v) x.1).le
  have hp (v : V) : Integrable (fun x => g x v * p x v) ρ := by
    apply (hg v).mul_bdd
      (((continuous_fieldMean energy spin (fun s => spin s v)).measurable.comp hy).aestronglyMeasurable)
    exact Filter.Eventually.of_forall fun x => by
      simpa only [Real.norm_eq_abs, Function.comp_def] using abs_fieldMean_le energy spin (fun s => spin s v)
        (Y x) 1 (fun s => (abs_spin_eq_one (fun s => spin s v) (fun s => hcoords s v) s).le)
  have hvEq (v : V) :
      (fun x : S × (V → ℝ) => g x v * gaussianObservationVelocity (spin x.1) x.2 t v) =
        (fun x => g x v * spin x.1 v + c * (g x v * x.2 v)) := by
    funext x
    change g x v * (spin x.1 v + c * x.2 v) = _
    ring
  have hv (v : V) : Integrable
      (fun x => g x v * gaussianObservationVelocity (spin x.1) x.2 t v) ρ := by
    rw [hvEq]
    exact (hs v).add ((hn v).const_mul c)
  have hcancel (x : S × (V → ℝ)) (v : V) :
      g x v * p x v + (1 / 2 : ℝ) * H x v =
        (1 + fieldMean energy spin observable (Y x) ^ 2) *
        normalizedFieldCovariance energy spin observable (Y x) v ^ 2 := by
    dsimp [g, H, p, fieldEntropyGradient, fieldEntropyHessianDiagonal]
    ring
  have hc (v : V) : Integrable
      (fun x => (1 + fieldMean energy spin observable (Y x) ^ 2) *
        normalizedFieldCovariance energy spin observable (Y x) v ^ 2) ρ := by
    exact ((hp v).add ((hH v).const_mul (1 / 2 : ℝ))).congr
      (Filter.Eventually.of_forall fun x => hcancel x v)
  have hstep (v : V) :
      (∫ x, g x v * gaussianObservationVelocity (spin x.1) x.2 t v ∂ρ) =
        ∫ x, (1 + fieldMean energy spin observable (Y x) ^ 2) *
        normalizedFieldCovariance energy spin observable (Y x) v ^ 2 ∂ρ := by
    rw [hvEq, integral_add (hs v) ((hn v).const_mul c), integral_const_mul]
    have hnoise : (∫ x, g x v * x.2 v ∂ρ) = Real.sqrt t * ∫ x, H x v ∂ρ :=
      integral_finiteStandardEntropyGradient_mul_noise μ energy spin observable hspin hneg hpos hcoords t v
    rw [hnoise]
    have hcoef : c * Real.sqrt t = (1 / 2 : ℝ) := by
      dsimp [c]
      field_simp [ne_of_gt (Real.sqrt_pos.mpr ht)]
    rw [← mul_assoc, hcoef, hposterior v]
    rw [← integral_const_mul, ← integral_add (hp v) ((hH v).const_mul (1 / 2 : ℝ))]
    exact integral_congr_ae (Filter.Eventually.of_forall fun x => hcancel x v)
  change (∫ x, ∑ v, g x v * gaussianObservationVelocity (spin x.1) x.2 t v ∂ρ) = _
  simp_rw [Finset.mul_sum]
  rw [integral_finsetSum _ (fun v _ => hv v), integral_finsetSum _ (fun v _ => hc v)]
  exact Finset.sum_congr rfl fun v _ => hstep v

omit [Nonempty S] [DecidableEq V] in
theorem integrable_finiteStandardSignal (μ : Measure S) [IsFiniteMeasure μ]
    (spin : S → V → ℝ) (hcoords : ∀ s v, spin s v = -1 ∨ spin s v = 1) :
    Integrable (fun x : S × (V → ℝ) => spin x.1)
      (μ.prod (Measure.pi (fun _ : V => gaussianReal 0 1))) := by
  apply Integrable.of_eval
  intro v
  apply Integrable.of_bound
    (((measurable_of_finite (fun s => spin s v)).comp measurable_fst).aestronglyMeasurable) 1
  exact Filter.Eventually.of_forall fun x => by
    simpa only [Real.norm_eq_abs, Function.comp_def] using
      (abs_spin_eq_one (fun s => spin s v) (fun s => hcoords s v) x.1).le

omit [Nonempty S] [DecidableEq V] in
theorem integrable_finiteStandardObservation (μ : Measure S) [IsFiniteMeasure μ]
    (spin : S → V → ℝ) (hcoords : ∀ s v, spin s v = -1 ∨ spin s v = 1) (t : ℝ) :
    Integrable (finiteStandardObservation spin t)
      (μ.prod (Measure.pi (fun _ : V => gaussianReal 0 1))) := by
  have hn : Integrable (Prod.snd : S × (V → ℝ) → (V → ℝ))
      (μ.prod (Measure.pi (fun _ : V => gaussianReal 0 1))) :=
    Integrable.of_eval (fun v => integrable_finiteStandardNoise μ v)
  exact ((integrable_finiteStandardSignal μ spin hcoords).smul t).add
    (hn.smul (Real.sqrt t))

omit [DecidableEq V] in
theorem integrable_finiteStandardEntropy (μ : Measure S) [IsFiniteMeasure μ]
    (energy : S → ℝ) (spin : S → V → ℝ) (observable : S → ℝ)
    (hspin : ∀ s, observable s = -1 ∨ observable s = 1)
    (hneg : ∃ s, observable s = -1) (hpos : ∃ s, observable s = 1)
    (hcoords : ∀ s v, spin s v = -1 ∨ spin s v = 1) (t : ℝ) :
    Integrable (fun x => fieldEntropy energy spin observable (finiteStandardObservation spin t x))
      (μ.prod (Measure.pi (fun _ : V => gaussianReal 0 1))) :=
  integrable_fieldEntropy_comp _ energy spin observable hspin hneg hpos
    (fun s v => (abs_spin_eq_one (fun s => spin s v) (fun s => hcoords s v) s).le)
    (integrable_finiteStandardObservation μ spin hcoords t)

end Planted

omit [DecidableEq V] in
theorem continuous_normalizedRowEnergy (energy : S → ℝ) (spin : S → V → ℝ)
    (observable : S → ℝ)
    (hspin : ∀ s, observable s = -1 ∨ observable s = 1)
    (hneg : ∃ s, observable s = -1) (hpos : ∃ s, observable s = 1) :
    Continuous (fun x => ∑ v, normalizedFieldCovariance energy spin observable x v ^ 2) := by
  apply continuous_finsetSum
  intro v _
  exact (continuous_normalizedFieldCovariance_entropy energy spin observable v hspin hneg hpos).pow 2

omit [DecidableEq V] in
theorem abs_normalizedRowEnergy_le_card (energy : S → ℝ) (spin : S → V → ℝ)
    (observable : S → ℝ) (x : V → ℝ)
    (hspin : ∀ s, observable s = -1 ∨ observable s = 1)
    (hneg : ∃ s, observable s = -1) (hpos : ∃ s, observable s = 1)
    (hsignal : ∀ s v, |spin s v| ≤ 1) :
    |∑ v, normalizedFieldCovariance energy spin observable x v ^ 2| ≤ Fintype.card V := by
  rw [abs_of_nonneg (Finset.sum_nonneg (fun v _ => sq_nonneg _))]
  calc
    (∑ v, normalizedFieldCovariance energy spin observable x v ^ 2) ≤ ∑ _v : V, (1 : ℝ) := by
      apply Finset.sum_le_sum
      intro v _
      exact (sq_le_one_iff_abs_le_one _).mpr
        (abs_normalizedFieldCovariance_le_one_entropy energy spin observable x v
          hspin hneg hpos (fun s => hsignal s v))
    _ = _ := by simp

end Problem367.FinitePosterior

end

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Posterior_LipschitzObservationDerivative
attribute [-instance] _root_.OAI.Problem367.WienerSampler.pathMeasurableSpace _root_.OAI.Problem367.reducedTailFinite _root_.OAI.Problem367.treeBallFinite _root_.OAI.Problem367.treeShellFinite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory Filter Set
open scoped Topology BigOperators NNReal

namespace Problem367

theorem hasDerivAt_integral_sqrt_observation_vector_of_integrable
    {Ω E : Type*} [MeasurableSpace Ω] [NormedAddCommGroup E] [NormedSpace ℝ E]
    {P : Measure Ω} [IsFiniteMeasure P]
    {S G : Ω → E} (hS : Integrable S P) (hG : Integrable G P)
    {f : E → ℝ} {f' : E → E →L[ℝ] ℝ}
    (hf : ∀ x, HasFDerivAt f (f' x) x) (hf'cont : Continuous f')
    {M : ℝ} (hM : 0 ≤ M)
    (hf'bound : ∀ x, ‖f' x‖ ≤ M) {t : ℝ} (ht : 0 < t)
    (hFint : Integrable (fun ω => f (t • S ω + Real.sqrt t • G ω)) P) :
    Integrable (fun ω => f' (t • S ω + Real.sqrt t • G ω)
      (S ω + (1 / (2 * Real.sqrt t)) • G ω)) P ∧
    HasDerivAt (fun r : ℝ => ∫ ω, f (r • S ω + Real.sqrt r • G ω) ∂P)
      (∫ ω, f' (t • S ω + Real.sqrt t • G ω)
        (S ω + (1 / (2 * Real.sqrt t)) • G ω) ∂P) t := by
  have hfcont : Continuous f := continuous_iff_continuousAt.mpr
    (fun x => (hf x).continuousAt)
  let F : ℝ → Ω → ℝ := fun r ω => f (r • S ω + Real.sqrt r • G ω)
  let F' : ℝ → Ω → ℝ := fun r ω => f' (r • S ω + Real.sqrt r • G ω)
    (S ω + (1 / (2 * Real.sqrt r)) • G ω)
  let a : ℝ := 1 / (2 * Real.sqrt (t / 2))
  have ha : 0 ≤ a := by dsimp [a] <;> positivity
  have hargm (r : ℝ) : AEStronglyMeasurable
      (fun ω => r • S ω + Real.sqrt r • G ω) P :=
    (hS.aestronglyMeasurable.const_smul r).add
      (hG.aestronglyMeasurable.const_smul (Real.sqrt r))
  have hFm (r : ℝ) : AEStronglyMeasurable (F r) P :=
    hfcont.comp_aestronglyMeasurable (hargm r)
  have hF'm (r : ℝ) : AEStronglyMeasurable (F' r) P :=
    (isBoundedBilinearMap_apply (𝕜 := ℝ) (E := E) (F := ℝ)).continuous
      |>.comp_aestronglyMeasurable
        ((hf'cont.comp_aestronglyMeasurable (hargm r)).prodMk
          (hS.aestronglyMeasurable.add
            (hG.aestronglyMeasurable.const_smul (1 / (2 * Real.sqrt r)))))
  have hdom : Integrable (fun ω => M * (‖S ω‖ + a * ‖G ω‖)) P :=
    (hS.norm.add (hG.norm.const_mul a)).const_mul M
  have hbound : ∀ᵐ ω ∂P, ∀ r ∈ Ioi (t / 2),
      ‖F' r ω‖ ≤ M * (‖S ω‖ + a * ‖G ω‖) := by
    filter_upwards [] with ω
    intro r hr
    have hrpos : 0 < r := lt_trans (by linarith) hr
    have hden : 0 < 2 * Real.sqrt (t / 2) := by positivity
    have hrecip : 1 / (2 * Real.sqrt r) ≤ a := by
      apply one_div_le_one_div_of_le hden
      exact mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt hr.le) (by norm_num)
    have hinner : ‖S ω + (1 / (2 * Real.sqrt r)) • G ω‖ ≤
        ‖S ω‖ + a * ‖G ω‖ := by
      calc
        _ ≤ ‖S ω‖ + ‖(1 / (2 * Real.sqrt r)) • G ω‖ := norm_add_le _ _
        _ = ‖S ω‖ + (1 / (2 * Real.sqrt r)) * ‖G ω‖ := by
          rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
        _ ≤ ‖S ω‖ + a * ‖G ω‖ := by gcongr
    exact ((f' (r • S ω + Real.sqrt r • G ω)).le_opNorm _).trans
      (mul_le_mul (hf'bound _) hinner (norm_nonneg _) hM)
  have hdiff : ∀ᵐ ω ∂P, ∀ r ∈ Ioi (t / 2),
      HasDerivAt (fun q => F q ω) (F' r ω) r := by
    filter_upwards [] with ω
    intro r hr
    have hrpos : 0 < r := lt_trans (by linarith) hr
    have harg := ((hasDerivAt_id r).smul_const (S ω)).add
      ((Real.hasDerivAt_sqrt hrpos.ne').smul_const (G ω))
    have harg' : HasDerivAt (fun q : ℝ => q • S ω + Real.sqrt q • G ω)
        (S ω + (1 / (2 * Real.sqrt r)) • G ω) r := by
      simpa only [Pi.add_def, id_eq, one_smul, one_div] using harg
    exact (hf (r • S ω + Real.sqrt r • G ω)).comp_hasDerivAt r harg'
  exact hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (Ioi_mem_nhds (by linarith : t / 2 < t))
    (Eventually.of_forall hFm) hFint (hF'm t) hbound hdom hdiff

theorem continuous_integral_sqrt_observation_lipschitz
    {Ω E : Type*} [MeasurableSpace Ω] [NormedAddCommGroup E] [NormedSpace ℝ E]
    {P : Measure Ω} [IsFiniteMeasure P] {S G : Ω → E}
    (hS : Integrable S P) (hG : Integrable G P)
    {f : E → ℝ} {K : ℝ≥0} (hf : LipschitzWith K f) :
    Continuous (fun t : ℝ => ∫ ω, f (t • S ω + Real.sqrt t • G ω) ∂P) := by
  apply continuous_iff_continuousAt.mpr
  intro t
  let a : ℝ := |t| + 1
  have ha : 0 ≤ a := by dsimp [a] <;> positivity
  have hloc : ∀ᶠ r in 𝓝 t, |r| < a :=
    continuous_abs.continuousAt.eventually
      (gt_mem_nhds (by dsimp [a]; linarith : |t| < a))
  apply continuousAt_of_dominated
    (bound := fun ω => ‖f 0‖ + (K : ℝ) *
      (a * ‖S ω‖ + Real.sqrt a * ‖G ω‖))
  · exact Eventually.of_forall fun r => hf.continuous.comp_aestronglyMeasurable
      ((hS.aestronglyMeasurable.const_smul r).add
        (hG.aestronglyMeasurable.const_smul (Real.sqrt r)))
  · filter_upwards [hloc] with r hr
    exact Eventually.of_forall fun ω => by
      have harg : ‖r • S ω + Real.sqrt r • G ω‖ ≤
          a * ‖S ω‖ + Real.sqrt a * ‖G ω‖ := by
        calc
          _ ≤ ‖r • S ω‖ + ‖Real.sqrt r • G ω‖ := norm_add_le _ _
          _ = |r| * ‖S ω‖ + Real.sqrt r * ‖G ω‖ := by
            rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs,
              abs_of_nonneg (Real.sqrt_nonneg r)]
          _ ≤ _ := add_le_add
            (mul_le_mul_of_nonneg_right hr.le (norm_nonneg _))
            (mul_le_mul_of_nonneg_right
              (Real.sqrt_le_sqrt ((le_abs_self r).trans hr.le)) (norm_nonneg _))
      calc
        _ ≤ ‖f 0‖ + ‖f (r • S ω + Real.sqrt r • G ω) - f 0‖ :=
          norm_le_norm_add_norm_sub' _ _
        _ ≤ ‖f 0‖ + (K : ℝ) * ‖r • S ω + Real.sqrt r • G ω‖ := by
          gcongr
          simpa only [sub_zero] using hf.norm_sub_le
            (r • S ω + Real.sqrt r • G ω) 0
        _ ≤ _ := add_le_add le_rfl (mul_le_mul_of_nonneg_left harg K.coe_nonneg)
  · exact (integrable_const ‖f 0‖).add
      (((hS.norm.const_mul a).add (hG.norm.const_mul (Real.sqrt a))).const_mul (K : ℝ))
  · exact Eventually.of_forall fun ω => (hf.continuous.comp
      ((continuous_id.smul continuous_const).add
        (Real.continuous_sqrt.smul continuous_const))).continuousAt

namespace FinitePosterior

variable {V Ω : Type*} [Fintype V] [MeasurableSpace Ω]

theorem hasDerivAt_integral_gaussianObservationCurve_of_integrable
    (μ : Measure Ω) [IsFiniteMeasure μ]
    (f : (V → ℝ) → ℝ) (g : (V → ℝ) → V → ℝ)
    (hdf : ∀ x, HasFDerivAt f (∑ v, g x v •
      (ContinuousLinearMap.proj v : (V → ℝ) →L[ℝ] ℝ)) x)
    (hg : ∀ v, Continuous (fun x => g x v))
    (C : ℝ) (hC : 0 ≤ C) (hgbound : ∀ x v, |g x v| ≤ C)
    (signal noise : Ω → V → ℝ)
    (hsignal : Measurable signal) (hnoise : Measurable noise)
    (hspin : ∀ ω v, |signal ω v| ≤ 1)
    (hnoiseInt : ∀ v, Integrable (fun ω => noise ω v) μ)
    {t : ℝ} (ht : 0 < t)
    (hFint : Integrable (fun ω =>
      f (gaussianObservationCurve (signal ω) (noise ω) t)) μ) :
    HasDerivAt (fun r => ∫ ω, f (gaussianObservationCurve (signal ω) (noise ω) r) ∂μ)
      (∫ ω, ∑ v, g (gaussianObservationCurve (signal ω) (noise ω) t) v *
        gaussianObservationVelocity (signal ω) (noise ω) t v ∂μ) t := by
  let D : (V → ℝ) → (V → ℝ) →L[ℝ] ℝ := fun x => ∑ v, g x v •
    (ContinuousLinearMap.proj v : (V → ℝ) →L[ℝ] ℝ)
  have hDcont : Continuous D := by
    apply continuous_finsetSum
    intro v _
    exact (hg v).smul continuous_const
  have hDbound (x : V → ℝ) : ‖D x‖ ≤ (Fintype.card V : ℝ) * C := by
    apply ContinuousLinearMap.opNorm_le_bound _ (mul_nonneg (by positivity) hC)
    intro y
    simp only [D, sum_apply, smul_apply, ContinuousLinearMap.proj_apply, smul_eq_mul]
    calc
      ‖∑ v, g x v * y v‖ ≤ ∑ v, ‖g x v * y v‖ := norm_sum_le _ _
      _ ≤ ∑ v : V, C * ‖y‖ := by
        apply Finset.sum_le_sum
        intro v _
        rw [norm_mul, Real.norm_eq_abs (g x v)]
        exact mul_le_mul (hgbound x v) (norm_le_pi_norm y v) (norm_nonneg _) hC
      _ = _ := by simp [Finset.sum_const, nsmul_eq_mul, mul_assoc]
  have hsInt : Integrable signal μ := Integrable.of_eval fun v =>
    Integrable.of_bound ((measurable_pi_apply v).comp hsignal).aestronglyMeasurable 1
      (Filter.Eventually.of_forall fun ω => by simpa only [Real.norm_eq_abs] using hspin ω v)
  have hnInt : Integrable noise μ :=
    ⟨hnoise.aestronglyMeasurable, (Integrable.of_eval hnoiseInt).hasFiniteIntegral⟩
  have hd := (hasDerivAt_integral_sqrt_observation_vector_of_integrable hsInt hnInt hdf hDcont
    (mul_nonneg (by positivity) hC) hDbound ht hFint).2
  simpa only [gaussianObservationCurve, gaussianObservationVelocity, D, sum_apply,
    smul_apply, ContinuousLinearMap.proj_apply, smul_eq_mul] using hd

end FinitePosterior

end Problem367

end

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Stochastic_FiniteFieldEntropyIntegral
attribute [-instance] _root_.OAI.Problem367.WienerSampler.pathMeasurableSpace _root_.OAI.Problem367.reducedTailFinite _root_.OAI.Problem367.treeBallFinite _root_.OAI.Problem367.treeShellFinite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped BigOperators NNReal

namespace Problem367.FinitePosterior

variable {S V : Type*} [Fintype S] [Nonempty S] [Fintype V] [DecidableEq V]
  [MeasurableSpace S] [MeasurableSingletonClass S] [StandardBorelSpace S]

theorem hasDerivAt_finiteStandardEntropyEnergy
    (μ : Measure S) [IsProbabilityMeasure μ] (energy : S → ℝ)
    (hprior : ∀ s, μ.real {s} = Real.exp (energy s) / ∑ a, Real.exp (energy a))
    (spin : S → V → ℝ) (observable : S → ℝ)
    (hspin : ∀ s, observable s = -1 ∨ observable s = 1)
    (hneg : ∃ s, observable s = -1) (hpos : ∃ s, observable s = 1)
    (hcoords : ∀ s v, spin s v = -1 ∨ spin s v = 1)
    {t : ℝ} (ht : 0 < t) :
    HasDerivAt
      (fun r => ∫ x, fieldEntropy energy spin observable (finiteStandardObservation spin r x)
        ∂μ.prod (Measure.pi (fun _ : V => gaussianReal 0 1)))
      (∫ x, (1 + fieldMean energy spin observable (finiteStandardObservation spin t x) ^ 2) *
          ∑ v, normalizedFieldCovariance energy spin observable
            (finiteStandardObservation spin t x) v ^ 2
        ∂μ.prod (Measure.pi (fun _ : V => gaussianReal 0 1))) t := by
  have hd := hasDerivAt_integral_gaussianObservationCurve_of_integrable
    (μ.prod (Measure.pi (fun _ : V => gaussianReal 0 1)))
    (fieldEntropy energy spin observable) (fieldEntropyGradient energy spin observable)
    (fun x => hasFDerivAt_fieldEntropy energy spin observable x hspin hneg hpos)
    (fun v => continuous_fieldEntropyGradient energy spin observable v hspin hneg hpos)
    2 (by norm_num)
    (fun x v => abs_fieldEntropyGradient_le energy spin observable x v hspin hneg hpos
      (fun s => (abs_spin_eq_one (fun s => spin s v) (fun s => hcoords s v) s).le))
    (fun x : S × (V → ℝ) => spin x.1) Prod.snd
    ((measurable_of_finite spin).comp measurable_fst) measurable_snd
    (fun x v => (abs_spin_eq_one (fun s => spin s v) (fun s => hcoords s v) x.1).le)
    (fun v => integrable_finiteStandardNoise μ v) ht
    (integrable_finiteStandardEntropy μ energy spin observable hspin hneg hpos hcoords t)
  apply hd.congr_deriv
  exact integral_finiteStandardEntropyVelocity μ energy hprior spin observable hspin hneg hpos hcoords ht

theorem integral_finiteStandardEntropyEnergy
    (μ : Measure S) [IsProbabilityMeasure μ] (energy : S → ℝ)
    (hprior : ∀ s, μ.real {s} = Real.exp (energy s) / ∑ a, Real.exp (energy a))
    (spin : S → V → ℝ) (observable : S → ℝ)
    (hspin : ∀ s, observable s = -1 ∨ observable s = 1)
    (hneg : ∃ s, observable s = -1) (hpos : ∃ s, observable s = 1)
    (hcoords : ∀ s v, spin s v = -1 ∨ spin s v = 1)
    {T : ℝ} (hT : 0 ≤ T) :
    let C : ℝ → ℝ := fun t => ∫ x,
      (1 + fieldMean energy spin observable (finiteStandardObservation spin t x) ^ 2) *
        ∑ v, normalizedFieldCovariance energy spin observable
          (finiteStandardObservation spin t x) v ^ 2
      ∂μ.prod (Measure.pi (fun _ : V => gaussianReal 0 1))
    IntervalIntegrable C volume 0 T ∧
      (∫ t in 0..T, C t) =
        (∫ x, fieldEntropy energy spin observable (finiteStandardObservation spin T x)
          ∂μ.prod (Measure.pi (fun _ : V => gaussianReal 0 1))) -
        fieldEntropy energy spin observable 0 ∧
      0 ≤ (∫ t in 0..T, C t) := by
  let ρ := μ.prod (Measure.pi (fun _ : V => gaussianReal 0 1))
  let E : ℝ → ℝ := fun t => ∫ x,
    fieldEntropy energy spin observable (finiteStandardObservation spin t x) ∂ρ
  let C : ℝ → ℝ := fun t => ∫ x,
    (1 + fieldMean energy spin observable (finiteStandardObservation spin t x) ^ 2) *
      ∑ v, normalizedFieldCovariance energy spin observable (finiteStandardObservation spin t x) v ^ 2 ∂ρ
  have hG : Integrable (Prod.snd : S × (V → ℝ) → (V → ℝ)) ρ :=
    Integrable.of_eval (fun v => integrable_finiteStandardNoise μ v)
  have hE : Continuous E := by
    simpa only [E, finiteStandardObservation, gaussianObservationCurve] using
      continuous_integral_sqrt_observation_lipschitz
        (integrable_finiteStandardSignal μ spin hcoords) hG
        (lipschitzWith_fieldEntropy energy spin observable hspin hneg hpos
          (fun s v => (abs_spin_eq_one (fun s => spin s v) (fun s => hcoords s v) s).le))
  have hd (t : ℝ) (ht : 0 < t) : HasDerivAt E (C t) t :=
    hasDerivAt_finiteStandardEntropyEnergy μ energy hprior spin observable hspin hneg hpos hcoords ht
  have hCpos (t : ℝ) : 0 ≤ C t := integral_nonneg fun x =>
    mul_nonneg (by positivity) (Finset.sum_nonneg (fun v _ => sq_nonneg _))
  have hCI : IntervalIntegrable C volume 0 T := by
    apply intervalIntegral.intervalIntegrable_deriv_of_nonneg hE.continuousOn
    · intro t ht
      exact hd t (by simpa only [min_eq_left hT, max_eq_right hT] using ht.1)
    · exact fun t _ => hCpos t
  have hFTC : (∫ t in 0..T, C t) = E T - E 0 :=
    intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hT hE.continuousOn
      (fun t ht => hd t ht.1) hCI
  have hzero : E 0 = fieldEntropy energy spin observable 0 := by
    simp [E, finiteStandardObservation, gaussianObservationCurve, ρ]
  exact ⟨hCI, by simpa only [hzero] using hFTC,
    intervalIntegral.integral_nonneg_of_forall hT hCpos⟩

omit [DecidableEq V] [StandardBorelSpace S] in
theorem continuous_finiteStandardNormalizedEnergy
    (μ : Measure S) [IsFiniteMeasure μ] (energy : S → ℝ)
    (spin : S → V → ℝ) (observable : S → ℝ)
    (hspin : ∀ s, observable s = -1 ∨ observable s = 1)
    (hneg : ∃ s, observable s = -1) (hpos : ∃ s, observable s = 1)
    (hcoords : ∀ s v, spin s v = -1 ∨ spin s v = 1) :
    Continuous (fun t : ℝ => ∫ x, ∑ v, normalizedFieldCovariance energy spin observable
      (finiteStandardObservation spin t x) v ^ 2
        ∂μ.prod (Measure.pi (fun _ : V => gaussianReal 0 1))) := by
  simpa only [finiteStandardObservation, gaussianObservationCurve, Function.comp_def] using
    continuous_integral_sqrt_observation
      (((measurable_of_finite spin).comp measurable_fst).aestronglyMeasurable)
      (measurable_snd.aestronglyMeasurable)
      (continuous_normalizedRowEnergy energy spin observable hspin hneg hpos)
      (fun x => abs_normalizedRowEnergy_le_card energy spin observable x hspin hneg hpos
        (fun s v => (abs_spin_eq_one (fun s => spin s v) (fun s => hcoords s v) s).le))

theorem integral_finiteStandardNormalizedEnergy_le
    (μ : Measure S) [IsProbabilityMeasure μ] (energy : S → ℝ)
    (hprior : ∀ s, μ.real {s} = Real.exp (energy s) / ∑ a, Real.exp (energy a))
    (spin : S → V → ℝ) (observable : S → ℝ)
    (hspin : ∀ s, observable s = -1 ∨ observable s = 1)
    (hneg : ∃ s, observable s = -1) (hpos : ∃ s, observable s = 1)
    (hcoords : ∀ s v, spin s v = -1 ∨ spin s v = 1)
    {T : ℝ} (hT : 0 ≤ T) :
    let Q : ℝ → ℝ := fun t => ∫ x, ∑ v, normalizedFieldCovariance energy spin observable
      (finiteStandardObservation spin t x) v ^ 2
      ∂μ.prod (Measure.pi (fun _ : V => gaussianReal 0 1))
    IntervalIntegrable Q volume 0 T ∧
      (∫ t in 0..T, Q t) ≤
        (∫ x, fieldEntropy energy spin observable (finiteStandardObservation spin T x)
          ∂μ.prod (Measure.pi (fun _ : V => gaussianReal 0 1))) -
        fieldEntropy energy spin observable 0 ∧
      0 ≤ (∫ t in 0..T, Q t) := by
  let ρ := μ.prod (Measure.pi (fun _ : V => gaussianReal 0 1))
  let Q : ℝ → ℝ := fun t => ∫ x, ∑ v, normalizedFieldCovariance energy spin observable
    (finiteStandardObservation spin t x) v ^ 2 ∂ρ
  let C : ℝ → ℝ := fun t => ∫ x,
    (1 + fieldMean energy spin observable (finiteStandardObservation spin t x) ^ 2) *
      ∑ v, normalizedFieldCovariance energy spin observable (finiteStandardObservation spin t x) v ^ 2 ∂ρ
  have hsignal : ∀ s v, |spin s v| ≤ 1 :=
    fun s v => (abs_spin_eq_one (fun s => spin s v) (fun s => hcoords s v) s).le
  have hQI : IntervalIntegrable Q volume 0 T :=
    (continuous_finiteStandardNormalizedEnergy μ energy spin observable hspin hneg hpos hcoords).intervalIntegrable 0 T
  have hFTC := integral_finiteStandardEntropyEnergy μ energy hprior spin observable
    hspin hneg hpos hcoords hT
  have hmono (t : ℝ) : Q t ≤ C t := by
    let Y := finiteStandardObservation spin t
    let q := fun x => ∑ v, normalizedFieldCovariance energy spin observable (Y x) v ^ 2
    let a := fun x => 1 + fieldMean energy spin observable (Y x) ^ 2
    have hY : Measurable Y := measurable_finiteStandardObservation spin t
    have hq : Integrable q ρ := by
      apply Integrable.of_bound
        (((continuous_normalizedRowEnergy energy spin observable hspin hneg hpos).measurable.comp hY).aestronglyMeasurable)
        (Fintype.card V : ℝ)
      exact Filter.Eventually.of_forall fun x => by
        simpa only [Real.norm_eq_abs, Function.comp_def] using
          abs_normalizedRowEnergy_le_card energy spin observable (Y x) hspin hneg hpos hsignal
    have ha : AEStronglyMeasurable a ρ :=
      ((continuous_const.add ((continuous_fieldMean energy spin observable).pow 2)).measurable.comp hY).aestronglyMeasurable
    have hbound : ∀ x, ‖a x‖ ≤ 2 := by
      intro x
      have hm := abs_fieldMean_le energy spin observable (Y x) 1
        (fun s => (abs_spin_eq_one observable hspin s).le)
      have hm2 := (sq_le_one_iff_abs_le_one _).mpr hm
      simp only [a, Real.norm_eq_abs, abs_of_nonneg (by positivity : 0 ≤ 1 + fieldMean energy spin observable (Y x) ^ 2)]
      linarith
    have hCInt : Integrable (fun x => a x * q x) ρ := by
      simpa only [mul_comm] using hq.mul_bdd ha (Filter.Eventually.of_forall hbound)
    apply integral_mono hq hCInt
    intro x
    have hqpos : 0 ≤ q x := Finset.sum_nonneg fun v _ => sq_nonneg _
    have hp := mul_nonneg (sq_nonneg (fieldMean energy spin observable (Y x))) hqpos
    dsimp [a]
    nlinarith
  have hQC : (∫ t in 0..T, Q t) ≤ ∫ t in 0..T, C t :=
    intervalIntegral.integral_mono hT hQI hFTC.1 hmono
  refine ⟨hQI, hQC.trans_eq hFTC.2.1, ?_⟩
  exact intervalIntegral.integral_nonneg_of_forall hT fun t =>
    integral_nonneg fun x => Finset.sum_nonneg fun v _ => sq_nonneg _

end Problem367.FinitePosterior

end

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Energy_FiniteIsingFieldEnergy
attribute [-instance] _root_.OAI.Problem367.IsingConditionalCopyBounds.graphLaw_isProbabilityMeasure _root_.OAI.Problem367.IsingObservationFactor.copies_probability _root_.OAI.Problem367.IsingObservationFactor.kernel_markov _root_.OAI.Problem367.IsingObservationInnovation.innovationMap_observationLaw_probability _root_.OAI.Problem367.IsingObservationInnovation.observationLaw_probability _root_.OAI.Problem367.TreeKoopman.labelProbability _root_.OAI.Problem367.freeIsingMeasure_probability _root_.OAI.Problem367.reducedTailFintype _root_.OAI.Problem367.treeBallFintype _root_.OAI.Problem367.treeShellFintype
attribute [-simp] _root_.OAI.Problem367.ConnectedHull.pathAssignment_path _root_.OAI.Problem367.ConnectedHull.path_last _root_.OAI.Problem367.ConnectedHull.path_zero _root_.OAI.Problem367.ConnectedHull.prefix_length _root_.OAI.Problem367.ConnectedHull.prefix_zero _root_.OAI.Problem367.CutContinuationChannels.averageChannel_globalCone _root_.OAI.Problem367.CutContinuationChannels.continuationChannel_globalCone _root_.OAI.Problem367.FactorObservable.centeredSpinLp_coe _root_.OAI.Problem367.FiniteIsingSplit.splitEquiv_fst _root_.OAI.Problem367.FiniteIsingSplit.splitEquiv_snd _root_.OAI.Problem367.FinitePathGibbs.tailPartition_zero _root_.OAI.Problem367.GaussianTreeResponseNaturality.fieldEquiv_apply_image _root_.OAI.Problem367.IsingObservationInnovation.innovationMap_apply _root_.OAI.Problem367.IsingObservationInnovation.innovationMap_uniformObservation _root_.OAI.Problem367.IsingObservationInnovation.innovationMap_zero _root_.OAI.Problem367.IsingObservationInnovation.uniformObservation_relabel _root_.OAI.Problem367.IsingOrientedPath.attenuation_outward _root_.OAI.Problem367.IsingOrientedPath.endpoint_extensionAt _root_.OAI.Problem367.LocalSupportGeometry.prefixVertex_length _root_.OAI.Problem367.PathSideBranches.parent_sideVertex _root_.OAI.Problem367.PathSideBranches.restrictNoisyRegion_array _root_.OAI.Problem367.PathSideBranches.sideVertex_length _root_.OAI.Problem367.PathSideBranches.sideVertex_val _root_.OAI.Problem367.PosteriorChain.transition_spinMean _root_.OAI.Problem367.PosteriorChain.transition_sum _root_.OAI.Problem367.RootedBroadcast.flipBranchToComplement_val _root_.OAI.Problem367.RootedBroadcast.pos_spinMul _root_.OAI.Problem367.RootedBroadcast.prefixFlip_branchRoot _root_.OAI.Problem367.RootedBroadcast.prefixFlip_root _root_.OAI.Problem367.RootedBroadcast.prefixTreeAut_symm_branchRoot _root_.OAI.Problem367.RootedBroadcast.prefixTreeAut_symm_root _root_.OAI.Problem367.RootedBroadcast.spinMul_pos _root_.OAI.Problem367.RootedBroadcast.spinMul_self _root_.OAI.Problem367.TreeConeCoding.length_vertex _root_.OAI.Problem367.TreeConeCoding.vertex_nil _root_.OAI.Problem367.TreeConeCoding.vertex_val _root_.OAI.Problem367.TreeGibbsAut.spinEquiv_apply_image _root_.OAI.Problem367.TreeKoopman.centeredAverage_apply_coe _root_.OAI.Problem367.TreeKoopman.centeredAverage_pow_apply_coe _root_.OAI.Problem367.TreeKoopman.centeredGenerator_apply_coe _root_.OAI.Problem367.TreeKoopman.centeredGenerator_sq _root_.OAI.Problem367.TreeKoopman.generatorOperator_sq _root_.OAI.Problem367.TreeKoopman.reverseVertex_twice _root_.OAI.Problem367.TreeKoopman.wordRelabel_cons _root_.OAI.Problem367.TreeKoopman.wordRelabel_nil _root_.OAI.Problem367.TreeLawKoopman.centeredAverage_apply_coe _root_.OAI.Problem367.TreeLawKoopman.generatorOperator_sq _root_.OAI.Problem367.TreePathGibbs.vertexEquiv_val _root_.OAI.Problem367.branchColorAut_length _root_.OAI.Problem367.branchColorAut_singleton _root_.OAI.Problem367.branchColorAut_val _root_.OAI.Problem367.branchColorMap_symm_apply _root_.OAI.Problem367.card_treeBallFinset _root_.OAI.Problem367.colorPermAut_length _root_.OAI.Problem367.colorPermAut_nil _root_.OAI.Problem367.colorPermAut_val _root_.OAI.Problem367.colorPermMap_symm_apply _root_.OAI.Problem367.colorPermMap_val _root_.OAI.Problem367.connectedSpinEncode_apply_root _root_.OAI.Problem367.connectedSpinEquiv_apply _root_.OAI.Problem367.dropVertex_length _root_.OAI.Problem367.dropVertex_val _root_.OAI.Problem367.iUnion_treeBallFinset _root_.OAI.Problem367.mem_rootComplementFinset _root_.OAI.Problem367.mem_rootComponentFinset _root_.OAI.Problem367.mem_rootComponentIndices _root_.OAI.Problem367.mem_treeBallFinset _root_.OAI.Problem367.parentVertex_length _root_.OAI.Problem367.parentVertex_val _root_.OAI.Problem367.prefixColorAut_length _root_.OAI.Problem367.prefixColorAut_val _root_.OAI.Problem367.prefixColorMap_symm_apply _root_.OAI.Problem367.prefixFlip_twice _root_.OAI.Problem367.spinAgreementCode_eq_neg_iff _root_.OAI.Problem367.spinAgreementCode_eq_pos_iff _root_.OAI.Problem367.spinSign_flip _root_.OAI.Problem367.sum_treeShell_zero _root_.OAI.Problem367.tsum_treeShell_radial _root_.OAI.Problem367.vertexSampler_relabel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory
open scoped BigOperators NNReal

namespace Problem367

local instance finiteIsingFieldEnergyNonemptySpin_raa325a_1 : Nonempty IsingSpin := ⟨.neg⟩
theorem finiteIsingEntropy_zero {d : ℕ} (beta : ℝ) (D : Finset (TreeVertex d)) (v : D) :
    FinitePosterior.fieldEntropy (finiteIsingEnergy beta D)
      (fun (eta : D → IsingSpin) w => spinSign (eta w))
      (fun eta => spinSign (eta v)) 0 = 0 := by
  have hz := finiteIsingPosterior_spin_zero beta D v
  change FinitePosterior.fieldMean (finiteIsingEnergy beta D)
    (fun (eta : D → IsingSpin) w => spinSign (eta w))
    (fun eta => spinSign (eta v)) 0 = 0 at hz
  simp [FinitePosterior.fieldEntropy, hz]

end Problem367

end

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Stochastic_FiniteIsingBrownianEnergy
attribute [-instance] _root_.OAI.Problem367.IsingConditionalCopyBounds.graphLaw_isProbabilityMeasure _root_.OAI.Problem367.IsingObservationFactor.copies_probability _root_.OAI.Problem367.IsingObservationFactor.kernel_markov _root_.OAI.Problem367.IsingObservationInnovation.innovationMap_observationLaw_probability _root_.OAI.Problem367.IsingObservationInnovation.observationLaw_probability _root_.OAI.Problem367.TreeKoopman.labelProbability _root_.OAI.Problem367.WienerSampler.pathMeasurableSpace _root_.OAI.Problem367.freeIsingMeasure_probability _root_.OAI.Problem367.reducedTailFinite _root_.OAI.Problem367.reducedTailFintype _root_.OAI.Problem367.treeBallFinite _root_.OAI.Problem367.treeBallFintype _root_.OAI.Problem367.treeShellFinite _root_.OAI.Problem367.treeShellFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory ProbabilityTheory Set
open scoped NNReal ENNReal

namespace Problem367

theorem finiteBrownianNoise_restrict_measurePreserving
    {ι Ω : Type*} [MeasurableSpace Ω]
    (ν : ι → Measure Ω) {B : ι → ℝ≥0 → Ω → ℝ}
    (hB : ∀ i, IsPreBrownianReal (B i) (ν i))
    (hmB : ∀ i t, Measurable (B i t)) (D : Finset ι) (t : ℝ≥0) :
    MeasurePreserving (fun ω (v : D) => B v t (ω v))
      (Measure.infinitePi ν) (Measure.pi (fun _ : D => gaussianReal 0 t)) := by
  have (i : ι) : IsProbabilityMeasure (ν i) :=
    (hB i).isGaussianProcess.isProbabilityMeasure
  have hr : MeasurePreserving (D.restrict : (ι → Ω) → D → Ω)
      (Measure.infinitePi ν) (Measure.pi fun v : D => ν v) :=
    ⟨D.measurable_restrict, Measure.infinitePi_map_restrict ν⟩
  have he : MeasurePreserving (fun ω (v : D) => B v t (ω v))
      (Measure.pi fun v : D => ν v) (Measure.pi fun _ : D => gaussianReal 0 t) := by
    refine ⟨Measurable.of_eval (fun vertex => (hmB vertex t).comp
      (measurable_pi_apply vertex)), ?_⟩
    rw [Measure.pi_map_pi (μ := fun v : D => ν v)
      (f := fun v ω => B v t ω) (fun v => (hmB v t).aemeasurable)]
    congr 1
    funext v
    exact (hB v).hasLaw_eval t |>.map_eq
  exact he.comp hr

local instance finiteIsingBrownianEnergyNonemptySpin_raa325a_1 : Nonempty IsingSpin := ⟨.neg⟩
theorem integral_finiteIsingBrownian_observation_eq_standard
    {d : ℕ} {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure (TreeVertex d → IsingSpin)) [IsProbabilityMeasure μ]
    (ν : TreeVertex d → Measure Ω)
    {B : TreeVertex d → ℝ≥0 → Ω → ℝ}
    (hB : ∀ i, IsPreBrownianReal (B i) (ν i))
    (hmB : ∀ i t, Measurable (B i t))
    (D : Finset (TreeVertex d)) (t : ℝ≥0)
    (f : (D → ℝ) → ℝ) (hf : Measurable f) :
    (∫ p : (TreeVertex d → IsingSpin) × (TreeVertex d → Ω),
      f (fun v : D => (t : ℝ) * spinSign (p.1 v) + B v t (p.2 v))
      ∂μ.prod (Measure.infinitePi ν)) =
    ∫ p : (D → IsingSpin) × (D → ℝ),
      f (FinitePosterior.finiteStandardObservation
        (fun eta v => spinSign (eta v)) t p)
      ∂(μ.map D.restrict).prod (Measure.pi fun _ : D => gaussianReal 0 1) := by
  have (i : TreeVertex d) : IsProbabilityMeasure (ν i) :=
    (hB i).isGaussianProcess.isProbabilityMeasure
  let π := μ.map D.restrict
  let : IsProbabilityMeasure π := by first | (set_option synthInstance.maxHeartbeats 20000 in infer_instance) | exact Measure.isProbabilityMeasure_map (by first | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability)
  let Y : (D → IsingSpin) × (D → ℝ) → D → ℝ :=
    fun p v => (t : ℝ) * spinSign (p.1 v) + p.2 v
  have hY : Measurable Y := by
    apply Measurable.of_eval
    intro v
    exact (measurable_const.mul
      ((measurable_of_finite (fun eta : D → IsingSpin => spinSign (eta v))).comp
        measurable_fst)).add ((measurable_pi_apply v).comp measurable_snd)
  have hr : MeasurePreserving D.restrict μ π := ⟨D.measurable_restrict, rfl⟩
  have hp := hr.prod (finiteBrownianNoise_restrict_measurePreserving ν hB hmB D t)
  have hs : MeasurePreserving (fun z : D → ℝ => fun v => Real.sqrt (t : ℝ) * z v)
      (Measure.pi fun _ : D => gaussianReal 0 1)
      (Measure.pi fun _ : D => gaussianReal 0 t) := by
    refine ⟨by fun_prop, ?_⟩
    exact gaussianPi_map_sqrt (t : ℝ) t.property
  have hps := (MeasurePreserving.id π).prod hs
  have hleft := integral_map (μ := μ.prod (Measure.infinitePi ν)) hp.measurable.aemeasurable
    (hf.comp hY).aestronglyMeasurable
  have hright := integral_map (μ := π.prod (Measure.pi fun _ : D => gaussianReal 0 1))
    hps.measurable.aemeasurable
    (hf.comp hY).aestronglyMeasurable
  rw [hp.map_eq] at hleft
  rw [hps.map_eq] at hright
  exact hleft.symm.trans hright

end Problem367

end

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Brownian_EntropyEnergy
attribute [-instance] _root_.OAI.Problem367.IsingConditionalCopyBounds.graphLaw_isProbabilityMeasure _root_.OAI.Problem367.IsingObservationFactor.copies_probability _root_.OAI.Problem367.IsingObservationFactor.kernel_markov _root_.OAI.Problem367.IsingObservationInnovation.innovationMap_observationLaw_probability _root_.OAI.Problem367.IsingObservationInnovation.observationLaw_probability _root_.OAI.Problem367.TreeKoopman.labelProbability _root_.OAI.Problem367.WienerSampler.pathMeasurableSpace _root_.OAI.Problem367.freeIsingMeasure_probability _root_.OAI.Problem367.reducedTailFinite _root_.OAI.Problem367.reducedTailFintype _root_.OAI.Problem367.treeBallFinite _root_.OAI.Problem367.treeBallFintype _root_.OAI.Problem367.treeShellFinite _root_.OAI.Problem367.treeShellFintype
attribute [-simp] _root_.OAI.Problem367.ConnectedHull.pathAssignment_path _root_.OAI.Problem367.ConnectedHull.path_last _root_.OAI.Problem367.ConnectedHull.path_zero _root_.OAI.Problem367.ConnectedHull.prefix_length _root_.OAI.Problem367.ConnectedHull.prefix_zero _root_.OAI.Problem367.CutContinuationChannels.averageChannel_globalCone _root_.OAI.Problem367.CutContinuationChannels.continuationChannel_globalCone _root_.OAI.Problem367.FactorObservable.centeredSpinLp_coe _root_.OAI.Problem367.FiniteIsingSplit.splitEquiv_fst _root_.OAI.Problem367.FiniteIsingSplit.splitEquiv_snd _root_.OAI.Problem367.FinitePathGibbs.tailPartition_zero _root_.OAI.Problem367.GaussianTreeResponseNaturality.fieldEquiv_apply_image _root_.OAI.Problem367.IsingObservationInnovation.innovationMap_apply _root_.OAI.Problem367.IsingObservationInnovation.innovationMap_uniformObservation _root_.OAI.Problem367.IsingObservationInnovation.innovationMap_zero _root_.OAI.Problem367.IsingObservationInnovation.uniformObservation_relabel _root_.OAI.Problem367.IsingOrientedPath.attenuation_outward _root_.OAI.Problem367.IsingOrientedPath.endpoint_extensionAt _root_.OAI.Problem367.LocalSupportGeometry.prefixVertex_length _root_.OAI.Problem367.PathSideBranches.parent_sideVertex _root_.OAI.Problem367.PathSideBranches.restrictNoisyRegion_array _root_.OAI.Problem367.PathSideBranches.sideVertex_length _root_.OAI.Problem367.PathSideBranches.sideVertex_val _root_.OAI.Problem367.PosteriorChain.transition_spinMean _root_.OAI.Problem367.PosteriorChain.transition_sum _root_.OAI.Problem367.RootedBroadcast.flipBranchToComplement_val _root_.OAI.Problem367.RootedBroadcast.pos_spinMul _root_.OAI.Problem367.RootedBroadcast.prefixFlip_branchRoot _root_.OAI.Problem367.RootedBroadcast.prefixFlip_root _root_.OAI.Problem367.RootedBroadcast.prefixTreeAut_symm_branchRoot _root_.OAI.Problem367.RootedBroadcast.prefixTreeAut_symm_root _root_.OAI.Problem367.RootedBroadcast.spinMul_pos _root_.OAI.Problem367.RootedBroadcast.spinMul_self _root_.OAI.Problem367.TreeConeCoding.length_vertex _root_.OAI.Problem367.TreeConeCoding.vertex_nil _root_.OAI.Problem367.TreeConeCoding.vertex_val _root_.OAI.Problem367.TreeGibbsAut.spinEquiv_apply_image _root_.OAI.Problem367.TreeKoopman.centeredAverage_apply_coe _root_.OAI.Problem367.TreeKoopman.centeredAverage_pow_apply_coe _root_.OAI.Problem367.TreeKoopman.centeredGenerator_apply_coe _root_.OAI.Problem367.TreeKoopman.centeredGenerator_sq _root_.OAI.Problem367.TreeKoopman.generatorOperator_sq _root_.OAI.Problem367.TreeKoopman.reverseVertex_twice _root_.OAI.Problem367.TreeKoopman.wordRelabel_cons _root_.OAI.Problem367.TreeKoopman.wordRelabel_nil _root_.OAI.Problem367.TreeLawKoopman.centeredAverage_apply_coe _root_.OAI.Problem367.TreeLawKoopman.generatorOperator_sq _root_.OAI.Problem367.TreePathGibbs.vertexEquiv_val _root_.OAI.Problem367.branchColorAut_length _root_.OAI.Problem367.branchColorAut_singleton _root_.OAI.Problem367.branchColorAut_val _root_.OAI.Problem367.branchColorMap_symm_apply _root_.OAI.Problem367.card_treeBallFinset _root_.OAI.Problem367.colorPermAut_length _root_.OAI.Problem367.colorPermAut_nil _root_.OAI.Problem367.colorPermAut_val _root_.OAI.Problem367.colorPermMap_symm_apply _root_.OAI.Problem367.colorPermMap_val _root_.OAI.Problem367.connectedSpinEncode_apply_root _root_.OAI.Problem367.connectedSpinEquiv_apply _root_.OAI.Problem367.dropVertex_length _root_.OAI.Problem367.dropVertex_val _root_.OAI.Problem367.iUnion_treeBallFinset _root_.OAI.Problem367.mem_rootComplementFinset _root_.OAI.Problem367.mem_rootComponentFinset _root_.OAI.Problem367.mem_rootComponentIndices _root_.OAI.Problem367.mem_treeBallFinset _root_.OAI.Problem367.parentVertex_length _root_.OAI.Problem367.parentVertex_val _root_.OAI.Problem367.prefixColorAut_length _root_.OAI.Problem367.prefixColorAut_val _root_.OAI.Problem367.prefixColorMap_symm_apply _root_.OAI.Problem367.prefixFlip_twice _root_.OAI.Problem367.spinAgreementCode_eq_neg_iff _root_.OAI.Problem367.spinAgreementCode_eq_pos_iff _root_.OAI.Problem367.spinSign_flip _root_.OAI.Problem367.sum_treeShell_zero _root_.OAI.Problem367.tsum_treeShell_radial _root_.OAI.Problem367.vertexSampler_relabel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal

namespace Problem367

local instance finiteIsingBrownianEntropyNonemptySpin : Nonempty IsingSpin := ⟨.neg⟩

theorem finiteIsingBrownianEntropy_nonneg {d : ℕ} {Ω : Type*}
    (beta : ℝ) (D : Finset (TreeVertex d)) (v : D)
    (B : TreeVertex d → ℝ≥0 → Ω → ℝ) (t : ℝ)
    (p : (TreeVertex d → IsingSpin) × (TreeVertex d → Ω)) :
    0 ≤ finiteIsingBrownianEntropy beta D v B t p := by
  exact FinitePosterior.fieldEntropy_nonneg _ _ _ _
    (fun eta => by cases eta v <;> simp [spinSign])
    ⟨fun _ => .neg, rfl⟩ ⟨fun _ => .pos, rfl⟩

theorem finiteIsingBrownianEntropy_le_noise {d : ℕ} {Ω : Type*}
    {beta : ℝ} (hbeta : 0 ≤ beta) (D : Finset (TreeVertex d)) (v : D)
    (B : TreeVertex d → ℝ≥0 → Ω → ℝ) (t : ℝ≥0)
    (p : (TreeVertex d → IsingSpin) × (TreeVertex d → Ω)) :
    finiteIsingBrownianEntropy beta D v B t p ≤
      2 * ((d : ℝ) * beta + (t : ℝ) + |B v t (p.2 v)|) := by
  let y := finiteIsingBrownianObservation B D t p
  have he := FinitePosterior.fieldEntropy_le_abs_field (finiteIsingEnergy beta D)
    (fun (eta : D → IsingSpin) w => spinSign (eta w)) (fun eta => spinSign (eta v)) y
    (fun eta => by cases eta v <;> simp [spinSign])
    ⟨fun _ => .neg, rfl⟩ ⟨fun _ => .pos, rfl⟩
  have hb := finite_tree_gibbs_field_uniform_bound D hbeta y v
  have ho : |y v| ≤ (t : ℝ) + |B v t (p.2 v)| := by
    change |(t : ℝ) * spinSign (p.1 v) + B v (Real.toNNReal (t : ℝ)) (p.2 v)| ≤ _
    rw [Real.toNNReal_coe]
    calc
      _ ≤ |(t : ℝ) * spinSign (p.1 v)| + |B v t (p.2 v)| := abs_add_le _ _
      _ = _ := by cases p.1 v <;> simp [spinSign, abs_of_nonneg t.coe_nonneg]
  have hfield : |FinitePosterior.fieldField (finiteIsingEnergy beta D)
      (fun (eta : D → IsingSpin) w => spinSign (eta w)) (fun eta => spinSign (eta v)) y| ≤
      (d : ℝ) * beta + (t : ℝ) + |B v t (p.2 v)| := by
    have htri := abs_sub_le (FinitePosterior.fieldField (finiteIsingEnergy beta D)
      (fun (eta : D → IsingSpin) w => spinSign (eta w)) (fun eta => spinSign (eta v)) y)
      (y v) 0
    simp only [sub_zero] at htri
    change |FinitePosterior.fieldField (finiteIsingEnergy beta D)
      (fun (eta : D → IsingSpin) w => spinSign (eta w))
      (fun eta => spinSign (eta v)) y - y v| ≤ (d : ℝ) * beta at hb
    linarith
  exact he.trans (mul_le_mul_of_nonneg_left hfield (by norm_num))

private theorem integral_abs_gaussian_le_sqrt
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {X : Ω → ℝ} {t : ℝ≥0} (hX : HasLaw X (gaussianReal 0 t) P) :
    (∫ ω, |X ω| ∂P) ≤ Real.sqrt (t : ℝ) := by
  have hX2 : Integrable (fun ω => X ω ^ 2) P := by
    simpa only [sq_abs] using integrable_abs_pow_of_gaussianLaw hX 2
  have htrans := hX.integral_comp (f := fun x : ℝ => x ^ 2) (by fun_prop)
  have hvar := variance_fun_id_gaussianReal (μ := 0) (v := t)
  rw [variance_of_integral_eq_zero (μ := gaussianReal 0 t) (X := fun x : ℝ => x)
    (by fun_prop) (by simp)] at hvar
  have hsq : (∫ ω, X ω ^ 2 ∂P) = (t : ℝ) := htrans.trans hvar
  exact (integral_abs_le_sqrt_integral_sq hX.aemeasurable hX2).trans_eq
    (congrArg Real.sqrt hsq)

theorem finiteIsingBrownianEntropy_moment
    {d : ℕ} {Ω : Type*} [MeasurableSpace Ω] {beta : ℝ} (hbeta : 0 ≤ beta)
    (μ : Measure (TreeVertex d → IsingSpin)) [IsProbabilityMeasure μ]
    (ν : TreeVertex d → Measure Ω) {B : TreeVertex d → ℝ≥0 → Ω → ℝ}
    (hB : ∀ i, IsPreBrownianReal (B i) (ν i))
    (hmB : ∀ i t, Measurable (B i t))
    (D : Finset (TreeVertex d)) (v : D) (t : ℝ≥0) :
    Integrable (finiteIsingBrownianEntropy beta D v B t) (μ.prod (Measure.infinitePi ν)) ∧
      (∫ p, finiteIsingBrownianEntropy beta D v B t p ∂μ.prod (Measure.infinitePi ν)) ≤
        2 * ((d : ℝ) * beta + (t : ℝ) + Real.sqrt (t : ℝ)) := by
  have (i : TreeVertex d) : IsProbabilityMeasure (ν i) :=
    (hB i).isGaussianProcess.isProbabilityMeasure
  let ρ := μ.prod (Measure.infinitePi ν)
  let X : ((TreeVertex d → IsingSpin) × (TreeVertex d → Ω)) → ℝ :=
    fun p => B v t (p.2 v)
  have hcoord := (measurePreserving_eval_infinitePi ν (v : TreeVertex d)).comp
    (measurePreserving_snd (μ := μ) (ν := Measure.infinitePi ν))
  have hX : HasLaw X (gaussianReal 0 t) ρ :=
    (hB v).hasLaw_eval t |>.comp ⟨hcoord.measurable.aemeasurable, hcoord.map_eq⟩
  have hXi : Integrable (fun p => |X p|) ρ := by
    simpa only [pow_one] using integrable_abs_pow_of_gaussianLaw hX 1
  have hY : Measurable (finiteIsingBrownianObservation B D (t : ℝ)) := by
    apply Measurable.of_eval
    intro w
    exact (((measurable_of_finite spinSign).comp
      ((measurable_pi_apply (w : TreeVertex d)).comp measurable_fst)).const_mul (t : ℝ)).add
      ((hmB w (t : ℝ).toNNReal).comp ((measurable_pi_apply (w : TreeVertex d)).comp measurable_snd))
  have hF : Measurable (finiteIsingBrownianEntropy beta D v B (t : ℝ)) :=
    (FinitePosterior.continuous_fieldEntropy (finiteIsingEnergy beta D)
      (fun (eta : D → IsingSpin) w => spinSign (eta w)) (fun eta => spinSign (eta v))
      (fun eta => by cases eta v <;> simp [spinSign])
      ⟨fun _ => .neg, rfl⟩ ⟨fun _ => .pos, rfl⟩).measurable.comp hY
  have hdom : Integrable (fun p => 2 * ((d : ℝ) * beta + (t : ℝ) + |X p|)) ρ :=
    ((integrable_const _).add hXi).const_mul 2
  have hFi : Integrable (finiteIsingBrownianEntropy beta D v B t) ρ := by
    apply hdom.mono' hF.aestronglyMeasurable
    exact Eventually.of_forall fun p => by
      rw [Real.norm_of_nonneg (finiteIsingBrownianEntropy_nonneg beta D v B t p)]
      exact finiteIsingBrownianEntropy_le_noise hbeta D v B t p
  refine ⟨hFi, ?_⟩
  calc
    _ ≤ ∫ p, 2 * ((d : ℝ) * beta + (t : ℝ) + |X p|) ∂ρ :=
      integral_mono hFi hdom (finiteIsingBrownianEntropy_le_noise hbeta D v B t)
    _ = 2 * ((d : ℝ) * beta + (t : ℝ) + ∫ p, |X p| ∂ρ) := by
      rw [integral_const_mul, integral_add (integrable_const _) hXi]
      simp [ρ]
    _ ≤ _ := mul_le_mul_of_nonneg_left
      (add_le_add le_rfl (integral_abs_gaussian_le_sqrt hX)) (by norm_num)

theorem HasFreeIsingLaw.integral_finiteIsingBrownianNormalizedEnergy_le
    {d : ℕ} {beta : ℝ} {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure (TreeVertex d → IsingSpin)}
    (hμ : HasFreeIsingLaw (Real.tanh beta) μ) (hbeta : 0 ≤ beta)
    (ν : TreeVertex d → Measure Ω)
    {B : TreeVertex d → ℝ≥0 → Ω → ℝ}
    (hB : ∀ i, IsPreBrownianReal (B i) (ν i))
    (hmB : ∀ i t, Measurable (B i t))
    (D : Finset (TreeVertex d)) (hD : ConnectedFinset D) (v : D)
    {T : ℝ} (hT : 0 ≤ T) :
    let ρ := μ.prod (Measure.infinitePi ν)
    let E : ℝ → ℝ := fun t => ∫ p,
      ∑ u : D, finiteIsingBrownianNormalizedCovariance beta D v u B t p ^ 2 ∂ρ
    IntervalIntegrable E volume 0 T ∧
      (∫ t in 0..T, E t) ≤ (∫ p, finiteIsingBrownianEntropy beta D v B T p ∂ρ) ∧
      0 ≤ (∫ t in 0..T, E t) ∧
      (∫ t in 0..T, E t) ≤ 2 * ((d : ℝ) * beta + T + Real.sqrt T) := by
  classical
  let : IsProbabilityMeasure μ := hμ.isProbabilityMeasure
  let π := μ.map D.restrict
  let : IsProbabilityMeasure π :=
    (Measure.isProbabilityMeasure_map_iff D.measurable_restrict.aemeasurable).mpr inferInstance
  let spin : (D → IsingSpin) → D → ℝ := fun eta u => spinSign (eta u)
  let q : (D → IsingSpin) → ℝ := fun eta => spinSign (eta v)
  let F : (D → ℝ) → ℝ := FinitePosterior.fieldEntropy (finiteIsingEnergy beta D) spin q
  let C : (D → ℝ) → D → ℝ :=
    FinitePosterior.normalizedFieldCovariance (finiteIsingEnergy beta D) spin q
  let ρ := μ.prod (Measure.infinitePi ν)
  let ρG := π.prod (Measure.pi fun _ : D => gaussianReal 0 1)
  let EG : ℝ → ℝ := fun t => ∫ p,
    ∑ u : D, C (FinitePosterior.finiteStandardObservation spin t p) u ^ 2 ∂ρG
  let MG : ℝ → ℝ := fun t => ∫ p,
    F (FinitePosterior.finiteStandardObservation spin t p) ∂ρG
  let E : ℝ → ℝ := fun t => ∫ p,
    ∑ u : D, finiteIsingBrownianNormalizedCovariance beta D v u B t p ^ 2 ∂ρ
  let M : ℝ → ℝ := fun t => ∫ p, finiteIsingBrownianEntropy beta D v B t p ∂ρ
  have hcoords (eta : D → IsingSpin) (u : D) : spin eta u = -1 ∨ spin eta u = 1 := by
    dsimp only [spin]
    cases eta u <;> simp [spinSign]
  have hneg : ∃ eta, q eta = -1 := ⟨fun _ => .neg, rfl⟩
  have hpos : ∃ eta, q eta = 1 := ⟨fun _ => .pos, rfl⟩
  have hfm : Measurable F :=
    (FinitePosterior.continuous_fieldEntropy _ _ _ (fun eta => hcoords eta v) hneg hpos).measurable
  have hcm : Measurable (fun y => ∑ u : D, C y u ^ 2) :=
    (FinitePosterior.continuous_normalizedRowEnergy _ _ _ (fun eta => hcoords eta v) hneg hpos).measurable
  have hE (t : ℝ) (ht : 0 ≤ t) : E t = EG t := by
    have h := integral_finiteIsingBrownian_observation_eq_standard μ ν hB hmB D
      t.toNNReal (fun y => ∑ u : D, C y u ^ 2) hcm
    unfold E EG finiteIsingBrownianNormalizedCovariance finiteIsingBrownianObservation
    simpa only [C, spin, q, ρ, ρG, π, Real.coe_toNNReal t ht] using h
  have hM (t : ℝ) (ht : 0 ≤ t) : M t = MG t := by
    have h := integral_finiteIsingBrownian_observation_eq_standard μ ν hB hmB D
      t.toNNReal F hfm
    unfold M MG finiteIsingBrownianEntropy finiteIsingBrownianObservation
    simpa only [F, spin, q, ρ, ρG, π, Real.coe_toNNReal t ht] using h
  have hstd := FinitePosterior.integral_finiteStandardNormalizedEnergy_le π
    (finiteIsingEnergy beta D) (hμ.restrict_real_eq_normalized_exp D hD)
    spin q (fun eta => hcoords eta v) hneg hpos hcoords hT
  change IntervalIntegrable EG volume 0 T ∧
    (∫ t in 0..T, EG t) ≤ MG T - F 0 ∧ 0 ≤ (∫ t in 0..T, EG t) at hstd
  have hzero : F 0 = 0 := finiteIsingEntropy_zero beta D v
  have hEq : EqOn EG E (uIcc 0 T) := by
    intro t ht
    exact (hE t (by simpa only [min_eq_left hT] using ht.1)).symm
  have hInt : (∫ t in 0..T, EG t) = ∫ t in 0..T, E t :=
    intervalIntegral.integral_congr hEq
  have hle : (∫ t in 0..T, E t) ≤ M T := by
    simpa only [hzero, sub_zero, hInt, ← hM T hT] using hstd.2.1
  have hterminal : M T ≤ 2 * ((d : ℝ) * beta + T + Real.sqrt T) := by
    have h := (finiteIsingBrownianEntropy_moment hbeta μ ν hB hmB D v T.toNNReal).2
    simpa only [M, ρ, Real.coe_toNNReal T hT] using h
  change IntervalIntegrable E volume 0 T ∧ (∫ t in 0..T, E t) ≤ M T ∧
    0 ≤ (∫ t in 0..T, E t) ∧ (∫ t in 0..T, E t) ≤ _
  exact ⟨hstd.1.congr (fun t ht => hEq (uIoc_subset_uIcc ht)), hle,
    by simpa only [hInt] using hstd.2.2, hle.trans hterminal⟩

theorem HasFreeIsingLaw.lintegral_finiteIsingBrownianNormalizedEnergy_le
    {d : ℕ} {beta : ℝ} {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure (TreeVertex d → IsingSpin)}
    (hμ : HasFreeIsingLaw (Real.tanh beta) μ) (hbeta : 0 ≤ beta)
    (ν : TreeVertex d → Measure Ω)
    {B : TreeVertex d → ℝ≥0 → Ω → ℝ}
    (hB : ∀ i, IsPreBrownianReal (B i) (ν i))
    (hmB : ∀ i t, Measurable (B i t))
    (D : Finset (TreeVertex d)) (hD : ConnectedFinset D) (v : D)
    {T : ℝ} (hT : 0 ≤ T) :
    (∫⁻ t in Ioc 0 T, ∫⁻ p,
      ENNReal.ofReal (∑ u : D, finiteIsingBrownianNormalizedCovariance beta D v u B t p ^ 2)
      ∂μ.prod (Measure.infinitePi ν)) ≤
      ENNReal.ofReal (2 * ((d : ℝ) * beta + T + Real.sqrt T)) := by
  classical
  let : IsProbabilityMeasure μ := hμ.isProbabilityMeasure
  have (i : TreeVertex d) : IsProbabilityMeasure (ν i) :=
    (hB i).isGaussianProcess.isProbabilityMeasure
  let ρ := μ.prod (Measure.infinitePi ν)
  let R := fun t p => ∑ u : D, finiteIsingBrownianNormalizedCovariance beta D v u B t p ^ 2
  let E : ℝ → ℝ := fun t => ∫ p, R t p ∂ρ
  have hRpos (t : ℝ) (p) : 0 ≤ R t p := Finset.sum_nonneg fun u _ => sq_nonneg _
  have hRI (t : ℝ) : Integrable (R t) ρ := by
    have hY : Measurable (finiteIsingBrownianObservation B D t) := by
      apply Measurable.of_eval
      intro w
      exact (((measurable_of_finite spinSign).comp
        ((measurable_pi_apply (w : TreeVertex d)).comp measurable_fst)).const_mul t).add
        ((hmB w t.toNNReal).comp ((measurable_pi_apply (w : TreeVertex d)).comp measurable_snd))
    have hs (eta : D → IsingSpin) : spinSign (eta v) = -1 ∨ spinSign (eta v) = 1 := by
      cases eta v <;> simp [spinSign]
    have hn : ∃ eta : D → IsingSpin, spinSign (eta v) = -1 := ⟨fun _ => .neg, rfl⟩
    have hp : ∃ eta : D → IsingSpin, spinSign (eta v) = 1 := ⟨fun _ => .pos, rfl⟩
    apply Integrable.of_bound
      ((FinitePosterior.continuous_normalizedRowEnergy (finiteIsingEnergy beta D)
        (fun (eta : D → IsingSpin) w => spinSign (eta w)) (fun eta => spinSign (eta v))
        hs hn hp).measurable.comp hY).aestronglyMeasurable (Fintype.card D)
    exact Eventually.of_forall fun p => by
      simpa only [Real.norm_eq_abs, Function.comp_def] using
        FinitePosterior.abs_normalizedRowEnergy_le_card (finiteIsingEnergy beta D)
          (fun (eta : D → IsingSpin) w => spinSign (eta w)) (fun eta => spinSign (eta v))
          (finiteIsingBrownianObservation B D t p) hs hn hp
          (fun eta w => by cases eta w <;> norm_num [spinSign])
  have hinner (t : ℝ) : (∫⁻ p, ENNReal.ofReal (R t p) ∂ρ) = ENNReal.ofReal (E t) :=
    (ofReal_integral_eq_lintegral_ofReal (hRI t) (Eventually.of_forall (hRpos t))).symm
  have hbound := hμ.integral_finiteIsingBrownianNormalizedEnergy_le hbeta ν hB hmB D hD v hT
  have hEI : Integrable E (volume.restrict (Ioc 0 T)) :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le hT).mp hbound.1
  change (∫⁻ t in Ioc 0 T, ∫⁻ p, ENNReal.ofReal (R t p) ∂ρ) ≤ _
  simp_rw [hinner]
  rw [← ofReal_integral_eq_lintegral_ofReal hEI
    (Eventually.of_forall fun t => integral_nonneg (hRpos t))]
  rw [← intervalIntegral.integral_of_le hT]
  exact ENNReal.ofReal_le_ofReal hbound.2.2.2

end Problem367

end

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Posterior_Limit
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory Filter
open scoped Topology

namespace Problem367

theorem tendsto_conditional_covariance_ae
    {Ω : Type*} [m : MeasurableSpace Ω] (μ : Measure Ω) [IsFiniteMeasure μ]
    (ℱ : Filtration ℕ m) (f g : Ω → ℝ) :
    ∀ᵐ ω ∂μ, Tendsto
      (fun n => (μ[fun x => f x * g x | ℱ n]) ω -
        (μ[f | ℱ n]) ω * (μ[g | ℱ n]) ω)
      atTop (𝓝 ((μ[fun x => f x * g x | ⨆ n, ℱ n]) ω -
        (μ[f | ⨆ n, ℱ n]) ω * (μ[g | ⨆ n, ℱ n]) ω)) := by
  filter_upwards [tendsto_ae_condExp (μ := μ) (ℱ := ℱ) (fun x => f x * g x),
    tendsto_ae_condExp (μ := μ) (ℱ := ℱ) f,
    tendsto_ae_condExp (μ := μ) (ℱ := ℱ) g] with ω hfg hf hg
  exact hfg.sub (hf.mul hg)

end Problem367

end

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Conditioning_CovarianceLimit
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory Filter
open scoped Topology

namespace Problem367

variable {Ω : Type*} [mΩ : MeasurableSpace Ω]

theorem tendsto_ae_posteriorCovariance (μ : Measure Ω) [IsFiniteMeasure μ]
    (F : Filtration ℕ mΩ) (f g : Ω → ℝ) :
    ∀ᵐ ω ∂μ, Tendsto (fun n => posteriorCovariance μ (F n) f g ω) atTop
      (𝓝 (posteriorCovariance μ (⨆ n, F n) f g ω)) := by
  exact tendsto_conditional_covariance_ae μ F f g

end Problem367

end

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Energy_NormalizedResponseLimit
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory Filter
open scoped Topology

namespace Problem367

variable {Ω : Type*} [mΩ : MeasurableSpace Ω]

theorem tendsto_ae_posteriorResponse
    (μ : Measure Ω) [IsFiniteMeasure μ] (F : Filtration ℕ mΩ)
    (f g : Ω → ℝ)
    (hinterior : ∀ᵐ ω ∂μ, μ[f | ⨆ n, F n] ω ∈ Set.Ioo (-1 : ℝ) 1) :
    ∀ᵐ ω ∂μ, Tendsto (fun n => posteriorResponse μ (F n) f g ω) atTop
      (𝓝 (posteriorResponse μ (⨆ n, F n) f g ω)) := by
  filter_upwards [tendsto_ae_posteriorCovariance μ F f g,
    tendsto_ae_condExp (μ := μ) (ℱ := F) f, hinterior] with ω hc hm hi
  have hden : 1 - (μ[f | ⨆ n, F n] ω) ^ 2 ≠ 0 := by
    have hsq : (μ[f | ⨆ n, F n] ω) ^ 2 < 1 := by
      nlinarith [mul_pos (show 0 < 1 - μ[f | ⨆ n, F n] ω by linarith [hi.2])
        (show 0 < 1 + μ[f | ⨆ n, F n] ω by linarith [hi.1])]
    exact ne_of_gt (sub_pos.mpr hsq)
  exact hc.div (tendsto_const_nhds.sub (hm.pow 2)) hden

end Problem367

end

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Energy_NormalizedResponseEnergy
attribute [-instance] _root_.OAI.Problem367.WienerSampler.pathMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory Filter
open scoped Topology ENNReal

namespace Problem367

variable {Ω : Type*} [mΩ : MeasurableSpace Ω]

theorem tsum_lintegral_sq_le_liminf_of_ae_tendsto
    {ι : Type*} [Countable ι] (μ : Measure Ω)
    {X : ℕ → ι → Ω → ℝ} {Y : ι → Ω → ℝ}
    (hX : ∀ n i, AEStronglyMeasurable (X n i) μ)
    (hlim : ∀ i, ∀ᵐ ω ∂μ, Tendsto (fun n => X n i ω) atTop (𝓝 (Y i ω))) :
    (∑' i, ∫⁻ ω, ENNReal.ofReal ((Y i ω) ^ 2) ∂μ) ≤
      liminf (fun n => ∑' i, ∫⁻ ω, ENNReal.ofReal ((X n i ω) ^ 2) ∂μ) atTop := by
  have hcoord (i : ι) : (∫⁻ ω, ENNReal.ofReal ((Y i ω) ^ 2) ∂μ) ≤
      liminf (fun n => ∫⁻ ω, ENNReal.ofReal ((X n i ω) ^ 2) ∂μ) atTop := by
    calc
      _ = ∫⁻ ω, liminf (fun n => ENNReal.ofReal ((X n i ω) ^ 2)) atTop ∂μ := by
        apply lintegral_congr_ae
        filter_upwards [hlim i] with ω hω
        exact (ENNReal.tendsto_ofReal (hω.pow 2)).liminf_eq.symm
      _ ≤ _ := lintegral_liminf_le' (fun n => ((hX n i).aemeasurable.pow_const 2).ennreal_ofReal)
  apply (ENNReal.tsum_le_tsum hcoord).trans
  let : MeasurableSpace ι := ⊤
  have hmeas (n : ℕ) : Measurable
      (fun i => ∫⁻ ω, ENNReal.ofReal ((X n i ω) ^ 2) ∂μ) := measurable_of_countable _
  simpa only [lintegral_count] using
    (lintegral_liminf_le (μ := Measure.count) hmeas)

theorem tsum_lintegral_sq_le_of_ae_tendsto
    {ι : Type*} [Countable ι] (μ : Measure Ω)
    {X : ℕ → ι → Ω → ℝ} {Y : ι → Ω → ℝ} {C : ℝ≥0∞}
    (hX : ∀ n i, AEStronglyMeasurable (X n i) μ)
    (hlim : ∀ i, ∀ᵐ ω ∂μ, Tendsto (fun n => X n i ω) atTop (𝓝 (Y i ω)))
    (henergy : ∀ n, (∑' i, ∫⁻ ω, ENNReal.ofReal ((X n i ω) ^ 2) ∂μ) ≤ C) :
    (∑' i, ∫⁻ ω, ENNReal.ofReal ((Y i ω) ^ 2) ∂μ) ≤ C :=
  (tsum_lintegral_sq_le_liminf_of_ae_tendsto μ hX hlim).trans
    (liminf_le_of_frequently_le' (Filter.Frequently.of_forall henergy))

theorem ae_summable_sq_of_tsum_lintegral_sq_ne_top
    {ι : Type*} [Countable ι] (μ : Measure Ω) {Y : ι → Ω → ℝ}
    (hY : ∀ i, AEStronglyMeasurable (Y i) μ)
    (henergy : (∑' i, ∫⁻ ω, ENNReal.ofReal ((Y i ω) ^ 2) ∂μ) ≠ ⊤) :
    ∀ᵐ ω ∂μ, Summable (fun i => (Y i ω) ^ 2) := by
  have hfinite : (∫⁻ ω, ∑' i, ENNReal.ofReal ((Y i ω) ^ 2) ∂μ) ≠ ⊤ := by
    rw [lintegral_tsum (fun i => ((hY i).aemeasurable.pow_const 2).ennreal_ofReal)]
    exact henergy
  filter_upwards [ae_lt_top' (AEMeasurable.tsum
    (fun i => ((hY i).aemeasurable.pow_const 2).ennreal_ofReal)) hfinite] with ω hω
  have hs : Summable (fun i => ((Y i ω) ^ 2).toNNReal) :=
    ENNReal.tsum_coe_ne_top_iff_summable.mp hω.ne
  have hs' := NNReal.summable_coe.mpr hs
  simpa only [Real.coe_toNNReal', max_eq_left (sq_nonneg _)] using hs'

theorem integrable_tsum_sq_of_tsum_lintegral_sq_ne_top
    {ι : Type*} [Countable ι] (μ : Measure Ω) {Y : ι → Ω → ℝ}
    (hY : ∀ i, AEStronglyMeasurable (Y i) μ)
    (henergy : (∑' i, ∫⁻ ω, ENNReal.ofReal ((Y i ω) ^ 2) ∂μ) ≠ ⊤) :
    Integrable (fun ω => ∑' i, (Y i ω) ^ 2) μ := by
  refine ⟨(AEMeasurable.tsum (fun i => (hY i).aemeasurable.pow_const 2)).aestronglyMeasurable, ?_⟩
  have heq : (∫⁻ ω, ‖∑' i, (Y i ω) ^ 2‖ₑ ∂μ) =
      ∑' i, ∫⁻ ω, ENNReal.ofReal ((Y i ω) ^ 2) ∂μ := by
    rw [← lintegral_tsum (fun i => ((hY i).aemeasurable.pow_const 2).ennreal_ofReal)]
    apply lintegral_congr_ae
    filter_upwards [ae_summable_sq_of_tsum_lintegral_sq_ne_top μ hY henergy] with ω hω
    rw [Real.enorm_of_nonneg (tsum_nonneg (fun i => sq_nonneg _))]
    exact ENNReal.ofReal_tsum_of_nonneg (fun i => sq_nonneg _) hω
  change (∫⁻ ω, ‖∑' i, (Y i ω) ^ 2‖ₑ ∂μ) < ⊤
  rw [heq]
  exact henergy.lt_top

theorem integral_tsum_sq_le_of_tsum_lintegral_sq_le
    {ι : Type*} [Countable ι] (μ : Measure Ω) {Y : ι → Ω → ℝ} {C : ℝ}
    (hY : ∀ i, AEStronglyMeasurable (Y i) μ) (hC : 0 ≤ C)
    (henergy : (∑' i, ∫⁻ ω, ENNReal.ofReal ((Y i ω) ^ 2) ∂μ) ≤ ENNReal.ofReal C) :
    Integrable (fun ω => ∑' i, (Y i ω) ^ 2) μ ∧
      (∫ ω, ∑' i, (Y i ω) ^ 2 ∂μ) ≤ C := by
  have hfinite := ne_top_of_le_ne_top ENNReal.ofReal_ne_top henergy
  have hint := integrable_tsum_sq_of_tsum_lintegral_sq_ne_top μ hY hfinite
  refine ⟨hint, ?_⟩
  have heq : ENNReal.ofReal (∫ ω, ∑' i, (Y i ω) ^ 2 ∂μ) =
      ∑' i, ∫⁻ ω, ENNReal.ofReal ((Y i ω) ^ 2) ∂μ := by
    rw [ofReal_integral_eq_lintegral_ofReal hint
      (Filter.Eventually.of_forall (fun ω => tsum_nonneg (fun i => sq_nonneg _)))]
    rw [← lintegral_tsum (fun i => ((hY i).aemeasurable.pow_const 2).ennreal_ofReal)]
    apply lintegral_congr_ae
    filter_upwards [ae_summable_sq_of_tsum_lintegral_sq_ne_top μ hY hfinite] with ω hω
    exact ENNReal.ofReal_tsum_of_nonneg (fun i => sq_nonneg _) hω
  exact (ENNReal.ofReal_le_ofReal_iff hC).mp (heq.trans_le henergy)

end Problem367

end

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Energy_ProgressiveIsingCovariance
attribute [-instance] _root_.OAI.Problem367.IsingConditionalCopyBounds.graphLaw_isProbabilityMeasure _root_.OAI.Problem367.IsingObservationFactor.copies_probability _root_.OAI.Problem367.IsingObservationFactor.kernel_markov _root_.OAI.Problem367.IsingObservationInnovation.innovationMap_observationLaw_probability _root_.OAI.Problem367.IsingObservationInnovation.observationLaw_probability _root_.OAI.Problem367.TreeKoopman.labelProbability _root_.OAI.Problem367.WienerSampler.pathMeasurableSpace _root_.OAI.Problem367.freeIsingMeasure_probability
attribute [-simp] _root_.OAI.Problem367.ConnectedHull.pathAssignment_path _root_.OAI.Problem367.ConnectedHull.path_last _root_.OAI.Problem367.ConnectedHull.path_zero _root_.OAI.Problem367.CutContinuationChannels.averageChannel_globalCone _root_.OAI.Problem367.CutContinuationChannels.continuationChannel_globalCone _root_.OAI.Problem367.FactorObservable.centeredSpinLp_coe _root_.OAI.Problem367.FiniteIsingSplit.splitEquiv_fst _root_.OAI.Problem367.FiniteIsingSplit.splitEquiv_snd _root_.OAI.Problem367.FinitePathGibbs.tailPartition_zero _root_.OAI.Problem367.GaussianTreeResponseNaturality.fieldEquiv_apply_image _root_.OAI.Problem367.IsingObservationInnovation.innovationMap_apply _root_.OAI.Problem367.IsingObservationInnovation.innovationMap_uniformObservation _root_.OAI.Problem367.IsingObservationInnovation.innovationMap_zero _root_.OAI.Problem367.IsingObservationInnovation.uniformObservation_relabel _root_.OAI.Problem367.IsingOrientedPath.attenuation_outward _root_.OAI.Problem367.IsingOrientedPath.endpoint_extensionAt _root_.OAI.Problem367.LocalSupportGeometry.prefixVertex_length _root_.OAI.Problem367.PathSideBranches.parent_sideVertex _root_.OAI.Problem367.PathSideBranches.restrictNoisyRegion_array _root_.OAI.Problem367.PathSideBranches.sideVertex_length _root_.OAI.Problem367.PathSideBranches.sideVertex_val _root_.OAI.Problem367.PosteriorChain.transition_spinMean _root_.OAI.Problem367.PosteriorChain.transition_sum _root_.OAI.Problem367.RootedBroadcast.flipBranchToComplement_val _root_.OAI.Problem367.RootedBroadcast.pos_spinMul _root_.OAI.Problem367.RootedBroadcast.prefixFlip_branchRoot _root_.OAI.Problem367.RootedBroadcast.prefixFlip_root _root_.OAI.Problem367.RootedBroadcast.prefixTreeAut_symm_branchRoot _root_.OAI.Problem367.RootedBroadcast.prefixTreeAut_symm_root _root_.OAI.Problem367.RootedBroadcast.spinMul_pos _root_.OAI.Problem367.RootedBroadcast.spinMul_self _root_.OAI.Problem367.TreeConeCoding.length_vertex _root_.OAI.Problem367.TreeConeCoding.vertex_nil _root_.OAI.Problem367.TreeConeCoding.vertex_val _root_.OAI.Problem367.TreeGibbsAut.spinEquiv_apply_image _root_.OAI.Problem367.TreeKoopman.centeredAverage_apply_coe _root_.OAI.Problem367.TreeKoopman.centeredAverage_pow_apply_coe _root_.OAI.Problem367.TreeKoopman.centeredGenerator_apply_coe _root_.OAI.Problem367.TreeKoopman.centeredGenerator_sq _root_.OAI.Problem367.TreeKoopman.generatorOperator_sq _root_.OAI.Problem367.TreeKoopman.reverseVertex_twice _root_.OAI.Problem367.TreeKoopman.wordRelabel_cons _root_.OAI.Problem367.TreeKoopman.wordRelabel_nil _root_.OAI.Problem367.TreeLawKoopman.centeredAverage_apply_coe _root_.OAI.Problem367.TreeLawKoopman.generatorOperator_sq _root_.OAI.Problem367.TreePathGibbs.vertexEquiv_val _root_.OAI.Problem367.branchColorAut_length _root_.OAI.Problem367.branchColorAut_singleton _root_.OAI.Problem367.branchColorAut_val _root_.OAI.Problem367.branchColorMap_symm_apply _root_.OAI.Problem367.colorPermAut_length _root_.OAI.Problem367.colorPermAut_nil _root_.OAI.Problem367.colorPermAut_val _root_.OAI.Problem367.colorPermMap_symm_apply _root_.OAI.Problem367.colorPermMap_val _root_.OAI.Problem367.connectedSpinEncode_apply_root _root_.OAI.Problem367.connectedSpinEquiv_apply _root_.OAI.Problem367.dropVertex_length _root_.OAI.Problem367.dropVertex_val _root_.OAI.Problem367.mem_rootComplementFinset _root_.OAI.Problem367.mem_rootComponentFinset _root_.OAI.Problem367.mem_rootComponentIndices _root_.OAI.Problem367.parentVertex_length _root_.OAI.Problem367.parentVertex_val _root_.OAI.Problem367.prefixColorAut_length _root_.OAI.Problem367.prefixColorAut_val _root_.OAI.Problem367.prefixColorMap_symm_apply _root_.OAI.Problem367.prefixFlip_twice _root_.OAI.Problem367.spinAgreementCode_eq_neg_iff _root_.OAI.Problem367.spinAgreementCode_eq_pos_iff _root_.OAI.Problem367.spinSign_flip _root_.OAI.Problem367.tsum_treeShell_radial _root_.OAI.Problem367.vertexSampler_relabel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory ProbabilityTheory Filter
open scoped NNReal Topology

namespace Problem367

open PlantedSymmetry

local instance progressiveIsingCovarianceNonemptySpin : Nonempty IsingSpin := ⟨.neg⟩

lemma pairExhaustion_monotone {d : ℕ} (v w : TreeVertex d) :
    Monotone (pairExhaustion v w) := by
  intro n m hnm
  exact connectedExhaustion_monotone v (Nat.add_le_add_right hnm _)

lemma pairExhaustion_connected {d : ℕ} (v w : TreeVertex d) (n : ℕ) :
    ConnectedFinset (pairExhaustion v w n) := connectedExhaustion_connected v _

lemma exists_mem_pairExhaustion {d : ℕ} (v w u : TreeVertex d) :
    ∃ n, u ∈ pairExhaustion v w n := by
  obtain ⟨n, hn⟩ := (eventually_mem_connectedExhaustion v u).exists
  exact ⟨n, connectedExhaustion_monotone v (Nat.le_add_right n _) hn⟩

lemma continuous_finiteGibbsPairMean {d : ℕ} (beta : ℝ) (v w : TreeVertex d) (n : ℕ) :
    Continuous (finiteGibbsPairMean beta v w n) := by
  apply (FinitePosterior.continuous_fieldMean _ _ _).comp
  exact continuous_pi (fun u => continuous_apply u.1)

lemma measurable_infiniteGibbsPairMean {d : ℕ} (beta : ℝ) (v w : TreeVertex d) :
    Measurable (infiniteGibbsPairMean beta v w) := by
  have hm : StronglyMeasurable (fun y =>
      limUnder atTop (fun n => finiteGibbsPairMean beta v w n y)) :=
    StronglyMeasurable.limUnder
      (fun n => (continuous_finiteGibbsPairMean beta v w n).measurable.stronglyMeasurable)
  exact measurable_const.max (measurable_const.min hm.measurable)

lemma spinSign_pair_norm_le_one {d : ℕ} (v w : TreeVertex d)
    (sigma : TreeVertex d → IsingSpin) : ‖spinSign (sigma v) * spinSign (sigma w)‖ ≤ 1 := by
  cases hv : sigma v <;> cases hw : sigma w <;> norm_num [spinSign, hv, hw]

theorem HasFreeIsingLaw.infiniteGibbsPairMean_eq_posterior {d : ℕ} {beta : ℝ}
    {μ : Measure (TreeVertex d → IsingSpin)}
    (hμ : HasFreeIsingLaw (Real.tanh beta) μ) (t : ℝ≥0) (v w : TreeVertex d) :
    (fun p => infiniteGibbsPairMean beta v w (observation t p)) =ᵐ[
        μ.prod (gaussianNoiseLaw (TreeVertex d) t)]
      (μ.prod (gaussianNoiseLaw (TreeVertex d) t))[
        fun p => spinSign (p.1 v) * spinSign (p.1 w) |
        observationSigma (TreeVertex d) t] := by
  let : IsProbabilityMeasure μ := hμ.isProbabilityMeasure
  have hce (n : ℕ) := hμ.finiteObservation_condExp (pairExhaustion v w n)
    (pairExhaustion_connected v w n) t
    (fun eta => spinSign (eta ⟨v, mem_pairExhaustion_left v w n⟩) *
      spinSign (eta ⟨w, mem_pairExhaustion_right v w n⟩))
  have hlim := tendsto_ae_condExp (μ := μ.prod (gaussianNoiseLaw (TreeVertex d) t))
    (ℱ := finiteObservationFiltration (pairExhaustion v w)
      (pairExhaustion_monotone v w) t)
    (fun p => spinSign (p.1 v) * spinSign (p.1 w))
  rw [finiteObservationFiltration_iSup (pairExhaustion v w)
    (pairExhaustion_monotone v w) (exists_mem_pairExhaustion v w) t] at hlim
  have hb := ae_bdd_norm_condExp_of_ae_bdd_norm
    (μ := μ.prod (gaussianNoiseLaw (TreeVertex d) t))
    (m := observationSigma (TreeVertex d) t)
    (Eventually.of_forall (fun p => spinSign_pair_norm_le_one v w p.1))
  filter_upwards [ae_all_iff.mpr hce, hlim, hb] with p hp hlim hb
  have hseq : Tendsto (fun n => finiteGibbsPairMean beta v w n (observation t p)) atTop
      (𝓝 ((μ.prod (gaussianNoiseLaw (TreeVertex d) t))[
        fun p => spinSign (p.1 v) * spinSign (p.1 w) |
        observationSigma (TreeVertex d) t] p)) := by
    convert hlim using 1
    all_goals try with_reducible_and_instances rfl
    ext n
    exact (hp n).symm
  change max (-1) (min 1 (limUnder atTop _)) = _
  rw [hseq.limUnder_eq, min_eq_right (abs_le.mp hb).2, max_eq_right (abs_le.mp hb).1]

lemma measurable_infiniteGibbsCovariance {d : ℕ} (beta : ℝ) (v w : TreeVertex d) :
    Measurable (infiniteGibbsCovariance beta v w) :=
  (measurable_infiniteGibbsPairMean beta v w).sub
    ((measurable_infiniteGibbsSpinMean beta v).mul
      (measurable_infiniteGibbsSpinMean beta w))

theorem HasFreeIsingLaw.infiniteGibbsCovariance_eq_posterior {d : ℕ} {beta : ℝ}
    {μ : Measure (TreeVertex d → IsingSpin)}
    (hμ : HasFreeIsingLaw (Real.tanh beta) μ) (t : ℝ≥0) (v w : TreeVertex d) :
    (fun p => infiniteGibbsCovariance beta v w (observation t p)) =ᵐ[
        μ.prod (gaussianNoiseLaw (TreeVertex d) t)]
      posteriorCovariance (μ.prod (gaussianNoiseLaw (TreeVertex d) t))
        (observationSigma (TreeVertex d) t)
        (fun p => spinSign (p.1 v)) (fun p => spinSign (p.1 w)) := by
  filter_upwards [hμ.infiniteGibbsPairMean_eq_posterior t v w,
    hμ.infiniteGibbsSpinMean_eq_posterior t v,
    hμ.infiniteGibbsSpinMean_eq_posterior t w] with p hp hv hw
  exact congrArg₂ (fun a b : ℝ => a - b) hp (congrArg₂ (· * ·) hv hw)

lemma measurable_infiniteGibbsResponse {d : ℕ} (beta : ℝ) (v w : TreeVertex d) :
    Measurable (infiniteGibbsResponse beta v w) :=
  (measurable_infiniteGibbsCovariance beta v w).div
    (measurable_const.sub ((measurable_infiniteGibbsSpinMean beta v).pow_const 2))

lemma measurable_infiniteGibbsResponseRow {d : ℕ} (beta : ℝ) (v : TreeVertex d) :
    Measurable (infiniteGibbsResponseRow beta v) := by
  exact (StronglyMeasurable.tsum (fun w =>
    ((measurable_infiniteGibbsResponse beta v w).pow_const 2).stronglyMeasurable)).measurable

theorem isStronglyProgressive_infiniteGibbsResponseRow
    {d : ℕ} {Ω : Type*} [mΩ : MeasurableSpace Ω]
    (F : Filtration ℝ≥0 mΩ) (beta : ℝ) (v : TreeVertex d)
    (X : TreeVertex d → ℝ≥0 → Ω → ℝ)
    (hX : ∀ i, IsStronglyProgressive F (X i)) :
    IsStronglyProgressive F
      (fun t omega => infiniteGibbsResponseRow beta v (fun i => X i t omega)) := by
  intro t
  let : MeasurableSpace Ω := F t
  exact ((measurable_infiniteGibbsResponseRow beta v).comp
    (Measurable.of_eval (fun vertex => (hX vertex t).measurable))).stronglyMeasurable

end Problem367

end

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Gaussian_TreeResponse
attribute [-instance] _root_.OAI.Problem367.IsingConditionalCopyBounds.graphLaw_isProbabilityMeasure _root_.OAI.Problem367.IsingObservationFactor.copies_probability _root_.OAI.Problem367.IsingObservationFactor.kernel_markov _root_.OAI.Problem367.IsingObservationInnovation.innovationMap_observationLaw_probability _root_.OAI.Problem367.IsingObservationInnovation.observationLaw_probability _root_.OAI.Problem367.TreeKoopman.labelProbability _root_.OAI.Problem367.WienerSampler.pathMeasurableSpace _root_.OAI.Problem367.freeIsingMeasure_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

namespace Problem367.GaussianTreeResponse

open GaussianTreeCovariance (gaussianContraction )

lemma measurable_response {d : ℕ} (beta : ℝ) (E : Finset (TreeVertex d))
    (r v : TreeVertex d) : Measurable (response beta E r v) := by
  classical
  unfold response TreePathResponse.response TreePathResponse.covariance
    TreePathResponse.mean LeafGibbs.covariance LeafGibbs.expectation GibbsLeaf.energy
  fun_prop

end Problem367.GaussianTreeResponse

end

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Gaussian_TreeResponsePosterior
attribute [-instance] _root_.OAI.Problem367.IsingConditionalCopyBounds.graphLaw_isProbabilityMeasure _root_.OAI.Problem367.IsingObservationFactor.copies_probability _root_.OAI.Problem367.IsingObservationFactor.kernel_markov _root_.OAI.Problem367.IsingObservationInnovation.innovationMap_observationLaw_probability _root_.OAI.Problem367.IsingObservationInnovation.observationLaw_probability _root_.OAI.Problem367.TreeKoopman.labelProbability _root_.OAI.Problem367.WienerSampler.pathMeasurableSpace _root_.OAI.Problem367.freeIsingMeasure_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory
open scoped NNReal

namespace Problem367

open PlantedSymmetry

theorem GibbsLeaf.energy_eq_fieldEnergy {d : ℕ} (beta : ℝ)
    (D : Finset (TreeVertex d)) (h : TreeVertex d → ℝ) (eta : D → IsingSpin) :
    GibbsLeaf.energy beta h D (extendFiniteSpin D eta) =
      FinitePosterior.fieldEnergy (finiteIsingEnergy beta D)
        (fun (eta : D → IsingSpin) v => spinSign (eta v)) (D.restrict h) eta := by
  classical
  have hsum : (∑ x ∈ D, h x * spinSign (extendFiniteSpin D eta x)) =
      ∑ x : D, h x * spinSign (eta x) := by
    rw [← Finset.sum_coe_sort D (fun x => h x * spinSign (extendFiniteSpin D eta x))]
    apply Finset.sum_congr rfl
    intro x _
    rw [extendFiniteSpin_apply D eta x]
  unfold GibbsLeaf.energy FinitePosterior.fieldEnergy finiteIsingEnergy
  rw [hsum]
  exact add_comm _ _

theorem GibbsLeaf.expectation_eq_fieldMean {d : ℕ} (beta : ℝ)
    (D : Finset (TreeVertex d)) (h : TreeVertex d → ℝ)
    (q : (D → IsingSpin) → ℝ) :
    LeafGibbs.expectation
      (fun eta => GibbsLeaf.energy beta h D (extendFiniteSpin D eta)) q =
      FinitePosterior.fieldMean (finiteIsingEnergy beta D)
        (fun (eta : D → IsingSpin) v => spinSign (eta v)) q (D.restrict h) := by
  simp only [LeafGibbs.expectation, FinitePosterior.fieldMean,
    GibbsLeaf.energy_eq_fieldEnergy]

theorem HasFreeIsingLaw.finiteObservation_condExp_treeMean {d : ℕ} {beta : ℝ}
    {μ : Measure (TreeVertex d → IsingSpin)}
    (hμ : HasFreeIsingLaw (Real.tanh beta) μ)
    (D : Finset (TreeVertex d)) (hD : ConnectedFinset D) (t : ℝ≥0) (v : D) :
    (μ.prod (gaussianNoiseLaw (TreeVertex d) t))[
      fun p => spinSign (p.1 v.1) |
      MeasurableSpace.comap (finiteObservation D t) inferInstance] =ᵐ[
        μ.prod (gaussianNoiseLaw (TreeVertex d) t)]
      fun p => TreePathResponse.mean beta (PlantedSymmetry.observation t p) D v.1 := by
  have heq := hμ.finiteObservation_condExp D hD t (fun eta => spinSign (eta v))
  filter_upwards [heq] with p hp
  change (μ.prod (gaussianNoiseLaw (TreeVertex d) t))[
    fun p => spinSign (p.1 v.1) |
    MeasurableSpace.comap (finiteObservation D t) inferInstance] p = _ at hp
  rw [hp]
  simp only [TreePathResponse.mean, extendFiniteSpin_apply D _ v,
    GibbsLeaf.expectation_eq_fieldMean]
  rfl

theorem HasFreeIsingLaw.finiteObservation_normalizedResponse {d : ℕ} {beta : ℝ}
    {μ : Measure (TreeVertex d → IsingSpin)}
    (hμ : HasFreeIsingLaw (Real.tanh beta) μ)
    (D : Finset (TreeVertex d)) (hD : ConnectedFinset D) (t : ℝ≥0) (u v : D) :
    let P := μ.prod (gaussianNoiseLaw (TreeVertex d) t)
    let m := MeasurableSpace.comap (finiteObservation D t) inferInstance
    (fun p => ((P[fun q => spinSign (q.1 u.1) * spinSign (q.1 v.1) | m]) p -
      (P[fun q => spinSign (q.1 u.1) | m]) p *
      (P[fun q => spinSign (q.1 v.1) | m]) p) /
      (1 - (P[fun q => spinSign (q.1 u.1) | m]) p ^ 2)) =ᵐ[P]
      fun p => GaussianTreeResponse.response beta D u.1 v.1
        (PlantedSymmetry.observation t p) := by
  dsimp only
  have hpair := hμ.finiteObservation_condExp D hD t
    (fun eta => spinSign (eta u) * spinSign (eta v))
  filter_upwards [hpair, hμ.finiteObservation_condExp_treeMean D hD t u,
    hμ.finiteObservation_condExp_treeMean D hD t v] with p hp hu hv
  change (μ.prod (gaussianNoiseLaw (TreeVertex d) t))[
    fun q => spinSign (q.1 u.1) * spinSign (q.1 v.1) |
    MeasurableSpace.comap (finiteObservation D t) inferInstance] p = _ at hp
  rw [hp, hu, hv]
  unfold GaussianTreeResponse.response TreePathResponse.response TreePathResponse.covariance
    LeafGibbs.covariance
  simp only [extendFiniteSpin_apply D _ u, extendFiniteSpin_apply D _ v,
    GibbsLeaf.expectation_eq_fieldMean, TreePathResponse.mean]
  rfl

end Problem367

end

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Posterior_NormalizedPosteriorLimit
attribute [-instance] _root_.OAI.Problem367.IsingConditionalCopyBounds.graphLaw_isProbabilityMeasure _root_.OAI.Problem367.IsingObservationFactor.copies_probability _root_.OAI.Problem367.IsingObservationFactor.kernel_markov _root_.OAI.Problem367.IsingObservationInnovation.innovationMap_observationLaw_probability _root_.OAI.Problem367.IsingObservationInnovation.observationLaw_probability _root_.OAI.Problem367.TreeKoopman.labelProbability _root_.OAI.Problem367.WienerSampler.pathMeasurableSpace _root_.OAI.Problem367.freeIsingMeasure_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory Filter
open scoped Topology ENNReal NNReal

namespace Problem367

variable {Ω : Type*} [mΩ : MeasurableSpace Ω]

section Gaussian

open PlantedSymmetry

theorem HasFreeIsingLaw.gaussian_posteriorResponse_tendsto_ae
    {d : ℕ} {beta : ℝ} {μ : Measure (TreeVertex d → IsingSpin)}
    (hμ : HasFreeIsingLaw (Real.tanh beta) μ) (hbeta : 0 ≤ beta)
    (D : ℕ → Finset (TreeVertex d)) (hD : Monotone D)
    (hex : ∀ w, ∃ n, w ∈ D n) (t : ℝ≥0) (v w : TreeVertex d) :
    ∀ᵐ p ∂μ.prod (gaussianNoiseLaw (TreeVertex d) t),
      Tendsto (fun n => posteriorResponse (μ.prod (gaussianNoiseLaw (TreeVertex d) t))
        (MeasurableSpace.comap (finiteObservation (D n) t) inferInstance)
        (fun p => spinSign (p.1 v)) (fun p => spinSign (p.1 w)) p) atTop
        (𝓝 (gaussianPosteriorResponse μ t v w p)) := by
  let : IsProbabilityMeasure μ := hμ.isProbabilityMeasure
  have hi := (hμ.gaussian_posterior_field_bound hbeta t v).mono (fun _ h => h.1)
  have hi' : ∀ᵐ p ∂μ.prod (gaussianNoiseLaw (TreeVertex d) t),
      (μ.prod (gaussianNoiseLaw (TreeVertex d) t))[
        fun p => spinSign (p.1 v) | ⨆ n, finiteObservationFiltration D hD t n] p ∈
        Set.Ioo (-1 : ℝ) 1 := by
    rw [finiteObservationFiltration_iSup D hD hex t]
    exact hi
  have h := tendsto_ae_posteriorResponse
    (μ.prod (gaussianNoiseLaw (TreeVertex d) t)) (finiteObservationFiltration D hD t)
    (fun p => spinSign (p.1 v)) (fun p => spinSign (p.1 w)) hi'
  rw [finiteObservationFiltration_iSup D hD hex t] at h
  exact h

end Gaussian

end Problem367

end

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Posterior_NormalizedPosteriorRowConvergence
attribute [-instance] _root_.OAI.Problem367.IsingConditionalCopyBounds.graphLaw_isProbabilityMeasure _root_.OAI.Problem367.IsingObservationFactor.copies_probability _root_.OAI.Problem367.IsingObservationFactor.kernel_markov _root_.OAI.Problem367.IsingObservationInnovation.innovationMap_observationLaw_probability _root_.OAI.Problem367.IsingObservationInnovation.observationLaw_probability _root_.OAI.Problem367.TreeKoopman.labelProbability _root_.OAI.Problem367.WienerSampler.pathMeasurableSpace _root_.OAI.Problem367.freeIsingMeasure_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory ProbabilityTheory Filter
open scoped Topology NNReal

namespace Problem367

open PlantedSymmetry GaussianTreeResponse GaussianTreeCovariance

theorem HasFreeIsingLaw.observedRow_eq_posteriorResponse
    {d : ℕ} {beta : ℝ} {μ : Measure (TreeVertex d → IsingSpin)}
    (hμ : HasFreeIsingLaw (Real.tanh beta) μ)
    (D : Finset (TreeVertex d)) (hD : ConnectedFinset D) (r v : TreeVertex d)
    (hr : r ∈ D) (hv : v ∈ D) (t : ℝ≥0) :
    observedRow beta D r t v =ᵐ[μ.prod (gaussianNoiseLaw (TreeVertex d) t)]
      posteriorResponse (μ.prod (gaussianNoiseLaw (TreeVertex d) t))
        (MeasurableSpace.comap (finiteObservation D t) inferInstance)
        (fun p => spinSign (p.1 r)) (fun p => spinSign (p.1 v)) := by
  have h := hμ.finiteObservation_normalizedResponse D hD t ⟨r, hr⟩ ⟨v, hv⟩
  filter_upwards [h] with p hp
  simpa only [observedRow, ite_eq_left hv, posteriorResponse, posteriorCovariance] using hp.symm

theorem HasFreeIsingLaw.observedRow_tendsto_ae
    {d : ℕ} {beta : ℝ} {μ : Measure (TreeVertex d → IsingSpin)}
    (hμ : HasFreeIsingLaw (Real.tanh beta) μ) (hbeta : 0 ≤ beta)
    (D : ℕ → Finset (TreeVertex d)) (hD : Monotone D)
    (hconn : ∀ n, ConnectedFinset (D n)) (r : TreeVertex d)
    (hr : ∀ n, r ∈ D n) (hex : ∀ v, ∃ n, v ∈ D n) (t : ℝ≥0) (v : TreeVertex d) :
    ∀ᵐ p ∂μ.prod (gaussianNoiseLaw (TreeVertex d) t),
      Tendsto (fun n => observedRow beta (D n) r t v p) atTop
        (𝓝 (gaussianPosteriorResponse μ t r v p)) := by
  have heq (n : ℕ) : ∀ᵐ p ∂μ.prod (gaussianNoiseLaw (TreeVertex d) t),
      v ∈ D n → observedRow beta (D n) r t v p =
        posteriorResponse (μ.prod (gaussianNoiseLaw (TreeVertex d) t))
          (MeasurableSpace.comap (finiteObservation (D n) t) inferInstance)
          (fun p => spinSign (p.1 r)) (fun p => spinSign (p.1 v)) p := by
    by_cases hv : v ∈ D n
    · exact (hμ.observedRow_eq_posteriorResponse (D n) (hconn n) r v (hr n) hv t).mono
        (fun p hp _ => hp)
    · exact Filter.Eventually.of_forall (fun _ hv' => (hv hv').elim)
  obtain ⟨N, hN⟩ := hex v
  have hmem : ∀ᶠ n in atTop, v ∈ D n :=
    eventually_atTop.2 ⟨N, fun n hn => hD hn hN⟩
  filter_upwards [ae_all_iff.mpr heq,
    hμ.gaussian_posteriorResponse_tendsto_ae hbeta D hD hex t r v] with p hp hlim
  exact hlim.congr' (hmem.mono (fun n hn => (hp n hn).symm))

end Problem367

end

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Energy_NormalizedResponseTime
attribute [-instance] _root_.OAI.Problem367.IsingConditionalCopyBounds.graphLaw_isProbabilityMeasure _root_.OAI.Problem367.IsingObservationFactor.copies_probability _root_.OAI.Problem367.IsingObservationFactor.kernel_markov _root_.OAI.Problem367.IsingObservationInnovation.innovationMap_observationLaw_probability _root_.OAI.Problem367.IsingObservationInnovation.observationLaw_probability _root_.OAI.Problem367.TreeKoopman.labelProbability _root_.OAI.Problem367.WienerSampler.pathMeasurableSpace _root_.OAI.Problem367.freeIsingMeasure_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory Filter
open scoped NNReal Topology

namespace Problem367.NormalizedResponseTime

open PlantedSymmetry GaussianTreeResponse

lemma infiniteGibbsResponse_eq_gaussianPosteriorResponse
    {d : ℕ} {beta : ℝ} {μ : Measure (TreeVertex d → IsingSpin)}
    (hμ : HasFreeIsingLaw (Real.tanh beta) μ) (t : ℝ≥0) (v w : TreeVertex d) :
    (fun p => infiniteGibbsResponse beta v w (observation t p)) =ᵐ[
      μ.prod (gaussianNoiseLaw (TreeVertex d) t)] gaussianPosteriorResponse μ t v w := by
  filter_upwards [hμ.infiniteGibbsCovariance_eq_posterior t v w,
    hμ.infiniteGibbsSpinMean_eq_posterior t v] with p hc hm
  unfold infiniteGibbsResponse gaussianPosteriorResponse posteriorResponse
  rw [hc, hm]
  rfl

theorem observedRow_tendsto_ae_gaussian
    {d : ℕ} {beta : ℝ} {μ : Measure (TreeVertex d → IsingSpin)}
    (hμ : HasFreeIsingLaw (Real.tanh beta) μ) (hbeta : 0 ≤ beta)
    (D : ℕ → Finset (TreeVertex d)) (hD : Monotone D)
    (hconn : ∀ n, ConnectedFinset (D n)) (hex : ∀ u, ∃ n, u ∈ D n)
    (v : TreeVertex d) (hv : ∀ n, v ∈ D n) (w : TreeVertex d) (t : ℝ≥0) :
    ∀ᵐ p ∂μ.prod (gaussianNoiseLaw (TreeVertex d) t),
      Tendsto (fun n => observedRow beta (D n) v t w p) atTop
        (𝓝 (infiniteGibbsResponse beta v w (observation t p))) := by
  filter_upwards [hμ.observedRow_tendsto_ae hbeta D hD hconn v hv hex t w,
    infiniteGibbsResponse_eq_gaussianPosteriorResponse hμ t v w] with p hlim hinf
  rw [hinf]
  exact hlim

theorem observedRow_tendsto_ae_brownian
    {d : ℕ} {beta : ℝ} {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure (TreeVertex d → IsingSpin)}
    (hμ : HasFreeIsingLaw (Real.tanh beta) μ) (hbeta : 0 ≤ beta)
    (ν : TreeVertex d → Measure Ω)
    {B : TreeVertex d → ℝ≥0 → Ω → ℝ}
    (hB : ∀ i, IsPreBrownianReal (B i) (ν i))
    (hmB : ∀ i t, Measurable (B i t))
    (D : ℕ → Finset (TreeVertex d)) (hD : Monotone D)
    (hconn : ∀ n, ConnectedFinset (D n)) (hex : ∀ u, ∃ n, u ∈ D n)
    (v : TreeVertex d) (hv : ∀ n, v ∈ D n) (w : TreeVertex d) (t : ℝ≥0) :
    ∀ᵐ p ∂μ.prod (Measure.infinitePi ν),
      Tendsto (fun n => observedRow beta (D n) v t w
        (p.1, fun i => B i t (p.2 i))) atTop
        (𝓝 (infiniteGibbsResponse beta v w
          (fun i => (t : ℝ) * spinSign (p.1 i) + B i t (p.2 i)))) := by
  let : IsProbabilityMeasure μ := hμ.isProbabilityMeasure
  have (vertex : TreeVertex d) : IsProbabilityMeasure (ν vertex) :=
    (hB vertex).isGaussianProcess.isProbabilityMeasure
  let T : ((TreeVertex d → IsingSpin) × (TreeVertex d → Ω)) →
      (TreeVertex d → IsingSpin) × (TreeVertex d → ℝ) :=
    Prod.map id (fun omega i => B i t (omega i))
  have hT : MeasurePreserving T (μ.prod (Measure.infinitePi ν))
      (μ.prod (gaussianNoiseLaw (TreeVertex d) t)) :=
    (MeasurePreserving.id μ).prod (brownian_array_eval_measurePreserving ν hB hmB t)
  have h := observedRow_tendsto_ae_gaussian hμ hbeta D hD hconn hex v hv w t
  rw [← hT.map_eq] at h
  exact ae_of_ae_map hT.measurable.aemeasurable h

end Problem367.NormalizedResponseTime

end

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Energy_NormalizedInfiniteTimeEnergy
attribute [-instance] _root_.OAI.Problem367.IsingConditionalCopyBounds.graphLaw_isProbabilityMeasure _root_.OAI.Problem367.IsingObservationFactor.copies_probability _root_.OAI.Problem367.IsingObservationFactor.kernel_markov _root_.OAI.Problem367.IsingObservationInnovation.innovationMap_observationLaw_probability _root_.OAI.Problem367.IsingObservationInnovation.observationLaw_probability _root_.OAI.Problem367.TreeKoopman.labelProbability _root_.OAI.Problem367.WienerSampler.pathMeasurableSpace _root_.OAI.Problem367.freeIsingMeasure_probability
attribute [-simp] _root_.OAI.Problem367.CutContinuationChannels.averageChannel_globalCone _root_.OAI.Problem367.CutContinuationChannels.continuationChannel_globalCone _root_.OAI.Problem367.FactorObservable.centeredSpinLp_coe _root_.OAI.Problem367.FiniteIsingSplit.splitEquiv_fst _root_.OAI.Problem367.FiniteIsingSplit.splitEquiv_snd _root_.OAI.Problem367.GaussianTreeResponseNaturality.fieldEquiv_apply_image _root_.OAI.Problem367.IsingObservationInnovation.innovationMap_apply _root_.OAI.Problem367.IsingObservationInnovation.innovationMap_uniformObservation _root_.OAI.Problem367.IsingObservationInnovation.innovationMap_zero _root_.OAI.Problem367.IsingObservationInnovation.uniformObservation_relabel _root_.OAI.Problem367.IsingOrientedPath.attenuation_outward _root_.OAI.Problem367.IsingOrientedPath.endpoint_extensionAt _root_.OAI.Problem367.LocalSupportGeometry.prefixVertex_length _root_.OAI.Problem367.PathSideBranches.parent_sideVertex _root_.OAI.Problem367.PathSideBranches.restrictNoisyRegion_array _root_.OAI.Problem367.PathSideBranches.sideVertex_length _root_.OAI.Problem367.PathSideBranches.sideVertex_val _root_.OAI.Problem367.RootedBroadcast.flipBranchToComplement_val _root_.OAI.Problem367.RootedBroadcast.pos_spinMul _root_.OAI.Problem367.RootedBroadcast.prefixFlip_branchRoot _root_.OAI.Problem367.RootedBroadcast.prefixFlip_root _root_.OAI.Problem367.RootedBroadcast.prefixTreeAut_symm_branchRoot _root_.OAI.Problem367.RootedBroadcast.prefixTreeAut_symm_root _root_.OAI.Problem367.RootedBroadcast.spinMul_pos _root_.OAI.Problem367.RootedBroadcast.spinMul_self _root_.OAI.Problem367.TreeConeCoding.length_vertex _root_.OAI.Problem367.TreeConeCoding.vertex_nil _root_.OAI.Problem367.TreeConeCoding.vertex_val _root_.OAI.Problem367.TreeKoopman.centeredAverage_apply_coe _root_.OAI.Problem367.TreeKoopman.centeredAverage_pow_apply_coe _root_.OAI.Problem367.TreeKoopman.centeredGenerator_apply_coe _root_.OAI.Problem367.TreeKoopman.centeredGenerator_sq _root_.OAI.Problem367.TreeKoopman.generatorOperator_sq _root_.OAI.Problem367.TreeKoopman.reverseVertex_twice _root_.OAI.Problem367.TreeKoopman.wordRelabel_cons _root_.OAI.Problem367.TreeKoopman.wordRelabel_nil _root_.OAI.Problem367.TreeLawKoopman.centeredAverage_apply_coe _root_.OAI.Problem367.TreeLawKoopman.generatorOperator_sq _root_.OAI.Problem367.branchColorAut_length _root_.OAI.Problem367.branchColorAut_singleton _root_.OAI.Problem367.branchColorAut_val _root_.OAI.Problem367.branchColorMap_symm_apply _root_.OAI.Problem367.colorPermAut_length _root_.OAI.Problem367.colorPermAut_nil _root_.OAI.Problem367.colorPermAut_val _root_.OAI.Problem367.colorPermMap_symm_apply _root_.OAI.Problem367.colorPermMap_val _root_.OAI.Problem367.connectedSpinEncode_apply_root _root_.OAI.Problem367.connectedSpinEquiv_apply _root_.OAI.Problem367.dropVertex_length _root_.OAI.Problem367.dropVertex_val _root_.OAI.Problem367.mem_rootComplementFinset _root_.OAI.Problem367.mem_rootComponentFinset _root_.OAI.Problem367.mem_rootComponentIndices _root_.OAI.Problem367.prefixColorAut_length _root_.OAI.Problem367.prefixColorAut_val _root_.OAI.Problem367.prefixColorMap_symm_apply _root_.OAI.Problem367.spinAgreementCode_eq_neg_iff _root_.OAI.Problem367.spinAgreementCode_eq_pos_iff _root_.OAI.Problem367.spinSign_flip _root_.OAI.Problem367.vertexSampler_relabel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal Topology

namespace Problem367.NormalizedInfiniteTimeEnergy

open GaussianTreeResponse

variable {d : ℕ} {Ω : Type*} [MeasurableSpace Ω]

lemma measurable_observation
    {B : TreeVertex d → ℝ≥0 → Ω → ℝ}
    (hjoint : ∀ i, Measurable (fun z : ℝ≥0 × Ω => B i z.1 z.2)) :
    Measurable (fun q : ℝ × ((TreeVertex d → IsingSpin) × (TreeVertex d → Ω)) =>
      observation B q.1 q.2) := by
  apply Measurable.of_eval
  intro i
  exact (measurable_fst.mul ((measurable_of_finite spinSign).comp
    ((measurable_pi_apply i).comp (measurable_fst.comp measurable_snd)))).add
    ((hjoint i).comp ((measurable_real_toNNReal.comp measurable_fst).prodMk
      ((measurable_pi_apply i).comp (measurable_snd.comp measurable_snd))))

lemma measurable_finiteRow (beta : ℝ) (D : Finset (TreeVertex d))
    (v : TreeVertex d) {B : TreeVertex d → ℝ≥0 → Ω → ℝ}
    (hjoint : ∀ i, Measurable (fun z : ℝ≥0 × Ω => B i z.1 z.2))
    (w : TreeVertex d) : Measurable (finiteRow beta D v B w) := by
  classical
  by_cases hw : w ∈ D
  · unfold finiteRow
    simp only [observedRow, ite_eq_left hw]
    exact (measurable_response beta D v w).comp (measurable_observation hjoint)
  · unfold finiteRow
    simp only [observedRow, ite_eq_right hw]
    exact measurable_const

lemma measurable_infiniteRow (beta : ℝ) (v : TreeVertex d)
    {B : TreeVertex d → ℝ≥0 → Ω → ℝ}
    (hjoint : ∀ i, Measurable (fun z : ℝ≥0 × Ω => B i z.1 z.2))
    (w : TreeVertex d) : Measurable (infiniteRow beta v B w) :=
  (measurable_infiniteGibbsResponse beta v w).comp (measurable_observation hjoint)

omit [MeasurableSpace Ω] in

lemma finiteRow_eq_normalizedCovariance (beta : ℝ) (D : Finset (TreeVertex d))
    (v w : D) (B : TreeVertex d → ℝ≥0 → Ω → ℝ) (t : ℝ)
    (p : (TreeVertex d → IsingSpin) × (TreeVertex d → Ω)) :
    finiteRow beta D v B w (t, p) =
      finiteIsingBrownianNormalizedCovariance beta D v w B t p := by
  classical
  simp only [finiteRow, observedRow, ite_eq_left w.property]
  unfold response TreePathResponse.response TreePathResponse.covariance
    LeafGibbs.covariance TreePathResponse.mean
    finiteIsingBrownianNormalizedCovariance FinitePosterior.normalizedFieldCovariance
    FinitePosterior.fieldCovariance
  simp only [extendFiniteSpin_apply D _ v, extendFiniteSpin_apply D _ w,
    GibbsLeaf.expectation_eq_fieldMean]
  rfl

omit [MeasurableSpace Ω] in
lemma finiteRow_eq_zero (beta : ℝ) (D : Finset (TreeVertex d)) (v w : TreeVertex d)
    (B : TreeVertex d → ℝ≥0 → Ω → ℝ) (hw : w ∉ D)
    (q : ℝ × ((TreeVertex d → IsingSpin) × (TreeVertex d → Ω))) :
    finiteRow beta D v B w q = 0 := by
  simp [finiteRow, observedRow, hw]

omit [MeasurableSpace Ω] in
lemma tsum_finiteRow_sq (beta : ℝ) (D : Finset (TreeVertex d)) (v : D)
    (B : TreeVertex d → ℝ≥0 → Ω → ℝ)
    (q : ℝ × ((TreeVertex d → IsingSpin) × (TreeVertex d → Ω))) :
    (∑' w, ENNReal.ofReal (finiteRow beta D v B w q ^ 2)) =
      ENNReal.ofReal (∑ w : D,
        finiteIsingBrownianNormalizedCovariance beta D v w B q.1 q.2 ^ 2) := by
  classical
  rcases q with ⟨t, p⟩
  rw [tsum_eq_sum (s := D)]
  · rw [← Finset.sum_coe_sort D]
    simp_rw [finiteRow_eq_normalizedCovariance]
    exact (ENNReal.ofReal_sum_of_nonneg (fun _ _ => sq_nonneg _)).symm
  · intro w hw
    simp [finiteRow_eq_zero beta D v w B hw]

theorem finiteRow_tendsto_ae
    {beta : ℝ} {μ : Measure (TreeVertex d → IsingSpin)}
    (hμ : HasFreeIsingLaw (Real.tanh beta) μ) (hbeta : 0 ≤ beta)
    (ν : TreeVertex d → Measure Ω) {B : TreeVertex d → ℝ≥0 → Ω → ℝ}
    (hB : ∀ i, IsPreBrownianReal (B i) (ν i))
    (hmB : ∀ i t, Measurable (B i t))
    (hjoint : ∀ i, Measurable (fun z : ℝ≥0 × Ω => B i z.1 z.2))
    (D : ℕ → Finset (TreeVertex d)) (hD : Monotone D)
    (hconn : ∀ n, ConnectedFinset (D n)) (hex : ∀ u, ∃ n, u ∈ D n)
    (v : TreeVertex d) (hv : ∀ n, v ∈ D n) (w : TreeVertex d) (T : ℝ) :
    ∀ᵐ q ∂(volume.restrict (Ioc 0 T)).prod (μ.prod (Measure.infinitePi ν)),
      Tendsto (fun n => finiteRow beta (D n) v B w q) atTop
        (𝓝 (infiniteRow beta v B w q)) := by
  let : IsProbabilityMeasure μ := hμ.isProbabilityMeasure
  have (vertex : TreeVertex d) : IsProbabilityMeasure (ν vertex) :=
    (hB vertex).isGaussianProcess.isProbabilityMeasure
  apply (Measure.ae_prod_iff_ae_ae (measurableSet_tendsto_fun
    (fun n => measurable_finiteRow beta (D n) v hjoint w)
    (measurable_infiniteRow beta v hjoint w))).mpr
  filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
  have h := NormalizedResponseTime.observedRow_tendsto_ae_brownian
    hμ hbeta ν hB hmB D hD hconn hex v hv w t.toNNReal
  simpa only [finiteRow, infiniteRow, Real.coe_toNNReal t ht.1.le] using h

theorem lintegral_infiniteRow_le_of_finite
    {beta : ℝ} {μ : Measure (TreeVertex d → IsingSpin)}
    (hμ : HasFreeIsingLaw (Real.tanh beta) μ) (hbeta : 0 ≤ beta)
    (ν : TreeVertex d → Measure Ω) {B : TreeVertex d → ℝ≥0 → Ω → ℝ}
    (hB : ∀ i, IsPreBrownianReal (B i) (ν i))
    (hmB : ∀ i t, Measurable (B i t))
    (hjoint : ∀ i, Measurable (fun z : ℝ≥0 × Ω => B i z.1 z.2))
    (D : ℕ → Finset (TreeVertex d)) (hD : Monotone D)
    (hconn : ∀ n, ConnectedFinset (D n)) (hex : ∀ u, ∃ n, u ∈ D n)
    (v : TreeVertex d) (hv : ∀ n, v ∈ D n) (T : ℝ) {K : ℝ≥0∞}
    (henergy : ∀ n,
      (∫⁻ q : ℝ × ((TreeVertex d → IsingSpin) × (TreeVertex d → Ω)),
        ∑ u : D n, ENNReal.ofReal
          (finiteIsingBrownianNormalizedCovariance beta (D n) ⟨v, hv n⟩ u B q.1 q.2 ^ 2)
        ∂(volume.restrict (Ioc 0 T)).prod (μ.prod (Measure.infinitePi ν))) ≤ K) :
    (∫⁻ q, ∑' w, ENNReal.ofReal (infiniteRow beta v B w q ^ 2)
      ∂(volume.restrict (Ioc 0 T)).prod (μ.prod (Measure.infinitePi ν))) ≤ K := by
  let : IsProbabilityMeasure μ := hμ.isProbabilityMeasure
  have (vertex : TreeVertex d) : IsProbabilityMeasure (ν vertex) :=
    (hB vertex).isGaussianProcess.isProbabilityMeasure
  let P := (volume.restrict (Ioc 0 T)).prod (μ.prod (Measure.infinitePi ν))
  rw [lintegral_tsum (fun w =>
    ((measurable_infiniteRow beta v hjoint w).pow_const 2).ennreal_ofReal.aemeasurable)]
  apply tsum_lintegral_sq_le_of_ae_tendsto P
    (fun n w => (measurable_finiteRow beta (D n) v hjoint w).aestronglyMeasurable)
    (fun w => finiteRow_tendsto_ae hμ hbeta ν hB hmB hjoint D hD hconn hex v hv w T)
  intro n
  rw [← lintegral_tsum (fun w =>
    ((measurable_finiteRow beta (D n) v hjoint w).pow_const 2).ennreal_ofReal.aemeasurable)]
  calc
    _ = ∫⁻ q : ℝ × ((TreeVertex d → IsingSpin) × (TreeVertex d → Ω)),
        ∑ u : D n, ENNReal.ofReal
          (finiteIsingBrownianNormalizedCovariance beta (D n) ⟨v, hv n⟩ u B q.1 q.2 ^ 2)
        ∂P := by
      apply lintegral_congr
      intro q
      rw [tsum_finiteRow_sq beta (D n) ⟨v, hv n⟩ B q]
      exact ENNReal.ofReal_sum_of_nonneg (fun _ _ => sq_nonneg _)
    _ ≤ K := henergy n

theorem lintegral_infiniteRow_le
    {beta : ℝ} {μ : Measure (TreeVertex d → IsingSpin)}
    (hμ : HasFreeIsingLaw (Real.tanh beta) μ) (hbeta : 0 ≤ beta)
    (ν : TreeVertex d → Measure Ω) {B : TreeVertex d → ℝ≥0 → Ω → ℝ}
    (hB : ∀ i, IsPreBrownianReal (B i) (ν i))
    (hmB : ∀ i t, Measurable (B i t))
    (hjoint : ∀ i, Measurable (fun z : ℝ≥0 × Ω => B i z.1 z.2))
    (v : TreeVertex d) {T : ℝ} (hT : 0 ≤ T) :
    (∫⁻ q, ∑' w, ENNReal.ofReal (infiniteRow beta v B w q ^ 2)
      ∂(volume.restrict (Ioc 0 T)).prod (μ.prod (Measure.infinitePi ν))) ≤
      ENNReal.ofReal (2 * ((d : ℝ) * beta + T + Real.sqrt T)) := by
  let : IsProbabilityMeasure μ := hμ.isProbabilityMeasure
  have (vertex : TreeVertex d) : IsProbabilityMeasure (ν vertex) :=
    (hB vertex).isGaussianProcess.isProbabilityMeasure
  apply lintegral_infiniteRow_le_of_finite hμ hbeta ν hB hmB hjoint
    (connectedExhaustion v) (connectedExhaustion_monotone v)
    (connectedExhaustion_connected v)
    (fun u => (eventually_mem_connectedExhaustion v u).exists)
    v (mem_connectedExhaustion v) T
  intro n
  let D := connectedExhaustion v n
  let r : D := ⟨v, mem_connectedExhaustion v n⟩
  let R : ℝ × ((TreeVertex d → IsingSpin) × (TreeVertex d → Ω)) → ℝ≥0∞ :=
    fun q => ENNReal.ofReal (∑ u : D,
      finiteIsingBrownianNormalizedCovariance beta D r u B q.1 q.2 ^ 2)
  have hR : Measurable R := by
    have heq : R = fun q => ∑' w, ENNReal.ofReal (finiteRow beta D v B w q ^ 2) := by
      funext q
      exact (tsum_finiteRow_sq beta D r B q).symm
    rw [heq]
    exact Measurable.tsum (fun w =>
      ((measurable_finiteRow beta D v hjoint w).pow_const 2).ennreal_ofReal)
  calc
    _ = ∫⁻ q, R q
        ∂(volume.restrict (Ioc 0 T)).prod (μ.prod (Measure.infinitePi ν)) := by
      apply lintegral_congr
      intro q
      exact (ENNReal.ofReal_sum_of_nonneg (fun _ _ => sq_nonneg _)).symm
    _ = ∫⁻ t in Ioc 0 T, ∫⁻ p, R (t, p) ∂μ.prod (Measure.infinitePi ν) :=
      lintegral_prod R hR.aemeasurable
    _ ≤ _ := hμ.lintegral_finiteIsingBrownianNormalizedEnergy_le hbeta ν hB hmB
      D (connectedExhaustion_connected v n) r hT

end Problem367.NormalizedInfiniteTimeEnergy

end

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Estimates_ProgressivePrimitive
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory ProbabilityTheory
open scoped NNReal

namespace Problem367

theorem continuous_nnreal_primitive_of_integrable_horizons
    (f : ℝ → ℝ) (hf : ∀ n : ℕ, IntervalIntegrable f volume 0 (n : ℝ)) :
    Continuous (fun t : ℝ≥0 => ∫ u in (0 : ℝ)..(t : ℝ), f u) := by
  rw [continuous_iff_continuousAt]
  intro t
  obtain ⟨n, hn⟩ := exists_nat_gt (t : ℝ)
  have hcont : Continuous (fun s : ℝ≥0 => ∫ u in (0 : ℝ)..min (s : ℝ) (n : ℝ), f u) := by
    apply (intervalIntegral.continuousOn_primitive_interval' (hf n)
      (Set.left_mem_uIcc : (0 : ℝ) ∈ Set.uIcc 0 (n : ℝ))).comp_continuous
        (NNReal.continuous_coe.min continuous_const)
    intro s
    rw [Set.uIcc_of_le (Nat.cast_nonneg n)]
    exact ⟨le_min s.coe_nonneg (Nat.cast_nonneg n), min_le_right _ _⟩
  apply hcont.continuousAt.congr_of_eventuallyEq
  filter_upwards [NNReal.continuous_coe.continuousAt.eventually (gt_mem_nhds hn)] with s hs
  simp only [min_eq_left hs.le]

end Problem367

end

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Estimates_IntegrableTimePrimitive
attribute [-instance] _root_.OAI.Problem367.WienerSampler.pathMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory Set
open scoped NNReal
namespace Problem367

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [SFinite μ]
  {a : ℝ≥0 → Ω → ℝ}

theorem ae_intervalIntegrable_horizons_of_joint
    (ha : ∀ n : ℕ, Integrable (fun p : ℝ × Ω => a p.1.toNNReal p.2)
      ((volume.restrict (Ioc (0 : ℝ) (n : ℝ))).prod μ)) :
    ∀ᵐ ω ∂μ, ∀ n : ℕ,
      IntervalIntegrable (fun r : ℝ => a r.toNNReal ω) volume 0 (n : ℝ) := by
  apply ae_all_iff.mpr
  intro n
  filter_upwards [(ha n).prod_left_ae] with ω hω
  exact (intervalIntegrable_iff_integrableOn_Ioc_of_le (Nat.cast_nonneg n)).mpr hω

theorem ae_continuous_nnrealTimePrimitive_of_joint
    (ha : ∀ n : ℕ, Integrable (fun p : ℝ × Ω => a p.1.toNNReal p.2)
      ((volume.restrict (Ioc (0 : ℝ) (n : ℝ))).prod μ)) :
    ∀ᵐ ω ∂μ, Continuous (fun t => nnrealTimePrimitive a t ω) := by
  filter_upwards [ae_intervalIntegrable_horizons_of_joint ha] with ω hω
  exact continuous_nnreal_primitive_of_integrable_horizons _ hω

end Problem367

end

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Ising_ObservationPosteriorTransport
attribute [-instance] _root_.OAI.Problem367.IsingConditionalCopyBounds.graphLaw_isProbabilityMeasure _root_.OAI.Problem367.IsingObservationFactor.copies_probability _root_.OAI.Problem367.IsingObservationFactor.kernel_markov _root_.OAI.Problem367.TreeKoopman.labelProbability _root_.OAI.Problem367.freeIsingMeasure_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

namespace Problem367.IsingObservationInnovation

theorem measurePreserving_uniformObservation {d : ℕ}
    (μ : Measure (TreeVertex d → IsingSpin)) :
    MeasurePreserving (uniformObservation (d := d))
      (μ.prod (labelMeasure d)) (observationLaw μ) :=
  ⟨measurable_uniformObservation, rfl⟩

end Problem367.IsingObservationInnovation

end

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Ising_CopyEnergyIntegrability
attribute [-instance] _root_.OAI.Problem367.TreeKoopman.labelProbability _root_.OAI.Problem367.freeIsingMeasure_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal Topology

namespace Problem367.IsingCopyEnergy
open IsingObservationInnovation IsingObservationFactor

theorem measurable_responseRow {d : ℕ} (beta : ℝ) (v w : TreeVertex d) :
    Measurable (responseRow beta v w) := by
  apply (measurable_infiniteGibbsResponse beta v w).comp
  apply Measurable.of_eval
  intro i
  exact continuous_eval.measurable.comp
    (((measurable_pi_apply i).comp measurable_snd).prodMk
      (measurable_real_toNNReal.comp measurable_fst))

theorem observation_extended_energy_le
    {d : ℕ} {beta : ℝ} {μ : Measure (TreeVertex d → IsingSpin)}
    (hμ : HasFreeIsingLaw (Real.tanh beta) μ) (hb : 0 ≤ beta)
    (v : TreeVertex d) {T : ℝ} (hT : 0 ≤ T) :
    (∫⁻ p, ∑' w, ENNReal.ofReal (responseRow beta v w p ^ 2)
      ∂(volume.restrict (Ioc 0 T)).prod (observationLaw μ)) ≤
      ENNReal.ofReal (2 * ((d : ℝ) * beta + T + Real.sqrt T)) := by
  let : IsProbabilityMeasure μ := hμ.isProbabilityMeasure
  let : IsProbabilityMeasure (labelMeasure d) := by unfold labelMeasure; (first | (set_option synthInstance.maxHeartbeats 20000 in infer_instance) | exact Measure.isProbabilityMeasure_map (by first | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability))
  let Q := (volume.restrict (Ioc (0 : ℝ) T)).prod (μ.prod (labelMeasure d))
  let R := (volume.restrict (Ioc (0 : ℝ) T)).prod (observationLaw μ)
  let f : ℝ × Paths d → ℝ≥0∞ := fun p => ∑' w, ENNReal.ofReal (responseRow beta v w p ^ 2)
  have hf : Measurable f := Measurable.tsum (fun w =>
    ((measurable_responseRow beta v w).pow_const 2).ennreal_ofReal)
  have hmp : MeasurePreserving (Prod.map id uniformObservation) Q R :=
    (MeasurePreserving.id _).prod (measurePreserving_uniformObservation μ)
  have henergy := NormalizedInfiniteTimeEnergy.lintegral_infiniteRow_le hμ hb
    (fun _ : TreeVertex d => uniform01)
    (fun _ => WienerSampler.sample_isBrownianReal.toIsPreBrownianReal)
    (fun _ t => (continuous_eval_const t).measurable.comp WienerSampler.measurable_sample)
    (fun _ => WienerSampler.measurable_sample_eval) v hT
  have heq : (fun p => f (Prod.map id uniformObservation p)) =ᵐ[Q]
      (fun p => ∑' w, ENNReal.ofReal
        (NormalizedInfiniteTimeEnergy.infiniteRow beta v
          (fun _ t u => WienerSampler.sample u t) w p ^ 2)) := by
    have hmem : ∀ᵐ p ∂Q, p.1 ∈ Ioc (0 : ℝ) T :=
      Measure.quasiMeasurePreserving_fst.ae (ae_restrict_mem measurableSet_Ioc)
    filter_upwards [hmem] with p hp
    apply tsum_congr
    intro w
    apply congrArg ENNReal.ofReal
    apply congrArg (fun r : ℝ => r ^ 2)
    change infiniteGibbsResponse beta v w (fun i => uniformObservation p.2 i p.1.toNNReal) = _
    apply congrArg (infiniteGibbsResponse beta v w)
    funext i
    change WienerSampler.sample (p.2.2 i) p.1.toNNReal +
      (p.1.toNNReal : ℝ) * spinSign (p.2.1 i) =
        p.1 * spinSign (p.2.1 i) + WienerSampler.sample (p.2.2 i) p.1.toNNReal
    rw [Real.coe_toNNReal p.1 hp.1.le, add_comm]
  calc
    _ = ∫⁻ p, f (Prod.map id uniformObservation p) ∂Q := (hmp.lintegral_comp hf).symm
    _ = _ := lintegral_congr_ae heq
    _ ≤ _ := henergy

theorem observation_row_energy_integrable
    {d : ℕ} {beta : ℝ} {μ : Measure (TreeVertex d → IsingSpin)}
    (hμ : HasFreeIsingLaw (Real.tanh beta) μ) (hb : 0 ≤ beta)
    (v : TreeVertex d) {T : ℝ} (hT : 0 ≤ T) :
    (∀ᵐ p ∂(volume.restrict (Ioc 0 T)).prod (observationLaw μ),
      Summable (fun w => responseRow beta v w p ^ 2)) ∧
    Integrable (fun p => ∑' w, responseRow beta v w p ^ 2)
      ((volume.restrict (Ioc 0 T)).prod (observationLaw μ)) ∧
    (∫ p, ∑' w, responseRow beta v w p ^ 2
      ∂(volume.restrict (Ioc 0 T)).prod (observationLaw μ)) ≤
      2 * ((d : ℝ) * beta + T + Real.sqrt T) := by
  let P := (volume.restrict (Ioc (0 : ℝ) T)).prod (observationLaw μ)
  have he := observation_extended_energy_le hμ hb v hT
  rw [lintegral_tsum (fun w =>
    ((measurable_responseRow beta v w).pow_const 2).ennreal_ofReal.aemeasurable)] at he
  have hm (w : TreeVertex d) : AEStronglyMeasurable (responseRow beta v w) P :=
    (measurable_responseRow beta v w).aestronglyMeasurable
  exact ⟨ae_summable_sq_of_tsum_lintegral_sq_ne_top P hm
      (ne_top_of_le_ne_top ENNReal.ofReal_ne_top he),
    integral_tsum_sq_le_of_tsum_lintegral_sq_le P hm (by positivity) he⟩

end Problem367.IsingCopyEnergy

end

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Ising_CanonicalMartingales
attribute [-instance] _root_.OAI.Problem367.TreeKoopman.labelProbability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal Topology
namespace Problem367.IsingObservationFactor
open IsingObservationInnovation

lemma evaluation_progressive {d : ℕ} (v : TreeVertex d) :
    IsStronglyProgressive (filtration d) (evaluation v) :=
  (arrayNaturalFiltration_stronglyAdapted evaluation measurable_evaluation v).isStronglyProgressive_of_continuous
    (fun x => (x v).continuous)

end Problem367.IsingObservationFactor

end

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Ising_CanonicalArtanh
attribute [-instance] _root_.OAI.Problem367.TreeKoopman.labelProbability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal Topology
namespace Problem367.IsingObservationFactor
open IsingObservationInnovation PosteriorCompensatorStopping ArtanhMartingaleFormula

lemma canonicalResponseDrift_progressive {d : ℕ} (beta : ℝ) (v : TreeVertex d) :
    IsStronglyProgressive (filtration d) (canonicalResponseDrift beta v) :=
  (posterior_progressive beta v).mul
    (isStronglyProgressive_infiniteGibbsResponseRow _ beta v _ evaluation_progressive)

end Problem367.IsingObservationFactor

end

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Ising_CanonicalDriftRegularity
attribute [-instance] _root_.OAI.Problem367.TreeKoopman.labelProbability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal

namespace Problem367.IsingObservationFactor
open IsingObservationInnovation IsingCopyEnergy

theorem norm_canonicalResponseDrift_le {d : ℕ} (beta : ℝ)
    (v : TreeVertex d) (t : ℝ≥0) (x : Paths d) :
    ‖canonicalResponseDrift beta v t x‖ ≤
      infiniteGibbsResponseRow beta v (fun i => x i t) := by
  have hnonneg : 0 ≤ infiniteGibbsResponseRow beta v (fun i => x i t) :=
    tsum_nonneg (fun _ => sq_nonneg _)
  rw [canonicalResponseDrift, norm_mul, Real.norm_of_nonneg hnonneg]
  exact mul_le_of_le_one_left hnonneg (posterior_norm_le_one beta v t x)

theorem measurable_canonicalResponseDrift_real {d : ℕ} (beta : ℝ)
    (v : TreeVertex d) :
    Measurable (fun p : ℝ × Paths d => canonicalResponseDrift beta v p.1.toNNReal p.2) := by
  have hc : Measurable (fun p : ℝ≥0 × Paths d => canonicalResponseDrift beta v p.1 p.2) :=
    (stronglyMeasurable_joint_of_isStronglyProgressive
      (canonicalResponseDrift_progressive beta v)).measurable
  have hn : Measurable (fun p : ℝ × Paths d => (p.1.toNNReal, p.2)) :=
    (measurable_real_toNNReal.comp measurable_fst).prodMk measurable_snd
  exact Measurable.comp
    (g := fun p : ℝ≥0 × Paths d => canonicalResponseDrift beta v p.1 p.2)
    (f := fun p : ℝ × Paths d => (p.1.toNNReal, p.2)) hc hn

theorem canonicalResponseDrift_integrable
    {d : ℕ} {beta : ℝ} {μ : Measure (TreeVertex d → IsingSpin)}
    (hμ : HasFreeIsingLaw (Real.tanh beta) μ) (hb : 0 ≤ beta)
    (v : TreeVertex d) (T : ℝ≥0) :
    Integrable (fun p : ℝ × Paths d => canonicalResponseDrift beta v p.1.toNNReal p.2)
      ((volume.restrict (Ioc (0 : ℝ) T)).prod (observationLaw μ)) := by
  have hi : Integrable (fun p : ℝ × Paths d =>
      infiniteGibbsResponseRow beta v (fun i => p.2 i p.1.toNNReal))
      ((volume.restrict (Ioc (0 : ℝ) T)).prod (observationLaw μ)) := by
    simpa only [infiniteGibbsResponseRow, responseRow] using
      (observation_row_energy_integrable hμ hb v T.coe_nonneg).2.1
  exact hi.mono' (measurable_canonicalResponseDrift_real beta v).aestronglyMeasurable
    (Eventually.of_forall (fun p => norm_canonicalResponseDrift_le beta v p.1.toNNReal p.2))

theorem canonicalResponseDrift_primitive_continuous_oai
    {d : ℕ} {beta : ℝ} {μ : Measure (TreeVertex d → IsingSpin)}
    (hμ : HasFreeIsingLaw (Real.tanh beta) μ) (hb : 0 ≤ beta)
    (v : TreeVertex d) :
    ∀ᵐ x ∂observationLaw μ,
      Continuous (fun t => nnrealTimePrimitive (canonicalResponseDrift beta v) t x) := by
  let : IsProbabilityMeasure μ := hμ.isProbabilityMeasure
  apply ae_continuous_nnrealTimePrimitive_of_joint
  intro n
  simpa only [NNReal.coe_natCast] using
    canonicalResponseDrift_integrable hμ hb v (n : ℝ≥0)

end Problem367.IsingObservationFactor

end

end OAI
end

theorem solution : type_of% @OAI.Problem367.IsingObservationFactor.canonicalResponseDrift_primitive_continuous_oai := @OAI.Problem367.IsingObservationFactor.canonicalResponseDrift_primitive_continuous_oai
