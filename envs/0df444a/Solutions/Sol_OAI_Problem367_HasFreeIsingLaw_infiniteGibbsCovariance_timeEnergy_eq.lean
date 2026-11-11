-- Prove2me | solution 1 for OAI.Problem367.HasFreeIsingLaw.infiniteGibbsCovariance_timeEnergy_eq
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-11T01:42:57.858747+00:00
-- url     : https://prove2.me/submissions/a71091bc-3130-413f-b9ed-b9edfd83b967

import Mathlib
import Mathlib.MeasureTheory.Integral.Marginal
import Definitions.Def_FreeIsing
import Definitions.Def_Q243FI005
import Theorems.Thm_OAI_Problem367_HasFreeIsingLaw_infiniteGibbsCovariance_windowEnergy_eq
import Theorems.Thm_OAI_Problem367_HasFreeIsingLaw_infiniteGibbsSpinMean_brownian_critical_tendsto_zero
import Theorems.Thm_OAI_Problem367_HasFreeIsingLaw_infiniteGibbsSpinMean_brownian_critical_zero

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Cavity_LogOdds
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace Problem367

theorem cavityMessage_eq_half_log_cosh_ratio (beta z : ℝ) :
    cavityMessage (Real.tanh beta) z =
      (1 / 2 : ℝ) * Real.log (Real.cosh (z + beta) / Real.cosh (z - beta)) := by
  have htheta_sq : Real.tanh beta ^ 2 ≤ 1 := (Real.tanh_sq_lt_one beta).le
  have hmem := cavityMessage_argument_mem htheta_sq z
  have hratio : (1 + Real.tanh beta * Real.tanh z) /
      (1 - Real.tanh beta * Real.tanh z) =
      Real.cosh (z + beta) / Real.cosh (z - beta) := by
    apply (div_eq_div_iff (by linarith [hmem.2]) (Real.cosh_pos (z - beta)).ne').2
    rw [Real.cosh_add, Real.cosh_sub]
    simp only [Real.tanh_eq_sinh_div_cosh]
    field_simp
  rw [cavityMessage, Real.artanh_eq_half_log ⟨hmem.1.le, hmem.2.le⟩, hratio]

theorem cavityMessage_eq_log_cosh_sub (beta z : ℝ) :
    cavityMessage (Real.tanh beta) z =
      (Real.log (Real.cosh (z + beta)) - Real.log (Real.cosh (z - beta))) / 2 := by
  rw [cavityMessage_eq_half_log_cosh_ratio beta,
    Real.log_div (Real.cosh_pos (z + beta)).ne' (Real.cosh_pos (z - beta)).ne']
  ring

theorem tanh_field_difference_eq (beta z : ℝ) :
    (Real.tanh (z + beta) - Real.tanh (z - beta)) / 2 =
      Real.tanh beta * (1 - Real.tanh z ^ 2) /
        (1 - Real.tanh beta ^ 2 * Real.tanh z ^ 2) := by
  have hp := ((Real.hasDerivAt_cosh (z + beta)).comp z
    ((hasDerivAt_id z).add_const beta)).log (Real.cosh_pos (z + beta)).ne'
  have hm := ((Real.hasDerivAt_cosh (z - beta)).comp z
    ((hasDerivAt_id z).sub_const beta)).log (Real.cosh_pos (z - beta)).ne'
  simp only [id_eq, mul_one, Function.comp_apply, ← Real.tanh_eq_sinh_div_cosh] at hp hm
  have h : HasDerivAt (cavityMessage (Real.tanh beta))
      ((Real.tanh (z + beta) - Real.tanh (z - beta)) / 2) z := by
    apply ((hp.sub hm).div_const 2).congr_of_eventuallyEq
    exact Filter.Eventually.of_forall fun x => cavityMessage_eq_log_cosh_sub beta x
  simpa only [responseAttenuation, mul_div_assoc] using
    h.unique (hasDerivAt_cavityMessage (Real.tanh_sq_lt_one beta).le z)

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
-- module Solutions.Q243_FreeIsing.FreeIsing_Energy_DiscrepancyRowEnergy
attribute [-instance] _root_.OAI.Problem367.WienerSampler.pathMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory Filter Set
open scoped Topology ENNReal

namespace Problem367.DiscrepancyEnergy

theorem hasSum_integral_sq_row
    {Ω ι : Type*} [MeasurableSpace Ω] [Countable ι] {μ : Measure Ω}
    {c : ι → Ω → ℝ} (hc : ∀ i, AEStronglyMeasurable (c i) μ)
    (hsum : ∀ᵐ ω ∂μ, Summable (fun i => (c i ω) ^ 2))
    (hA : Integrable (fun ω => ∑' i, (c i ω) ^ 2) μ) :
    HasSum (fun i => ∫ ω, (c i ω) ^ 2 ∂μ) (∫ ω, (∑' i, (c i ω) ^ 2) ∂μ) := by
  refine hasSum_integral_of_dominated_convergence (fun i ω => (c i ω) ^ 2)
    (fun i => (hc i).pow 2) ?_ hsum hA ?_
  · intro i
    filter_upwards with ω
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
  · filter_upwards [hsum] with ω hω
    exact hω.hasSum

theorem sq_row_integrable_of_summable_integrals
    {Ω ι : Type*} [MeasurableSpace Ω] [Countable ι] {μ : Measure Ω}
    {c : ι → Ω → ℝ}
    (hc : ∀ i, Integrable (fun ω => (c i ω) ^ 2) μ)
    (hs : Summable (fun i => ∫ ω, (c i ω) ^ 2 ∂μ)) :
    (∀ᵐ ω ∂μ, Summable (fun i => (c i ω) ^ 2)) ∧
      Integrable (fun ω => ∑' i, (c i ω) ^ 2) μ := by
  have hm (i : ι) : AEMeasurable (fun ω => ENNReal.ofReal ((c i ω) ^ 2)) μ :=
    (hc i).aestronglyMeasurable.aemeasurable.ennreal_ofReal
  have hfin : (∫⁻ ω, ∑' i, ENNReal.ofReal ((c i ω) ^ 2) ∂μ) < ∞ := by
    rw [lintegral_tsum hm]
    calc
      (∑' i, ∫⁻ ω, ENNReal.ofReal ((c i ω) ^ 2) ∂μ) =
          ∑' i, ENNReal.ofReal (∫ ω, (c i ω) ^ 2 ∂μ) := by
        apply tsum_congr
        intro i
        exact (ofReal_integral_eq_lintegral_ofReal (hc i)
          (Eventually.of_forall (fun ω => sq_nonneg (c i ω)))).symm
      _ < ∞ := hs.tsum_ofReal_lt_top
  have hAe : ∀ᵐ ω ∂μ, Summable (fun i => (c i ω) ^ 2) := by
    filter_upwards [ae_lt_top' (AEMeasurable.tsum hm) hfin.ne] with ω hω
    simpa only [ENNReal.toReal_ofReal (sq_nonneg _)] using
      ENNReal.summable_toReal hω.ne
  refine ⟨hAe, ?_⟩
  have hI := integrable_toReal_of_lintegral_ne_top (AEMeasurable.tsum hm) hfin.ne
  simpa only [ENNReal.tsum_toReal_eq (fun i => ENNReal.ofReal_ne_top),
    ENNReal.toReal_ofReal (sq_nonneg _)] using hI

end Problem367.DiscrepancyEnergy

end

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Estimates_LeafDeletion
attribute [-instance] _root_.OAI.Problem367.IsingConditionalCopyBounds.graphLaw_isProbabilityMeasure _root_.OAI.Problem367.IsingObservationFactor.copies_probability _root_.OAI.Problem367.IsingObservationFactor.kernel_markov _root_.OAI.Problem367.IsingObservationInnovation.innovationMap_observationLaw_probability _root_.OAI.Problem367.IsingObservationInnovation.observationLaw_probability _root_.OAI.Problem367.TreeKoopman.labelProbability _root_.OAI.Problem367.freeIsingMeasure_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace Problem367

theorem inducedEdges_eq_insert_erase_of_unique_lower_neighbor
    {d : ℕ} {D : Finset (TreeVertex d)} {v p : TreeVertex d}
    (hv : v ∈ D) (hp : p ∈ D) (hpv : treeAdj p v)
    (hplen : p.1.length < v.1.length)
    (hleaf : ∀ x ∈ D, treeAdj v x → x = p) :
    inducedEdges D = insert (p, v) (inducedEdges (D.erase v)) := by
  classical
  ext e
  rcases e with ⟨x, y⟩
  simp only [inducedEdges, Finset.mem_filter, Finset.product_eq_sprod, Finset.mem_product,
    Finset.mem_insert, Prod.mk.injEq, Finset.mem_erase]
  constructor
  · rintro ⟨⟨hx, hy⟩, hxy, hlen⟩
    have hxv : x ≠ v := by
      intro h
      subst x
      have hyp := hleaf y hy hxy
      subst y
      omega
    by_cases hyv : y = v
    · exact Or.inl ⟨hleaf x hx ((hyv ▸ hxy).elim Or.inr Or.inl), hyv⟩
    · exact Or.inr ⟨⟨⟨hxv, hx⟩, ⟨hyv, hy⟩⟩, hxy, hlen⟩
  · rintro (⟨rfl, rfl⟩ | ⟨⟨⟨_, hx⟩, ⟨_, hy⟩⟩, hxy, hlen⟩)
    · exact ⟨⟨hp, hv⟩, hpv, hplen⟩
    · exact ⟨⟨hx, hy⟩, hxy, hlen⟩

end Problem367

end

end OAI
end

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

lemma variance_eq_sum [Nonempty ι] (energy signal observable : ι → ℝ) (t : ℝ) :
    mean energy signal (fun s => (observable s) ^ 2) t -
        (mean energy signal observable t) ^ 2 =
      ∑ s, (observable s - mean energy signal observable t) ^ 2 *
        mass energy signal t s := by
  have heq (s : ι) :
      (observable s - mean energy signal observable t) ^ 2 * mass energy signal t s =
      (observable s) ^ 2 * mass energy signal t s -
        (2 * mean energy signal observable t) * (observable s * mass energy signal t s) +
        (mean energy signal observable t) ^ 2 * mass energy signal t s := by ring
  simp_rw [heq]
  rw [Finset.sum_add_distrib, Finset.sum_sub_distrib,
    ← Finset.mul_sum, ← Finset.mul_sum, sum_mass,
    ← mean_eq_sum_mass, ← mean_eq_sum_mass]
  ring

lemma variance_nonneg [Nonempty ι] (energy signal observable : ι → ℝ) (t : ℝ) :
    0 ≤ mean energy signal (fun s => (observable s) ^ 2) t -
      (mean energy signal observable t) ^ 2 := by
  rw [variance_eq_sum]
  exact Finset.sum_nonneg (fun s _ => mul_nonneg (sq_nonneg _) (mass_pos energy signal t s).le)

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

lemma fieldMean_const [Nonempty S] (energy : S → ℝ) (spin : S → V → ℝ)
    (x : V → ℝ) (c : ℝ) : fieldMean energy spin (fun _ => c) x = c := by
  rw [← mean_fieldEnergy_zero energy spin (fun _ => 0), mean_const]

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

lemma infiniteGibbsPairMean_abs_le_one {d : ℕ} (beta : ℝ) (v w : TreeVertex d)
    (y : TreeVertex d → ℝ) : |infiniteGibbsPairMean beta v w y| ≤ 1 := by
  rw [abs_le]
  exact ⟨le_max_left _ _, max_le (by norm_num) (min_le_left _ _)⟩

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

lemma infiniteGibbsCovariance_abs_le_two {d : ℕ} (beta : ℝ) (v w : TreeVertex d)
    (y : TreeVertex d → ℝ) : |infiniteGibbsCovariance beta v w y| ≤ 2 := by
  have hp := infiniteGibbsPairMean_abs_le_one beta v w y
  have hv := infiniteGibbsSpinMean_abs_le_one beta v y
  have hw := infiniteGibbsSpinMean_abs_le_one beta w y
  have hprod : |infiniteGibbsSpinMean beta v y * infiniteGibbsSpinMean beta w y| ≤ 1 := by
    rw [abs_mul]
    simpa using mul_le_mul hv hw (abs_nonneg _) (by norm_num : (0 : ℝ) ≤ 1)
  exact (abs_sub _ _).trans (by linarith)

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

lemma finiteGibbsPairMean_self {d : ℕ} (beta : ℝ) (v : TreeVertex d) (n : ℕ)
    (y : TreeVertex d → ℝ) : finiteGibbsPairMean beta v v n y = 1 := by
  unfold finiteGibbsPairMean
  have heq : (fun eta : pairExhaustion v v n → IsingSpin =>
      spinSign (eta ⟨v, mem_pairExhaustion_left v v n⟩) *
        spinSign (eta ⟨v, mem_pairExhaustion_right v v n⟩)) = fun _ => (1 : ℝ) := by
    funext eta
    cases h : eta ⟨v, mem_pairExhaustion_left v v n⟩ <;> simp [spinSign]
  rw [heq, FinitePosterior.fieldMean_const]

lemma infiniteGibbsPairMean_self {d : ℕ} (beta : ℝ) (v : TreeVertex d)
    (y : TreeVertex d → ℝ) : infiniteGibbsPairMean beta v v y = 1 := by
  unfold infiniteGibbsPairMean
  simp only [finiteGibbsPairMean_self]
  rw [tendsto_const_nhds.limUnder_eq]
  norm_num

lemma infiniteGibbsCovariance_self {d : ℕ} (beta : ℝ) (v : TreeVertex d)
    (y : TreeVertex d → ℝ) :
    infiniteGibbsCovariance beta v v y = 1 - infiniteGibbsSpinMean beta v y ^ 2 := by
  rw [infiniteGibbsCovariance, infiniteGibbsPairMean_self, pow_two]

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

theorem mean_square_drift_cancellation (energy signal observable : S → ℝ) (t : ℝ)
    (hsignal : ∀ s, signal s = -1 ∨ signal s = 1) :
    deriv (fun u => mean energy signal observable u ^ 2) t * mean energy signal signal t +
      (1 / 2 : ℝ) * deriv (deriv (fun u => mean energy signal observable u ^ 2)) t =
        tiltCovariance energy signal observable t ^ 2 := by
  have hfun : deriv (fun u => mean energy signal observable u ^ 2) =
      (fun u => 2 * mean energy signal observable u * tiltCovariance energy signal observable u) := by
    funext u
    have hd := (hasDerivAt_mean_covariance energy signal observable u).pow 2
    change HasDerivAt (fun u => mean energy signal observable u ^ 2) _ u at hd
    simpa only [Nat.cast_ofNat, Nat.reduceSub, pow_one] using hd.deriv
  rw [hfun]
  have hd := ((hasDerivAt_mean_covariance energy signal observable t).const_mul 2).mul
    (hasDerivAt_tiltCovariance energy signal observable t hsignal)
  change HasDerivAt (fun u => 2 * mean energy signal observable u *
    tiltCovariance energy signal observable u) _ t at hd
  rw [hd.deriv]
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

theorem abs_mean_spin_le_one (energy signal : S → ℝ) (t : ℝ)
    (hsignal : ∀ s, signal s = -1 ∨ signal s = 1) :
    |mean energy signal signal t| ≤ 1 :=
  abs_mean_le energy signal signal t 1 (fun s => (abs_spin_eq_one signal hsignal s).le)

theorem abs_tiltCovariance_le (energy signal observable : S → ℝ) (t A : ℝ)
    (hsignal : ∀ s, signal s = -1 ∨ signal s = 1)
    (hbound : ∀ s, |observable s| ≤ A) :
    |tiltCovariance energy signal observable t| ≤ 2 * A := by
  have hA : 0 ≤ A := (abs_nonneg (observable (Classical.arbitrary S))).trans
    (hbound (Classical.arbitrary S))
  have hprod : ∀ s, |observable s * signal s| ≤ A := by
    intro s
    rw [abs_mul, abs_spin_eq_one signal hsignal s, mul_one]
    exact hbound s
  unfold tiltCovariance
  calc
    |mean energy signal (fun s => observable s * signal s) t -
        mean energy signal observable t * mean energy signal signal t| ≤
      |mean energy signal (fun s => observable s * signal s) t| +
        |mean energy signal observable t * mean energy signal signal t| := abs_sub _ _
    _ ≤ A + A * 1 := add_le_add (abs_mean_le energy signal _ t A hprod)
      (by
        rw [abs_mul]
        exact mul_le_mul (abs_mean_le energy signal observable t A hbound)
          (abs_mean_spin_le_one energy signal t hsignal) (abs_nonneg _) hA)
    _ = 2 * A := by ring

lemma deriv_mean_square (energy signal observable : S → ℝ) (t : ℝ) :
    deriv (fun u => mean energy signal observable u ^ 2) t =
      2 * mean energy signal observable t * tiltCovariance energy signal observable t := by
  have hd := (hasDerivAt_mean_covariance energy signal observable t).pow 2
  change HasDerivAt (fun u => mean energy signal observable u ^ 2) _ t at hd
  simpa only [Nat.cast_ofNat, Nat.reduceSub, pow_one] using hd.deriv

theorem abs_deriv_mean_square_le (energy signal observable : S → ℝ) (t A : ℝ)
    (hsignal : ∀ s, signal s = -1 ∨ signal s = 1)
    (hbound : ∀ s, |observable s| ≤ A) :
    |deriv (fun u => mean energy signal observable u ^ 2) t| ≤ 4 * A ^ 2 := by
  have hA : 0 ≤ A := (abs_nonneg (observable (Classical.arbitrary S))).trans
    (hbound (Classical.arbitrary S))
  rw [deriv_mean_square, abs_mul, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
  have hm := abs_mean_le energy signal observable t A hbound
  have hc := abs_tiltCovariance_le energy signal observable t A hsignal hbound
  calc
    2 * |mean energy signal observable t| * |tiltCovariance energy signal observable t| ≤
      2 * A * (2 * A) := by gcongr
    _ = 4 * A ^ 2 := by ring

theorem abs_deriv_deriv_mean_square_le (energy signal observable : S → ℝ) (t A : ℝ)
    (hsignal : ∀ s, signal s = -1 ∨ signal s = 1)
    (hbound : ∀ s, |observable s| ≤ A) :
    |deriv (deriv (fun u => mean energy signal observable u ^ 2)) t| ≤ 16 * A ^ 2 := by
  have he := mean_square_drift_cancellation energy signal observable t hsignal
  have hderiv := abs_deriv_mean_square_le energy signal observable t A hsignal hbound
  have hmean := abs_mean_spin_le_one energy signal t hsignal
  have hcov := abs_tiltCovariance_le energy signal observable t A hsignal hbound
  have hA : 0 ≤ A := (abs_nonneg (observable (Classical.arbitrary S))).trans
    (hbound (Classical.arbitrary S))
  have hsq : tiltCovariance energy signal observable t ^ 2 ≤ 4 * A ^ 2 := by
    have hs := mul_le_mul hcov hcov (abs_nonneg _) (by positivity : 0 ≤ 2 * A)
    nlinarith [sq_abs (tiltCovariance energy signal observable t)]
  have heq : deriv (deriv (fun u => mean energy signal observable u ^ 2)) t =
      2 * (tiltCovariance energy signal observable t ^ 2 -
        deriv (fun u => mean energy signal observable u ^ 2) t * mean energy signal signal t) := by
    linarith
  rw [heq, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
  calc
    2 * |tiltCovariance energy signal observable t ^ 2 -
        deriv (fun u => mean energy signal observable u ^ 2) t * mean energy signal signal t| ≤
      2 * (|tiltCovariance energy signal observable t ^ 2| +
        |deriv (fun u => mean energy signal observable u ^ 2) t * mean energy signal signal t|) := by
          exact mul_le_mul_of_nonneg_left (abs_sub _ _) (by norm_num)
    _ ≤ 2 * (4 * A ^ 2 + 4 * A ^ 2 * 1) := by
      rw [abs_of_nonneg (sq_nonneg _), abs_mul]
      gcongr
    _ = 16 * A ^ 2 := by ring

section Fields

variable {V : Type*} [Fintype V]

theorem abs_fieldMean_le (energy : S → ℝ) (spin : S → V → ℝ)
    (observable : S → ℝ) (x : V → ℝ) (A : ℝ)
    (hbound : ∀ s, |observable s| ≤ A) :
    |fieldMean energy spin observable x| ≤ A := by
  rw [← mean_fieldEnergy_zero energy spin (fun _ => 0)]
  exact abs_mean_le _ _ _ _ _ hbound

theorem abs_fieldCovariance_le (energy : S → ℝ) (spin : S → V → ℝ)
    (observable : S → ℝ) (x : V → ℝ) (u : V) (A : ℝ)
    (hcoord : ∀ s, spin s u = -1 ∨ spin s u = 1)
    (hbound : ∀ s, |observable s| ≤ A) :
    |fieldCovariance energy spin observable x u| ≤ 2 * A := by
  have h := abs_tiltCovariance_le (fieldEnergy energy spin x) (fun s => spin s u)
    observable 0 A hcoord hbound
  simpa only [tiltCovariance, mean_fieldEnergy_zero, fieldCovariance] using h

theorem abs_fieldMean_square_le (energy : S → ℝ) (spin : S → V → ℝ)
    (observable : S → ℝ) (x : V → ℝ) (A : ℝ)
    (hbound : ∀ s, |observable s| ≤ A) :
    |fieldMean energy spin observable x ^ 2| ≤ A ^ 2 := by
  have h := abs_fieldMean_le energy spin observable x A hbound
  have hA : 0 ≤ A := (abs_nonneg _).trans h
  have hs := mul_le_mul h h (abs_nonneg _) hA
  rw [abs_of_nonneg (sq_nonneg _)]
  nlinarith [sq_abs (fieldMean energy spin observable x)]

variable [DecidableEq V]

theorem abs_deriv_deriv_fieldMean_square_coordinate_le
    (energy : S → ℝ) (spin : S → V → ℝ) (observable : S → ℝ)
    (x : V → ℝ) (u : V) (t A : ℝ)
    (hcoord : ∀ s, spin s u = -1 ∨ spin s u = 1)
    (hbound : ∀ s, |observable s| ≤ A) :
    |deriv (deriv (fun r => fieldMean energy spin observable
      (fun v => x v + if v = u then r else 0) ^ 2)) t| ≤ 16 * A ^ 2 := by
  simp_rw [fieldMean_coordinate_tilt]
  exact abs_deriv_deriv_mean_square_le _ _ _ _ _ hcoord hbound

end Fields

end Problem367.FinitePosterior

end

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Gibbs_CovarianceL2Limit
attribute [-instance] _root_.OAI.Problem367.IsingConditionalCopyBounds.graphLaw_isProbabilityMeasure _root_.OAI.Problem367.IsingObservationFactor.copies_probability _root_.OAI.Problem367.IsingObservationFactor.kernel_markov _root_.OAI.Problem367.IsingObservationInnovation.innovationMap_observationLaw_probability _root_.OAI.Problem367.IsingObservationInnovation.observationLaw_probability _root_.OAI.Problem367.TreeKoopman.labelProbability _root_.OAI.Problem367.WienerSampler.pathMeasurableSpace _root_.OAI.Problem367.freeIsingMeasure_probability
attribute [-simp] _root_.OAI.Problem367.ConnectedHull.pathAssignment_path _root_.OAI.Problem367.ConnectedHull.path_last _root_.OAI.Problem367.ConnectedHull.path_zero _root_.OAI.Problem367.CutContinuationChannels.averageChannel_globalCone _root_.OAI.Problem367.CutContinuationChannels.continuationChannel_globalCone _root_.OAI.Problem367.FactorObservable.centeredSpinLp_coe _root_.OAI.Problem367.FiniteIsingSplit.splitEquiv_fst _root_.OAI.Problem367.FiniteIsingSplit.splitEquiv_snd _root_.OAI.Problem367.FinitePathGibbs.tailPartition_zero _root_.OAI.Problem367.GaussianTreeResponseNaturality.fieldEquiv_apply_image _root_.OAI.Problem367.IsingObservationInnovation.innovationMap_apply _root_.OAI.Problem367.IsingObservationInnovation.innovationMap_uniformObservation _root_.OAI.Problem367.IsingObservationInnovation.innovationMap_zero _root_.OAI.Problem367.IsingObservationInnovation.uniformObservation_relabel _root_.OAI.Problem367.IsingOrientedPath.attenuation_outward _root_.OAI.Problem367.IsingOrientedPath.endpoint_extensionAt _root_.OAI.Problem367.LocalSupportGeometry.prefixVertex_length _root_.OAI.Problem367.PathSideBranches.parent_sideVertex _root_.OAI.Problem367.PathSideBranches.restrictNoisyRegion_array _root_.OAI.Problem367.PathSideBranches.sideVertex_length _root_.OAI.Problem367.PathSideBranches.sideVertex_val _root_.OAI.Problem367.PosteriorChain.transition_spinMean _root_.OAI.Problem367.PosteriorChain.transition_sum _root_.OAI.Problem367.RootedBroadcast.flipBranchToComplement_val _root_.OAI.Problem367.RootedBroadcast.pos_spinMul _root_.OAI.Problem367.RootedBroadcast.prefixFlip_branchRoot _root_.OAI.Problem367.RootedBroadcast.prefixFlip_root _root_.OAI.Problem367.RootedBroadcast.prefixTreeAut_symm_branchRoot _root_.OAI.Problem367.RootedBroadcast.prefixTreeAut_symm_root _root_.OAI.Problem367.RootedBroadcast.spinMul_pos _root_.OAI.Problem367.RootedBroadcast.spinMul_self _root_.OAI.Problem367.TreeConeCoding.length_vertex _root_.OAI.Problem367.TreeConeCoding.vertex_nil _root_.OAI.Problem367.TreeConeCoding.vertex_val _root_.OAI.Problem367.TreeGibbsAut.spinEquiv_apply_image _root_.OAI.Problem367.TreeKoopman.centeredAverage_apply_coe _root_.OAI.Problem367.TreeKoopman.centeredAverage_pow_apply_coe _root_.OAI.Problem367.TreeKoopman.centeredGenerator_apply_coe _root_.OAI.Problem367.TreeKoopman.centeredGenerator_sq _root_.OAI.Problem367.TreeKoopman.generatorOperator_sq _root_.OAI.Problem367.TreeKoopman.reverseVertex_twice _root_.OAI.Problem367.TreeKoopman.wordRelabel_cons _root_.OAI.Problem367.TreeKoopman.wordRelabel_nil _root_.OAI.Problem367.TreeLawKoopman.centeredAverage_apply_coe _root_.OAI.Problem367.TreeLawKoopman.generatorOperator_sq _root_.OAI.Problem367.TreePathGibbs.vertexEquiv_val _root_.OAI.Problem367.branchColorAut_length _root_.OAI.Problem367.branchColorAut_singleton _root_.OAI.Problem367.branchColorAut_val _root_.OAI.Problem367.branchColorMap_symm_apply _root_.OAI.Problem367.colorPermAut_length _root_.OAI.Problem367.colorPermAut_nil _root_.OAI.Problem367.colorPermAut_val _root_.OAI.Problem367.colorPermMap_symm_apply _root_.OAI.Problem367.colorPermMap_val _root_.OAI.Problem367.connectedSpinEncode_apply_root _root_.OAI.Problem367.connectedSpinEquiv_apply _root_.OAI.Problem367.dropVertex_length _root_.OAI.Problem367.dropVertex_val _root_.OAI.Problem367.mem_rootComplementFinset _root_.OAI.Problem367.mem_rootComponentFinset _root_.OAI.Problem367.mem_rootComponentIndices _root_.OAI.Problem367.parentVertex_length _root_.OAI.Problem367.parentVertex_val _root_.OAI.Problem367.prefixColorAut_length _root_.OAI.Problem367.prefixColorAut_val _root_.OAI.Problem367.prefixColorMap_symm_apply _root_.OAI.Problem367.prefixFlip_twice _root_.OAI.Problem367.spinAgreementCode_eq_neg_iff _root_.OAI.Problem367.spinAgreementCode_eq_pos_iff _root_.OAI.Problem367.spinSign_flip _root_.OAI.Problem367.tsum_treeShell_radial _root_.OAI.Problem367.vertexSampler_relabel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory ProbabilityTheory Filter
open scoped BigOperators Topology NNReal

namespace Problem367

open PlantedSymmetry

local instance covarianceL2LimitNonemptyIsingSpin : Nonempty IsingSpin := ⟨.neg⟩

lemma continuous_finiteGibbsCovarianceOn {d : ℕ} (beta : ℝ)
    (D : Finset (TreeVertex d)) (v w : D) :
    Continuous (finiteGibbsCovarianceOn beta D v w) := by
  exact (FinitePosterior.continuous_fieldMean _ _ _).sub
    ((FinitePosterior.continuous_fieldMean _ _ _).mul
      (FinitePosterior.continuous_fieldMean _ _ _))

lemma finiteGibbsCovarianceOn_abs_le_two {d : ℕ} (beta : ℝ)
    (D : Finset (TreeVertex d)) (v w : D) (y : D → ℝ) :
    |finiteGibbsCovarianceOn beta D v w y| ≤ 2 := by
  have hv := FinitePosterior.abs_fieldMean_le (finiteIsingEnergy beta D)
    (fun (eta : D → IsingSpin) u => spinSign (eta u))
    (fun eta => spinSign (eta v)) y 1
    (fun eta => show |spinSign (eta v)| ≤ 1 by cases eta v <;> norm_num [spinSign])
  have hw := FinitePosterior.abs_fieldMean_le (finiteIsingEnergy beta D)
    (fun (eta : D → IsingSpin) u => spinSign (eta u))
    (fun eta => spinSign (eta w)) y 1
    (fun eta => show |spinSign (eta w)| ≤ 1 by cases eta w <;> norm_num [spinSign])
  have hp := FinitePosterior.abs_fieldMean_le (finiteIsingEnergy beta D)
    (fun (eta : D → IsingSpin) u => spinSign (eta u))
    (fun eta => spinSign (eta v) * spinSign (eta w)) y 1
    (fun eta => show |spinSign (eta v) * spinSign (eta w)| ≤ 1 by
      cases eta v <;> cases eta w <;> norm_num [spinSign])
  have hprod : |FinitePosterior.fieldMean (finiteIsingEnergy beta D)
      (fun (eta : D → IsingSpin) u => spinSign (eta u))
      (fun eta => spinSign (eta v)) y *
    FinitePosterior.fieldMean (finiteIsingEnergy beta D)
      (fun (eta : D → IsingSpin) u => spinSign (eta u))
      (fun eta => spinSign (eta w)) y| ≤ 1 := by
    rw [abs_mul]
    simpa using mul_le_mul hv hw (abs_nonneg _) (by norm_num : (0 : ℝ) ≤ 1)
  exact (abs_sub _ _).trans (by linarith)

lemma continuous_finiteGibbsCovariance {d : ℕ} (beta : ℝ)
    (v w : TreeVertex d) (n : ℕ) : Continuous (finiteGibbsCovariance beta v w n) := by
  classical
  unfold finiteGibbsCovariance
  split_ifs with hw
  · exact (continuous_finiteGibbsCovarianceOn _ _ _ _).comp
      (continuous_pi fun u => continuous_apply u.1)
  · exact continuous_const

lemma finiteGibbsCovariance_abs_le_two {d : ℕ} (beta : ℝ)
    (v w : TreeVertex d) (n : ℕ) (y : TreeVertex d → ℝ) :
    |finiteGibbsCovariance beta v w n y| ≤ 2 := by
  classical
  unfold finiteGibbsCovariance
  split_ifs with hw
  · exact finiteGibbsCovarianceOn_abs_le_two _ _ _ _ _
  · norm_num

theorem HasFreeIsingLaw.finiteGibbsCovarianceOn_eq_posterior
    {d : ℕ} {beta : ℝ} {μ : Measure (TreeVertex d → IsingSpin)}
    (hμ : HasFreeIsingLaw (Real.tanh beta) μ)
    (D : Finset (TreeVertex d)) (hD : ConnectedFinset D)
    (v w : D) (t : ℝ≥0) :
    (fun p => finiteGibbsCovarianceOn beta D v w (finiteObservation D t p)) =ᵐ[
      μ.prod (gaussianNoiseLaw (TreeVertex d) t)]
      posteriorCovariance (μ.prod (gaussianNoiseLaw (TreeVertex d) t))
        (MeasurableSpace.comap (finiteObservation D t) inferInstance)
        (fun p => spinSign (p.1 v.1)) (fun p => spinSign (p.1 w.1)) := by
  filter_upwards [hμ.finiteObservation_condExp D hD t
      (fun eta => spinSign (eta v) * spinSign (eta w)),
    hμ.finiteObservation_condExp D hD t (fun eta => spinSign (eta v)),
    hμ.finiteObservation_condExp D hD t (fun eta => spinSign (eta w))]
      with p hp hv hw
  exact congrArg₂ (fun a b : ℝ => a - b) hp.symm
    (congrArg₂ (· * ·) hv.symm hw.symm)

theorem HasFreeIsingLaw.finiteGibbsCovariance_tendsto_ae
    {d : ℕ} {beta : ℝ} {μ : Measure (TreeVertex d → IsingSpin)}
    (hμ : HasFreeIsingLaw (Real.tanh beta) μ) (t : ℝ≥0) (v w : TreeVertex d) :
    ∀ᵐ p ∂μ.prod (gaussianNoiseLaw (TreeVertex d) t),
      Tendsto (fun n => finiteGibbsCovariance beta v w n (observation t p)) atTop
        (𝓝 (infiniteGibbsCovariance beta v w (observation t p))) := by
  classical
  let : IsProbabilityMeasure μ := hμ.isProbabilityMeasure
  let F := finiteObservationFiltration (connectedExhaustion v)
    (connectedExhaustion_monotone v) t
  have hlim := tendsto_ae_posteriorCovariance
    (μ.prod (gaussianNoiseLaw (TreeVertex d) t)) F
    (fun p => spinSign (p.1 v)) (fun p => spinSign (p.1 w))
  have hsup : (⨆ n, F n) = observationSigma (TreeVertex d) t :=
    finiteObservationFiltration_iSup (connectedExhaustion v)
      (connectedExhaustion_monotone v)
      (fun u => (eventually_mem_connectedExhaustion v u).exists) t
  rw [hsup] at hlim
  have hfinite (n : ℕ) : ∀ᵐ p ∂μ.prod (gaussianNoiseLaw (TreeVertex d) t),
      w ∈ connectedExhaustion v n →
      finiteGibbsCovariance beta v w n (observation t p) =
        posteriorCovariance (μ.prod (gaussianNoiseLaw (TreeVertex d) t)) (F n)
          (fun p => spinSign (p.1 v)) (fun p => spinSign (p.1 w)) p := by
    by_cases hw : w ∈ connectedExhaustion v n
    · filter_upwards [hμ.finiteGibbsCovarianceOn_eq_posterior
        (connectedExhaustion v n) (connectedExhaustion_connected v n)
        ⟨v, mem_connectedExhaustion v n⟩ ⟨w, hw⟩ t] with p hp
      intro _
      simpa only [finiteGibbsCovariance, dite_eq_left hw, F,
        finiteObservationFiltration, finiteObservation] using hp
    · exact Eventually.of_forall fun _ h => (hw h).elim
  filter_upwards [hlim, ae_all_iff.mpr hfinite,
    hμ.infiniteGibbsCovariance_eq_posterior t v w] with p hp hfinite hinf
  rw [← hinf] at hp
  apply hp.congr'
  filter_upwards [eventually_mem_connectedExhaustion v w] with n hn
  exact (hfinite n hn).symm

theorem HasFreeIsingLaw.finiteGibbsCovariance_brownian_tendsto_ae
    {d : ℕ} {beta : ℝ} {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure (TreeVertex d → IsingSpin)}
    (hμ : HasFreeIsingLaw (Real.tanh beta) μ)
    (ν : TreeVertex d → Measure Ω) {B : TreeVertex d → ℝ≥0 → Ω → ℝ}
    (hB : ∀ i, IsPreBrownianReal (B i) (ν i))
    (hmB : ∀ i t, Measurable (B i t)) (t : ℝ≥0) (v w : TreeVertex d) :
    ∀ᵐ p ∂μ.prod (Measure.infinitePi ν),
      Tendsto (fun n => finiteGibbsCovariance beta v w n
        (fun i => (t : ℝ) * spinSign (p.1 i) + B i t (p.2 i))) atTop
        (𝓝 (infiniteGibbsCovariance beta v w
          (fun i => (t : ℝ) * spinSign (p.1 i) + B i t (p.2 i)))) := by
  let : IsProbabilityMeasure μ := hμ.isProbabilityMeasure
  have (i : TreeVertex d) : IsProbabilityMeasure (ν i) :=
    (hB i).isGaussianProcess.isProbabilityMeasure
  let T : ((TreeVertex d → IsingSpin) × (TreeVertex d → Ω)) →
      (TreeVertex d → IsingSpin) × (TreeVertex d → ℝ) :=
    Prod.map id (fun omega i => B i t (omega i))
  have hT : MeasurePreserving T (μ.prod (Measure.infinitePi ν))
      (μ.prod (gaussianNoiseLaw (TreeVertex d) t)) :=
    (MeasurePreserving.id μ).prod (brownian_array_eval_measurePreserving ν hB hmB t)
  exact hT.quasiMeasurePreserving.ae (hμ.finiteGibbsCovariance_tendsto_ae t v w)

end Problem367

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

local instance instNonemptyIsingSpin_r0a88de_1 : Nonempty IsingSpin := ⟨.neg⟩
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

theorem hasDerivAt_integral_sqrt_observation_vector
    {Ω E : Type*} [MeasurableSpace Ω] [NormedAddCommGroup E] [NormedSpace ℝ E]
    {P : Measure Ω} [IsFiniteMeasure P]
    {S G : Ω → E} (hS : Integrable S P) (hG : Integrable G P)
    {f : E → ℝ} {f' : E → E →L[ℝ] ℝ}
    (hf : ∀ x, HasFDerivAt f (f' x) x) (hf'cont : Continuous f')
    {C M : ℝ} (hfbound : ∀ x, |f x| ≤ C) (hM : 0 ≤ M)
    (hf'bound : ∀ x, ‖f' x‖ ≤ M) {t : ℝ} (ht : 0 < t) :
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
  have hFint : Integrable (F t) P := by
    apply (integrable_const C).mono' (hFm t)
    exact Eventually.of_forall fun ω => by
      simpa only [Real.norm_eq_abs] using (hfbound (t • S ω + Real.sqrt t • G ω))
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
attribute [-instance] _root_.OAI.Problem367.WienerSampler.pathMeasurableSpace _root_.OAI.Problem367.reducedTailFinite _root_.OAI.Problem367.treeBallFinite _root_.OAI.Problem367.treeShellFinite
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

section Expectation

variable {Ω : Type*} [MeasurableSpace Ω]

theorem hasDerivAt_integral_gaussianObservationCurve
    (μ : Measure Ω) [IsFiniteMeasure μ]
    (f : (V → ℝ) → ℝ) (g : (V → ℝ) → V → ℝ)
    (hdf : ∀ x, HasFDerivAt f (∑ v, g x v •
      (ContinuousLinearMap.proj v : (V → ℝ) →L[ℝ] ℝ)) x)
    (hg : ∀ v, Continuous (fun x => g x v))
    (M C : ℝ) (hC : 0 ≤ C)
    (hfbound : ∀ x, |f x| ≤ M) (hgbound : ∀ x v, |g x v| ≤ C)
    (signal noise : Ω → V → ℝ)
    (hsignal : Measurable signal) (hnoise : Measurable noise)
    (hspin : ∀ ω v, |signal ω v| ≤ 1)
    (hnoiseInt : ∀ v, Integrable (fun ω => noise ω v) μ)
    {t : ℝ} (ht : 0 < t) :
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
  have hd := (hasDerivAt_integral_sqrt_observation_vector hsInt hnInt hdf hDcont
    hfbound (mul_nonneg (by positivity) hC) hDbound ht).2
  simpa only [gaussianObservationCurve, gaussianObservationVelocity, D, sum_apply,
    smul_apply, ContinuousLinearMap.proj_apply, smul_eq_mul] using hd

end Expectation

section Posterior

variable {S : Type*} [Fintype S] [Nonempty S]

theorem continuous_fieldCovariance (energy : S → ℝ) (spin : S → V → ℝ)
    (observable : S → ℝ) (v : V) :
    Continuous (fun x => fieldCovariance energy spin observable x v) := by
  exact (continuous_fieldMean energy spin (fun s => observable s * spin s v)).sub
    ((continuous_fieldMean energy spin observable).mul
      (continuous_fieldMean energy spin (fun s => spin s v)))

theorem hasFDerivAt_fieldMean_square (energy : S → ℝ) (spin : S → V → ℝ)
    (observable : S → ℝ) (x : V → ℝ) :
    HasFDerivAt (fun y => fieldMean energy spin observable y ^ 2)
      (∑ v, (2 * fieldMean energy spin observable x * fieldCovariance energy spin observable x v) •
        (ContinuousLinearMap.proj v : (V → ℝ) →L[ℝ] ℝ)) x := by
  have hs : HasDerivAt (fun z : ℝ => z ^ 2)
      (2 * fieldMean energy spin observable x) (fieldMean energy spin observable x) := by
    have hd := (hasDerivAt_id (fieldMean energy spin observable x)).pow 2
    change HasDerivAt (fun z : ℝ => z ^ 2) _ (fieldMean energy spin observable x) at hd
    simpa only [Nat.cast_ofNat, Nat.reduceSub, pow_one, mul_one, id_eq] using hd
  have hd := hs.comp_hasFDerivAt x (hasFDerivAt_fieldMean energy spin observable x)
  simpa only [Function.comp_def, fieldMeanDerivative, Finset.smul_sum, smul_smul] using hd

variable {Ω : Type*} [MeasurableSpace Ω]

theorem hasDerivAt_integral_fieldMean_square_observation
    (μ : Measure Ω) [IsFiniteMeasure μ]
    (energy : S → ℝ) (spin : S → V → ℝ) (observable : S → ℝ)
    (A : ℝ) (hbound : ∀ s, |observable s| ≤ A)
    (hcoords : ∀ s v, spin s v = -1 ∨ spin s v = 1)
    (signal noise : Ω → V → ℝ)
    (hsignal : Measurable signal) (hnoise : Measurable noise)
    (hspin : ∀ ω v, |signal ω v| ≤ 1)
    (hnoiseInt : ∀ v, Integrable (fun ω => noise ω v) μ)
    {t : ℝ} (ht : 0 < t) :
    HasDerivAt (fun r => ∫ ω, fieldMean energy spin observable
        (gaussianObservationCurve (signal ω) (noise ω) r) ^ 2 ∂μ)
      (∫ ω, ∑ v, (2 * fieldMean energy spin observable
        (gaussianObservationCurve (signal ω) (noise ω) t) *
        fieldCovariance energy spin observable (gaussianObservationCurve (signal ω) (noise ω) t) v) *
          gaussianObservationVelocity (signal ω) (noise ω) t v ∂μ) t := by
  have hA : 0 ≤ A := (abs_nonneg (observable (Classical.arbitrary S))).trans
    (hbound (Classical.arbitrary S))
  apply hasDerivAt_integral_gaussianObservationCurve μ
    (fun x => fieldMean energy spin observable x ^ 2)
    (fun x v => 2 * fieldMean energy spin observable x * fieldCovariance energy spin observable x v)
    (hasFDerivAt_fieldMean_square energy spin observable)
    (fun v => ((continuous_fieldMean energy spin observable).const_mul 2).mul
      (continuous_fieldCovariance energy spin observable v))
    (A ^ 2) (4 * A ^ 2) (by positivity)
    (fun x => abs_fieldMean_square_le energy spin observable x A hbound) ?_
    signal noise hsignal hnoise hspin hnoiseInt ht
  intro x v
  rw [abs_mul, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
  have hm := abs_fieldMean_le energy spin observable x A hbound
  have hc := abs_fieldCovariance_le energy spin observable x v A (fun s => hcoords s v) hbound
  calc
    2 * |fieldMean energy spin observable x| * |fieldCovariance energy spin observable x v| ≤
      2 * A * (2 * A) := by gcongr
    _ = 4 * A ^ 2 := by ring

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

theorem continuous_fieldSquareGradient (energy : S → ℝ) (spin : S → V → ℝ)
    (observable : S → ℝ) (v : V) :
    Continuous (fun x => fieldSquareGradient energy spin observable x v) :=
  ((continuous_fieldMean energy spin observable).const_mul 2).mul
    (continuous_fieldCovariance energy spin observable v)

theorem continuous_fieldSquareHessianDiagonal (energy : S → ℝ) (spin : S → V → ℝ)
    (observable : S → ℝ) (v : V) :
    Continuous (fun x => fieldSquareHessianDiagonal energy spin observable x v) := by
  exact (((continuous_fieldCovariance energy spin observable v).pow 2).const_mul 2).sub
    ((((continuous_fieldMean energy spin observable).const_mul 4).mul
      (continuous_fieldMean energy spin (fun s => spin s v))).mul
        (continuous_fieldCovariance energy spin observable v))

theorem abs_fieldSquareGradient_le (energy : S → ℝ) (spin : S → V → ℝ)
    (observable : S → ℝ) (x : V → ℝ) (v : V) (A : ℝ)
    (hcoord : ∀ s, spin s v = -1 ∨ spin s v = 1)
    (hbound : ∀ s, |observable s| ≤ A) :
    |fieldSquareGradient energy spin observable x v| ≤ 4 * A ^ 2 := by
  have hm := abs_fieldMean_le energy spin observable x A hbound
  have hc := abs_fieldCovariance_le energy spin observable x v A hcoord hbound
  have hA : 0 ≤ A := (abs_nonneg _).trans hm
  unfold fieldSquareGradient
  rw [abs_mul, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
  calc
    2 * |fieldMean energy spin observable x| * |fieldCovariance energy spin observable x v| ≤
      2 * A * (2 * A) := by gcongr
    _ = 4 * A ^ 2 := by ring

variable [DecidableEq V]

omit [Nonempty S] in
lemma fieldCovariance_coordinate_tilt (energy : S → ℝ) (spin : S → V → ℝ)
    (observable : S → ℝ) (x : V → ℝ) (v : V) (t : ℝ) :
    fieldCovariance energy spin observable (fun u => x u + if u = v then t else 0) v =
      tiltCovariance (fieldEnergy energy spin x) (fun s => spin s v) observable t := by
  simp only [fieldCovariance, fieldMean_coordinate_tilt, tiltCovariance]

theorem hasDerivAt_fieldSquareGradient_coordinate (energy : S → ℝ) (spin : S → V → ℝ)
    (observable : S → ℝ) (x : V → ℝ) (v : V) (t : ℝ)
    (hcoord : ∀ s, spin s v = -1 ∨ spin s v = 1) :
    HasDerivAt (fun r => fieldSquareGradient energy spin observable
        (fun u => x u + if u = v then r else 0) v)
      (fieldSquareHessianDiagonal energy spin observable
        (fun u => x u + if u = v then t else 0) v) t := by
  have hd := ((hasDerivAt_mean_covariance (fieldEnergy energy spin x)
    (fun s => spin s v) observable t).const_mul 2).mul
      (hasDerivAt_tiltCovariance (fieldEnergy energy spin x) (fun s => spin s v)
        observable t hcoord)
  simp only [fieldSquareGradient, fieldSquareHessianDiagonal,
    fieldMean_coordinate_tilt, fieldCovariance_coordinate_tilt]
  change HasDerivAt (fun r => 2 * mean (fieldEnergy energy spin x)
    (fun s => spin s v) observable r *
      tiltCovariance (fieldEnergy energy spin x) (fun s => spin s v) observable r) _ t at hd
  apply hd.congr_deriv
  ring

theorem abs_fieldSquareHessianDiagonal_le (energy : S → ℝ) (spin : S → V → ℝ)
    (observable : S → ℝ) (x : V → ℝ) (v : V) (A : ℝ)
    (hcoord : ∀ s, spin s v = -1 ∨ spin s v = 1)
    (hbound : ∀ s, |observable s| ≤ A) :
    |fieldSquareHessianDiagonal energy spin observable x v| ≤ 16 * A ^ 2 := by
  have hd := (hasDerivAt_fieldSquareGradient_coordinate energy spin observable x v 0 hcoord).deriv
  have hfirst : (fun r => fieldSquareGradient energy spin observable
      (fun u => x u + if u = v then r else 0) v) =
      deriv (fun r => fieldMean energy spin observable
        (fun u => x u + if u = v then r else 0) ^ 2) := by
    funext r
    simp only [fieldSquareGradient, fieldMean_coordinate_tilt, fieldCovariance_coordinate_tilt]
    exact (deriv_mean_square _ _ _ _).symm
  rw [hfirst] at hd
  simp only [ite_self, add_zero] at hd
  rw [← hd]
  exact abs_deriv_deriv_fieldMean_square_coordinate_le energy spin observable x v 0 A hcoord hbound

omit [Fintype V] in
lemma update_eq_zero_shift (x : V → ℝ) (v : V) (t : ℝ) :
    Function.update x v t =
      (fun u => Function.update x v 0 u + if u = v then t else 0) := by
  funext u
  by_cases hu : u = v
  · subst u
    simp
  · simp [hu]

theorem hasDerivAt_fieldSquareGradient_update (energy : S → ℝ) (spin : S → V → ℝ)
    (observable : S → ℝ) (x : V → ℝ) (v : V) (t : ℝ)
    (hcoord : ∀ s, spin s v = -1 ∨ spin s v = 1) :
    HasDerivAt (fun r => fieldSquareGradient energy spin observable (Function.update x v r) v)
      (fieldSquareHessianDiagonal energy spin observable (Function.update x v t) v) t := by
  simpa only [← update_eq_zero_shift] using
    hasDerivAt_fieldSquareGradient_coordinate energy spin observable (Function.update x v 0) v t hcoord

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

theorem integral_fieldSquareGradient_mul_noise
    (energy : S → ℝ) (spin : S → V → ℝ) (observable : S → ℝ)
    (A : ℝ) (hbound : ∀ s, |observable s| ≤ A)
    (hcoords : ∀ s v, spin s v = -1 ∨ spin s v = 1)
    (signal : V → ℝ) (t : ℝ) (v : V) :
    (∫ z, fieldSquareGradient energy spin observable
      (gaussianObservationCurve signal z t) v * z v
      ∂Measure.pi (fun _ : V => gaussianReal 0 1)) =
    Real.sqrt t * ∫ z, fieldSquareHessianDiagonal energy spin observable
      (gaussianObservationCurve signal z t) v
      ∂Measure.pi (fun _ : V => gaussianReal 0 1) := by
  have h := Problem367.gaussian_pi_integral_mul_affine_of_bounded_deriv
    (fun j => t * signal j) (fun _ => Real.sqrt t) v
    (continuous_fieldSquareGradient energy spin observable v)
    (continuous_fieldSquareHessianDiagonal energy spin observable v)
    (fun z r => hasDerivAt_fieldSquareGradient_update energy spin observable z v r
      (fun s => hcoords s v))
    (fun z => abs_fieldSquareGradient_le energy spin observable z v A
      (fun s => hcoords s v) hbound)
    (fun z => abs_fieldSquareHessianDiagonal_le energy spin observable z v A
      (fun s => hcoords s v) hbound)
  simpa only [gaussianObservationCurve, Pi.add_def, Pi.smul_def, smul_eq_mul,
    mul_comm] using h

section Planted

variable [MeasurableSpace S] [MeasurableSingletonClass S]

omit [Nonempty S] [Fintype V] [DecidableEq V] in
lemma measurable_finiteStandardObservation (spin : S → V → ℝ) (t : ℝ) :
    Measurable (finiteStandardObservation spin t) := by
  unfold finiteStandardObservation gaussianObservationCurve
  exact ((measurable_of_finite spin).comp measurable_fst).const_smul t |>.add
    (measurable_snd.const_smul (Real.sqrt t))

omit [DecidableEq V] in
private theorem integrable_bounded_test
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsFiniteMeasure μ]
    (X : Ω → V → ℝ) (hX : Measurable X) (f : (V → ℝ) → ℝ)
    (hf : Continuous f) (C : ℝ) (hbound : ∀ z, |f z| ≤ C) :
    Integrable (fun x => f (X x)) μ := by
  apply Integrable.of_bound (hf.measurable.comp hX).aestronglyMeasurable C
  exact Filter.Eventually.of_forall fun x => by
    simpa only [Real.norm_eq_abs, Function.comp_def] using hbound (X x)

omit [Fintype S] [Nonempty S] [DecidableEq V] [MeasurableSingletonClass S] in

theorem integrable_finiteStandardNoise (μ : Measure S) [IsFiniteMeasure μ] (v : V) :
    Integrable (fun x : S × (V → ℝ) => x.2 v)
      (μ.prod (Measure.pi (fun _ : V => gaussianReal 0 1))) := by
  have h := (measurePreserving_eval (fun _ : V => gaussianReal 0 1) v).integrable_comp_of_integrable ((memLp_id_gaussianReal 1).integrable (by norm_num))
  exact h.comp_snd μ

omit [DecidableEq V] in
theorem integrable_finiteStandardGradient (μ : Measure S) [IsFiniteMeasure μ]
    (energy : S → ℝ) (spin : S → V → ℝ) (observable : S → ℝ)
    (A : ℝ) (hbound : ∀ s, |observable s| ≤ A)
    (hcoords : ∀ s v, spin s v = -1 ∨ spin s v = 1) (t : ℝ) (v : V) :
    Integrable (fun x => fieldSquareGradient energy spin observable
      (finiteStandardObservation spin t x) v)
      (μ.prod (Measure.pi (fun _ : V => gaussianReal 0 1))) :=
  integrable_bounded_test _ _ (measurable_finiteStandardObservation spin t) _
    (continuous_fieldSquareGradient energy spin observable v) (4 * A ^ 2)
    (fun z => abs_fieldSquareGradient_le energy spin observable z v A
      (fun s => hcoords s v) hbound)

theorem integrable_finiteStandardHessian (μ : Measure S) [IsFiniteMeasure μ]
    (energy : S → ℝ) (spin : S → V → ℝ) (observable : S → ℝ)
    (A : ℝ) (hbound : ∀ s, |observable s| ≤ A)
    (hcoords : ∀ s v, spin s v = -1 ∨ spin s v = 1) (t : ℝ) (v : V) :
    Integrable (fun x => fieldSquareHessianDiagonal energy spin observable
      (finiteStandardObservation spin t x) v)
      (μ.prod (Measure.pi (fun _ : V => gaussianReal 0 1))) :=
  integrable_bounded_test _ _ (measurable_finiteStandardObservation spin t) _
    (continuous_fieldSquareHessianDiagonal energy spin observable v) (16 * A ^ 2)
    (fun z => abs_fieldSquareHessianDiagonal_le energy spin observable z v A
      (fun s => hcoords s v) hbound)

omit [DecidableEq V] in
theorem integrable_finiteStandardGradient_mul_noise
    (μ : Measure S) [IsFiniteMeasure μ]
    (energy : S → ℝ) (spin : S → V → ℝ) (observable : S → ℝ)
    (A : ℝ) (hbound : ∀ s, |observable s| ≤ A)
    (hcoords : ∀ s v, spin s v = -1 ∨ spin s v = 1) (t : ℝ) (v : V) :
    Integrable (fun x => fieldSquareGradient energy spin observable
      (finiteStandardObservation spin t x) v * x.2 v)
      (μ.prod (Measure.pi (fun _ : V => gaussianReal 0 1))) := by
  have hg := integrable_finiteStandardGradient μ energy spin observable A hbound hcoords t v
  have h := (integrable_finiteStandardNoise μ v).mul_bdd hg.aestronglyMeasurable
    (Filter.Eventually.of_forall fun x => by
      simpa only [Real.norm_eq_abs, Function.comp_def] using abs_fieldSquareGradient_le energy spin observable
        (finiteStandardObservation spin t x) v A (fun s => hcoords s v) hbound)
  simpa only [mul_comm] using h

theorem integral_finiteStandardGradient_mul_noise
    (μ : Measure S) [IsFiniteMeasure μ]
    (energy : S → ℝ) (spin : S → V → ℝ) (observable : S → ℝ)
    (A : ℝ) (hbound : ∀ s, |observable s| ≤ A)
    (hcoords : ∀ s v, spin s v = -1 ∨ spin s v = 1) (t : ℝ) (v : V) :
    (∫ x, fieldSquareGradient energy spin observable
      (finiteStandardObservation spin t x) v * x.2 v
      ∂μ.prod (Measure.pi (fun _ : V => gaussianReal 0 1))) =
    Real.sqrt t * ∫ x, fieldSquareHessianDiagonal energy spin observable
      (finiteStandardObservation spin t x) v
      ∂μ.prod (Measure.pi (fun _ : V => gaussianReal 0 1)) := by
  rw [integral_prod _ (integrable_finiteStandardGradient_mul_noise
    μ energy spin observable A hbound hcoords t v),
    integral_prod _ (integrable_finiteStandardHessian
    μ energy spin observable A hbound hcoords t v), ← integral_const_mul]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall fun s =>
    integral_fieldSquareGradient_mul_noise energy spin observable A hbound hcoords (spin s) t v

theorem hasDerivAt_finiteStandardEnergy_of_posterior_test
    (μ : Measure S) [IsProbabilityMeasure μ]
    (energy : S → ℝ) (spin : S → V → ℝ) (observable : S → ℝ)
    (A : ℝ) (hbound : ∀ s, |observable s| ≤ A)
    (hcoords : ∀ s v, spin s v = -1 ∨ spin s v = 1)
    {t : ℝ} (ht : 0 < t)
    (hposterior : ∀ v,
      (∫ x, fieldSquareGradient energy spin observable
        (finiteStandardObservation spin t x) v * spin x.1 v
        ∂μ.prod (Measure.pi (fun _ : V => gaussianReal 0 1))) =
      ∫ x, fieldSquareGradient energy spin observable
        (finiteStandardObservation spin t x) v *
          fieldMean energy spin (fun s => spin s v) (finiteStandardObservation spin t x)
        ∂μ.prod (Measure.pi (fun _ : V => gaussianReal 0 1))) :
    HasDerivAt
      (fun r => ∫ x, fieldMean energy spin observable (finiteStandardObservation spin r x) ^ 2
        ∂μ.prod (Measure.pi (fun _ : V => gaussianReal 0 1)))
      (∫ x, ∑ v, fieldCovariance energy spin observable
        (finiteStandardObservation spin t x) v ^ 2
        ∂μ.prod (Measure.pi (fun _ : V => gaussianReal 0 1))) t := by
  let ρ := μ.prod (Measure.pi (fun _ : V => gaussianReal 0 1))
  let Y := finiteStandardObservation spin t
  let g := fun x v => fieldSquareGradient energy spin observable (Y x) v
  let H := fun x v => fieldSquareHessianDiagonal energy spin observable (Y x) v
  let p := fun x v => fieldMean energy spin (fun s => spin s v) (Y x)
  let c := 1 / (2 * Real.sqrt t)
  have hy : Measurable Y := measurable_finiteStandardObservation spin t
  have hg (v : V) : Integrable (fun x => g x v) ρ :=
    integrable_finiteStandardGradient μ energy spin observable A hbound hcoords t v
  have hH (v : V) : Integrable (fun x => H x v) ρ :=
    integrable_finiteStandardHessian μ energy spin observable A hbound hcoords t v
  have hn (v : V) : Integrable (fun x => g x v * x.2 v) ρ :=
    integrable_finiteStandardGradient_mul_noise μ energy spin observable A hbound hcoords t v
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
        fieldCovariance energy spin observable (Y x) v ^ 2 := by
    dsimp [g, H, p, fieldSquareGradient, fieldSquareHessianDiagonal]
    ring
  have hc (v : V) : Integrable
      (fun x => fieldCovariance energy spin observable (Y x) v ^ 2) ρ := by
    exact ((hp v).add ((hH v).const_mul (1 / 2 : ℝ))).congr
      (Filter.Eventually.of_forall fun x => hcancel x v)
  have hstep (v : V) :
      (∫ x, g x v * gaussianObservationVelocity (spin x.1) x.2 t v ∂ρ) =
        ∫ x, fieldCovariance energy spin observable (Y x) v ^ 2 ∂ρ := by
    rw [hvEq, integral_add (hs v) ((hn v).const_mul c), integral_const_mul]
    have hnoise : (∫ x, g x v * x.2 v ∂ρ) = Real.sqrt t * ∫ x, H x v ∂ρ :=
      integral_finiteStandardGradient_mul_noise μ energy spin observable A hbound hcoords t v
    rw [hnoise]
    have hcoef : c * Real.sqrt t = (1 / 2 : ℝ) := by
      dsimp [c]
      field_simp [ne_of_gt (Real.sqrt_pos.mpr ht)]
    rw [← mul_assoc, hcoef, hposterior v]
    rw [← integral_const_mul, ← integral_add (hp v) ((hH v).const_mul (1 / 2 : ℝ))]
    exact integral_congr_ae (Filter.Eventually.of_forall fun x => hcancel x v)
  have hd := hasDerivAt_integral_fieldMean_square_observation ρ energy spin observable A
    hbound hcoords (fun x : S × (V → ℝ) => spin x.1) Prod.snd
    ((measurable_of_finite spin).comp measurable_fst) measurable_snd
    (fun x v => (abs_spin_eq_one (fun s => spin s v) (fun s => hcoords s v) x.1).le)
    (fun v => integrable_finiteStandardNoise μ v) ht
  apply hd.congr_deriv
  change (∫ x, ∑ v, g x v * gaussianObservationVelocity (spin x.1) x.2 t v ∂ρ) = _
  rw [integral_finsetSum _ (fun v _ => hv v), integral_finsetSum _ (fun v _ => hc v)]
  exact Finset.sum_congr rfl fun v _ => hstep v

theorem hasDerivAt_finiteStandardEnergy [StandardBorelSpace S]
    (μ : Measure S) [IsProbabilityMeasure μ] (energy : S → ℝ)
    (hprior : ∀ s, μ.real {s} = Real.exp (energy s) / ∑ a, Real.exp (energy a))
    (spin : S → V → ℝ) (observable : S → ℝ)
    (A : ℝ) (hbound : ∀ s, |observable s| ≤ A)
    (hcoords : ∀ s v, spin s v = -1 ∨ spin s v = 1)
    {t : ℝ} (ht : 0 < t) :
    HasDerivAt
      (fun r => ∫ x, fieldMean energy spin observable (finiteStandardObservation spin r x) ^ 2
        ∂μ.prod (Measure.pi (fun _ : V => gaussianReal 0 1)))
      (∫ x, ∑ v, fieldCovariance energy spin observable
        (finiteStandardObservation spin t x) v ^ 2
        ∂μ.prod (Measure.pi (fun _ : V => gaussianReal 0 1))) t := by
  apply hasDerivAt_finiteStandardEnergy_of_posterior_test μ energy spin observable A hbound hcoords ht
  intro v
  have hsq : ∀ s i, spin s i ^ 2 = 1 := by
    intro s i
    rcases hcoords s i with h | h <;> simp [h]
  exact Problem367.finiteStandardGaussianPlanted_integral_test_fieldMean μ energy hprior t ht.le
    spin hsq (fun s => spin s v) (fun z => fieldSquareGradient energy spin observable z v)
    (continuous_fieldSquareGradient energy spin observable v).measurable (4 * A ^ 2)
    (fun z => by simpa only [Real.norm_eq_abs] using
      abs_fieldSquareGradient_le energy spin observable z v A (fun s => hcoords s v) hbound)

end Planted
end Problem367.FinitePosterior

end

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Posterior_GaussianEnergyIntegral
attribute [-instance] _root_.OAI.Problem367.WienerSampler.pathMeasurableSpace _root_.OAI.Problem367.reducedTailFinite _root_.OAI.Problem367.treeBallFinite _root_.OAI.Problem367.treeShellFinite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped NNReal

namespace Problem367.FinitePosterior

variable {S V : Type*} [Fintype S] [Nonempty S] [Fintype V] [DecidableEq V]
  [MeasurableSpace S] [MeasurableSingletonClass S] [StandardBorelSpace S]

theorem integral_finiteStandardEnergy
    (μ : Measure S) [IsProbabilityMeasure μ]
    (energy : S → ℝ)
    (hprior : ∀ s, μ.real {s} = Real.exp (energy s) / ∑ a, Real.exp (energy a))
    (spin : S → V → ℝ) (observable : S → ℝ)
    (A : ℝ) (hbound : ∀ s, |observable s| ≤ A)
    (hcoords : ∀ s v, spin s v = -1 ∨ spin s v = 1)
    {T : ℝ} (hT : 0 ≤ T) :
    let C : ℝ → ℝ := fun t => ∫ x, ∑ v, fieldCovariance energy spin observable
      (finiteStandardObservation spin t x) v ^ 2
      ∂μ.prod (Measure.pi (fun _ : V => gaussianReal 0 1))
    IntervalIntegrable C volume 0 T ∧
      (∫ t in 0..T, C t) =
        (∫ x, fieldMean energy spin observable (finiteStandardObservation spin T x) ^ 2
          ∂μ.prod (Measure.pi (fun _ : V => gaussianReal 0 1))) -
        fieldMean energy spin observable 0 ^ 2 ∧
      0 ≤ (∫ t in 0..T, C t) ∧ (∫ t in 0..T, C t) ≤ A ^ 2 := by
  let ρ := μ.prod (Measure.pi (fun _ : V => gaussianReal 0 1))
  let E : ℝ → ℝ := fun t => ∫ x,
    fieldMean energy spin observable (finiteStandardObservation spin t x) ^ 2 ∂ρ
  let C : ℝ → ℝ := fun t => ∫ x, ∑ v, fieldCovariance energy spin observable
    (finiteStandardObservation spin t x) v ^ 2 ∂ρ
  have hE : Continuous E := by
    simpa only [E, finiteStandardObservation, gaussianObservationCurve, Pi.pow_apply, Function.comp_def] using
      (continuous_integral_sqrt_observation (P := ρ)
        (((measurable_of_finite spin).comp measurable_fst).aestronglyMeasurable)
        (measurable_snd.aestronglyMeasurable)
        ((continuous_fieldMean energy spin observable).pow 2)
        (fun x => abs_fieldMean_square_le energy spin observable x A hbound))
  have hd (t : ℝ) (ht : 0 < t) : HasDerivAt E (C t) t :=
    hasDerivAt_finiteStandardEnergy μ energy hprior spin observable A
      hbound hcoords ht
  have hCpos (t : ℝ) : 0 ≤ C t :=
    integral_nonneg fun x => Finset.sum_nonneg fun v _ => sq_nonneg _
  have hCI : IntervalIntegrable C volume 0 T := by
    apply intervalIntegral.intervalIntegrable_deriv_of_nonneg hE.continuousOn
    · intro t ht
      exact hd t (by simpa only [min_eq_left hT, max_eq_right hT] using ht.1)
    · exact fun t _ => hCpos t
  have hFTC : (∫ t in 0..T, C t) = E T - E 0 :=
    intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hT hE.continuousOn
      (fun t ht => hd t ht.1) hCI
  have hzero : E 0 = fieldMean energy spin observable 0 ^ 2 := by
    simp [E, finiteStandardObservation, gaussianObservationCurve, ρ]
  have hm : AEStronglyMeasurable
      (fun x => fieldMean energy spin observable (finiteStandardObservation spin T x) ^ 2) ρ :=
    (((continuous_fieldMean energy spin observable).pow 2).measurable.comp
      (measurable_finiteStandardObservation spin T)).aestronglyMeasurable
  have hb (x : S × (V → ℝ)) :
      |fieldMean energy spin observable (finiteStandardObservation spin T x) ^ 2| ≤ A ^ 2 :=
    abs_fieldMean_square_le energy spin observable _ A hbound
  have hInt : Integrable
      (fun x => fieldMean energy spin observable (finiteStandardObservation spin T x) ^ 2) ρ :=
    Integrable.of_bound hm (A ^ 2) (Filter.Eventually.of_forall fun x => by
      simpa only [Real.norm_eq_abs] using hb x)
  have hEbound : E T ≤ A ^ 2 := by
    calc
      E T ≤ ∫ _x, A ^ 2 ∂ρ := integral_mono hInt (integrable_const _) fun x =>
        (le_abs_self _).trans (hb x)
      _ = A ^ 2 := by simp [ρ]
  refine ⟨hCI, ?_, intervalIntegral.integral_nonneg_of_forall hT hCpos, ?_⟩
  · simpa only [hzero] using hFTC
  · rw [hFTC, hzero]
    exact sub_le_self _ (sq_nonneg _) |>.trans hEbound

end Problem367.FinitePosterior

end

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Stochastic_FiniteIsingBrownianEnergy
attribute [-instance] _root_.OAI.Problem367.IsingConditionalCopyBounds.graphLaw_isProbabilityMeasure _root_.OAI.Problem367.IsingObservationFactor.copies_probability _root_.OAI.Problem367.IsingObservationFactor.kernel_markov _root_.OAI.Problem367.IsingObservationInnovation.innovationMap_observationLaw_probability _root_.OAI.Problem367.IsingObservationInnovation.observationLaw_probability _root_.OAI.Problem367.TreeKoopman.labelProbability _root_.OAI.Problem367.WienerSampler.pathMeasurableSpace _root_.OAI.Problem367.freeIsingMeasure_probability _root_.OAI.Problem367.reducedTailFinite _root_.OAI.Problem367.reducedTailFintype _root_.OAI.Problem367.treeBallFinite _root_.OAI.Problem367.treeBallFintype _root_.OAI.Problem367.treeShellFinite _root_.OAI.Problem367.treeShellFintype
attribute [-simp] _root_.OAI.Problem367.ConnectedHull.pathAssignment_path _root_.OAI.Problem367.ConnectedHull.path_last _root_.OAI.Problem367.ConnectedHull.path_zero _root_.OAI.Problem367.ConnectedHull.prefix_length _root_.OAI.Problem367.ConnectedHull.prefix_zero _root_.OAI.Problem367.CutContinuationChannels.averageChannel_globalCone _root_.OAI.Problem367.CutContinuationChannels.continuationChannel_globalCone _root_.OAI.Problem367.FactorObservable.centeredSpinLp_coe _root_.OAI.Problem367.FiniteIsingSplit.splitEquiv_fst _root_.OAI.Problem367.FiniteIsingSplit.splitEquiv_snd _root_.OAI.Problem367.FinitePathGibbs.tailPartition_zero _root_.OAI.Problem367.GaussianTreeResponseNaturality.fieldEquiv_apply_image _root_.OAI.Problem367.IsingObservationInnovation.innovationMap_apply _root_.OAI.Problem367.IsingObservationInnovation.innovationMap_uniformObservation _root_.OAI.Problem367.IsingObservationInnovation.innovationMap_zero _root_.OAI.Problem367.IsingObservationInnovation.uniformObservation_relabel _root_.OAI.Problem367.IsingOrientedPath.attenuation_outward _root_.OAI.Problem367.IsingOrientedPath.endpoint_extensionAt _root_.OAI.Problem367.LocalSupportGeometry.prefixVertex_length _root_.OAI.Problem367.PathSideBranches.parent_sideVertex _root_.OAI.Problem367.PathSideBranches.restrictNoisyRegion_array _root_.OAI.Problem367.PathSideBranches.sideVertex_length _root_.OAI.Problem367.PathSideBranches.sideVertex_val _root_.OAI.Problem367.PosteriorChain.transition_spinMean _root_.OAI.Problem367.PosteriorChain.transition_sum _root_.OAI.Problem367.RootedBroadcast.flipBranchToComplement_val _root_.OAI.Problem367.RootedBroadcast.pos_spinMul _root_.OAI.Problem367.RootedBroadcast.prefixFlip_branchRoot _root_.OAI.Problem367.RootedBroadcast.prefixFlip_root _root_.OAI.Problem367.RootedBroadcast.prefixTreeAut_symm_branchRoot _root_.OAI.Problem367.RootedBroadcast.prefixTreeAut_symm_root _root_.OAI.Problem367.RootedBroadcast.spinMul_pos _root_.OAI.Problem367.RootedBroadcast.spinMul_self _root_.OAI.Problem367.TreeConeCoding.length_vertex _root_.OAI.Problem367.TreeConeCoding.vertex_nil _root_.OAI.Problem367.TreeConeCoding.vertex_val _root_.OAI.Problem367.TreeGibbsAut.spinEquiv_apply_image _root_.OAI.Problem367.TreeKoopman.centeredAverage_apply_coe _root_.OAI.Problem367.TreeKoopman.centeredAverage_pow_apply_coe _root_.OAI.Problem367.TreeKoopman.centeredGenerator_apply_coe _root_.OAI.Problem367.TreeKoopman.centeredGenerator_sq _root_.OAI.Problem367.TreeKoopman.generatorOperator_sq _root_.OAI.Problem367.TreeKoopman.reverseVertex_twice _root_.OAI.Problem367.TreeKoopman.wordRelabel_cons _root_.OAI.Problem367.TreeKoopman.wordRelabel_nil _root_.OAI.Problem367.TreeLawKoopman.centeredAverage_apply_coe _root_.OAI.Problem367.TreeLawKoopman.generatorOperator_sq _root_.OAI.Problem367.TreePathGibbs.vertexEquiv_val _root_.OAI.Problem367.branchColorAut_length _root_.OAI.Problem367.branchColorAut_singleton _root_.OAI.Problem367.branchColorAut_val _root_.OAI.Problem367.branchColorMap_symm_apply _root_.OAI.Problem367.card_treeBallFinset _root_.OAI.Problem367.card_treeNeighborFinset _root_.OAI.Problem367.colorPermAut_length _root_.OAI.Problem367.colorPermAut_nil _root_.OAI.Problem367.colorPermAut_val _root_.OAI.Problem367.colorPermMap_symm_apply _root_.OAI.Problem367.colorPermMap_val _root_.OAI.Problem367.connectedSpinEncode_apply_root _root_.OAI.Problem367.connectedSpinEquiv_apply _root_.OAI.Problem367.dropVertex_length _root_.OAI.Problem367.dropVertex_val _root_.OAI.Problem367.iUnion_treeBallFinset _root_.OAI.Problem367.mem_rootComplementFinset _root_.OAI.Problem367.mem_rootComponentFinset _root_.OAI.Problem367.mem_rootComponentIndices _root_.OAI.Problem367.mem_treeBallFinset _root_.OAI.Problem367.mem_treeNeighborFinset _root_.OAI.Problem367.parentVertex_length _root_.OAI.Problem367.parentVertex_val _root_.OAI.Problem367.prefixColorAut_length _root_.OAI.Problem367.prefixColorAut_val _root_.OAI.Problem367.prefixColorMap_symm_apply _root_.OAI.Problem367.prefixFlip_twice _root_.OAI.Problem367.spinAgreementCode_eq_neg_iff _root_.OAI.Problem367.spinAgreementCode_eq_pos_iff _root_.OAI.Problem367.spinSign_flip _root_.OAI.Problem367.sum_treeShell_zero _root_.OAI.Problem367.tsum_treeShell_radial _root_.OAI.Problem367.vertexSampler_relabel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory ProbabilityTheory Set
open scoped NNReal ENNReal

namespace Problem367

local instance finiteIsingBrownianEnergyNonemptySpin : Nonempty IsingSpin := ⟨.neg⟩

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

theorem HasFreeIsingLaw.integral_finiteIsingBrownianEnergy
    {d : ℕ} {beta : ℝ} {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure (TreeVertex d → IsingSpin)}
    (hμ : HasFreeIsingLaw (Real.tanh beta) μ)
    (ν : TreeVertex d → Measure Ω)
    {B : TreeVertex d → ℝ≥0 → Ω → ℝ}
    (hB : ∀ i, IsPreBrownianReal (B i) (ν i))
    (hmB : ∀ i t, Measurable (B i t))
    (D : Finset (TreeVertex d)) (hD : ConnectedFinset D) (v : D)
    {T : ℝ} (hT : 0 ≤ T) :
    let ρ := μ.prod (Measure.infinitePi ν)
    let E : ℝ → ℝ := fun t => ∫ p,
      ∑ u : D, finiteIsingBrownianCovariance beta D v u B t p ^ 2 ∂ρ
    IntervalIntegrable E volume 0 T ∧
      (∫ t in 0..T, E t) =
        (∫ p, finiteIsingBrownianMean beta D v B T p ^ 2 ∂ρ) ∧
      0 ≤ (∫ t in 0..T, E t) ∧ (∫ t in 0..T, E t) ≤ 1 := by
  classical
  let : IsProbabilityMeasure μ := hμ.isProbabilityMeasure
  let π := μ.map D.restrict
  let : IsProbabilityMeasure π := by first | (set_option synthInstance.maxHeartbeats 20000 in infer_instance) | exact Measure.isProbabilityMeasure_map (by first | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability)
  let spin : (D → IsingSpin) → D → ℝ := fun eta u => spinSign (eta u)
  let q : (D → IsingSpin) → ℝ := fun eta => spinSign (eta v)
  let F : (D → ℝ) → ℝ := FinitePosterior.fieldMean (finiteIsingEnergy beta D) spin q
  let C : (D → ℝ) → D → ℝ :=
    FinitePosterior.fieldCovariance (finiteIsingEnergy beta D) spin q
  let ρ := μ.prod (Measure.infinitePi ν)
  let ρG := π.prod (Measure.pi fun _ : D => gaussianReal 0 1)
  let EG : ℝ → ℝ := fun t => ∫ p,
    ∑ u : D, C (FinitePosterior.finiteStandardObservation spin t p) u ^ 2 ∂ρG
  let MG : ℝ → ℝ := fun t => ∫ p,
    F (FinitePosterior.finiteStandardObservation spin t p) ^ 2 ∂ρG
  let E : ℝ → ℝ := fun t => ∫ p,
    ∑ u : D, finiteIsingBrownianCovariance beta D v u B t p ^ 2 ∂ρ
  let M : ℝ → ℝ := fun t => ∫ p,
    finiteIsingBrownianMean beta D v B t p ^ 2 ∂ρ
  have hfm : Measurable (fun y => F y ^ 2) :=
    ((FinitePosterior.continuous_fieldMean _ _ _).pow 2).measurable
  have hcm : Measurable (fun y => ∑ u : D, C y u ^ 2) := by
    apply Finset.measurable_sum
    intro u _
    exact ((FinitePosterior.continuous_fieldCovariance _ _ _ u).pow 2).measurable
  have hE (t : ℝ) (ht : 0 ≤ t) : E t = EG t := by
    have h := integral_finiteIsingBrownian_observation_eq_standard μ ν hB hmB D
      t.toNNReal (fun y => ∑ u : D, C y u ^ 2) hcm
    unfold E EG finiteIsingBrownianCovariance finiteIsingBrownianObservation
    simpa only [C, spin, q, ρ, ρG, π, Real.coe_toNNReal t ht] using h
  have hM (t : ℝ) (ht : 0 ≤ t) : M t = MG t := by
    have h := integral_finiteIsingBrownian_observation_eq_standard μ ν hB hmB D
      t.toNNReal (fun y => F y ^ 2) hfm
    unfold M MG finiteIsingBrownianMean finiteIsingBrownianObservation
    simpa only [F, spin, q, ρ, ρG, π, Real.coe_toNNReal t ht] using h
  have hcoords (eta : D → IsingSpin) (u : D) : spin eta u = -1 ∨ spin eta u = 1 := by
    dsimp only [spin]
    cases eta u <;> simp [spinSign]
  have hbound (eta : D → IsingSpin) : |q eta| ≤ 1 := by
    dsimp only [q]
    cases eta v <;> simp [spinSign]
  have hstd := FinitePosterior.integral_finiteStandardEnergy π
    (finiteIsingEnergy beta D) (hμ.restrict_real_eq_normalized_exp D hD)
    spin q 1 hbound hcoords hT
  change IntervalIntegrable EG volume 0 T ∧
    (∫ t in 0..T, EG t) = MG T - F 0 ^ 2 ∧
    0 ≤ (∫ t in 0..T, EG t) ∧ (∫ t in 0..T, EG t) ≤ (1 : ℝ) ^ 2 at hstd
  have hzero : F 0 = 0 := finiteIsingPosterior_spin_zero beta D v
  have hEq : EqOn EG E (uIcc 0 T) := by
    intro t ht
    exact (hE t (by simpa only [min_eq_left hT] using ht.1)).symm
  have hInt : (∫ t in 0..T, EG t) = ∫ t in 0..T, E t :=
    intervalIntegral.integral_congr hEq
  change IntervalIntegrable E volume 0 T ∧
    (∫ t in 0..T, E t) = M T ∧
    0 ≤ (∫ t in 0..T, E t) ∧ (∫ t in 0..T, E t) ≤ 1
  refine ⟨hstd.1.congr (fun t ht => hEq (uIoc_subset_uIcc ht)), ?_, ?_, ?_⟩
  · rw [← hInt, hstd.2.1, hzero, zero_pow (by decide), sub_zero, hM T hT]
  · simpa only [hInt] using hstd.2.2.1
  · simpa only [hInt, one_pow] using hstd.2.2.2

end Problem367

end

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Energy_FiniteIsingEnergyLimit
attribute [-instance] _root_.OAI.Problem367.IsingConditionalCopyBounds.graphLaw_isProbabilityMeasure _root_.OAI.Problem367.IsingObservationFactor.copies_probability _root_.OAI.Problem367.IsingObservationFactor.kernel_markov _root_.OAI.Problem367.IsingObservationInnovation.innovationMap_observationLaw_probability _root_.OAI.Problem367.IsingObservationInnovation.observationLaw_probability _root_.OAI.Problem367.TreeKoopman.labelProbability _root_.OAI.Problem367.WienerSampler.pathMeasurableSpace _root_.OAI.Problem367.freeIsingMeasure_probability
attribute [-simp] _root_.OAI.Problem367.ConnectedHull.pathAssignment_path _root_.OAI.Problem367.ConnectedHull.path_last _root_.OAI.Problem367.ConnectedHull.path_zero _root_.OAI.Problem367.CutContinuationChannels.averageChannel_globalCone _root_.OAI.Problem367.CutContinuationChannels.continuationChannel_globalCone _root_.OAI.Problem367.FactorObservable.centeredSpinLp_coe _root_.OAI.Problem367.FiniteIsingSplit.splitEquiv_fst _root_.OAI.Problem367.FiniteIsingSplit.splitEquiv_snd _root_.OAI.Problem367.FinitePathGibbs.tailPartition_zero _root_.OAI.Problem367.GaussianTreeResponseNaturality.fieldEquiv_apply_image _root_.OAI.Problem367.IsingObservationInnovation.innovationMap_apply _root_.OAI.Problem367.IsingObservationInnovation.innovationMap_uniformObservation _root_.OAI.Problem367.IsingObservationInnovation.innovationMap_zero _root_.OAI.Problem367.IsingObservationInnovation.uniformObservation_relabel _root_.OAI.Problem367.IsingOrientedPath.attenuation_outward _root_.OAI.Problem367.IsingOrientedPath.endpoint_extensionAt _root_.OAI.Problem367.LocalSupportGeometry.prefixVertex_length _root_.OAI.Problem367.PathSideBranches.parent_sideVertex _root_.OAI.Problem367.PathSideBranches.restrictNoisyRegion_array _root_.OAI.Problem367.PathSideBranches.sideVertex_length _root_.OAI.Problem367.PathSideBranches.sideVertex_val _root_.OAI.Problem367.PosteriorChain.transition_spinMean _root_.OAI.Problem367.PosteriorChain.transition_sum _root_.OAI.Problem367.RootedBroadcast.flipBranchToComplement_val _root_.OAI.Problem367.RootedBroadcast.pos_spinMul _root_.OAI.Problem367.RootedBroadcast.prefixFlip_branchRoot _root_.OAI.Problem367.RootedBroadcast.prefixFlip_root _root_.OAI.Problem367.RootedBroadcast.prefixTreeAut_symm_branchRoot _root_.OAI.Problem367.RootedBroadcast.prefixTreeAut_symm_root _root_.OAI.Problem367.RootedBroadcast.spinMul_pos _root_.OAI.Problem367.RootedBroadcast.spinMul_self _root_.OAI.Problem367.TreeConeCoding.length_vertex _root_.OAI.Problem367.TreeConeCoding.vertex_nil _root_.OAI.Problem367.TreeConeCoding.vertex_val _root_.OAI.Problem367.TreeGibbsAut.spinEquiv_apply_image _root_.OAI.Problem367.TreeKoopman.centeredAverage_apply_coe _root_.OAI.Problem367.TreeKoopman.centeredAverage_pow_apply_coe _root_.OAI.Problem367.TreeKoopman.centeredGenerator_apply_coe _root_.OAI.Problem367.TreeKoopman.centeredGenerator_sq _root_.OAI.Problem367.TreeKoopman.generatorOperator_sq _root_.OAI.Problem367.TreeKoopman.reverseVertex_twice _root_.OAI.Problem367.TreeKoopman.wordRelabel_cons _root_.OAI.Problem367.TreeKoopman.wordRelabel_nil _root_.OAI.Problem367.TreeLawKoopman.centeredAverage_apply_coe _root_.OAI.Problem367.TreeLawKoopman.generatorOperator_sq _root_.OAI.Problem367.TreePathGibbs.vertexEquiv_val _root_.OAI.Problem367.branchColorAut_length _root_.OAI.Problem367.branchColorAut_singleton _root_.OAI.Problem367.branchColorAut_val _root_.OAI.Problem367.branchColorMap_symm_apply _root_.OAI.Problem367.colorPermAut_length _root_.OAI.Problem367.colorPermAut_nil _root_.OAI.Problem367.colorPermAut_val _root_.OAI.Problem367.colorPermMap_symm_apply _root_.OAI.Problem367.colorPermMap_val _root_.OAI.Problem367.connectedSpinEncode_apply_root _root_.OAI.Problem367.connectedSpinEquiv_apply _root_.OAI.Problem367.dropVertex_length _root_.OAI.Problem367.dropVertex_val _root_.OAI.Problem367.mem_rootComplementFinset _root_.OAI.Problem367.mem_rootComponentFinset _root_.OAI.Problem367.mem_rootComponentIndices _root_.OAI.Problem367.parentVertex_length _root_.OAI.Problem367.parentVertex_val _root_.OAI.Problem367.prefixColorAut_length _root_.OAI.Problem367.prefixColorAut_val _root_.OAI.Problem367.prefixColorMap_symm_apply _root_.OAI.Problem367.prefixFlip_twice _root_.OAI.Problem367.spinAgreementCode_eq_neg_iff _root_.OAI.Problem367.spinAgreementCode_eq_pos_iff _root_.OAI.Problem367.spinSign_flip _root_.OAI.Problem367.tsum_treeShell_radial _root_.OAI.Problem367.vertexSampler_relabel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology NNReal ENNReal

namespace Problem367

lemma measurable_brownianIsingObservationR
    {d : ℕ} {Ω : Type*} [MeasurableSpace Ω]
    {B : TreeVertex d → ℝ≥0 → Ω → ℝ}
    (hmB : ∀ i t, Measurable (B i t))
    (hcB : ∀ i omega, Continuous (fun t => B i t omega)) :
    Measurable (brownianIsingObservationR B) := by
  apply Measurable.of_eval
  intro i
  apply measurable_uncurry_of_continuous_of_measurable
    (u := fun (t : ℝ) (p : (TreeVertex d → IsingSpin) × (TreeVertex d → Ω)) =>
      t * spinSign (p.1 i) + B i t.toNNReal (p.2 i))
  · intro p
    exact (continuous_id.mul continuous_const).add
      ((hcB i (p.2 i)).comp continuous_real_toNNReal)
  · intro t
    exact (measurable_const.mul ((measurable_of_finite spinSign).comp
      ((measurable_pi_apply i).comp measurable_fst))).add
      ((hmB i t.toNNReal).comp ((measurable_pi_apply i).comp measurable_snd))

lemma finiteGibbsCovariance_eq_finiteIsingBrownianCovariance
    {d : ℕ} {Ω : Type*} (beta : ℝ) (v : TreeVertex d) (n : ℕ)
    (B : TreeVertex d → ℝ≥0 → Ω → ℝ)
    (p : ℝ × ((TreeVertex d → IsingSpin) × (TreeVertex d → Ω)))
    (u : connectedExhaustion v n) :
    finiteGibbsCovariance beta v u n (brownianIsingObservationR B p) =
      finiteIsingBrownianCovariance beta (connectedExhaustion v n)
        ⟨v, mem_connectedExhaustion v n⟩ u B p.1 p.2 := by
  classical
  simp only [finiteGibbsCovariance, dite_eq_left u.property]
  rfl

theorem HasFreeIsingLaw.finiteGibbsCovariance_timeEnergy_le_one
    {d : ℕ} {beta : ℝ} {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure (TreeVertex d → IsingSpin)}
    (hμ : HasFreeIsingLaw (Real.tanh beta) μ)
    (ν : TreeVertex d → Measure Ω) {B : TreeVertex d → ℝ≥0 → Ω → ℝ}
    (hB : ∀ i, IsPreBrownianReal (B i) (ν i))
    (hmB : ∀ i t, Measurable (B i t))
    (hcB : ∀ i omega, Continuous (fun t => B i t omega))
    (v : TreeVertex d) (n : ℕ) {T : ℝ} (hT : 0 ≤ T) :
    (∫ p, ∑ u ∈ connectedExhaustion v n,
      finiteGibbsCovariance beta v u n (brownianIsingObservationR B p) ^ 2
      ∂(volume.restrict (Ioc (0 : ℝ) T)).prod (μ.prod (Measure.infinitePi ν))) ≤ 1 := by
  classical
  let : IsProbabilityMeasure μ := hμ.isProbabilityMeasure
  have (index : TreeVertex d) : IsProbabilityMeasure (ν index) :=
    (hB index).isGaussianProcess.isProbabilityMeasure
  let D := connectedExhaustion v n
  let ρ := μ.prod (Measure.infinitePi ν)
  let τ : Measure ℝ := volume.restrict (Ioc 0 T)
  have hX := measurable_brownianIsingObservationR hmB hcB
  have hi (u : TreeVertex d) : Integrable
      (fun p => finiteGibbsCovariance beta v u n (brownianIsingObservationR B p) ^ 2)
      (τ.prod ρ) := by
    apply Integrable.of_bound
      (((continuous_finiteGibbsCovariance beta v u n).measurable.comp hX).pow_const 2).aestronglyMeasurable 4
    filter_upwards with p
    have h := finiteGibbsCovariance_abs_le_two beta v u n (brownianIsingObservationR B p)
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    have hb := (sq_le_sq₀ (abs_nonneg _) (by norm_num : (0 : ℝ) ≤ 2)).mpr h
    norm_num only [sq_abs] at hb
    simpa only [Function.comp_def] using hb
  have hsum : Integrable (fun p => ∑ u ∈ D,
      finiteGibbsCovariance beta v u n (brownianIsingObservationR B p) ^ 2) (τ.prod ρ) :=
    integrable_finsetSum D (fun u _ => hi u)
  have heq (p : ℝ × ((TreeVertex d → IsingSpin) × (TreeVertex d → Ω))) :
      (∑ u ∈ D, finiteGibbsCovariance beta v u n (brownianIsingObservationR B p) ^ 2) =
      ∑ u : D, finiteIsingBrownianCovariance beta D
        ⟨v, mem_connectedExhaustion v n⟩ u B p.1 p.2 ^ 2 := by
    rw [← Finset.sum_attach D]
    apply Finset.sum_congr rfl
    intro u _
    rw [finiteGibbsCovariance_eq_finiteIsingBrownianCovariance]
  have he := hμ.integral_finiteIsingBrownianEnergy ν hB hmB D
    (connectedExhaustion_connected v n) ⟨v, mem_connectedExhaustion v n⟩ hT
  dsimp only at he
  calc
    (∫ p, ∑ u ∈ D,
        finiteGibbsCovariance beta v u n (brownianIsingObservationR B p) ^ 2 ∂τ.prod ρ) =
      ∫ t, ∫ p, ∑ u ∈ D,
        finiteGibbsCovariance beta v u n (brownianIsingObservationR B (t, p)) ^ 2 ∂ρ ∂τ :=
      integral_prod _ hsum
    _ = ∫ t in (0 : ℝ)..T, ∫ p, ∑ u : D,
        finiteIsingBrownianCovariance beta D ⟨v, mem_connectedExhaustion v n⟩ u B t p ^ 2 ∂ρ := by
      rw [intervalIntegral.integral_of_le hT]
      apply integral_congr_ae
      filter_upwards with t
      apply integral_congr_ae
      filter_upwards with p
      exact heq (t, p)
    _ ≤ 1 := he.2.2.2

theorem HasFreeIsingLaw.finiteGibbsCovariance_tendsto_timeSquareIntegral
    {d : ℕ} {beta : ℝ} {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure (TreeVertex d → IsingSpin)}
    (hμ : HasFreeIsingLaw (Real.tanh beta) μ)
    (ν : TreeVertex d → Measure Ω) {B : TreeVertex d → ℝ≥0 → Ω → ℝ}
    (hB : ∀ i, IsPreBrownianReal (B i) (ν i))
    (hmB : ∀ i t, Measurable (B i t))
    (hcB : ∀ i omega, Continuous (fun t => B i t omega))
    (v w : TreeVertex d) {T : ℝ} :
    Tendsto (fun n => ∫ p,
      finiteGibbsCovariance beta v w n (brownianIsingObservationR B p) ^ 2
        ∂(volume.restrict (Ioc (0 : ℝ) T)).prod (μ.prod (Measure.infinitePi ν))) atTop
      (𝓝 (∫ p, infiniteGibbsCovariance beta v w (brownianIsingObservationR B p) ^ 2
        ∂(volume.restrict (Ioc (0 : ℝ) T)).prod (μ.prod (Measure.infinitePi ν)))) := by
  let : IsProbabilityMeasure μ := hμ.isProbabilityMeasure
  have (index : TreeVertex d) : IsProbabilityMeasure (ν index) :=
    (hB index).isGaussianProcess.isProbabilityMeasure
  let ρ := μ.prod (Measure.infinitePi ν)
  let τ : Measure ℝ := volume.restrict (Ioc 0 T)
  have hX := measurable_brownianIsingObservationR hmB hcB
  have hm (n : ℕ) := ((continuous_finiteGibbsCovariance beta v w n).measurable.comp hX)
  have hy := (measurable_infiniteGibbsCovariance beta v w).comp hX
  have hlim : ∀ᵐ p ∂τ.prod ρ,
      Tendsto (fun n => finiteGibbsCovariance beta v w n (brownianIsingObservationR B p)) atTop
        (𝓝 (infiniteGibbsCovariance beta v w (brownianIsingObservationR B p))) := by
    apply (Measure.ae_prod_iff_ae_ae (measurableSet_tendsto_fun hm hy)).mpr
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
    have h := hμ.finiteGibbsCovariance_brownian_tendsto_ae ν hB hmB t.toNNReal v w
    unfold brownianIsingObservationR
    simpa only [Function.comp_def, ρ, Real.coe_toNNReal t ht.1.le] using h
  apply tendsto_integral_of_dominated_convergence (fun _ => (4 : ℝ))
    (fun n => ((hm n).pow_const 2).aestronglyMeasurable) (integrable_const 4)
  · intro n
    filter_upwards with p
    have h := finiteGibbsCovariance_abs_le_two beta v w n (brownianIsingObservationR B p)
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    have hb := (sq_le_sq₀ (abs_nonneg _) (by norm_num : (0 : ℝ) ≤ 2)).mpr h
    norm_num only [sq_abs] at hb
    simpa only [Function.comp_def] using hb
  · exact hlim.mono (fun p hp => hp.pow 2)

theorem HasFreeIsingLaw.infiniteGibbsCovariance_timeEnergy
    {d : ℕ} {beta : ℝ} {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure (TreeVertex d → IsingSpin)}
    (hμ : HasFreeIsingLaw (Real.tanh beta) μ)
    (ν : TreeVertex d → Measure Ω) {B : TreeVertex d → ℝ≥0 → Ω → ℝ}
    (hB : ∀ i, IsPreBrownianReal (B i) (ν i))
    (hmB : ∀ i t, Measurable (B i t))
    (hcB : ∀ i omega, Continuous (fun t => B i t omega))
    (v : TreeVertex d) {T : ℝ} (hT : 0 ≤ T) :
    let P := (volume.restrict (Ioc (0 : ℝ) T)).prod (μ.prod (Measure.infinitePi ν))
    let C := fun w p => infiniteGibbsCovariance beta v w (brownianIsingObservationR B p)
    Summable (fun w => ∫ p, C w p ^ 2 ∂P) ∧
      (∑' w, ∫ p, C w p ^ 2 ∂P) ≤ 1 ∧
      (∀ᵐ p ∂P, Summable (fun w => C w p ^ 2)) ∧
      Integrable (fun p => ∑' w, C w p ^ 2) P ∧
      (∫ p, ∑' w, C w p ^ 2 ∂P) ≤ 1 := by
  classical
  let : IsProbabilityMeasure μ := hμ.isProbabilityMeasure
  have (index : TreeVertex d) : IsProbabilityMeasure (ν index) :=
    (hB index).isGaussianProcess.isProbabilityMeasure
  let P := (volume.restrict (Ioc (0 : ℝ) T)).prod (μ.prod (Measure.infinitePi ν))
  let C := fun w p => infiniteGibbsCovariance beta v w (brownianIsingObservationR B p)
  let Cn := fun n w p => finiteGibbsCovariance beta v w n (brownianIsingObservationR B p)
  have hX := measurable_brownianIsingObservationR hmB hcB
  have hm (w : TreeVertex d) : Measurable (C w) :=
    (measurable_infiniteGibbsCovariance beta v w).comp hX
  have hmn (n : ℕ) (w : TreeVertex d) : Measurable (Cn n w) :=
    (continuous_finiteGibbsCovariance beta v w n).measurable.comp hX
  have hi (w : TreeVertex d) : Integrable (fun p => C w p ^ 2) P := by
    apply Integrable.of_bound ((hm w).pow_const 2).aestronglyMeasurable 4
    filter_upwards with p
    have h := infiniteGibbsCovariance_abs_le_two beta v w (brownianIsingObservationR B p)
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    have hb := (sq_le_sq₀ (abs_nonneg _) (by norm_num : (0 : ℝ) ≤ 2)).mpr h
    norm_num only [sq_abs] at hb
    exact hb
  have hin (n : ℕ) (w : TreeVertex d) : Integrable (fun p => Cn n w p ^ 2) P := by
    apply Integrable.of_bound ((hmn n w).pow_const 2).aestronglyMeasurable 4
    filter_upwards with p
    have h := finiteGibbsCovariance_abs_le_two beta v w n (brownianIsingObservationR B p)
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    have hb := (sq_le_sq₀ (abs_nonneg _) (by norm_num : (0 : ℝ) ≤ 2)).mpr h
    norm_num only [sq_abs] at hb
    exact hb
  have hevent (S : Finset (TreeVertex d)) :
      ∀ᶠ n in atTop, S ⊆ connectedExhaustion v n := by
    induction S using Finset.induction_on with
    | empty => exact Eventually.of_forall fun _ => Finset.empty_subset _
    | @insert w S hw ih =>
      filter_upwards [eventually_mem_connectedExhaustion v w, ih] with n hn hS
      exact Finset.insert_subset hn hS
  have hpartial (S : Finset (TreeVertex d)) (n : ℕ)
      (hS : S ⊆ connectedExhaustion v n) :
      (∑ w ∈ S, ∫ p, Cn n w p ^ 2 ∂P) ≤ 1 := by
    rw [← integral_finsetSum S (fun w _ => hin n w)]
    apply le_trans (integral_mono_ae
      (integrable_finsetSum S (fun w _ => hin n w))
      (integrable_finsetSum (connectedExhaustion v n) (fun w _ => hin n w))
      (Eventually.of_forall (fun p =>
        Finset.sum_le_sum_of_subset_of_nonneg hS (fun w _ _ => sq_nonneg (Cn n w p)))))
    exact hμ.finiteGibbsCovariance_timeEnergy_le_one ν hB hmB hcB v n hT
  have hbound (S : Finset (TreeVertex d)) :
      (∑ w ∈ S, ∫ p, C w p ^ 2 ∂P) ≤ 1 := by
    apply le_of_tendsto
      (tendsto_finsetSum S (fun w _ =>
        hμ.finiteGibbsCovariance_tendsto_timeSquareIntegral ν hB hmB hcB v w))
    exact (hevent S).mono (fun n hn => hpartial S n hn)
  have hs : Summable (fun w => ∫ p, C w p ^ 2 ∂P) :=
    summable_of_sum_le (fun w => integral_nonneg (fun p => sq_nonneg (C w p))) hbound
  have hle : (∑' w, ∫ p, C w p ^ 2 ∂P) ≤ 1 := hs.tsum_le_of_sum_le hbound
  have hrow := DiscrepancyEnergy.sq_row_integrable_of_summable_integrals hi hs
  have hident := DiscrepancyEnergy.hasSum_integral_sq_row
    (fun w => (hm w).aestronglyMeasurable) hrow.1 hrow.2
  dsimp only
  refine ⟨hs, hle, hrow.1, hrow.2, ?_⟩
  rw [← hident.tsum_eq]
  exact hle

end Problem367

end

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Energy_FiniteLeafCovariance
attribute [-instance] _root_.OAI.Problem367.IsingConditionalCopyBounds.graphLaw_isProbabilityMeasure _root_.OAI.Problem367.IsingObservationFactor.copies_probability _root_.OAI.Problem367.IsingObservationFactor.kernel_markov _root_.OAI.Problem367.IsingObservationInnovation.innovationMap_observationLaw_probability _root_.OAI.Problem367.IsingObservationInnovation.observationLaw_probability _root_.OAI.Problem367.freeIsingMeasure_probability _root_.OAI.Problem367.reducedTailFintype _root_.OAI.Problem367.treeBallFintype _root_.OAI.Problem367.treeShellFintype
attribute [-simp] _root_.OAI.Problem367.ConnectedHull.pathAssignment_path _root_.OAI.Problem367.CutContinuationChannels.averageChannel_globalCone _root_.OAI.Problem367.CutContinuationChannels.continuationChannel_globalCone _root_.OAI.Problem367.FactorObservable.centeredSpinLp_coe _root_.OAI.Problem367.FiniteIsingSplit.splitEquiv_fst _root_.OAI.Problem367.FiniteIsingSplit.splitEquiv_snd _root_.OAI.Problem367.FinitePathGibbs.tailPartition_zero _root_.OAI.Problem367.IsingObservationInnovation.uniformObservation_relabel _root_.OAI.Problem367.IsingSpin.flip_eq_iff _root_.OAI.Problem367.IsingSpin.flip_flip _root_.OAI.Problem367.IsingSpin.toReal_neg _root_.OAI.Problem367.IsingSpin.toReal_pos _root_.OAI.Problem367.PathSideBranches.restrictNoisyRegion_array _root_.OAI.Problem367.PosteriorChain.transition_spinMean _root_.OAI.Problem367.PosteriorChain.transition_sum _root_.OAI.Problem367.RootedBroadcast.pos_spinMul _root_.OAI.Problem367.RootedBroadcast.spinMul_pos _root_.OAI.Problem367.RootedBroadcast.spinMul_self _root_.OAI.Problem367.TreeGibbsAut.spinEquiv_apply_image _root_.OAI.Problem367.connectedSpinEncode_apply_root _root_.OAI.Problem367.connectedSpinEquiv_apply _root_.OAI.Problem367.extendFiniteSpin_apply _root_.OAI.Problem367.finiteFreeIsingPMF_apply _root_.OAI.Problem367.flipConfig_apply _root_.OAI.Problem367.flipConfig_flipConfig _root_.OAI.Problem367.flipConfig_preimage_spin _root_.OAI.Problem367.freeCylinderWeight_flipConfig _root_.OAI.Problem367.freeCylinderWeight_singleton _root_.OAI.Problem367.restrict_extendFiniteSpin _root_.OAI.Problem367.spinAgreementCode_eq_neg_iff _root_.OAI.Problem367.spinAgreementCode_eq_pos_iff _root_.OAI.Problem367.spinSign_flip
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open scoped BigOperators

namespace Problem367.LeafGibbs

theorem expectation_eq_mean_zero {A : Type*} [Fintype A] (E f : A → ℝ) :
    expectation E f = FinitePosterior.mean E (fun _ => 0) f 0 := by
  simp only [expectation, FinitePosterior.mean, FinitePosterior.partition,
    FinitePosterior.weight, zero_mul, add_zero]

lemma expectation_add {A : Type*} [Fintype A] (E f g : A → ℝ) :
    expectation E (fun a => f a + g a) = expectation E f + expectation E g := by
  simp only [expectation, add_mul, Finset.sum_add_distrib, add_div]

lemma expectation_const_mul {A : Type*} [Fintype A] (E f : A → ℝ) (c : ℝ) :
    expectation E (fun a => c * f a) = c * expectation E f := by
  simp only [expectation, mul_assoc, ← Finset.mul_sum, mul_div_assoc]

lemma expectation_const {A : Type*} [Fintype A] [Nonempty A] (E : A → ℝ) (c : ℝ) :
    expectation E (fun _ => c) = c := by
  have hpos : 0 < ∑ a, Real.exp (E a) :=
    Finset.sum_pos (fun a _ => Real.exp_pos _) Finset.univ_nonempty
  simp only [expectation, ← Finset.mul_sum]
  exact mul_div_cancel_right₀ c hpos.ne'

lemma spin_exponential_mean (z : ℝ) :
    (∑ l : IsingSpin, spinSign l * Real.exp (z * spinSign l)) =
      Real.tanh z * ∑ l : IsingSpin, Real.exp (z * spinSign l) := by
  simp only [sum_isingSpin, spinSign_neg, spinSign_pos, mul_neg_one,
    mul_one, neg_one_mul, one_mul]
  rw [Real.tanh_eq_sinh_div_cosh, Real.sinh_eq, Real.cosh_eq]
  have hpos : Real.exp z + Real.exp (-z) ≠ 0 :=
    ne_of_gt (add_pos (Real.exp_pos _) (Real.exp_pos _))
  field_simp
  ring

lemma tanh_leaf_affine (beta y : ℝ) (s : IsingSpin) :
    Real.tanh (y + beta * spinSign s) =
      (Real.tanh (y + beta) + Real.tanh (y - beta)) / 2 +
        (Real.tanh beta * responseAttenuation (Real.tanh beta) y) * spinSign s := by
  have hs : Real.tanh beta * responseAttenuation (Real.tanh beta) y =
      (Real.tanh (y + beta) - Real.tanh (y - beta)) / 2 := by
    simpa only [responseAttenuation, mul_div_assoc] using (tanh_field_difference_eq beta y).symm
  rw [hs]
  cases s <;> simp only [spinSign_neg, spinSign_pos, mul_neg_one, mul_one, ← sub_eq_add_neg] <;> ring

theorem expectation_mul_leaf_eq {A : Type*} [Fintype A]
    (E f : A → ℝ) (parent : A → IsingSpin) (beta y : ℝ) :
    expectation (energy E parent beta y) (fun s => f s.1 * spinSign s.2) =
    expectation (energy E parent beta y)
      (fun s => f s.1 * Real.tanh (y + beta * spinSign (parent s.1))) := by
  unfold expectation
  congr 1
  rw [Fintype.sum_prod_type, Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro a ha
  have he (l : IsingSpin) : energy E parent beta y (a, l) =
      E a + (y + beta * spinSign (parent a)) * spinSign l := by
    unfold energy
    ring
  simp_rw [he]
  simp only [Real.exp_add]
  calc
    _ = (f a * Real.exp (E a)) *
        ∑ l : IsingSpin, spinSign l *
          Real.exp ((y + beta * spinSign (parent a)) * spinSign l) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro l hl
      ring
    _ = _ := by
      rw [spin_exponential_mean, Finset.mul_sum, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro l hl
      ring

theorem expectation_mul_leaf_affine {A : Type*} [Fintype A]
    (E f : A → ℝ) (parent : A → IsingSpin) (beta y : ℝ) :
    expectation (energy E parent beta y) (fun s => f s.1 * spinSign s.2) =
      ((Real.tanh (y + beta) + Real.tanh (y - beta)) / 2) *
        expectation (energy E parent beta y) (fun s => f s.1) +
      (Real.tanh beta * responseAttenuation (Real.tanh beta) y) *
        expectation (energy E parent beta y) (fun s => f s.1 * spinSign (parent s.1)) := by
  rw [expectation_mul_leaf_eq]
  simp_rw [tanh_leaf_affine]
  have he : (fun s : A × IsingSpin => f s.1 *
      ((Real.tanh (y + beta) + Real.tanh (y - beta)) / 2 +
        (Real.tanh beta * responseAttenuation (Real.tanh beta) y) * spinSign (parent s.1))) =
      (fun s => ((Real.tanh (y + beta) + Real.tanh (y - beta)) / 2) * f s.1 +
        (Real.tanh beta * responseAttenuation (Real.tanh beta) y) *
          (f s.1 * spinSign (parent s.1))) := by
    funext s
    ring
  rw [he, expectation_add, expectation_const_mul, expectation_const_mul]

theorem covariance_leaf_eq_mul_parent {A : Type*} [Fintype A] [Nonempty A]
    (E f : A → ℝ) (parent : A → IsingSpin) (beta y : ℝ) :
    covariance (energy E parent beta y) (fun s => f s.1) (fun s => spinSign s.2) =
      (Real.tanh beta * responseAttenuation (Real.tanh beta) y) *
        covariance (energy E parent beta y) (fun s => f s.1)
          (fun s => spinSign (parent s.1)) := by
  let : Nonempty IsingSpin := ⟨.neg⟩
  have hmean := expectation_mul_leaf_affine E (fun _ => 1) parent beta y
  simp only [one_mul, expectation_const, mul_one] at hmean
  unfold covariance
  rw [expectation_mul_leaf_affine, hmean]
  ring

lemma spin_variance_bounds {A : Type*} [Fintype A] [Nonempty A]
    (E : A → ℝ) (spin : A → IsingSpin) :
    0 ≤ 1 - expectation E (fun a => spinSign (spin a)) ^ 2 ∧
      1 - expectation E (fun a => spinSign (spin a)) ^ 2 ≤ 1 := by
  constructor
  · have h := FinitePosterior.variance_nonneg E (fun _ => 0)
      (fun a => spinSign (spin a)) 0
    simpa only [spinSign_sq, FinitePosterior.mean_const, ← expectation_eq_mean_zero] using h
  · nlinarith [sq_nonneg (expectation E (fun a => spinSign (spin a)))]

end Problem367.LeafGibbs

end

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Estimates_PairCorrelation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory
namespace Problem367

theorem reducedWordDistance_cons_ne {α : Type*} [DecidableEq α]
    {a b : α} (hab : a ≠ b) (u v : List α) :
    reducedWordDistance (a::u) (b::v) = u.length + v.length + 2 := by
  simp only [reducedWordDistance, ite_eq_right hab]

theorem reducedWordDistance_move_head {α : Type*} [DecidableEq α]
    (a b : α) (u v : List α) (hab : a ≠ b)
    (hu : List.IsChain (fun x y : α => x ≠ y) (a::u)) :
    reducedWordDistance u (a::b::v) = reducedWordDistance (a::u) (b::v) := by
  rw [reducedWordDistance_cons_ne hab]
  cases u with
  | nil => simp
  | cons c u =>
    have hac : a ≠ c := (List.isChain_cons_cons.mp hu).1
    rw [reducedWordDistance_cons_ne hac.symm]
    simp only [List.length_cons]
    omega

end Problem367

end

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Estimates_RadialSummability
attribute [-instance] _root_.OAI.Problem367.IsingConditionalCopyBounds.graphLaw_isProbabilityMeasure _root_.OAI.Problem367.IsingObservationFactor.copies_probability _root_.OAI.Problem367.IsingObservationFactor.kernel_markov _root_.OAI.Problem367.IsingObservationInnovation.innovationMap_observationLaw_probability _root_.OAI.Problem367.IsingObservationInnovation.observationLaw_probability _root_.OAI.Problem367.TreeKoopman.labelProbability _root_.OAI.Problem367.freeIsingMeasure_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace Problem367

theorem summable_radial_iff (d : ℕ) (f : ℕ → ℝ) (hf : ∀ n, 0 ≤ f n) :
    Summable (fun v : TreeVertex d => f v.1.length) ↔
      Summable (fun n : ℕ => (Fintype.card (TreeShell d n) : ℝ) * f n) := by
  rw [← (treeShellSigmaEquiv d).summable_iff]
  change Summable (fun s : Σ n : ℕ, TreeShell d n => f s.2.1.1.length) ↔ _
  rw [summable_sigma_of_nonneg
    (f := fun s : Σ n : ℕ, TreeShell d n => f s.2.1.1.length)
    (fun s => hf s.2.1.1.length)]
  simp only [tsum_treeShell_radial]
  exact and_iff_right (fun _ => (hasSum_fintype _).summable)

theorem summable_geometric_radial (d : ℕ) {q : ℝ} (hq : 0 ≤ q)
    (hbranch : (d - 1 : ℕ) * q < 1) :
    Summable (fun v : TreeVertex d => q ^ v.1.length) := by
  apply (summable_radial_iff d (fun n => q ^ n) (fun _ => pow_nonneg hq _)).mpr
  apply (summable_nat_add_iff 1).mp
  have hgeom : Summable (fun n : ℕ => ((d - 1 : ℕ) * q) ^ n) :=
    summable_geometric_of_lt_one (mul_nonneg (Nat.cast_nonneg _) hq) hbranch
  have h := hgeom.mul_left ((d : ℝ) * q)
  refine h.congr fun n => ?_
  simp only [card_treeShell_succ, Nat.cast_mul, Nat.cast_pow, pow_succ, mul_pow]
  ring

end Problem367

end

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Gibbs_Leaf
attribute [-instance] _root_.OAI.Problem367.IsingConditionalCopyBounds.graphLaw_isProbabilityMeasure _root_.OAI.Problem367.IsingObservationFactor.copies_probability _root_.OAI.Problem367.IsingObservationFactor.kernel_markov _root_.OAI.Problem367.IsingObservationInnovation.innovationMap_observationLaw_probability _root_.OAI.Problem367.IsingObservationInnovation.observationLaw_probability _root_.OAI.Problem367.TreeKoopman.labelProbability _root_.OAI.Problem367.freeIsingMeasure_probability _root_.OAI.Problem367.reducedTailFintype _root_.OAI.Problem367.treeBallFintype _root_.OAI.Problem367.treeShellFintype
attribute [-simp] _root_.OAI.Problem367.ConnectedHull.pathAssignment_path _root_.OAI.Problem367.ConnectedHull.path_last _root_.OAI.Problem367.ConnectedHull.path_zero _root_.OAI.Problem367.ConnectedHull.prefix_length _root_.OAI.Problem367.ConnectedHull.prefix_zero _root_.OAI.Problem367.CutContinuationChannels.averageChannel_globalCone _root_.OAI.Problem367.CutContinuationChannels.continuationChannel_globalCone _root_.OAI.Problem367.FactorObservable.centeredSpinLp_coe _root_.OAI.Problem367.FiniteIsingSplit.splitEquiv_fst _root_.OAI.Problem367.FiniteIsingSplit.splitEquiv_snd _root_.OAI.Problem367.FinitePathGibbs.tailPartition_zero _root_.OAI.Problem367.GaussianTreeResponseNaturality.fieldEquiv_apply_image _root_.OAI.Problem367.IsingObservationInnovation.innovationMap_apply _root_.OAI.Problem367.IsingObservationInnovation.innovationMap_uniformObservation _root_.OAI.Problem367.IsingObservationInnovation.innovationMap_zero _root_.OAI.Problem367.IsingObservationInnovation.uniformObservation_relabel _root_.OAI.Problem367.IsingOrientedPath.attenuation_outward _root_.OAI.Problem367.IsingOrientedPath.endpoint_extensionAt _root_.OAI.Problem367.IsingSpin.flip_eq_iff _root_.OAI.Problem367.IsingSpin.flip_flip _root_.OAI.Problem367.IsingSpin.toReal_neg _root_.OAI.Problem367.IsingSpin.toReal_pos _root_.OAI.Problem367.LocalSupportGeometry.prefixVertex_length _root_.OAI.Problem367.PathSideBranches.parent_sideVertex _root_.OAI.Problem367.PathSideBranches.restrictNoisyRegion_array _root_.OAI.Problem367.PathSideBranches.sideVertex_length _root_.OAI.Problem367.PathSideBranches.sideVertex_val _root_.OAI.Problem367.PosteriorChain.transition_spinMean _root_.OAI.Problem367.PosteriorChain.transition_sum _root_.OAI.Problem367.RootedBroadcast.flipBranchToComplement_val _root_.OAI.Problem367.RootedBroadcast.pos_spinMul _root_.OAI.Problem367.RootedBroadcast.prefixFlip_branchRoot _root_.OAI.Problem367.RootedBroadcast.prefixFlip_root _root_.OAI.Problem367.RootedBroadcast.prefixTreeAut_symm_branchRoot _root_.OAI.Problem367.RootedBroadcast.prefixTreeAut_symm_root _root_.OAI.Problem367.RootedBroadcast.spinMul_pos _root_.OAI.Problem367.RootedBroadcast.spinMul_self _root_.OAI.Problem367.TreeConeCoding.length_vertex _root_.OAI.Problem367.TreeConeCoding.vertex_nil _root_.OAI.Problem367.TreeConeCoding.vertex_val _root_.OAI.Problem367.TreeGibbsAut.spinEquiv_apply_image _root_.OAI.Problem367.TreeKoopman.centeredAverage_apply_coe _root_.OAI.Problem367.TreeKoopman.centeredAverage_pow_apply_coe _root_.OAI.Problem367.TreeKoopman.centeredGenerator_apply_coe _root_.OAI.Problem367.TreeKoopman.centeredGenerator_sq _root_.OAI.Problem367.TreeKoopman.generatorOperator_sq _root_.OAI.Problem367.TreeKoopman.reverseVertex_twice _root_.OAI.Problem367.TreeKoopman.wordRelabel_cons _root_.OAI.Problem367.TreeKoopman.wordRelabel_nil _root_.OAI.Problem367.TreeLawKoopman.centeredAverage_apply_coe _root_.OAI.Problem367.TreeLawKoopman.generatorOperator_sq _root_.OAI.Problem367.TreePathGibbs.vertexEquiv_val _root_.OAI.Problem367.branchColorAut_length _root_.OAI.Problem367.branchColorAut_singleton _root_.OAI.Problem367.branchColorAut_val _root_.OAI.Problem367.branchColorMap_symm_apply _root_.OAI.Problem367.card_treeBallFinset _root_.OAI.Problem367.card_treeNeighborFinset _root_.OAI.Problem367.colorPermAut_length _root_.OAI.Problem367.colorPermAut_nil _root_.OAI.Problem367.colorPermAut_val _root_.OAI.Problem367.colorPermMap_symm_apply _root_.OAI.Problem367.colorPermMap_val _root_.OAI.Problem367.connectedSpinEncode_apply_root _root_.OAI.Problem367.connectedSpinEquiv_apply _root_.OAI.Problem367.dropVertex_length _root_.OAI.Problem367.dropVertex_val _root_.OAI.Problem367.flipConfig_apply _root_.OAI.Problem367.flipConfig_flipConfig _root_.OAI.Problem367.flipConfig_preimage_spin _root_.OAI.Problem367.freeCylinderWeight_flipConfig _root_.OAI.Problem367.freeCylinderWeight_singleton _root_.OAI.Problem367.iUnion_treeBallFinset _root_.OAI.Problem367.inducedEdges_singleton _root_.OAI.Problem367.mem_rootComplementFinset _root_.OAI.Problem367.mem_rootComponentFinset _root_.OAI.Problem367.mem_rootComponentIndices _root_.OAI.Problem367.mem_treeBallFinset _root_.OAI.Problem367.mem_treeNeighborFinset _root_.OAI.Problem367.parentVertex_length _root_.OAI.Problem367.parentVertex_val _root_.OAI.Problem367.prefixColorAut_length _root_.OAI.Problem367.prefixColorAut_val _root_.OAI.Problem367.prefixColorMap_symm_apply _root_.OAI.Problem367.prefixFlip_twice _root_.OAI.Problem367.spinAgreementCode_eq_neg_iff _root_.OAI.Problem367.spinAgreementCode_eq_pos_iff _root_.OAI.Problem367.spinSign_flip _root_.OAI.Problem367.sum_treeShell_zero _root_.OAI.Problem367.tsum_treeShell_radial _root_.OAI.Problem367.vertexSampler_relabel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace Problem367.GibbsLeaf

theorem energy_congr_on {d : ℕ} (beta : ℝ) (h : TreeVertex d → ℝ)
    (D : Finset (TreeVertex d)) {eta xi : TreeVertex d → IsingSpin}
    (heq : ∀ x ∈ D, eta x = xi x) : energy beta h D eta = energy beta h D xi := by
  classical
  unfold energy
  congr 1
  · exact Finset.sum_congr rfl (fun x hx => by rw [heq x hx])
  · congr 1
    apply Finset.sum_congr rfl
    intro e he
    have hm := (Finset.mem_filter.mp he).1
    rw [Finset.product_eq_sprod] at hm
    obtain ⟨hu, hv⟩ := Finset.mem_product.mp hm
    rw [heq e.1 hu, heq e.2 hv]

theorem energy_update_eq_erase_add
    {d : ℕ} {D : Finset (TreeVertex d)} {v p : TreeVertex d}
    (beta : ℝ) (h : TreeVertex d → ℝ) (hv : v ∈ D) (hpne : p ≠ v)
    (hedges : inducedEdges D = insert (p, v) (inducedEdges (D.erase v)))
    (eta : TreeVertex d → IsingSpin) (s : IsingSpin) :
    energy beta h D (Function.update eta v s) = energy beta h (D.erase v) eta +
      (h v + beta * spinSign (eta p)) * spinSign s := by
  classical
  have hnot : (p, v) ∉ inducedEdges (D.erase v) := by
    simp [inducedEdges, Finset.product_eq_sprod]
  have hfield : (∑ x ∈ D, h x * spinSign (Function.update eta v s x)) =
      (∑ x ∈ D.erase v, h x * spinSign (eta x)) + h v * spinSign s := by
    rw [← Finset.sum_erase_add D _ hv]
    simp only [Function.update_self]
    congr 1
    apply Finset.sum_congr rfl
    intro x hx
    rw [Function.update_of_ne (Finset.mem_erase.mp hx).1]
  have hedge : (∑ e ∈ inducedEdges (D.erase v),
      spinSign (Function.update eta v s e.1) * spinSign (Function.update eta v s e.2)) =
      ∑ e ∈ inducedEdges (D.erase v), spinSign (eta e.1) * spinSign (eta e.2) := by
    apply Finset.sum_congr rfl
    intro e he
    have hm := (Finset.mem_filter.mp he).1
    rw [Finset.product_eq_sprod] at hm
    obtain ⟨hu, hw⟩ := Finset.mem_product.mp hm
    rw [Function.update_of_ne (Finset.mem_erase.mp hu).1,
      Function.update_of_ne (Finset.mem_erase.mp hw).1]
  unfold energy
  rw [hfield, hedges, Finset.sum_insert hnot, hedge]
  simp only [Function.update_of_ne hpne, Function.update_self]
  ring

theorem sum_weight_update_of_edges
    {d : ℕ} {D : Finset (TreeVertex d)} {v p : TreeVertex d}
    (beta : ℝ) (h : TreeVertex d → ℝ) (hv : v ∈ D) (hpne : p ≠ v)
    (hedges : inducedEdges D = insert (p, v) (inducedEdges (D.erase v)))
    (eta : TreeVertex d → IsingSpin) :
    (∑ s : IsingSpin, weight beta h D (Function.update eta v s)) =
      2 * Real.cosh (h v + beta * spinSign (eta p)) * weight beta h (D.erase v) eta := by
  simp only [weight, energy_update_eq_erase_add beta h hv hpne hedges, Real.exp_add]
  rw [← Finset.mul_sum, sum_isingSpin]
  simp only [spinSign_neg, spinSign_pos, mul_neg_one, mul_one]
  rw [Real.cosh_eq]
  ring

theorem sum_weight_eq_erase_sum
    {d : ℕ} {D : Finset (TreeVertex d)} {v p : TreeVertex d}
    (beta : ℝ) (h : TreeVertex d → ℝ) (hv : v ∈ D) (hpne : p ≠ v)
    (hedges : inducedEdges D = insert (p, v) (inducedEdges (D.erase v))) :
    (∑ eta : D → IsingSpin, weight beta h D (extendFiniteSpin D eta)) =
      ∑ eta : D.erase v → IsingSpin,
        2 * Real.cosh (h v + beta * spinSign (extendFiniteSpin (D.erase v) eta p)) *
          weight beta h (D.erase v) (extendFiniteSpin (D.erase v) eta) := by
  classical
  calc
    _ = ∑ z : (D.erase v → IsingSpin) × IsingSpin,
        weight beta h D (extendFiniteSpin D ((finiteSpinEraseEquiv hv).symm z)) :=
      ((finiteSpinEraseEquiv hv).symm.sum_comp
        (fun eta => weight beta h D (extendFiniteSpin D eta))).symm
    _ = _ := by
      rw [Fintype.sum_prod_type]
      apply Finset.sum_congr rfl
      intro eta _
      simp only [extendFiniteSpin_eraseEquiv_symm]
      exact sum_weight_update_of_edges beta h hv hpne hedges _

end Problem367.GibbsLeaf

end

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Gibbs_LeafMessage
attribute [-instance] _root_.OAI.Problem367.IsingConditionalCopyBounds.graphLaw_isProbabilityMeasure _root_.OAI.Problem367.IsingObservationFactor.copies_probability _root_.OAI.Problem367.IsingObservationFactor.kernel_markov _root_.OAI.Problem367.IsingObservationInnovation.innovationMap_observationLaw_probability _root_.OAI.Problem367.IsingObservationInnovation.observationLaw_probability _root_.OAI.Problem367.TreeKoopman.labelProbability _root_.OAI.Problem367.freeIsingMeasure_probability _root_.OAI.Problem367.reducedTailFintype _root_.OAI.Problem367.treeBallFintype _root_.OAI.Problem367.treeShellFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace Problem367.GibbsLeaf

theorem eliminationConstant_pos (beta z : ℝ) : 0 < eliminationConstant beta z := by
  unfold eliminationConstant
  positivity

theorem cosh_eq_eliminationConstant_mul_message (beta z : ℝ) (s : IsingSpin) :
    2 * Real.cosh (z + beta * spinSign s) =
      eliminationConstant beta z * Real.exp
        (cavityMessage (Real.tanh beta) z * spinSign s) := by
  unfold eliminationConstant
  rw [mul_assoc, ← Real.exp_add, cavityMessage_eq_log_cosh_sub]
  cases s
  · simp only [spinSign_neg, mul_neg_one]
    rw [show (Real.log (Real.cosh (z + beta)) + Real.log (Real.cosh (z - beta))) / 2 +
        -((Real.log (Real.cosh (z + beta)) - Real.log (Real.cosh (z - beta))) / 2) =
        Real.log (Real.cosh (z - beta)) by ring]
    rw [Real.exp_log (Real.cosh_pos _)]
    congr 2
  · simp only [spinSign_pos, mul_one]
    rw [show (Real.log (Real.cosh (z + beta)) + Real.log (Real.cosh (z - beta))) / 2 +
        (Real.log (Real.cosh (z + beta)) - Real.log (Real.cosh (z - beta))) / 2 =
        Real.log (Real.cosh (z + beta)) by ring]
    rw [Real.exp_log (Real.cosh_pos _)]

theorem energy_update_field {d : ℕ} (beta : ℝ) (h : TreeVertex d → ℝ)
    (D : Finset (TreeVertex d)) {p : TreeVertex d} (hp : p ∈ D)
    (z : ℝ) (eta : TreeVertex d → IsingSpin) :
    energy beta (Function.update h p (h p + z)) D eta =
      energy beta h D eta + z * spinSign (eta p) := by
  classical
  have hsum : (∑ x ∈ D.erase p, Function.update h p (h p + z) x * spinSign (eta x)) =
      ∑ x ∈ D.erase p, h x * spinSign (eta x) := by
    apply Finset.sum_congr rfl
    intro x hx
    rw [Function.update_of_ne (Finset.mem_erase.mp hx).1]
  unfold energy
  rw [← Finset.sum_erase_add D
    (fun x => Function.update h p (h p + z) x * spinSign (eta x)) hp,
    ← Finset.sum_erase_add D (fun x => h x * spinSign (eta x)) hp, hsum]
  simp only [Function.update_self]
  ring

theorem sum_weight_update_eq_cavity
    {d : ℕ} {D : Finset (TreeVertex d)} {v p : TreeVertex d}
    (beta : ℝ) (h : TreeVertex d → ℝ) (hv : v ∈ D) (hp : p ∈ D.erase v)
    (hedges : inducedEdges D = insert (p, v) (inducedEdges (D.erase v)))
    (eta : TreeVertex d → IsingSpin) :
    (∑ s : IsingSpin, weight beta h D (Function.update eta v s)) =
      eliminationConstant beta (h v) *
        weight beta (Function.update h p (h p + cavityMessage (Real.tanh beta) (h v)))
          (D.erase v) eta := by
  rw [sum_weight_update_of_edges beta h hv (Finset.mem_erase.mp hp).1 hedges,
    cosh_eq_eliminationConstant_mul_message]
  simp only [weight, energy_update_field beta h (D.erase v) hp, Real.exp_add]
  ring

theorem partition_eq_cavity_partition
    {d : ℕ} {D : Finset (TreeVertex d)} {v p : TreeVertex d}
    (beta : ℝ) (h : TreeVertex d → ℝ) (hv : v ∈ D) (hp : p ∈ D.erase v)
    (hedges : inducedEdges D = insert (p, v) (inducedEdges (D.erase v))) :
    (∑ eta : D → IsingSpin, weight beta h D (extendFiniteSpin D eta)) =
      eliminationConstant beta (h v) *
        ∑ eta : D.erase v → IsingSpin,
          weight beta (Function.update h p (h p + cavityMessage (Real.tanh beta) (h v)))
            (D.erase v) (extendFiniteSpin (D.erase v) eta) := by
  classical
  rw [sum_weight_eq_erase_sum beta h hv (Finset.mem_erase.mp hp).1 hedges, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro eta _
  rw [← sum_weight_update_of_edges beta h hv (Finset.mem_erase.mp hp).1 hedges]
  exact sum_weight_update_eq_cavity beta h hv hp hedges _

theorem sum_mass_update_eq_cavity
    {d : ℕ} {D : Finset (TreeVertex d)} {v p : TreeVertex d}
    (beta : ℝ) (h : TreeVertex d → ℝ) (hv : v ∈ D) (hp : p ∈ D.erase v)
    (hedges : inducedEdges D = insert (p, v) (inducedEdges (D.erase v)))
    (eta : TreeVertex d → IsingSpin) :
    (∑ s : IsingSpin, mass beta h D (Function.update eta v s)) =
      mass beta (Function.update h p (h p + cavityMessage (Real.tanh beta) (h v)))
        (D.erase v) eta := by
  classical
  simp only [mass, ← Finset.sum_div]
  rw [sum_weight_update_eq_cavity beta h hv hp hedges]
  unfold partition
  rw [partition_eq_cavity_partition beta h hv hp hedges]
  exact mul_div_mul_left _ _ (ne_of_gt (eliminationConstant_pos beta (h v)))

end Problem367.GibbsLeaf

end

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Trees_LeafMarginal
attribute [-instance] _root_.OAI.Problem367.IsingConditionalCopyBounds.graphLaw_isProbabilityMeasure _root_.OAI.Problem367.IsingObservationFactor.copies_probability _root_.OAI.Problem367.IsingObservationFactor.kernel_markov _root_.OAI.Problem367.IsingObservationInnovation.innovationMap_observationLaw_probability _root_.OAI.Problem367.IsingObservationInnovation.observationLaw_probability _root_.OAI.Problem367.TreeKoopman.labelProbability _root_.OAI.Problem367.freeIsingMeasure_probability _root_.OAI.Problem367.reducedTailFintype _root_.OAI.Problem367.treeBallFintype _root_.OAI.Problem367.treeShellFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace Problem367

theorem tree_gibbs_expectation_eq_sum_mass
    {d : ℕ} (beta : ℝ) (h : TreeVertex d → ℝ) (D : Finset (TreeVertex d))
    (f : (D → IsingSpin) → ℝ) :
    LeafGibbs.expectation
      (fun eta => GibbsLeaf.energy beta h D (extendFiniteSpin D eta)) f =
      ∑ eta : D → IsingSpin, GibbsLeaf.mass beta h D (extendFiniteSpin D eta) * f eta := by
  classical
  simp only [LeafGibbs.expectation, GibbsLeaf.mass, GibbsLeaf.weight,
    GibbsLeaf.partition, div_mul_eq_mul_div, ← Finset.sum_div]
  congr 1
  apply Finset.sum_congr rfl
  intro eta heta
  ring

theorem tree_gibbs_expectation_erase
    {d : ℕ} {D : Finset (TreeVertex d)} {v p : TreeVertex d}
    (beta : ℝ) (h : TreeVertex d → ℝ) (hv : v ∈ D) (hp : p ∈ D.erase v)
    (hedges : inducedEdges D = insert (p, v) (inducedEdges (D.erase v)))
    (f : (D.erase v → IsingSpin) → ℝ) :
    LeafGibbs.expectation
      (fun eta => GibbsLeaf.energy beta h D (extendFiniteSpin D eta))
      (fun eta => f ((finiteSpinEraseEquiv hv eta).1)) =
    LeafGibbs.expectation
      (fun eta => GibbsLeaf.energy beta
        (Function.update h p (h p + cavityMessage (Real.tanh beta) (h v)))
        (D.erase v) (extendFiniteSpin (D.erase v) eta)) f := by
  classical
  rw [tree_gibbs_expectation_eq_sum_mass, tree_gibbs_expectation_eq_sum_mass]
  calc
    _ = ∑ z : (D.erase v → IsingSpin) × IsingSpin,
        GibbsLeaf.mass beta h D
          (extendFiniteSpin D ((finiteSpinEraseEquiv hv).symm z)) * f z.1 := by
      rw [← (finiteSpinEraseEquiv hv).symm.sum_comp
        (fun eta : D → IsingSpin => GibbsLeaf.mass beta h D (extendFiniteSpin D eta) *
          f ((finiteSpinEraseEquiv hv eta).1))]
      simp only [Equiv.apply_symm_apply]
    _ = ∑ eta : D.erase v → IsingSpin,
        (∑ s : IsingSpin, GibbsLeaf.mass beta h D
          (Function.update (extendFiniteSpin (D.erase v) eta) v s)) * f eta := by
      rw [Fintype.sum_prod_type]
      simp only [extendFiniteSpin_eraseEquiv_symm, Finset.sum_mul]
    _ = _ := by
      apply Finset.sum_congr rfl
      intro eta heta
      rw [GibbsLeaf.sum_mass_update_eq_cavity beta h hv hp hedges]

theorem tree_gibbs_covariance_erase
    {d : ℕ} {D : Finset (TreeVertex d)} {v p : TreeVertex d}
    (beta : ℝ) (h : TreeVertex d → ℝ) (hv : v ∈ D) (hp : p ∈ D.erase v)
    (hedges : inducedEdges D = insert (p, v) (inducedEdges (D.erase v)))
    (f g : (D.erase v → IsingSpin) → ℝ) :
    LeafGibbs.covariance
      (fun eta => GibbsLeaf.energy beta h D (extendFiniteSpin D eta))
      (fun eta => f ((finiteSpinEraseEquiv hv eta).1))
      (fun eta => g ((finiteSpinEraseEquiv hv eta).1)) =
    LeafGibbs.covariance
      (fun eta => GibbsLeaf.energy beta
        (Function.update h p (h p + cavityMessage (Real.tanh beta) (h v)))
        (D.erase v) (extendFiniteSpin (D.erase v) eta)) f g := by
  unfold LeafGibbs.covariance
  rw [tree_gibbs_expectation_erase beta h hv hp hedges (fun eta => f eta * g eta),
    tree_gibbs_expectation_erase beta h hv hp hedges f,
    tree_gibbs_expectation_erase beta h hv hp hedges g]

end Problem367

end

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Trees_Parents
attribute [-instance] _root_.OAI.Problem367.IsingConditionalCopyBounds.graphLaw_isProbabilityMeasure _root_.OAI.Problem367.IsingObservationFactor.copies_probability _root_.OAI.Problem367.IsingObservationFactor.kernel_markov _root_.OAI.Problem367.IsingObservationInnovation.innovationMap_observationLaw_probability _root_.OAI.Problem367.IsingObservationInnovation.observationLaw_probability _root_.OAI.Problem367.TreeKoopman.labelProbability _root_.OAI.Problem367.freeIsingMeasure_probability
attribute [-simp] _root_.OAI.Problem367.ConnectedHull.pathAssignment_path _root_.OAI.Problem367.ConnectedHull.path_last _root_.OAI.Problem367.ConnectedHull.path_zero _root_.OAI.Problem367.ConnectedHull.prefix_length _root_.OAI.Problem367.ConnectedHull.prefix_zero _root_.OAI.Problem367.CutContinuationChannels.averageChannel_globalCone _root_.OAI.Problem367.CutContinuationChannels.continuationChannel_globalCone _root_.OAI.Problem367.FactorObservable.centeredSpinLp_coe _root_.OAI.Problem367.GaussianTreeResponseNaturality.fieldEquiv_apply_image _root_.OAI.Problem367.IsingObservationInnovation.innovationMap_apply _root_.OAI.Problem367.IsingObservationInnovation.innovationMap_uniformObservation _root_.OAI.Problem367.IsingObservationInnovation.innovationMap_zero _root_.OAI.Problem367.IsingObservationInnovation.uniformObservation_relabel _root_.OAI.Problem367.IsingOrientedPath.attenuation_outward _root_.OAI.Problem367.IsingOrientedPath.endpoint_extensionAt _root_.OAI.Problem367.LocalSupportGeometry.prefixVertex_length _root_.OAI.Problem367.PathSideBranches.parent_sideVertex _root_.OAI.Problem367.PathSideBranches.restrictNoisyRegion_array _root_.OAI.Problem367.PathSideBranches.sideVertex_length _root_.OAI.Problem367.PathSideBranches.sideVertex_val _root_.OAI.Problem367.RootedBroadcast.flipBranchToComplement_val _root_.OAI.Problem367.RootedBroadcast.prefixFlip_branchRoot _root_.OAI.Problem367.RootedBroadcast.prefixFlip_root _root_.OAI.Problem367.RootedBroadcast.prefixTreeAut_symm_branchRoot _root_.OAI.Problem367.RootedBroadcast.prefixTreeAut_symm_root _root_.OAI.Problem367.TreeConeCoding.length_vertex _root_.OAI.Problem367.TreeConeCoding.vertex_nil _root_.OAI.Problem367.TreeConeCoding.vertex_val _root_.OAI.Problem367.TreeGibbsAut.spinEquiv_apply_image _root_.OAI.Problem367.TreeKoopman.centeredAverage_apply_coe _root_.OAI.Problem367.TreeKoopman.centeredAverage_pow_apply_coe _root_.OAI.Problem367.TreeKoopman.centeredGenerator_apply_coe _root_.OAI.Problem367.TreeKoopman.centeredGenerator_sq _root_.OAI.Problem367.TreeKoopman.generatorOperator_sq _root_.OAI.Problem367.TreeKoopman.reverseVertex_twice _root_.OAI.Problem367.TreeKoopman.wordRelabel_cons _root_.OAI.Problem367.TreeKoopman.wordRelabel_nil _root_.OAI.Problem367.TreeLawKoopman.centeredAverage_apply_coe _root_.OAI.Problem367.TreeLawKoopman.generatorOperator_sq _root_.OAI.Problem367.TreePathGibbs.vertexEquiv_val _root_.OAI.Problem367.branchColorAut_length _root_.OAI.Problem367.branchColorAut_singleton _root_.OAI.Problem367.branchColorAut_val _root_.OAI.Problem367.branchColorMap_symm_apply _root_.OAI.Problem367.card_treeBallFinset _root_.OAI.Problem367.card_treeNeighborFinset _root_.OAI.Problem367.colorPermAut_length _root_.OAI.Problem367.colorPermAut_nil _root_.OAI.Problem367.colorPermAut_val _root_.OAI.Problem367.colorPermMap_symm_apply _root_.OAI.Problem367.colorPermMap_val _root_.OAI.Problem367.connectedSpinEncode_apply_root _root_.OAI.Problem367.connectedSpinEquiv_apply _root_.OAI.Problem367.dropVertex_length _root_.OAI.Problem367.dropVertex_val _root_.OAI.Problem367.extendFiniteSpin_apply _root_.OAI.Problem367.finiteFreeIsingPMF_apply _root_.OAI.Problem367.freeCylinderWeight_flipConfig _root_.OAI.Problem367.freeCylinderWeight_singleton _root_.OAI.Problem367.iUnion_treeBallFinset _root_.OAI.Problem367.inducedEdges_singleton _root_.OAI.Problem367.mem_rootComplementFinset _root_.OAI.Problem367.mem_rootComponentFinset _root_.OAI.Problem367.mem_rootComponentIndices _root_.OAI.Problem367.mem_treeBallFinset _root_.OAI.Problem367.mem_treeNeighborFinset _root_.OAI.Problem367.prefixColorAut_length _root_.OAI.Problem367.prefixColorAut_val _root_.OAI.Problem367.prefixColorMap_symm_apply _root_.OAI.Problem367.prefixFlip_twice _root_.OAI.Problem367.restrict_extendFiniteSpin _root_.OAI.Problem367.sum_treeShell_zero _root_.OAI.Problem367.tsum_treeShell_radial _root_.OAI.Problem367.vertexSampler_relabel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Problem367

theorem treeAdj_length {d : ℕ} {u v : TreeVertex d} (h : treeAdj u v) :
    v.1.length = u.1.length + 1 ∨ u.1.length = v.1.length + 1 := by
  rcases h with ⟨c, hc⟩ | ⟨c, hc⟩
  · left; simp [hc]
  · right; simp [hc]

theorem treeAdj_parent_of_length_lt {d : ℕ} {u v : TreeVertex d}
    (h : treeAdj u v) (hlt : u.1.length < v.1.length) : parentVertex v = u := by
  rcases h with ⟨c, hc⟩ | ⟨c, hc⟩
  · apply Subtype.ext
    simp [parentVertex, hc]
  · have hlen : u.1.length = v.1.length + 1 := by simp [hc]
    omega

theorem treeAdj_parentVertex {d : ℕ} {v : TreeVertex d} (hv : v.1 ≠ []) :
    treeAdj (parentVertex v) v := by
  exact Or.inl ⟨v.1.getLast hv, (List.dropLast_append_getLast hv).symm⟩

end Problem367

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Trees_RootedProjectivity
attribute [-instance] _root_.OAI.Problem367.IsingConditionalCopyBounds.graphLaw_isProbabilityMeasure _root_.OAI.Problem367.IsingObservationFactor.copies_probability _root_.OAI.Problem367.IsingObservationFactor.kernel_markov _root_.OAI.Problem367.IsingObservationInnovation.innovationMap_observationLaw_probability _root_.OAI.Problem367.IsingObservationInnovation.observationLaw_probability _root_.OAI.Problem367.TreeKoopman.labelProbability _root_.OAI.Problem367.freeIsingMeasure_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace Problem367

theorem ConnectedFinset.exists_prunable_vertex_of_shared_min
    {d : ℕ} {D E : Finset (TreeVertex d)} (hD : ConnectedFinset D)
    (hE : ConnectedFinset E) (hDE : D ⊆ E) {r : TreeVertex d} (hr : r ∈ D)
    (hmin : ∀ x ∈ E, r.1.length ≤ x.1.length) (hne : D ≠ E) :
    ∃ v p : TreeVertex d, v ∈ E ∧ v ∉ D ∧ p ∈ E ∧ p ≠ v ∧
      ConnectedFinset (E.erase v) ∧ D ⊆ E.erase v ∧
      inducedEdges E = insert (p, v) (inducedEdges (E.erase v)) := by
  classical
  have hdiff : (E \ D).Nonempty := Finset.sdiff_nonempty.mpr (by
    intro hED
    exact hne (Finset.Subset.antisymm hDE hED))
  obtain ⟨v, hvdiff, hmax⟩ := Finset.exists_max_image (E \ D) (fun x => x.1.length) hdiff
  obtain ⟨hvE, hvD⟩ := Finset.mem_sdiff.mp hvdiff
  have hvr : v ≠ r := by
    intro h
    exact hvD (h ▸ hr)
  have hpE : parentVertex v ∈ E :=
    hE.parent_mem_of_ne_min (hDE hr) hmin hvE hvr
  have hvnil : v.1 ≠ [] := ConnectedFinset.ne_nil_of_ne_min hmin hvE hvr
  have hpv : treeAdj (parentVertex v) v := treeAdj_parentVertex hvnil
  have hplen : (parentVertex v).1.length < v.1.length := by
    rw [parentVertex_length]
    have : 0 < v.1.length := List.length_pos_iff.mpr hvnil
    omega
  have hleaf : ∀ x ∈ E, treeAdj v x → x = parentVertex v := by
    intro x hx hadj
    rcases treeAdj_length hadj with hlen | hlen
    · have hxD : x ∈ D := by
        by_contra hxD
        have hbound := hmax x (Finset.mem_sdiff.mpr ⟨hx, hxD⟩)
        omega
      have hxr : x ≠ r := by
        intro h
        subst x
        have := hmin v hvE
        omega
      have hpD := hD.parent_mem_of_ne_min hr (fun y hy => hmin y (hDE hy)) hxD hxr
      have hparent : parentVertex x = v := treeAdj_parent_of_length_lt hadj (by omega)
      exact False.elim (hvD (hparent ▸ hpD))
    · exact (treeAdj_parent_of_length_lt (hadj.elim Or.inr Or.inl) (by omega)).symm
  have hDEerase : D ⊆ E.erase v := by
    intro x hx
    exact Finset.mem_erase.mpr ⟨by intro h; exact hvD (h ▸ hx), hDE hx⟩
  have hconn : ConnectedFinset (E.erase v) :=
    connectedFinset_erase_of_leaf hE hvE ⟨r, hDEerase hr⟩
      (fun x hx y hy hvx hvy => (hleaf x hx hvx).trans (hleaf y hy hvy).symm)
  refine ⟨v, parentVertex v, hvE, hvD, hpE, ?_, hconn, hDEerase, ?_⟩
  · intro h
    have := congrArg (fun x : TreeVertex d => x.1.length) h
    omega
  · exact inducedEdges_eq_insert_erase_of_unique_lower_neighbor hvE hpE hpv hplen hleaf

end Problem367

end

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Trees_LeafCovariance
attribute [-instance] _root_.OAI.Problem367.IsingConditionalCopyBounds.graphLaw_isProbabilityMeasure _root_.OAI.Problem367.IsingObservationFactor.copies_probability _root_.OAI.Problem367.IsingObservationFactor.kernel_markov _root_.OAI.Problem367.IsingObservationInnovation.innovationMap_observationLaw_probability _root_.OAI.Problem367.IsingObservationInnovation.observationLaw_probability _root_.OAI.Problem367.TreeKoopman.labelProbability _root_.OAI.Problem367.freeIsingMeasure_probability _root_.OAI.Problem367.reducedTailFintype _root_.OAI.Problem367.treeBallFintype _root_.OAI.Problem367.treeShellFintype
attribute [-simp] _root_.OAI.Problem367.ConnectedHull.pathAssignment_path _root_.OAI.Problem367.ConnectedHull.path_last _root_.OAI.Problem367.ConnectedHull.path_zero _root_.OAI.Problem367.ConnectedHull.prefix_length _root_.OAI.Problem367.ConnectedHull.prefix_zero _root_.OAI.Problem367.CutContinuationChannels.averageChannel_globalCone _root_.OAI.Problem367.CutContinuationChannels.continuationChannel_globalCone _root_.OAI.Problem367.FactorObservable.centeredSpinLp_coe _root_.OAI.Problem367.FiniteIsingSplit.splitEquiv_fst _root_.OAI.Problem367.FiniteIsingSplit.splitEquiv_snd _root_.OAI.Problem367.FinitePathGibbs.tailPartition_zero _root_.OAI.Problem367.GaussianTreeResponseNaturality.fieldEquiv_apply_image _root_.OAI.Problem367.IsingObservationInnovation.innovationMap_apply _root_.OAI.Problem367.IsingObservationInnovation.innovationMap_uniformObservation _root_.OAI.Problem367.IsingObservationInnovation.innovationMap_zero _root_.OAI.Problem367.IsingObservationInnovation.uniformObservation_relabel _root_.OAI.Problem367.IsingOrientedPath.attenuation_outward _root_.OAI.Problem367.IsingOrientedPath.endpoint_extensionAt _root_.OAI.Problem367.IsingSpin.flip_eq_iff _root_.OAI.Problem367.IsingSpin.flip_flip _root_.OAI.Problem367.IsingSpin.toReal_neg _root_.OAI.Problem367.IsingSpin.toReal_pos _root_.OAI.Problem367.LocalSupportGeometry.prefixVertex_length _root_.OAI.Problem367.PathSideBranches.parent_sideVertex _root_.OAI.Problem367.PathSideBranches.restrictNoisyRegion_array _root_.OAI.Problem367.PathSideBranches.sideVertex_length _root_.OAI.Problem367.PathSideBranches.sideVertex_val _root_.OAI.Problem367.PosteriorChain.transition_spinMean _root_.OAI.Problem367.PosteriorChain.transition_sum _root_.OAI.Problem367.RootedBroadcast.flipBranchToComplement_val _root_.OAI.Problem367.RootedBroadcast.pos_spinMul _root_.OAI.Problem367.RootedBroadcast.prefixFlip_branchRoot _root_.OAI.Problem367.RootedBroadcast.prefixFlip_root _root_.OAI.Problem367.RootedBroadcast.prefixTreeAut_symm_branchRoot _root_.OAI.Problem367.RootedBroadcast.prefixTreeAut_symm_root _root_.OAI.Problem367.RootedBroadcast.spinMul_pos _root_.OAI.Problem367.RootedBroadcast.spinMul_self _root_.OAI.Problem367.TreeConeCoding.length_vertex _root_.OAI.Problem367.TreeConeCoding.vertex_nil _root_.OAI.Problem367.TreeConeCoding.vertex_val _root_.OAI.Problem367.TreeGibbsAut.spinEquiv_apply_image _root_.OAI.Problem367.TreeKoopman.centeredAverage_apply_coe _root_.OAI.Problem367.TreeKoopman.centeredAverage_pow_apply_coe _root_.OAI.Problem367.TreeKoopman.centeredGenerator_apply_coe _root_.OAI.Problem367.TreeKoopman.centeredGenerator_sq _root_.OAI.Problem367.TreeKoopman.generatorOperator_sq _root_.OAI.Problem367.TreeKoopman.reverseVertex_twice _root_.OAI.Problem367.TreeKoopman.wordRelabel_cons _root_.OAI.Problem367.TreeKoopman.wordRelabel_nil _root_.OAI.Problem367.TreeLawKoopman.centeredAverage_apply_coe _root_.OAI.Problem367.TreeLawKoopman.generatorOperator_sq _root_.OAI.Problem367.TreePathGibbs.vertexEquiv_val _root_.OAI.Problem367.branchColorAut_length _root_.OAI.Problem367.branchColorAut_singleton _root_.OAI.Problem367.branchColorAut_val _root_.OAI.Problem367.branchColorMap_symm_apply _root_.OAI.Problem367.card_treeBallFinset _root_.OAI.Problem367.card_treeNeighborFinset _root_.OAI.Problem367.colorPermAut_length _root_.OAI.Problem367.colorPermAut_nil _root_.OAI.Problem367.colorPermAut_val _root_.OAI.Problem367.colorPermMap_symm_apply _root_.OAI.Problem367.colorPermMap_val _root_.OAI.Problem367.connectedSpinEncode_apply_root _root_.OAI.Problem367.connectedSpinEquiv_apply _root_.OAI.Problem367.dropVertex_length _root_.OAI.Problem367.dropVertex_val _root_.OAI.Problem367.flipConfig_apply _root_.OAI.Problem367.flipConfig_flipConfig _root_.OAI.Problem367.flipConfig_preimage_spin _root_.OAI.Problem367.freeCylinderWeight_flipConfig _root_.OAI.Problem367.freeCylinderWeight_singleton _root_.OAI.Problem367.iUnion_treeBallFinset _root_.OAI.Problem367.inducedEdges_singleton _root_.OAI.Problem367.mem_rootComplementFinset _root_.OAI.Problem367.mem_rootComponentFinset _root_.OAI.Problem367.mem_rootComponentIndices _root_.OAI.Problem367.mem_treeBallFinset _root_.OAI.Problem367.mem_treeNeighborFinset _root_.OAI.Problem367.parentVertex_length _root_.OAI.Problem367.parentVertex_val _root_.OAI.Problem367.prefixColorAut_length _root_.OAI.Problem367.prefixColorAut_val _root_.OAI.Problem367.prefixColorMap_symm_apply _root_.OAI.Problem367.prefixFlip_twice _root_.OAI.Problem367.spinAgreementCode_eq_neg_iff _root_.OAI.Problem367.spinAgreementCode_eq_pos_iff _root_.OAI.Problem367.spinSign_flip _root_.OAI.Problem367.sum_treeShell_zero _root_.OAI.Problem367.tsum_treeShell_radial _root_.OAI.Problem367.vertexSampler_relabel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace Problem367

private theorem leaf_expectation_equiv {A B : Type*} [Fintype A] [Fintype B]
    (e : A ≃ B) (E f : B → ℝ) :
    LeafGibbs.expectation (E ∘ e) (f ∘ e) = LeafGibbs.expectation E f := by
  unfold LeafGibbs.expectation
  simp only [Function.comp_apply]
  rw [e.sum_comp (fun b => f b * Real.exp (E b)), e.sum_comp (fun b => Real.exp (E b))]

private theorem leaf_covariance_equiv {A B : Type*} [Fintype A] [Fintype B]
    (e : A ≃ B) (E f g : B → ℝ) :
    LeafGibbs.covariance (E ∘ e) (f ∘ e) (g ∘ e) = LeafGibbs.covariance E f g := by
  unfold LeafGibbs.covariance
  rw [leaf_expectation_equiv, leaf_expectation_equiv]
  congr 1
  exact leaf_expectation_equiv e E (fun b => f b * g b)

theorem tree_gibbs_leaf_energy_split
    {d : ℕ} {D : Finset (TreeVertex d)} {v p : TreeVertex d}
    (beta : ℝ) (h : TreeVertex d → ℝ) (hv : v ∈ D) (hpne : p ≠ v)
    (hedges : inducedEdges D = insert (p, v) (inducedEdges (D.erase v))) :
    (fun eta => GibbsLeaf.energy beta h D (extendFiniteSpin D eta)) ∘
      (finiteSpinEraseEquiv hv).symm =
    LeafGibbs.energy
      (fun eta => GibbsLeaf.energy beta h (D.erase v) (extendFiniteSpin (D.erase v) eta))
      (fun eta => extendFiniteSpin (D.erase v) eta p) beta (h v) := by
  funext z
  rcases z with ⟨eta, s⟩
  simp only [Function.comp_apply, extendFiniteSpin_eraseEquiv_symm,
    GibbsLeaf.energy_update_eq_erase_add beta h hv hpne hedges, LeafGibbs.energy]
  ring

theorem tree_gibbs_covariance_leaf
    {d : ℕ} {D : Finset (TreeVertex d)} {v p : TreeVertex d}
    (beta : ℝ) (h : TreeVertex d → ℝ) (hv : v ∈ D) (hp : p ∈ D.erase v)
    (hedges : inducedEdges D = insert (p, v) (inducedEdges (D.erase v)))
    (f : (D.erase v → IsingSpin) → ℝ) :
    LeafGibbs.covariance
      (fun eta => GibbsLeaf.energy beta h D (extendFiniteSpin D eta))
      (fun eta => f ((finiteSpinEraseEquiv hv eta).1))
      (fun eta => spinSign (eta ⟨v, hv⟩)) =
    (Real.tanh beta * responseAttenuation (Real.tanh beta) (h v)) *
      LeafGibbs.covariance
        (fun eta => GibbsLeaf.energy beta h D (extendFiniteSpin D eta))
        (fun eta => f ((finiteSpinEraseEquiv hv eta).1))
        (fun eta => spinSign (eta ⟨p, (Finset.mem_erase.mp hp).2⟩)) := by
  classical
  let : Nonempty (D.erase v → IsingSpin) := ⟨fun _ => .neg⟩
  let e := (finiteSpinEraseEquiv hv).symm
  let E : (D → IsingSpin) → ℝ :=
    fun eta => GibbsLeaf.energy beta h D (extendFiniteSpin D eta)
  let F : (D → IsingSpin) → ℝ := fun eta => f ((finiteSpinEraseEquiv hv eta).1)
  let L : (D → IsingSpin) → ℝ := fun eta => spinSign (eta ⟨v, hv⟩)
  let P : (D → IsingSpin) → ℝ :=
    fun eta => spinSign (eta ⟨p, (Finset.mem_erase.mp hp).2⟩)
  change LeafGibbs.covariance E F L = _ * LeafGibbs.covariance E F P
  rw [← leaf_covariance_equiv e E F L, ← leaf_covariance_equiv e E F P]
  have he : E ∘ e = LeafGibbs.energy
      (fun eta => GibbsLeaf.energy beta h (D.erase v) (extendFiniteSpin (D.erase v) eta))
      (fun eta => extendFiniteSpin (D.erase v) eta p) beta (h v) :=
    tree_gibbs_leaf_energy_split beta h hv (Finset.mem_erase.mp hp).1 hedges
  have hf : F ∘ e = fun z => f z.1 := by
    funext z
    simp [F, e]
  have hl : L ∘ e = fun z => spinSign z.2 := by
    funext z
    simp [L, e, finiteSpinEraseEquiv]
  have hp' : P ∘ e = fun z => spinSign (extendFiniteSpin (D.erase v) z.1 p) := by
    funext z
    simp [P, e, finiteSpinEraseEquiv, extendFiniteSpin,
      (Finset.mem_erase.mp hp).1, hp]
  rw [he, hf, hl, hp']
  exact LeafGibbs.covariance_leaf_eq_mul_parent _ f _ beta (h v)

end Problem367

end

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Trees_RootCovariance
attribute [-instance] _root_.OAI.Problem367.IsingConditionalCopyBounds.graphLaw_isProbabilityMeasure _root_.OAI.Problem367.IsingObservationFactor.copies_probability _root_.OAI.Problem367.IsingObservationFactor.kernel_markov _root_.OAI.Problem367.IsingObservationInnovation.innovationMap_observationLaw_probability _root_.OAI.Problem367.IsingObservationInnovation.observationLaw_probability _root_.OAI.Problem367.TreeKoopman.labelProbability _root_.OAI.Problem367.freeIsingMeasure_probability _root_.OAI.Problem367.reducedTailFintype _root_.OAI.Problem367.treeBallFintype _root_.OAI.Problem367.treeShellFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace Problem367

theorem tree_gibbs_root_covariance_bounds
    {d : ℕ} {beta : ℝ} (hbeta : 0 ≤ beta)
    {E : Finset (TreeVertex d)} {r : TreeVertex d}
    (hE : ConnectedFinset E) (hr : r ∈ E)
    (hmin : ∀ x ∈ E, r.1.length ≤ x.1.length)
    (h : TreeVertex d → ℝ) (v : TreeVertex d) (hv : v ∈ E) :
    0 ≤ LeafGibbs.covariance
      (fun eta => GibbsLeaf.energy beta h E (extendFiniteSpin E eta))
      (fun eta => spinSign (eta ⟨r, hr⟩)) (fun eta => spinSign (eta ⟨v, hv⟩)) ∧
    LeafGibbs.covariance
      (fun eta => GibbsLeaf.energy beta h E (extendFiniteSpin E eta))
      (fun eta => spinSign (eta ⟨r, hr⟩)) (fun eta => spinSign (eta ⟨v, hv⟩)) ≤
        Real.tanh beta ^ (v.1.length - r.1.length) := by
  classical
  have ht : 0 ≤ Real.tanh beta := by
    rw [Real.tanh_eq_sinh_div_cosh]
    exact div_nonneg (Real.sinh_nonneg_iff.mpr hbeta) (Real.cosh_pos beta).le
  revert hE hr hmin h v
  refine Finset.strongInductionOn E ?_
  intro E ih hE hr hmin h v hv
  let : Nonempty (E → IsingSpin) := ⟨fun _ => .neg⟩
  by_cases hvr : v = r
  · subst v
    simpa only [LeafGibbs.covariance, spinSign_mul_self, LeafGibbs.expectation_const,
      Nat.sub_self, pow_zero, pow_two] using
      LeafGibbs.spin_variance_bounds
        (fun eta => GibbsLeaf.energy beta h E (extendFiniteSpin E eta))
        (fun eta => eta ⟨r, hr⟩)
  have hsub : ({r} : Finset (TreeVertex d)) ⊆ E := Finset.singleton_subset_iff.mpr hr
  have hne : ({r} : Finset (TreeVertex d)) ≠ E := by
    intro heq
    exact hvr (Finset.mem_singleton.mp (heq.symm ▸ hv))
  obtain ⟨w, p, hwE, hwr, hpE, hpw, hEr, hsubr, hedges⟩ :=
    (connectedFinset_singleton r).exists_prunable_vertex_of_shared_min
      hE hsub (Finset.mem_singleton_self r) hmin hne
  have hrEr : r ∈ E.erase w := hsubr (Finset.mem_singleton_self r)
  have hpEr : p ∈ E.erase w := Finset.mem_erase.mpr ⟨hpw, hpE⟩
  have hErE : E.erase w ⊆ E := Finset.erase_subset _ _
  let h' := Function.update h p (h p + cavityMessage (Real.tanh beta) (h w))
  have hmin' : ∀ x ∈ E.erase w, r.1.length ≤ x.1.length :=
    fun x hx => hmin x (hErE hx)
  by_cases hvw : v = w
  · subst v
    have hrec := ih (E.erase w) (Finset.erase_ssubset hwE) hEr hrEr hmin' h' p hpEr
    have hcov := tree_gibbs_covariance_leaf beta h hwE hpEr hedges
      (fun eta => spinSign (eta ⟨r, hrEr⟩))
    have hmarg := tree_gibbs_covariance_erase beta h hwE hpEr hedges
      (fun eta => spinSign (eta ⟨r, hrEr⟩))
      (fun eta => spinSign (eta ⟨p, hpEr⟩))
    change LeafGibbs.covariance _ (fun eta : E → IsingSpin => spinSign (eta ⟨r, hr⟩))
        (fun eta => spinSign (eta ⟨w, hv⟩)) =
        (Real.tanh beta * responseAttenuation (Real.tanh beta) (h w)) *
          LeafGibbs.covariance _ (fun eta : E → IsingSpin => spinSign (eta ⟨r, hr⟩))
            (fun eta => spinSign (eta ⟨p, hpE⟩)) at hcov
    change LeafGibbs.covariance _ (fun eta : E → IsingSpin => spinSign (eta ⟨r, hr⟩))
        (fun eta => spinSign (eta ⟨p, hpE⟩)) = _ at hmarg
    rw [hcov, hmarg]
    have ha := responseAttenuation_pos (Real.tanh_sq_lt_one beta).le (h w)
    have ha1 := responseAttenuation_le_one (Real.tanh_sq_lt_one beta).le (h w)
    have hslope : 0 ≤ Real.tanh beta * responseAttenuation (Real.tanh beta) (h w) :=
      mul_nonneg ht ha.le
    have hedge : (p, w) ∈ inducedEdges E := by rw [hedges]; exact Finset.mem_insert_self _ _
    have hdata := Finset.mem_filter.mp hedge
    have hadj : treeAdj p w := hdata.2.1
    have hlower : p.1.length < w.1.length := hdata.2.2
    have hlen := treeAdj_length hadj
    have hdist : w.1.length - r.1.length = (p.1.length - r.1.length) + 1 := by
      have := hmin p hpE
      omega
    constructor
    · exact mul_nonneg hslope hrec.1
    · rw [hdist, pow_succ]
      calc
        _ ≤ (Real.tanh beta * responseAttenuation (Real.tanh beta) (h w)) *
            Real.tanh beta ^ (p.1.length - r.1.length) :=
          mul_le_mul_of_nonneg_left hrec.2 hslope
        _ ≤ Real.tanh beta * Real.tanh beta ^ (p.1.length - r.1.length) :=
          mul_le_mul_of_nonneg_right (mul_le_of_le_one_right ht ha1) (pow_nonneg ht _)
        _ = _ := mul_comm _ _
  · have hvEr : v ∈ E.erase w := Finset.mem_erase.mpr ⟨hvw, hv⟩
    have hrec := ih (E.erase w) (Finset.erase_ssubset hwE) hEr hrEr hmin' h' v hvEr
    have hmarg := tree_gibbs_covariance_erase beta h hwE hpEr hedges
      (fun eta => spinSign (eta ⟨r, hrEr⟩))
      (fun eta => spinSign (eta ⟨v, hvEr⟩))
    change LeafGibbs.covariance _ (fun eta : E → IsingSpin => spinSign (eta ⟨r, hr⟩))
        (fun eta => spinSign (eta ⟨v, hv⟩)) = _ at hmarg
    rw [hmarg]
    exact hrec

end Problem367

end

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Trees_AutDistance
attribute [-instance] _root_.OAI.Problem367.IsingConditionalCopyBounds.graphLaw_isProbabilityMeasure _root_.OAI.Problem367.IsingObservationFactor.copies_probability _root_.OAI.Problem367.IsingObservationFactor.kernel_markov _root_.OAI.Problem367.IsingObservationInnovation.innovationMap_observationLaw_probability _root_.OAI.Problem367.IsingObservationInnovation.observationLaw_probability _root_.OAI.Problem367.TreeKoopman.labelProbability _root_.OAI.Problem367.freeIsingMeasure_probability
attribute [-simp] _root_.OAI.Problem367.CutContinuationChannels.averageChannel_globalCone _root_.OAI.Problem367.CutContinuationChannels.continuationChannel_globalCone _root_.OAI.Problem367.FactorObservable.centeredSpinLp_coe _root_.OAI.Problem367.GaussianTreeResponseNaturality.fieldEquiv_apply_image _root_.OAI.Problem367.IsingObservationInnovation.innovationMap_apply _root_.OAI.Problem367.IsingObservationInnovation.innovationMap_uniformObservation _root_.OAI.Problem367.IsingObservationInnovation.innovationMap_zero _root_.OAI.Problem367.IsingObservationInnovation.uniformObservation_relabel _root_.OAI.Problem367.IsingOrientedPath.attenuation_outward _root_.OAI.Problem367.IsingOrientedPath.endpoint_extensionAt _root_.OAI.Problem367.LocalSupportGeometry.prefixVertex_length _root_.OAI.Problem367.PathSideBranches.parent_sideVertex _root_.OAI.Problem367.PathSideBranches.restrictNoisyRegion_array _root_.OAI.Problem367.PathSideBranches.sideVertex_length _root_.OAI.Problem367.PathSideBranches.sideVertex_val _root_.OAI.Problem367.RootedBroadcast.flipBranchToComplement_val _root_.OAI.Problem367.RootedBroadcast.prefixFlip_branchRoot _root_.OAI.Problem367.RootedBroadcast.prefixFlip_root _root_.OAI.Problem367.RootedBroadcast.prefixTreeAut_symm_branchRoot _root_.OAI.Problem367.RootedBroadcast.prefixTreeAut_symm_root _root_.OAI.Problem367.TreeConeCoding.length_vertex _root_.OAI.Problem367.TreeConeCoding.vertex_nil _root_.OAI.Problem367.TreeConeCoding.vertex_val _root_.OAI.Problem367.TreeGibbsAut.spinEquiv_apply_image _root_.OAI.Problem367.TreeKoopman.centeredAverage_apply_coe _root_.OAI.Problem367.TreeKoopman.centeredAverage_pow_apply_coe _root_.OAI.Problem367.TreeKoopman.centeredGenerator_apply_coe _root_.OAI.Problem367.TreeKoopman.centeredGenerator_sq _root_.OAI.Problem367.TreeKoopman.generatorOperator_sq _root_.OAI.Problem367.TreeKoopman.reverseVertex_twice _root_.OAI.Problem367.TreeKoopman.wordRelabel_cons _root_.OAI.Problem367.TreeKoopman.wordRelabel_nil _root_.OAI.Problem367.TreeLawKoopman.centeredAverage_apply_coe _root_.OAI.Problem367.TreeLawKoopman.generatorOperator_sq _root_.OAI.Problem367.TreePathGibbs.vertexEquiv_val _root_.OAI.Problem367.branchColorAut_length _root_.OAI.Problem367.branchColorAut_singleton _root_.OAI.Problem367.branchColorAut_val _root_.OAI.Problem367.branchColorMap_symm_apply _root_.OAI.Problem367.card_treeBallFinset _root_.OAI.Problem367.card_treeNeighborFinset _root_.OAI.Problem367.colorPermAut_length _root_.OAI.Problem367.colorPermAut_nil _root_.OAI.Problem367.colorPermAut_val _root_.OAI.Problem367.colorPermMap_symm_apply _root_.OAI.Problem367.colorPermMap_val _root_.OAI.Problem367.connectedSpinEncode_apply_root _root_.OAI.Problem367.connectedSpinEquiv_apply _root_.OAI.Problem367.dropVertex_length _root_.OAI.Problem367.dropVertex_val _root_.OAI.Problem367.finiteFreeIsingPMF_apply _root_.OAI.Problem367.freeCylinderWeight_flipConfig _root_.OAI.Problem367.iUnion_treeBallFinset _root_.OAI.Problem367.mem_rootComplementFinset _root_.OAI.Problem367.mem_rootComponentFinset _root_.OAI.Problem367.mem_rootComponentIndices _root_.OAI.Problem367.mem_treeBallFinset _root_.OAI.Problem367.mem_treeNeighborFinset _root_.OAI.Problem367.parentVertex_length _root_.OAI.Problem367.parentVertex_val _root_.OAI.Problem367.prefixColorAut_length _root_.OAI.Problem367.prefixColorAut_val _root_.OAI.Problem367.prefixColorMap_symm_apply _root_.OAI.Problem367.sum_treeShell_zero _root_.OAI.Problem367.tsum_treeShell_radial _root_.OAI.Problem367.vertexSampler_relabel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace Problem367

theorem reducedWordDistance_prefixFlipWord {α : Type*} [DecidableEq α]
    (a : α) (u v : List α) (hu : List.IsChain (fun x y : α => x ≠ y) (a :: u)) :
    reducedWordDistance u (prefixFlipWord a v) = reducedWordDistance (a :: u) v := by
  cases v with
  | nil =>
      cases u with
      | nil => rfl
      | cons b u =>
          have hab : a ≠ b := (List.isChain_cons_cons.mp hu).1
          simp only [prefixFlipWord, reducedWordDistance_cons_ne hab.symm,
            List.length_nil, reducedWordDistance_nil_right, List.length_cons]
  | cons b v =>
      by_cases hab : a = b
      · subst b
        simp [prefixFlipWord]
      · simp only [prefixFlipWord, ite_eq_right hab]
        exact reducedWordDistance_move_head a b u v hab hu

theorem exists_treeAut_to_root_distance {d : ℕ} (u : TreeVertex d) :
    ∃ g : TreeAut d,
      g.toEquiv u = ⟨[], List.IsChain.nil⟩ ∧
      ∀ v : TreeVertex d, (g.toEquiv v).1.length = reducedWordDistance u.1 v.1 := by
  rcases u with ⟨w, hw⟩
  induction w with
  | nil =>
      exact ⟨TreeAut.refl d, rfl, fun v => rfl⟩
  | cons a w ih =>
      obtain ⟨g, hg, hdist⟩ := ih hw.tail
      refine ⟨(prefixTreeAut a).trans g, ?_, ?_⟩
      · change g.toEquiv (prefixFlip a ⟨a :: w, hw⟩) = _
        have hflip : prefixFlip a (⟨a :: w, hw⟩ : TreeVertex d) = ⟨w, hw.tail⟩ := by
          apply Subtype.ext
          simp [prefixFlip, prefixFlipWord]
        rw [hflip]
        exact hg
      · intro v
        change (g.toEquiv (prefixFlip a v)).1.length = reducedWordDistance (a :: w) v.1
        rw [hdist (prefixFlip a v)]
        exact reducedWordDistance_prefixFlipWord a w v.1 hw

end Problem367

end

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Trees_GibbsAutomorphism
attribute [-instance] _root_.OAI.Problem367.IsingConditionalCopyBounds.graphLaw_isProbabilityMeasure _root_.OAI.Problem367.IsingObservationFactor.copies_probability _root_.OAI.Problem367.IsingObservationFactor.kernel_markov _root_.OAI.Problem367.IsingObservationInnovation.innovationMap_observationLaw_probability _root_.OAI.Problem367.IsingObservationInnovation.observationLaw_probability _root_.OAI.Problem367.TreeKoopman.labelProbability _root_.OAI.Problem367.freeIsingMeasure_probability _root_.OAI.Problem367.reducedTailFintype _root_.OAI.Problem367.treeBallFintype _root_.OAI.Problem367.treeShellFintype
attribute [-simp] _root_.OAI.Problem367.ConnectedHull.pathAssignment_path _root_.OAI.Problem367.ConnectedHull.path_last _root_.OAI.Problem367.ConnectedHull.path_zero _root_.OAI.Problem367.CutContinuationChannels.averageChannel_globalCone _root_.OAI.Problem367.CutContinuationChannels.continuationChannel_globalCone _root_.OAI.Problem367.FactorObservable.centeredSpinLp_coe _root_.OAI.Problem367.FiniteIsingSplit.splitEquiv_fst _root_.OAI.Problem367.FiniteIsingSplit.splitEquiv_snd _root_.OAI.Problem367.FinitePathGibbs.tailPartition_zero _root_.OAI.Problem367.GaussianTreeResponseNaturality.fieldEquiv_apply_image _root_.OAI.Problem367.IsingObservationInnovation.innovationMap_apply _root_.OAI.Problem367.IsingObservationInnovation.innovationMap_uniformObservation _root_.OAI.Problem367.IsingObservationInnovation.innovationMap_zero _root_.OAI.Problem367.IsingObservationInnovation.uniformObservation_relabel _root_.OAI.Problem367.IsingOrientedPath.attenuation_outward _root_.OAI.Problem367.IsingOrientedPath.endpoint_extensionAt _root_.OAI.Problem367.IsingSpin.flip_eq_iff _root_.OAI.Problem367.IsingSpin.flip_flip _root_.OAI.Problem367.IsingSpin.toReal_neg _root_.OAI.Problem367.IsingSpin.toReal_pos _root_.OAI.Problem367.LocalSupportGeometry.prefixVertex_length _root_.OAI.Problem367.PathSideBranches.parent_sideVertex _root_.OAI.Problem367.PathSideBranches.restrictNoisyRegion_array _root_.OAI.Problem367.PathSideBranches.sideVertex_length _root_.OAI.Problem367.PathSideBranches.sideVertex_val _root_.OAI.Problem367.PosteriorChain.transition_spinMean _root_.OAI.Problem367.PosteriorChain.transition_sum _root_.OAI.Problem367.RootedBroadcast.flipBranchToComplement_val _root_.OAI.Problem367.RootedBroadcast.pos_spinMul _root_.OAI.Problem367.RootedBroadcast.prefixFlip_branchRoot _root_.OAI.Problem367.RootedBroadcast.prefixFlip_root _root_.OAI.Problem367.RootedBroadcast.prefixTreeAut_symm_branchRoot _root_.OAI.Problem367.RootedBroadcast.prefixTreeAut_symm_root _root_.OAI.Problem367.RootedBroadcast.spinMul_pos _root_.OAI.Problem367.RootedBroadcast.spinMul_self _root_.OAI.Problem367.TreeConeCoding.length_vertex _root_.OAI.Problem367.TreeConeCoding.vertex_nil _root_.OAI.Problem367.TreeConeCoding.vertex_val _root_.OAI.Problem367.TreeKoopman.centeredAverage_apply_coe _root_.OAI.Problem367.TreeKoopman.centeredAverage_pow_apply_coe _root_.OAI.Problem367.TreeKoopman.centeredGenerator_apply_coe _root_.OAI.Problem367.TreeKoopman.centeredGenerator_sq _root_.OAI.Problem367.TreeKoopman.generatorOperator_sq _root_.OAI.Problem367.TreeKoopman.reverseVertex_twice _root_.OAI.Problem367.TreeKoopman.wordRelabel_cons _root_.OAI.Problem367.TreeKoopman.wordRelabel_nil _root_.OAI.Problem367.TreeLawKoopman.centeredAverage_apply_coe _root_.OAI.Problem367.TreeLawKoopman.generatorOperator_sq _root_.OAI.Problem367.TreePathGibbs.vertexEquiv_val _root_.OAI.Problem367.branchColorAut_length _root_.OAI.Problem367.branchColorAut_singleton _root_.OAI.Problem367.branchColorAut_val _root_.OAI.Problem367.branchColorMap_symm_apply _root_.OAI.Problem367.card_treeBallFinset _root_.OAI.Problem367.card_treeNeighborFinset _root_.OAI.Problem367.colorPermAut_length _root_.OAI.Problem367.colorPermAut_nil _root_.OAI.Problem367.colorPermAut_val _root_.OAI.Problem367.colorPermMap_symm_apply _root_.OAI.Problem367.colorPermMap_val _root_.OAI.Problem367.connectedSpinEncode_apply_root _root_.OAI.Problem367.connectedSpinEquiv_apply _root_.OAI.Problem367.dropVertex_length _root_.OAI.Problem367.dropVertex_val _root_.OAI.Problem367.flipConfig_apply _root_.OAI.Problem367.flipConfig_flipConfig _root_.OAI.Problem367.flipConfig_preimage_spin _root_.OAI.Problem367.freeCylinderWeight_flipConfig _root_.OAI.Problem367.iUnion_treeBallFinset _root_.OAI.Problem367.mem_rootComplementFinset _root_.OAI.Problem367.mem_rootComponentFinset _root_.OAI.Problem367.mem_rootComponentIndices _root_.OAI.Problem367.mem_treeBallFinset _root_.OAI.Problem367.mem_treeNeighborFinset _root_.OAI.Problem367.prefixColorAut_length _root_.OAI.Problem367.prefixColorAut_val _root_.OAI.Problem367.prefixColorMap_symm_apply _root_.OAI.Problem367.spinAgreementCode_eq_neg_iff _root_.OAI.Problem367.spinAgreementCode_eq_pos_iff _root_.OAI.Problem367.spinSign_flip _root_.OAI.Problem367.sum_treeShell_zero _root_.OAI.Problem367.tsum_treeShell_radial _root_.OAI.Problem367.vertexSampler_relabel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators Classical

namespace Problem367.TreeGibbsAut

variable {d : ℕ}

theorem sum_inducedEdges_image {M : Type*} [AddCommMonoid M]
    (g : TreeAut d) (D : Finset (TreeVertex d))
    (f : TreeVertex d → TreeVertex d → M) (hf : ∀ u v, f u v = f v u) :
    (∑ e ∈ inducedEdges (D.image g.toEquiv),
      f (g.toEquiv.symm e.1) (g.toEquiv.symm e.2)) =
        ∑ e ∈ inducedEdges D, f e.1 e.2 := by
  have h := CylinderAut.prod_inducedEdges_image g D
    (fun u v => Multiplicative.ofAdd (f u v))
    (fun u v => congrArg Multiplicative.ofAdd (hf u v))
  simpa using congrArg Multiplicative.toAdd h

theorem energy_relabel (g : TreeAut d) (D : Finset (TreeVertex d))
    (beta : ℝ) (h : TreeVertex d → ℝ) (eta : TreeVertex d → IsingSpin) :
    GibbsLeaf.energy beta (relabel g h) (D.image g.toEquiv) (relabel g eta) =
      GibbsLeaf.energy beta h D eta := by
  unfold GibbsLeaf.energy relabel
  rw [Finset.sum_image g.toEquiv.injective.injOn]
  simp only [Equiv.symm_apply_apply]
  rw [sum_inducedEdges_image g D
    (fun u v => spinSign (eta u) * spinSign (eta v))
    (fun u v => mul_comm _ _)]

theorem energy_spinEquiv (g : TreeAut d) (D : Finset (TreeVertex d))
    (beta : ℝ) (h : TreeVertex d → ℝ) (eta : D → IsingSpin) :
    GibbsLeaf.energy beta (relabel g h) (D.image g.toEquiv)
      (extendFiniteSpin (D.image g.toEquiv) (spinEquiv g D eta)) =
        GibbsLeaf.energy beta h D (extendFiniteSpin D eta) := by
  calc
    _ = GibbsLeaf.energy beta (relabel g h) (D.image g.toEquiv)
        (relabel g (extendFiniteSpin D eta)) := by
      apply GibbsLeaf.energy_congr_on
      intro x hx
      obtain ⟨u, hu, rfl⟩ := Finset.mem_image.mp hx
      change extendFiniteSpin (D.image g.toEquiv) (spinEquiv g D eta)
          ((vertexEquiv g D ⟨u, hu⟩).val) = _
      rw [extendFiniteSpin_apply, spinEquiv_apply_image]
      simp [relabel, extendFiniteSpin, hu]
    _ = _ := energy_relabel g D beta h _

theorem expectation_equiv {A B : Type*} [Fintype A] [Fintype B]
    (e : A ≃ B) (E f : B → ℝ) :
    LeafGibbs.expectation (E ∘ e) (f ∘ e) = LeafGibbs.expectation E f := by
  unfold LeafGibbs.expectation
  simp only [Function.comp_apply]
  rw [e.sum_comp (fun b => f b * Real.exp (E b)), e.sum_comp (fun b => Real.exp (E b))]

theorem expectation_relabel (g : TreeAut d) (D : Finset (TreeVertex d))
    (beta : ℝ) (h : TreeVertex d → ℝ) (f : (D.image g.toEquiv → IsingSpin) → ℝ) :
    LeafGibbs.expectation
      (fun eta => GibbsLeaf.energy beta (relabel g h) (D.image g.toEquiv)
        (extendFiniteSpin (D.image g.toEquiv) eta)) f =
    LeafGibbs.expectation
      (fun eta => GibbsLeaf.energy beta h D (extendFiniteSpin D eta))
      (fun eta => f (spinEquiv g D eta)) := by
  rw [← expectation_equiv (spinEquiv g D)]
  congr 1
  funext eta
  exact energy_spinEquiv g D beta h eta

theorem covariance_relabel (g : TreeAut d) (D : Finset (TreeVertex d))
    (beta : ℝ) (h : TreeVertex d → ℝ) (f k : (D.image g.toEquiv → IsingSpin) → ℝ) :
    LeafGibbs.covariance
      (fun eta => GibbsLeaf.energy beta (relabel g h) (D.image g.toEquiv)
        (extendFiniteSpin (D.image g.toEquiv) eta)) f k =
    LeafGibbs.covariance
      (fun eta => GibbsLeaf.energy beta h D (extendFiniteSpin D eta))
      (fun eta => f (spinEquiv g D eta)) (fun eta => k (spinEquiv g D eta)) := by
  unfold LeafGibbs.covariance
  rw [expectation_relabel, expectation_relabel, expectation_relabel]

theorem spin_covariance_relabel (g : TreeAut d) (D : Finset (TreeVertex d))
    (beta : ℝ) (h : TreeVertex d → ℝ) (u v : D) :
    LeafGibbs.covariance
      (fun eta => GibbsLeaf.energy beta (relabel g h) (D.image g.toEquiv)
        (extendFiniteSpin (D.image g.toEquiv) eta))
      (fun eta => spinSign (eta (vertexEquiv g D u)))
      (fun eta => spinSign (eta (vertexEquiv g D v))) =
    LeafGibbs.covariance
      (fun eta => GibbsLeaf.energy beta h D (extendFiniteSpin D eta))
      (fun eta => spinSign (eta u)) (fun eta => spinSign (eta v)) := by
  rw [covariance_relabel]
  simp only [spinEquiv_apply_image]

theorem covariance_bounds_of_reroot {beta : ℝ} (hbeta : 0 ≤ beta)
    (D : Finset (TreeVertex d)) (hD : ConnectedFinset D)
    (h : TreeVertex d → ℝ) (u v : D) (g : TreeAut d)
    (hg : g.toEquiv u = ConnectedHull.root d) :
    0 ≤ LeafGibbs.covariance
      (fun eta => GibbsLeaf.energy beta h D (extendFiniteSpin D eta))
      (fun eta => spinSign (eta u)) (fun eta => spinSign (eta v)) ∧
    LeafGibbs.covariance
      (fun eta => GibbsLeaf.energy beta h D (extendFiniteSpin D eta))
      (fun eta => spinSign (eta u)) (fun eta => spinSign (eta v)) ≤
        Real.tanh beta ^ (g.toEquiv v).1.length := by
  have hzero : (g.toEquiv u).1.length = 0 := by rw [hg]; rfl
  have hb := tree_gibbs_root_covariance_bounds hbeta (hD.image g)
    (vertexEquiv g D u).property
    (fun x hx => by change (g.toEquiv u).1.length ≤ x.1.length; rw [hzero]; exact Nat.zero_le _)
    (relabel g h) (g.toEquiv v) (vertexEquiv g D v).property
  change 0 ≤ LeafGibbs.covariance
      (fun eta => GibbsLeaf.energy beta (relabel g h) (D.image g.toEquiv)
        (extendFiniteSpin (D.image g.toEquiv) eta))
      (fun eta => spinSign (eta (vertexEquiv g D u)))
      (fun eta => spinSign (eta (vertexEquiv g D v))) ∧
    LeafGibbs.covariance
      (fun eta => GibbsLeaf.energy beta (relabel g h) (D.image g.toEquiv)
        (extendFiniteSpin (D.image g.toEquiv) eta))
      (fun eta => spinSign (eta (vertexEquiv g D u)))
      (fun eta => spinSign (eta (vertexEquiv g D v))) ≤
        Real.tanh beta ^ ((g.toEquiv v).1.length - (g.toEquiv u).1.length) at hb
  simpa only [spin_covariance_relabel, hzero, Nat.sub_zero] using hb

end Problem367.TreeGibbsAut

end

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Gaussian_TreeResponsePosterior
attribute [-instance] _root_.OAI.Problem367.IsingConditionalCopyBounds.graphLaw_isProbabilityMeasure _root_.OAI.Problem367.IsingObservationFactor.copies_probability _root_.OAI.Problem367.IsingObservationFactor.kernel_markov _root_.OAI.Problem367.IsingObservationInnovation.innovationMap_observationLaw_probability _root_.OAI.Problem367.IsingObservationInnovation.observationLaw_probability _root_.OAI.Problem367.TreeKoopman.labelProbability _root_.OAI.Problem367.freeIsingMeasure_probability
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

end Problem367

end

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Gibbs_CovarianceEnergy
attribute [-instance] _root_.OAI.Problem367.IsingConditionalCopyBounds.graphLaw_isProbabilityMeasure _root_.OAI.Problem367.IsingObservationFactor.copies_probability _root_.OAI.Problem367.IsingObservationFactor.kernel_markov _root_.OAI.Problem367.IsingObservationInnovation.innovationMap_observationLaw_probability _root_.OAI.Problem367.IsingObservationInnovation.observationLaw_probability _root_.OAI.Problem367.TreeKoopman.labelProbability _root_.OAI.Problem367.WienerSampler.pathMeasurableSpace _root_.OAI.Problem367.freeIsingMeasure_probability
attribute [-simp] _root_.OAI.Problem367.CutContinuationChannels.averageChannel_globalCone _root_.OAI.Problem367.CutContinuationChannels.continuationChannel_globalCone _root_.OAI.Problem367.FactorObservable.centeredSpinLp_coe _root_.OAI.Problem367.GaussianTreeResponseNaturality.fieldEquiv_apply_image _root_.OAI.Problem367.IsingObservationInnovation.innovationMap_apply _root_.OAI.Problem367.IsingObservationInnovation.innovationMap_uniformObservation _root_.OAI.Problem367.IsingObservationInnovation.innovationMap_zero _root_.OAI.Problem367.IsingObservationInnovation.uniformObservation_relabel _root_.OAI.Problem367.IsingOrientedPath.attenuation_outward _root_.OAI.Problem367.IsingOrientedPath.endpoint_extensionAt _root_.OAI.Problem367.LocalSupportGeometry.prefixVertex_length _root_.OAI.Problem367.PathSideBranches.parent_sideVertex _root_.OAI.Problem367.PathSideBranches.restrictNoisyRegion_array _root_.OAI.Problem367.PathSideBranches.sideVertex_length _root_.OAI.Problem367.PathSideBranches.sideVertex_val _root_.OAI.Problem367.RootedBroadcast.flipBranchToComplement_val _root_.OAI.Problem367.RootedBroadcast.prefixFlip_branchRoot _root_.OAI.Problem367.RootedBroadcast.prefixFlip_root _root_.OAI.Problem367.RootedBroadcast.prefixTreeAut_symm_branchRoot _root_.OAI.Problem367.RootedBroadcast.prefixTreeAut_symm_root _root_.OAI.Problem367.TreeConeCoding.length_vertex _root_.OAI.Problem367.TreeConeCoding.vertex_nil _root_.OAI.Problem367.TreeConeCoding.vertex_val _root_.OAI.Problem367.TreeKoopman.centeredAverage_apply_coe _root_.OAI.Problem367.TreeKoopman.centeredAverage_pow_apply_coe _root_.OAI.Problem367.TreeKoopman.centeredGenerator_apply_coe _root_.OAI.Problem367.TreeKoopman.centeredGenerator_sq _root_.OAI.Problem367.TreeKoopman.generatorOperator_sq _root_.OAI.Problem367.TreeKoopman.reverseVertex_twice _root_.OAI.Problem367.TreeKoopman.wordRelabel_cons _root_.OAI.Problem367.TreeKoopman.wordRelabel_nil _root_.OAI.Problem367.TreeLawKoopman.centeredAverage_apply_coe _root_.OAI.Problem367.TreeLawKoopman.generatorOperator_sq _root_.OAI.Problem367.branchColorAut_length _root_.OAI.Problem367.branchColorAut_singleton _root_.OAI.Problem367.branchColorAut_val _root_.OAI.Problem367.branchColorMap_symm_apply _root_.OAI.Problem367.colorPermAut_length _root_.OAI.Problem367.colorPermAut_nil _root_.OAI.Problem367.colorPermAut_val _root_.OAI.Problem367.colorPermMap_symm_apply _root_.OAI.Problem367.colorPermMap_val _root_.OAI.Problem367.connectedSpinEncode_apply_root _root_.OAI.Problem367.connectedSpinEquiv_apply _root_.OAI.Problem367.dropVertex_length _root_.OAI.Problem367.dropVertex_val _root_.OAI.Problem367.mem_rootComplementFinset _root_.OAI.Problem367.mem_rootComponentFinset _root_.OAI.Problem367.mem_rootComponentIndices _root_.OAI.Problem367.prefixColorAut_length _root_.OAI.Problem367.prefixColorAut_val _root_.OAI.Problem367.prefixColorMap_symm_apply _root_.OAI.Problem367.vertexSampler_relabel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory ProbabilityTheory Filter
open scoped NNReal Topology BigOperators

namespace Problem367

open PlantedSymmetry GaussianTreeCovariance

theorem finiteGibbsCovarianceOn_eq_treeCovariance {d : ℕ} (beta : ℝ)
    (D : Finset (TreeVertex d)) (v w : D) (y : TreeVertex d → ℝ) :
    finiteGibbsCovarianceOn beta D v w (D.restrict y) =
      TreePathResponse.covariance beta y D v.1 w.1 := by
  unfold finiteGibbsCovarianceOn TreePathResponse.covariance LeafGibbs.covariance
  simp only [extendFiniteSpin_apply D _ v, extendFiniteSpin_apply D _ w,
    GibbsLeaf.expectation_eq_fieldMean]

lemma integrable_finiteGibbsCovariance_sq {d : ℕ} (beta : ℝ)
    (v w : TreeVertex d) (n : ℕ) {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} [IsFiniteMeasure P]
    {X : Ω → TreeVertex d → ℝ} (hX : Measurable X) :
    Integrable (fun ω => finiteGibbsCovariance beta v w n (X ω) ^ 2) P := by
  apply (integrable_const (4 : ℝ)).mono'
    (((continuous_finiteGibbsCovariance beta v w n).measurable.comp hX).pow_const 2).aestronglyMeasurable
  refine Eventually.of_forall fun ω => ?_
  rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
  have h := finiteGibbsCovariance_abs_le_two beta v w n (X ω)
  have hs := (sq_le_sq₀ (abs_nonneg _) (by norm_num : (0 : ℝ) ≤ 2)).2 h
  norm_num [sq_abs] at hs
  exact hs

end Problem367

end

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Gibbs_CovarianceIntrinsicEnergy
attribute [-instance] _root_.OAI.Problem367.IsingConditionalCopyBounds.graphLaw_isProbabilityMeasure _root_.OAI.Problem367.IsingObservationFactor.copies_probability _root_.OAI.Problem367.IsingObservationFactor.kernel_markov _root_.OAI.Problem367.IsingObservationInnovation.innovationMap_observationLaw_probability _root_.OAI.Problem367.IsingObservationInnovation.observationLaw_probability _root_.OAI.Problem367.TreeKoopman.labelProbability _root_.OAI.Problem367.freeIsingMeasure_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory Filter
open scoped NNReal Topology BigOperators
namespace Problem367
open PlantedSymmetry GaussianTreeCovariance

theorem summable_geometric_intrinsic {d : ℕ} (v : TreeVertex d) {r : ℝ}
    (hr : 0 ≤ r) (hsmall : ((d - 1 : ℕ) : ℝ) * r < 1) :
    Summable (fun w : TreeVertex d => r ^ reducedWordDistance v.1 w.1) := by
  obtain ⟨g, _, hd⟩ := exists_treeAut_to_root_distance v
  apply g.toEquiv.symm.summable_iff.mp
  have hdist (w : TreeVertex d) :
      reducedWordDistance v.1 (g.toEquiv.symm w).1 = w.1.length := by
    simpa only [Equiv.apply_symm_apply] using (hd (g.toEquiv.symm w)).symm
  simpa only [Function.comp_def, hdist] using summable_geometric_radial d hr hsmall

end Problem367

end

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Trees_GibbsCovariance
attribute [-instance] _root_.OAI.Problem367.IsingConditionalCopyBounds.graphLaw_isProbabilityMeasure _root_.OAI.Problem367.IsingObservationFactor.copies_probability _root_.OAI.Problem367.IsingObservationFactor.kernel_markov _root_.OAI.Problem367.IsingObservationInnovation.innovationMap_observationLaw_probability _root_.OAI.Problem367.IsingObservationInnovation.observationLaw_probability _root_.OAI.Problem367.TreeKoopman.labelProbability _root_.OAI.Problem367.freeIsingMeasure_probability _root_.OAI.Problem367.reducedTailFintype _root_.OAI.Problem367.treeBallFintype _root_.OAI.Problem367.treeShellFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace Problem367

theorem tree_gibbs_covariance_bounds {d : ℕ} {beta : ℝ} (hbeta : 0 ≤ beta)
    {D : Finset (TreeVertex d)} (hD : ConnectedFinset D) (h : TreeVertex d → ℝ)
    {u v : TreeVertex d} (hu : u ∈ D) (hv : v ∈ D) :
    0 ≤ LeafGibbs.covariance
      (fun eta => GibbsLeaf.energy beta h D (extendFiniteSpin D eta))
      (fun eta => spinSign (eta ⟨u, hu⟩)) (fun eta => spinSign (eta ⟨v, hv⟩)) ∧
    LeafGibbs.covariance
      (fun eta => GibbsLeaf.energy beta h D (extendFiniteSpin D eta))
      (fun eta => spinSign (eta ⟨u, hu⟩)) (fun eta => spinSign (eta ⟨v, hv⟩)) ≤
        Real.tanh beta ^ reducedWordDistance u.1 v.1 := by
  obtain ⟨g, hg, hdist⟩ := exists_treeAut_to_root_distance u
  simpa only [hdist] using
    TreeGibbsAut.covariance_bounds_of_reroot hbeta D hD h ⟨u, hu⟩ ⟨v, hv⟩ g hg

theorem abs_tree_gibbs_covariance_le {d : ℕ} {beta : ℝ} (hbeta : 0 ≤ beta)
    {D : Finset (TreeVertex d)} (hD : ConnectedFinset D) (h : TreeVertex d → ℝ)
    {u v : TreeVertex d} (hu : u ∈ D) (hv : v ∈ D) :
    |LeafGibbs.covariance
      (fun eta => GibbsLeaf.energy beta h D (extendFiniteSpin D eta))
      (fun eta => spinSign (eta ⟨u, hu⟩)) (fun eta => spinSign (eta ⟨v, hv⟩))| ≤
        Real.tanh beta ^ reducedWordDistance u.1 v.1 := by
  have hb := tree_gibbs_covariance_bounds hbeta hD h hu hv
  rw [abs_of_nonneg hb.1]
  exact hb.2

end Problem367

end

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Gibbs_CovarianceStrictConvergence
attribute [-instance] _root_.OAI.Problem367.IsingConditionalCopyBounds.graphLaw_isProbabilityMeasure _root_.OAI.Problem367.IsingObservationFactor.copies_probability _root_.OAI.Problem367.IsingObservationFactor.kernel_markov _root_.OAI.Problem367.IsingObservationInnovation.innovationMap_observationLaw_probability _root_.OAI.Problem367.IsingObservationInnovation.observationLaw_probability _root_.OAI.Problem367.TreeKoopman.labelProbability _root_.OAI.Problem367.freeIsingMeasure_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory Filter
open scoped NNReal Topology BigOperators
namespace Problem367
open PlantedSymmetry

theorem finiteGibbsCovariance_abs_le_distance {d : ℕ} {beta : ℝ}
    (hb : 0 ≤ beta) (v w : TreeVertex d) (n : ℕ) (y : TreeVertex d → ℝ) :
    |finiteGibbsCovariance beta v w n y| ≤
      Real.tanh beta ^ reducedWordDistance v.1 w.1 := by
  classical
  unfold finiteGibbsCovariance
  split_ifs with hw
  · rw [finiteGibbsCovarianceOn_eq_treeCovariance]
    simp only [TreePathResponse.covariance,
      extendFiniteSpin_apply (connectedExhaustion v n) _ ⟨v, mem_connectedExhaustion v n⟩,
      extendFiniteSpin_apply (connectedExhaustion v n) _ ⟨w, hw⟩]
    exact abs_tree_gibbs_covariance_le hb (connectedExhaustion_connected v n) y
        (mem_connectedExhaustion v n) hw
  · simpa only [abs_zero] using
      pow_nonneg (tanh_nonneg_of_beta_nonneg hb) (reducedWordDistance v.1 w.1)

end Problem367

end

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Gibbs_CovarianceStrictEnergy
attribute [-instance] _root_.OAI.Problem367.IsingConditionalCopyBounds.graphLaw_isProbabilityMeasure _root_.OAI.Problem367.IsingObservationFactor.copies_probability _root_.OAI.Problem367.IsingObservationFactor.kernel_markov _root_.OAI.Problem367.IsingObservationInnovation.innovationMap_observationLaw_probability _root_.OAI.Problem367.IsingObservationInnovation.observationLaw_probability _root_.OAI.Problem367.TreeKoopman.labelProbability _root_.OAI.Problem367.WienerSampler.pathMeasurableSpace _root_.OAI.Problem367.freeIsingMeasure_probability
attribute [-simp] _root_.OAI.Problem367.CutContinuationChannels.averageChannel_globalCone _root_.OAI.Problem367.CutContinuationChannels.continuationChannel_globalCone _root_.OAI.Problem367.FactorObservable.centeredSpinLp_coe _root_.OAI.Problem367.FiniteIsingSplit.splitEquiv_fst _root_.OAI.Problem367.FiniteIsingSplit.splitEquiv_snd _root_.OAI.Problem367.IsingObservationInnovation.innovationMap_apply _root_.OAI.Problem367.IsingObservationInnovation.innovationMap_uniformObservation _root_.OAI.Problem367.IsingObservationInnovation.innovationMap_zero _root_.OAI.Problem367.IsingObservationInnovation.uniformObservation_relabel _root_.OAI.Problem367.IsingOrientedPath.attenuation_outward _root_.OAI.Problem367.IsingOrientedPath.endpoint_extensionAt _root_.OAI.Problem367.LocalSupportGeometry.prefixVertex_length _root_.OAI.Problem367.PathSideBranches.parent_sideVertex _root_.OAI.Problem367.PathSideBranches.restrictNoisyRegion_array _root_.OAI.Problem367.PathSideBranches.sideVertex_length _root_.OAI.Problem367.PathSideBranches.sideVertex_val _root_.OAI.Problem367.RootedBroadcast.flipBranchToComplement_val _root_.OAI.Problem367.RootedBroadcast.pos_spinMul _root_.OAI.Problem367.RootedBroadcast.prefixFlip_branchRoot _root_.OAI.Problem367.RootedBroadcast.prefixFlip_root _root_.OAI.Problem367.RootedBroadcast.prefixTreeAut_symm_branchRoot _root_.OAI.Problem367.RootedBroadcast.prefixTreeAut_symm_root _root_.OAI.Problem367.RootedBroadcast.spinMul_pos _root_.OAI.Problem367.RootedBroadcast.spinMul_self _root_.OAI.Problem367.TreeConeCoding.length_vertex _root_.OAI.Problem367.TreeConeCoding.vertex_nil _root_.OAI.Problem367.TreeConeCoding.vertex_val _root_.OAI.Problem367.TreeKoopman.centeredAverage_apply_coe _root_.OAI.Problem367.TreeKoopman.centeredAverage_pow_apply_coe _root_.OAI.Problem367.TreeKoopman.centeredGenerator_apply_coe _root_.OAI.Problem367.TreeKoopman.centeredGenerator_sq _root_.OAI.Problem367.TreeKoopman.generatorOperator_sq _root_.OAI.Problem367.TreeKoopman.reverseVertex_twice _root_.OAI.Problem367.TreeKoopman.wordRelabel_cons _root_.OAI.Problem367.TreeKoopman.wordRelabel_nil _root_.OAI.Problem367.TreeLawKoopman.centeredAverage_apply_coe _root_.OAI.Problem367.TreeLawKoopman.generatorOperator_sq _root_.OAI.Problem367.branchColorAut_length _root_.OAI.Problem367.branchColorAut_singleton _root_.OAI.Problem367.branchColorAut_val _root_.OAI.Problem367.branchColorMap_symm_apply _root_.OAI.Problem367.colorPermAut_length _root_.OAI.Problem367.colorPermAut_nil _root_.OAI.Problem367.colorPermAut_val _root_.OAI.Problem367.colorPermMap_symm_apply _root_.OAI.Problem367.colorPermMap_val _root_.OAI.Problem367.connectedSpinEncode_apply_root _root_.OAI.Problem367.connectedSpinEquiv_apply _root_.OAI.Problem367.dropVertex_length _root_.OAI.Problem367.dropVertex_val _root_.OAI.Problem367.mem_rootComplementFinset _root_.OAI.Problem367.mem_rootComponentFinset _root_.OAI.Problem367.mem_rootComponentIndices _root_.OAI.Problem367.prefixColorAut_length _root_.OAI.Problem367.prefixColorAut_val _root_.OAI.Problem367.prefixColorMap_symm_apply _root_.OAI.Problem367.spinAgreementCode_eq_neg_iff _root_.OAI.Problem367.spinAgreementCode_eq_pos_iff _root_.OAI.Problem367.spinSign_flip _root_.OAI.Problem367.vertexSampler_relabel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal Topology BigOperators
namespace Problem367

local instance covarianceStrictEnergyNonemptyIsingSpin : Nonempty IsingSpin := ⟨.neg⟩

lemma finiteGibbsSpinMean_abs_le_one {d : ℕ} (beta : ℝ)
    (v : TreeVertex d) (n : ℕ) (y : TreeVertex d → ℝ) :
    |finiteGibbsSpinMean beta v n y| ≤ 1 := by
  apply FinitePosterior.abs_fieldMean_le
  intro eta
  cases eta ⟨v, mem_connectedExhaustion v n⟩ <;> norm_num [spinSign]

lemma finiteGibbsCovariance_self {d : ℕ} (beta : ℝ)
    (v : TreeVertex d) (n : ℕ) (y : TreeVertex d → ℝ) :
    finiteGibbsCovariance beta v v n y = 1 - finiteGibbsSpinMean beta v n y ^ 2 := by
  classical
  simp only [finiteGibbsCovariance, dite_eq_left (mem_connectedExhaustion v n)]
  unfold finiteGibbsCovarianceOn finiteGibbsSpinMean
  have heq : (fun eta : connectedExhaustion v n → IsingSpin =>
      spinSign (eta ⟨v, mem_connectedExhaustion v n⟩) *
        spinSign (eta ⟨v, mem_connectedExhaustion v n⟩)) = fun _ => (1 : ℝ) := by
    funext eta
    cases eta ⟨v, mem_connectedExhaustion v n⟩ <;> norm_num [spinSign]
  rw [heq, FinitePosterior.fieldMean_const, pow_two]

theorem HasFreeIsingLaw.finiteGibbsSpinMean_brownian_tendsto_integral_sq
    {d : ℕ} {beta : ℝ} {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure (TreeVertex d → IsingSpin)}
    (hμ : HasFreeIsingLaw (Real.tanh beta) μ)
    (ν : TreeVertex d → Measure Ω) {B : TreeVertex d → ℝ≥0 → Ω → ℝ}
    (hB : ∀ i, IsPreBrownianReal (B i) (ν i))
    (hmB : ∀ i t, Measurable (B i t)) (t : ℝ≥0) (v : TreeVertex d) :
    Tendsto (fun n => ∫ p,
      finiteGibbsSpinMean beta v n
        (fun i => (t : ℝ) * spinSign (p.1 i) + B i t (p.2 i)) ^ 2
      ∂μ.prod (Measure.infinitePi ν)) atTop
      (𝓝 (∫ p, infiniteGibbsSpinMean beta v
        (fun i => (t : ℝ) * spinSign (p.1 i) + B i t (p.2 i)) ^ 2
        ∂μ.prod (Measure.infinitePi ν))) := by
  let : IsProbabilityMeasure μ := hμ.isProbabilityMeasure
  have (i : TreeVertex d) : IsProbabilityMeasure (ν i) :=
    (hB i).isGaussianProcess.isProbabilityMeasure
  let X := fun p : (TreeVertex d → IsingSpin) × (TreeVertex d → Ω) =>
    fun i => (t : ℝ) * spinSign (p.1 i) + B i t (p.2 i)
  have hX : Measurable X := by
    apply Measurable.of_eval
    intro i
    exact (measurable_const.mul ((measurable_of_finite spinSign).comp
      ((measurable_pi_apply i).comp measurable_fst))).add
      ((hmB i t).comp ((measurable_pi_apply i).comp measurable_snd))
  apply tendsto_integral_of_dominated_convergence (fun _ => (1 : ℝ))
    (fun n => (((continuous_finiteGibbsSpinMean beta v n).measurable.comp hX).pow_const 2).aestronglyMeasurable)
    (integrable_const 1)
  · intro n
    filter_upwards with p
    have hs := pow_le_pow_left₀ (abs_nonneg _)
      (finiteGibbsSpinMean_abs_le_one beta v n (X p)) 2
    simpa only [Function.comp_def, Real.norm_eq_abs, abs_pow, sq_abs, one_pow] using hs
  · filter_upwards [hμ.finiteGibbsCovariance_brownian_tendsto_ae ν hB hmB t v v]
      with p hp
    simpa only [finiteGibbsCovariance_self, infiniteGibbsCovariance_self,
      sub_sub_cancel, Function.comp_def, X] using hp.const_sub 1

theorem HasFreeIsingLaw.finiteGibbsCovariance_timeEnergy_eq
    {d : ℕ} {beta : ℝ} {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure (TreeVertex d → IsingSpin)}
    (hμ : HasFreeIsingLaw (Real.tanh beta) μ)
    (ν : TreeVertex d → Measure Ω) {B : TreeVertex d → ℝ≥0 → Ω → ℝ}
    (hB : ∀ i, IsPreBrownianReal (B i) (ν i))
    (hmB : ∀ i t, Measurable (B i t))
    (hcB : ∀ i omega, Continuous (fun t => B i t omega))
    (v : TreeVertex d) (n : ℕ) {T : ℝ} (hT : 0 ≤ T) :
    (∑' w, ∫ p, finiteGibbsCovariance beta v w n (brownianIsingObservationR B p) ^ 2
      ∂(volume.restrict (Ioc (0 : ℝ) T)).prod (μ.prod (Measure.infinitePi ν))) =
    ∫ p, finiteGibbsSpinMean beta v n (brownianIsingObservationR B (T, p)) ^ 2
      ∂μ.prod (Measure.infinitePi ν) := by
  classical
  let : IsProbabilityMeasure μ := hμ.isProbabilityMeasure
  have (i : TreeVertex d) : IsProbabilityMeasure (ν i) :=
    (hB i).isGaussianProcess.isProbabilityMeasure
  let D := connectedExhaustion v n
  let ρ := μ.prod (Measure.infinitePi ν)
  let τ : Measure ℝ := volume.restrict (Ioc 0 T)
  let C := fun w p => finiteGibbsCovariance beta v w n (brownianIsingObservationR B p)
  have hi (w : TreeVertex d) : Integrable (fun p => C w p ^ 2) (τ.prod ρ) :=
    integrable_finiteGibbsCovariance_sq beta v w n (measurable_brownianIsingObservationR hmB hcB)
  have hsum : Integrable (fun p => ∑ w ∈ D, C w p ^ 2) (τ.prod ρ) :=
    integrable_finsetSum D (fun w _ => hi w)
  have heq (p : ℝ × ((TreeVertex d → IsingSpin) × (TreeVertex d → Ω))) :
      (∑ w ∈ D, C w p ^ 2) =
      ∑ w : D, finiteIsingBrownianCovariance beta D
        ⟨v, mem_connectedExhaustion v n⟩ w B p.1 p.2 ^ 2 := by
    rw [← Finset.sum_attach D]
    apply Finset.sum_congr rfl
    intro w _
    rw [show C w p = finiteIsingBrownianCovariance beta D
      ⟨v, mem_connectedExhaustion v n⟩ w B p.1 p.2 from
        finiteGibbsCovariance_eq_finiteIsingBrownianCovariance beta v n B p w]
  have he := hμ.integral_finiteIsingBrownianEnergy ν hB hmB D
    (connectedExhaustion_connected v n) ⟨v, mem_connectedExhaustion v n⟩ hT
  calc
    (∑' w, ∫ p, C w p ^ 2 ∂τ.prod ρ) = ∑ w ∈ D, ∫ p, C w p ^ 2 ∂τ.prod ρ := by
      apply tsum_eq_sum
      intro w hw
      change w ∉ connectedExhaustion v n at hw
      simp only [C, finiteGibbsCovariance, dite_eq_right hw, zero_pow (by decide : 2 ≠ 0), integral_zero]
    _ = ∫ p, ∑ w ∈ D, C w p ^ 2 ∂τ.prod ρ :=
      (integral_finsetSum D (fun w _ => hi w)).symm
    _ = ∫ t, ∫ p, ∑ w ∈ D, C w (t, p) ^ 2 ∂ρ ∂τ := integral_prod _ hsum
    _ = ∫ t in (0 : ℝ)..T, ∫ p, ∑ w : D,
        finiteIsingBrownianCovariance beta D ⟨v, mem_connectedExhaustion v n⟩ w B t p ^ 2 ∂ρ := by
      rw [intervalIntegral.integral_of_le hT]
      apply integral_congr_ae
      filter_upwards with t
      apply integral_congr_ae
      filter_upwards with p
      exact heq (t, p)
    _ = ∫ p, finiteIsingBrownianMean beta D ⟨v, mem_connectedExhaustion v n⟩ B T p ^ 2 ∂ρ := he.2.1
    _ = _ := rfl

theorem HasFreeIsingLaw.infiniteGibbsCovariance_timeEnergy_eq_of_strict
    {d : ℕ} {beta : ℝ} {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure (TreeVertex d → IsingSpin)}
    (hμ : HasFreeIsingLaw (Real.tanh beta) μ) (hb : 0 ≤ beta)
    (hstrict : ((d - 1 : ℕ) : ℝ) * Real.tanh beta ^ 2 < 1)
    (ν : TreeVertex d → Measure Ω) {B : TreeVertex d → ℝ≥0 → Ω → ℝ}
    (hB : ∀ i, IsPreBrownianReal (B i) (ν i))
    (hmB : ∀ i t, Measurable (B i t))
    (hcB : ∀ i omega, Continuous (fun t => B i t omega))
    (v : TreeVertex d) {T : ℝ} (hT : 0 ≤ T) :
    let P := (volume.restrict (Ioc (0 : ℝ) T)).prod (μ.prod (Measure.infinitePi ν))
    let C := fun w p => infiniteGibbsCovariance beta v w (brownianIsingObservationR B p)
    let M := ∫ p, infiniteGibbsSpinMean beta v (brownianIsingObservationR B (T, p)) ^ 2
      ∂μ.prod (Measure.infinitePi ν)
    HasSum (fun w => ∫ p, C w p ^ 2 ∂P) M ∧
      (∫ p, ∑' w, C w p ^ 2 ∂P) = M := by
  let : IsProbabilityMeasure μ := hμ.isProbabilityMeasure
  have (i : TreeVertex d) : IsProbabilityMeasure (ν i) :=
    (hB i).isGaussianProcess.isProbabilityMeasure
  let P := (volume.restrict (Ioc (0 : ℝ) T)).prod (μ.prod (Measure.infinitePi ν))
  let C := fun w p => infiniteGibbsCovariance beta v w (brownianIsingObservationR B p)
  let Cn := fun n w p => finiteGibbsCovariance beta v w n (brownianIsingObservationR B p)
  let M := ∫ p, infiniteGibbsSpinMean beta v (brownianIsingObservationR B (T, p)) ^ 2
    ∂μ.prod (Measure.infinitePi ν)
  have hX := measurable_brownianIsingObservationR hmB hcB
  have hi (n : ℕ) (w : TreeVertex d) : Integrable (fun p => Cn n w p ^ 2) P :=
    integrable_finiteGibbsCovariance_sq beta v w n hX
  have hbound (n : ℕ) (w : TreeVertex d) :
      (∫ p, Cn n w p ^ 2 ∂P) ≤
        P.real univ * (Real.tanh beta ^ 2) ^ reducedWordDistance v.1 w.1 := by
    calc
      _ ≤ ∫ _p, (Real.tanh beta ^ reducedWordDistance v.1 w.1) ^ 2 ∂P := by
        apply integral_mono (hi n w) (integrable_const _)
        intro p
        simpa only [sq_abs] using pow_le_pow_left₀ (abs_nonneg _)
          (finiteGibbsCovariance_abs_le_distance hb v w n (brownianIsingObservationR B p)) 2
      _ = _ := by
        rw [integral_const, smul_eq_mul]
        congr 1
        rw [← pow_mul, ← pow_mul, Nat.mul_comm]
  have hs := (summable_geometric_intrinsic v (sq_nonneg (Real.tanh beta)) hstrict).mul_left
    (P.real univ)
  have hlim : Tendsto (fun n => ∑' w, ∫ p, Cn n w p ^ 2 ∂P) atTop
      (𝓝 (∑' w, ∫ p, C w p ^ 2 ∂P)) := by
    apply tendsto_tsum_of_dominated_convergence hs
      (fun w => hμ.finiteGibbsCovariance_tendsto_timeSquareIntegral ν hB hmB hcB v w)
    exact Eventually.of_forall fun n w => by
      rw [Real.norm_eq_abs, abs_of_nonneg (integral_nonneg (fun p => sq_nonneg _))]
      exact hbound n w
  have hterminal : Tendsto (fun n => ∫ p,
      finiteGibbsSpinMean beta v n (brownianIsingObservationR B (T, p)) ^ 2
      ∂μ.prod (Measure.infinitePi ν)) atTop (𝓝 M) := by
    have h := hμ.finiteGibbsSpinMean_brownian_tendsto_integral_sq ν hB hmB T.toNNReal v
    rw [Real.coe_toNNReal T hT] at h
    convert h using 1 <;> rfl
  have hfinite (n : ℕ) : (∑' w, ∫ p, Cn n w p ^ 2 ∂P) =
      ∫ p, finiteGibbsSpinMean beta v n (brownianIsingObservationR B (T, p)) ^ 2
        ∂μ.prod (Measure.infinitePi ν) :=
    hμ.finiteGibbsCovariance_timeEnergy_eq ν hB hmB hcB v n hT
  have heq : (∑' w, ∫ p, C w p ^ 2 ∂P) = M :=
    tendsto_nhds_unique hlim (hterminal.congr' (Eventually.of_forall fun n => (hfinite n).symm))
  have hrow := hμ.infiniteGibbsCovariance_timeEnergy ν hB hmB hcB v hT
  have hh : HasSum (fun w => ∫ p, C w p ^ 2 ∂P) M := by
    rw [← heq]
    exact hrow.1.hasSum
  have hident := DiscrepancyEnergy.hasSum_integral_sq_row
    (fun w => ((measurable_infiniteGibbsCovariance beta v w).comp hX).aestronglyMeasurable)
    hrow.2.2.1 hrow.2.2.2.1
  dsimp only
  exact ⟨hh, hident.unique hh⟩

end Problem367

end

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Gibbs_CovarianceWindowEnergy
attribute [-instance] _root_.OAI.Problem367.WienerSampler.pathMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal Topology BigOperators
namespace Problem367
open PlantedSymmetry GaussianTreeCovariance

lemma integral_prod_Ioc_sub {Ω : Type*} [MeasurableSpace Ω]
    {ρ : Measure Ω} [SFinite ρ] {f : ℝ × Ω → ℝ} {δ T : ℝ}
    (hδ : 0 ≤ δ) (hδT : δ ≤ T)
    (hf : Integrable f ((volume.restrict (Ioc (0 : ℝ) T)).prod ρ)) :
    (∫ p, f p ∂(volume.restrict (Ioc δ T)).prod ρ) =
      (∫ p, f p ∂(volume.restrict (Ioc (0 : ℝ) T)).prod ρ) -
      ∫ p, f p ∂(volume.restrict (Ioc (0 : ℝ) δ)).prod ρ := by
  have hm : (volume.restrict (Ioc (0 : ℝ) T)).prod ρ =
      (volume.restrict (Ioc (0 : ℝ) δ)).prod ρ +
        (volume.restrict (Ioc δ T)).prod ρ := by
    rw [← Ioc_union_Ioc_eq_Ioc hδ hδT,
      Measure.restrict_union (Ioc_disjoint_Ioc_of_le le_rfl) measurableSet_Ioc,
      Measure.add_prod]
  rw [hm, integrable_add_measure] at hf
  rw [hm, integral_add_measure hf.1 hf.2]
  ring

end Problem367

end

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Gibbs_CovarianceCriticalEnergy
attribute [-instance] _root_.OAI.Problem367.IsingConditionalCopyBounds.graphLaw_isProbabilityMeasure _root_.OAI.Problem367.IsingObservationFactor.copies_probability _root_.OAI.Problem367.IsingObservationFactor.kernel_markov _root_.OAI.Problem367.IsingObservationInnovation.innovationMap_observationLaw_probability _root_.OAI.Problem367.IsingObservationInnovation.observationLaw_probability _root_.OAI.Problem367.TreeKoopman.labelProbability _root_.OAI.Problem367.WienerSampler.pathMeasurableSpace
attribute [-simp] _root_.OAI.Problem367.CutContinuationChannels.averageChannel_globalCone _root_.OAI.Problem367.CutContinuationChannels.continuationChannel_globalCone _root_.OAI.Problem367.FactorObservable.centeredSpinLp_coe _root_.OAI.Problem367.FiniteIsingSplit.splitEquiv_fst _root_.OAI.Problem367.FiniteIsingSplit.splitEquiv_snd _root_.OAI.Problem367.IsingObservationInnovation.innovationMap_apply _root_.OAI.Problem367.IsingObservationInnovation.innovationMap_uniformObservation _root_.OAI.Problem367.IsingObservationInnovation.innovationMap_zero _root_.OAI.Problem367.IsingObservationInnovation.uniformObservation_relabel _root_.OAI.Problem367.IsingOrientedPath.attenuation_outward _root_.OAI.Problem367.IsingOrientedPath.endpoint_extensionAt _root_.OAI.Problem367.LocalSupportGeometry.prefixVertex_length _root_.OAI.Problem367.PathSideBranches.parent_sideVertex _root_.OAI.Problem367.PathSideBranches.restrictNoisyRegion_array _root_.OAI.Problem367.PathSideBranches.sideVertex_length _root_.OAI.Problem367.PathSideBranches.sideVertex_val _root_.OAI.Problem367.TreeConeCoding.length_vertex _root_.OAI.Problem367.TreeConeCoding.vertex_nil _root_.OAI.Problem367.TreeConeCoding.vertex_val _root_.OAI.Problem367.TreeKoopman.centeredAverage_apply_coe _root_.OAI.Problem367.TreeKoopman.centeredAverage_pow_apply_coe _root_.OAI.Problem367.TreeKoopman.centeredGenerator_apply_coe _root_.OAI.Problem367.TreeKoopman.centeredGenerator_sq _root_.OAI.Problem367.TreeKoopman.generatorOperator_sq _root_.OAI.Problem367.TreeKoopman.reverseVertex_twice _root_.OAI.Problem367.TreeKoopman.wordRelabel_cons _root_.OAI.Problem367.TreeKoopman.wordRelabel_nil _root_.OAI.Problem367.TreeLawKoopman.centeredAverage_apply_coe _root_.OAI.Problem367.TreeLawKoopman.generatorOperator_sq _root_.OAI.Problem367.dropVertex_length _root_.OAI.Problem367.dropVertex_val _root_.OAI.Problem367.mem_rootComplementFinset _root_.OAI.Problem367.mem_rootComponentFinset _root_.OAI.Problem367.mem_rootComponentIndices _root_.OAI.Problem367.prefixColorAut_length _root_.OAI.Problem367.prefixColorAut_val _root_.OAI.Problem367.prefixColorMap_symm_apply _root_.OAI.Problem367.spinSign_flip _root_.OAI.Problem367.vertexSampler_relabel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal Topology BigOperators
namespace Problem367
open PlantedSymmetry

theorem HasFreeIsingLaw.infiniteGibbsCovariance_timeEnergy_eq_of_critical
    {d : ℕ} (hd : 3 ≤ d) {beta : ℝ} {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure (TreeVertex d → IsingSpin)}
    (hμ : HasFreeIsingLaw (Real.tanh beta) μ) (hb : 0 ≤ beta)
    (hcritical : ((d - 1 : ℕ) : ℝ) * Real.tanh beta ^ 2 = 1)
    (ν : TreeVertex d → Measure Ω) {B : TreeVertex d → ℝ≥0 → Ω → ℝ}
    (hB : ∀ i, IsPreBrownianReal (B i) (ν i))
    (hmB : ∀ i t, Measurable (B i t))
    (hcB : ∀ i omega, Continuous (fun t => B i t omega))
    (v : TreeVertex d) {T : ℝ} (hT : 0 ≤ T) :
    let P := (volume.restrict (Ioc (0 : ℝ) T)).prod (μ.prod (Measure.infinitePi ν))
    let C := fun w p => infiniteGibbsCovariance beta v w (brownianIsingObservationR B p)
    let M := ∫ p, infiniteGibbsSpinMean beta v (brownianIsingObservationR B (T, p)) ^ 2
      ∂μ.prod (Measure.infinitePi ν)
    HasSum (fun w => ∫ p, C w p ^ 2 ∂P) M ∧
      (∫ p, ∑' w, C w p ^ 2 ∂P) = M := by
  let : IsProbabilityMeasure μ := hμ.isProbabilityMeasure
  have (i : TreeVertex d) : IsProbabilityMeasure (ν i) :=
    (hB i).isGaussianProcess.isProbabilityMeasure
  let ρ := μ.prod (Measure.infinitePi ν)
  let P := fun t : ℝ => (volume.restrict (Ioc (0 : ℝ) t)).prod ρ
  let C := fun w p => infiniteGibbsCovariance beta v w (brownianIsingObservationR B p)
  let E := fun t : ℝ => ∫ p, ∑' w, C w p ^ 2 ∂P t
  let M := fun t : ℝ => ∫ p, infiniteGibbsSpinMean beta v (brownianIsingObservationR B (t, p)) ^ 2 ∂ρ
  have hrow (t : ℝ) (ht : 0 ≤ t) := hμ.infiniteGibbsCovariance_timeEnergy ν hB hmB hcB v ht
  have hi (t : ℝ) (ht : 0 ≤ t) : Integrable (fun p => ∑' w, C w p ^ 2) (P t) :=
    (hrow t ht).2.2.2.1
  have heq : E T = M T := by
    rcases eq_or_lt_of_le hT with hzero | hpos
    · subst T
      have hM0 : M 0 = 0 := hμ.infiniteGibbsSpinMean_brownian_critical_zero
        hd hb hcritical ν hB hmB v
      simp only [E, P, Ioc_self, Measure.restrict_empty, Measure.zero_prod, integral_zero_measure, hM0]
    · let δ := fun n : ℕ => T / ((n : ℝ) + 1)
      have hδpos (n : ℕ) : 0 < δ n := div_pos hpos (by positivity)
      have hδT (n : ℕ) : δ n ≤ T := by
        dsimp [δ]
        exact div_le_self hT (le_add_of_nonneg_left (Nat.cast_nonneg n))
      have hδlim : Tendsto δ atTop (𝓝 0) := by
        simpa only [δ, mul_one_div, mul_zero] using
          (tendsto_const_nhds (x := T)).mul
            (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))
      have hMlim : Tendsto (fun n => M (δ n)) atTop (𝓝 0) := by
        have hn : Tendsto (fun n => (δ n).toNNReal) atTop (𝓝 0) := by
          simpa only [Function.comp_def, Real.toNNReal_zero] using
            (continuous_real_toNNReal.tendsto 0).comp hδlim
        have h := (hμ.infiniteGibbsSpinMean_brownian_critical_tendsto_zero
          hd hb hcritical ν hB hmB v).comp hn
        convert h using 1
        all_goals try with_reducible_and_instances rfl
        funext n
        simp only [Function.comp_def, M, ρ,
          Real.coe_toNNReal (δ n) (hδpos n).le]
        rfl
      let f := fun t : ℝ => ∫ p, ∑' w, C w (t, p) ^ 2 ∂ρ
      have hf : Integrable f (volume.restrict (Ioc (0 : ℝ) T)) :=
        (hi T hT).integral_prod_left
      have hprim := (hf.continuous_primitive 0).tendsto 0
      have hElim : Tendsto (fun n => E (δ n)) atTop (𝓝 0) := by
        have h := hprim.comp hδlim
        simp only [intervalIntegral.integral_same] at h
        convert h using 1
        all_goals try with_reducible_and_instances rfl
        funext n
        dsimp only [E, Function.comp_def]
        rw [integral_prod _ (hi (δ n) (hδpos n).le),
          intervalIntegral.integral_of_le (hδpos n).le,
          Measure.restrict_restrict measurableSet_Ioc,
          inter_eq_left.mpr (Ioc_subset_Ioc_right (hδT n))]
      have hdiff (n : ℕ) : E T - E (δ n) = M T - M (δ n) := by
        have hw := (hμ.infiniteGibbsCovariance_windowEnergy_eq hb hcritical.le
          ν hB hmB hcB v (hδpos n) (hδT n)).2
        exact (integral_prod_Ioc_sub (hδpos n).le (hδT n) (hi T hT)).symm.trans hw
      have hsame := tendsto_nhds_unique
        ((tendsto_const_nhds (x := E T)).sub hElim)
        (((tendsto_const_nhds (x := M T)).sub hMlim).congr'
          (Eventually.of_forall fun n => (hdiff n).symm))
      simpa only [sub_zero] using hsame
  have hX := measurable_brownianIsingObservationR hmB hcB
  have hident := DiscrepancyEnergy.hasSum_integral_sq_row
    (fun w => ((measurable_infiniteGibbsCovariance beta v w).comp hX).aestronglyMeasurable)
    (hrow T hT).2.2.1 (hi T hT)
  have hh : HasSum (fun w => ∫ p, C w p ^ 2 ∂P T) (M T) := by
    rw [← heq]
    exact hident
  dsimp only
  exact ⟨hh, heq⟩

theorem HasFreeIsingLaw.infiniteGibbsCovariance_timeEnergy_eq_oai
    {d : ℕ} (hd : 3 ≤ d) {beta : ℝ} {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure (TreeVertex d → IsingSpin)}
    (hμ : HasFreeIsingLaw (Real.tanh beta) μ) (hb : 0 ≤ beta)
    (hcrit : ((d - 1 : ℕ) : ℝ) * Real.tanh beta ^ 2 ≤ 1)
    (ν : TreeVertex d → Measure Ω) {B : TreeVertex d → ℝ≥0 → Ω → ℝ}
    (hB : ∀ i, IsPreBrownianReal (B i) (ν i))
    (hmB : ∀ i t, Measurable (B i t))
    (hcB : ∀ i omega, Continuous (fun t => B i t omega))
    (v : TreeVertex d) {T : ℝ} (hT : 0 ≤ T) :
    let P := (volume.restrict (Ioc (0 : ℝ) T)).prod (μ.prod (Measure.infinitePi ν))
    let C := fun w p => infiniteGibbsCovariance beta v w (brownianIsingObservationR B p)
    let M := ∫ p, infiniteGibbsSpinMean beta v (brownianIsingObservationR B (T, p)) ^ 2
      ∂μ.prod (Measure.infinitePi ν)
    HasSum (fun w => ∫ p, C w p ^ 2 ∂P) M ∧
      (∫ p, ∑' w, C w p ^ 2 ∂P) = M := by
  rcases lt_or_eq_of_le hcrit with hs | he
  · exact hμ.infiniteGibbsCovariance_timeEnergy_eq_of_strict hb hs ν hB hmB hcB v hT
  · exact hμ.infiniteGibbsCovariance_timeEnergy_eq_of_critical hd hb he ν hB hmB hcB v hT

end Problem367

end

end OAI
end

theorem solution.{u_1} : type_of% @OAI.Problem367.HasFreeIsingLaw.infiniteGibbsCovariance_timeEnergy_eq_oai.{u_1} := @OAI.Problem367.HasFreeIsingLaw.infiniteGibbsCovariance_timeEnergy_eq_oai.{u_1}
