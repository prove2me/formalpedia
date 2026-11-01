-- Prove2me | solution 1 for GittinsUCB.Patient.equation_5
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-31T07:51:27.432997+00:00
-- url     : https://prove2.me/submissions/7bfa8311-a860-4a13-853a-cf1b8144194b

import Mathlib
import Definitions.Def_GittinsUCB_Patient_Model
open MeasureTheory ProbabilityTheory Filter Asymptotics NNReal
open GittinsUCB.Patient

namespace GittinsEq5Aux

instance (μ : ℝ) (σ2 σW2 : ℝ≥0) : IsProbabilityMeasure (model μ σ2 σW2) := by
  unfold model; infer_instance

lemma integrable_gauss_id : Integrable (fun x : ℝ => x) (gaussianReal 0 1) :=
  (memLp_id_gaussianReal 1).integrable le_rfl

lemma integrable_theta (σW2 : ℝ≥0) : Integrable (θ : Ω → ℝ) (model 0 1 σW2) := by
  unfold model θ
  exact integrable_gauss_id.comp_fst _

lemma measurable_R (t : ℕ) : Measurable (R t) :=
  measurable_fst.add ((measurable_pi_apply t).comp measurable_snd)

lemma rewardSigma_le (t : ℕ) : rewardSigma t ≤ (inferInstance : MeasurableSpace Ω) := by
  unfold rewardSigma
  apply Measurable.comap_le
  exact measurable_pi_lambda _ (fun s => measurable_R s)

lemma measurableSet_ge {τ : Ω → ℕ∞} (hτ : IsRetirementTime τ) (t : ℕ) :
    MeasurableSet {ω | (t : ℕ∞) ≤ τ ω} := by
  cases t with
  | zero => simp
  | succ n =>
    have h : {ω | ((n + 1 : ℕ) : ℕ∞) ≤ τ ω} = {ω | τ ω ≤ (n : ℕ∞)}ᶜ := by
      ext ω
      simp only [Set.mem_setOf_eq, Set.mem_compl_iff, not_le, Nat.cast_add, Nat.cast_one]
      exact ENat.add_one_le_iff (ENat.coe_ne_top n)
    rw [h]
    exact (rewardSigma_le n _ (hτ.1 n)).compl

/-- Pointwise facts about the stopped reward with constant reward `θ`. -/
lemma summand_bound (γ lam : ℝ) (hγ0 : 0 < γ) (τ : Ω → ℕ∞) (ω : Ω) (t : ℕ) :
    ‖(if (t : ℕ∞) ≤ τ ω then γ ^ t * (θ ω - lam) else 0)‖ ≤ γ ^ t * |θ ω - lam| := by
  split_ifs
  · rw [Real.norm_eq_abs, abs_mul, abs_of_pos (pow_pos hγ0 t)]
  · simp; positivity

lemma summable_summand (γ lam : ℝ) (hγ0 : 0 < γ) (hγ1 : γ < 1) (τ : Ω → ℕ∞) (ω : Ω) :
    Summable (fun t : ℕ => if (t : ℕ∞) ≤ τ ω then γ ^ t * (θ ω - lam) else 0) :=
  Summable.of_norm_bounded ((summable_geometric_of_lt_one hγ0.le hγ1).mul_right _)
    (summand_bound γ lam hγ0 τ ω)

lemma stoppedReward_le (γ lam : ℝ) (hγ0 : 0 < γ) (hγ1 : γ < 1) (τ : Ω → ℕ∞) (ω : Ω) :
    stoppedReward γ lam (fun _ => θ) τ ω ≤
      (θ ω - lam) + γ / (1 - γ) * max (θ ω - lam) 0 := by
  unfold stoppedReward
  have hs := summable_summand γ lam hγ0 hγ1 τ ω
  rw [hs.tsum_eq_zero_add]
  have h0 : (if ((0 : ℕ) : ℕ∞) ≤ τ ω then γ ^ 0 * (θ ω - lam) else 0) = θ ω - lam := by
    simp
  rw [h0]
  have hgeo : Summable (fun n : ℕ => γ * max (θ ω - lam) 0 * γ ^ n) :=
    (summable_geometric_of_lt_one hγ0.le hγ1).mul_left _
  have hle : (∑' n : ℕ, (if ((n + 1 : ℕ) : ℕ∞) ≤ τ ω then γ ^ (n + 1) * (θ ω - lam) else 0)) ≤
      ∑' n : ℕ, γ * max (θ ω - lam) 0 * γ ^ n := by
    refine Summable.tsum_mono ((_root_.summable_nat_add_iff 1).mpr hs) hgeo (fun n => ?_)
    have hp : 0 < γ ^ (n + 1) := pow_pos hγ0 _
    split_ifs
    · rw [pow_succ]
      have := le_max_left (θ ω - lam) 0
      have h2 : γ ^ n * γ * (θ ω - lam) ≤ γ ^ n * γ * max (θ ω - lam) 0 :=
        mul_le_mul_of_nonneg_left this (by positivity)
      linarith
    · have := le_max_right (θ ω - lam) 0
      positivity
  rw [_root_.tsum_mul_left, tsum_geometric_of_lt_one hγ0.le hγ1] at hle
  have e : γ * max (θ ω - lam) 0 * (1 - γ)⁻¹ = γ / (1 - γ) * max (θ ω - lam) 0 := by
    field_simp
  linarith

lemma integrable_stoppedReward (γ lam : ℝ) (hγ0 : 0 < γ) (hγ1 : γ < 1) (σW2 : ℝ≥0)
    {τ : Ω → ℕ∞} (hτ : IsRetirementTime τ) :
    Integrable (stoppedReward γ lam (fun _ => θ) τ) (model 0 1 σW2) := by
  have hθ : Measurable (θ : Ω → ℝ) := measurable_fst
  have hmeas_t : ∀ t : ℕ, Measurable
      (fun ω : Ω => if (t : ℕ∞) ≤ τ ω then γ ^ t * (θ ω - lam) else 0) := by
    intro t
    exact Measurable.ite (measurableSet_ge hτ t) (measurable_const.mul (hθ.sub_const _))
      measurable_const
  have hmeas : Measurable (stoppedReward γ lam (fun _ => θ) τ) := by
    unfold stoppedReward
    refine measurable_of_tendsto_metrizable (fun n => Finset.measurable_sum (Finset.range n)
      (fun t _ => hmeas_t t)) ?_
    rw [tendsto_pi_nhds]
    intro ω
    exact (summable_summand γ lam hγ0 hγ1 τ ω).hasSum.tendsto_sum_nat
  have hθint : Integrable (θ : Ω → ℝ) (model 0 1 σW2) := integrable_theta σW2
  refine Integrable.mono' ((hθint.sub (integrable_const lam)).abs.mul_const (1 - γ)⁻¹)
    hmeas.aestronglyMeasurable (Eventually.of_forall fun ω => ?_)
  unfold stoppedReward
  have hg : HasSum (fun t : ℕ => γ ^ t * |θ ω - lam|) (|θ ω - lam| * (1 - γ)⁻¹) := by
    have := (hasSum_geometric_of_lt_one hγ0.le hγ1).mul_right (|θ ω - lam|)
    simpa [mul_comm] using this
  exact tsum_of_norm_bounded hg (summand_bound γ lam hγ0 τ ω)

end GittinsEq5Aux

open GittinsEq5Aux in
theorem solution (σW2 : ℝ≥0) (hW : 0 < σW2)
    (γ lam : ℝ) (hγ0 : 0 < γ) (hγ1 : γ < 1) :
    value σW2 γ lam 0 1 ≤
      -lam + γ / (1 - γ) *
        ∫ ω, max (θ ω - lam) 0 ∂(model 0 1 σW2) := by
  have hθint : Integrable (θ : Ω → ℝ) (model 0 1 σW2) := integrable_theta σW2
  have hθ0 : ∫ ω, θ ω ∂(model 0 1 σW2) = 0 := by
    unfold model θ
    exact (integral_fun_fst (μ := gaussianReal 0 1) (fun x : ℝ => x)).trans
      (by simp [integral_id_gaussianReal])
  have hmaxint : Integrable (fun ω => max (θ ω - lam) 0) (model 0 1 σW2) :=
    (hθint.sub (integrable_const lam)).sup (integrable_const 0)
  have hB : ∫ ω, ((θ ω - lam) + γ / (1 - γ) * max (θ ω - lam) 0) ∂(model 0 1 σW2) =
      -lam + γ / (1 - γ) * ∫ ω, max (θ ω - lam) 0 ∂(model 0 1 σW2) := by
    have hsub : Integrable (fun ω => θ ω - lam) (model 0 1 σW2) :=
      hθint.sub (integrable_const lam)
    rw [integral_add (f := fun ω => θ ω - lam)
      (g := fun ω => γ / (1 - γ) * max (θ ω - lam) 0) hsub (hmaxint.const_mul _),
      integral_sub (f := fun ω => θ ω) (g := fun _ => lam) hθint (integrable_const lam),
      integral_const_mul, hθ0]
    simp
  have hne : Nonempty {τ : Ω → ℕ∞ // IsRetirementTime τ} :=
    ⟨⟨fun _ => ⊤, fun t => by simp, fun ω => le_top⟩⟩
  unfold value
  refine ciSup_le (fun τ => ?_)
  rw [← hB]
  exact integral_mono (integrable_stoppedReward γ lam hγ0 hγ1 σW2 τ.2)
    ((hθint.sub (integrable_const lam)).add (hmaxint.const_mul _))
    (fun ω => stoppedReward_le γ lam hγ0 hγ1 τ.1 ω)
