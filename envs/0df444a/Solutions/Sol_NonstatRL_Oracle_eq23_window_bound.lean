-- Prove2me | solution 1 for NonstatRL.Oracle.eq23_window_bound
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-22T18:06:34.587481+00:00
-- url     : https://prove2.me/submissions/11998b83-e49d-4194-a96e-4f2e915085ab

import Mathlib
import Definitions.Def_FiniteMDPLearning
import Definitions.Def_NonstatRL_Oracle_Model
import Definitions.Def_NonstatRL_Oracle_Trajectory
import Theorems.Thm_NonstatRL_Oracle_exists_bounded_optimal_dual
import Theorems.Thm_NonstatRL_Oracle_eq18_optGain_drift
import Theorems.Thm_NonstatRL_Oracle_eq19_dual_drift

open BanditAlgorithm ENNReal MeasureTheory ProbabilityTheory

namespace NonstatRL.Oracle

theorem eq23_meas_restr {S A k m : ℕ} (hkm : k ≤ m) :
    Measurable (fun (h : MDPTrajectory S A m) (j : Fin k) => h (Fin.castLE hkm j)) :=
  measurable_pi_lambda _ (fun j => measurable_pi_apply _)

theorem eq23_prefix {S A : ℕ} (M : ℕ → FiniteMDP S A) (s₁ : Fin S) (π : MDPPolicy S A)
    (k m : ℕ) (hkm : k ≤ m) :
    (nsMeasure M s₁ π m).map (fun h (j : Fin k) => h (Fin.castLE hkm j)) =
      nsMeasure M s₁ π k := by
  induction m, hkm using Nat.le_induction with
  | base =>
    have : (fun (h : MDPTrajectory S A k) (j : Fin k) => h (Fin.castLE le_rfl j)) = id := by
      funext h j; simp
    rw [this, Measure.map_id]
  | succ n hn ih =>
    rw [nsMeasure, Measure.map_map (eq23_meas_restr _) measurable_mdpTrajectorySnoc]
    have hcomp : ((fun (h : MDPTrajectory S A (n + 1)) (j : Fin k) => h (Fin.castLE (by omega) j)) ∘
        (fun p : MDPTrajectory S A n × (Fin S × Fin A) =>
          Fin.snoc (α := fun _ => Fin S × Fin A) p.1 p.2)) =
        (fun (h : MDPTrajectory S A n) (j : Fin k) => h (Fin.castLE hn j)) ∘ Prod.fst := by
      funext p j
      have hj : ((Fin.castLE (show k ≤ n + 1 by omega) j : Fin (n+1)) : ℕ) < n := by
        simp; omega
      have hj' : (j : ℕ) < n := by simpa using hj
      simp only [Function.comp]
      simp [Fin.snoc, hj']
      exact congrArg p.1 (Fin.ext rfl)
    rw [hcomp, ← Measure.map_map (eq23_meas_restr hn) measurable_fst]
    rw [← Measure.fst, Measure.fst_compProd, ih]

theorem eq23_step_integral {S A : ℕ} (M : ℕ → FiniteMDP S A) (s₁ : Fin S) (π : MDPPolicy S A)
    (n : ℕ) (φ : MDPTrajectory S A (n + 1) → ℝ) :
    ∫ h, φ h ∂(nsMeasure M s₁ π (n + 1)) =
      ∫ h, ∫ p, φ (Fin.snoc (α := fun _ => Fin S × Fin A) h p) ∂(nsStepKernel M s₁ π n h)
        ∂(nsMeasure M s₁ π n) := by
  rw [nsMeasure, integral_map measurable_mdpTrajectorySnoc.aemeasurable
    (measurable_of_countable φ).aestronglyMeasurable]
  rw [Measure.integral_compProd Integrable.of_finite]

theorem eq23_inner_fst {S A : ℕ} (M : ℕ → FiniteMDP S A) (s₁ : Fin S) (π : MDPPolicy S A)
    (n : ℕ) (h : MDPTrajectory S A n) (f : Fin S → ℝ) :
    ∫ p, f p.1 ∂(nsStepKernel M s₁ π n h) = ∫ s, f s ∂(nsStateKernel M s₁ n h) := by
  rw [← integral_map measurable_fst.aemeasurable (measurable_of_countable f).aestronglyMeasurable]
  rw [← Kernel.fst_apply, nsStepKernel, Kernel.fst_compProd]

theorem eq23_trans_integral {S : ℕ} (P : MDPStateDistribution S) (f : Fin S → ℝ) :
    ∫ s, f s ∂P.toMeasure = ∑ s', (P.prob s' : ℝ) * f s' := by
  rw [MDPStateDistribution.toMeasure, integral_finsetSum_measure]
  · apply Finset.sum_congr rfl; intro s' _
    rw [integral_smul_measure, integral_dirac]
    simp
  · intro i _; exact Integrable.smul_measure Integrable.of_finite ENNReal.coe_ne_top

theorem eq23_state_kernel_succ {S A : ℕ} (M : ℕ → FiniteMDP S A) (s₁ : Fin S) (n : ℕ)
    (h : MDPTrajectory S A (n + 1)) :
    nsStateKernel M s₁ (n + 1) h =
      ((M n).transitionDist (h (Fin.last n)).1 (h (Fin.last n)).2).toMeasure := by
  rw [nsStateKernel, Kernel.comap_apply, mdpTransitionKernel]; rfl

theorem eq23_next_state {S A : ℕ} (M : ℕ → FiniteMDP S A) (s₁ : Fin S) (π : MDPPolicy S A)
    (T i : ℕ) (hi : i + 1 < T) (f : Fin S → ℝ) :
    ∫ h, f (h ⟨i + 1, hi⟩).1 ∂(nsMeasure M s₁ π T) =
      ∫ h, ∑ s', ((M i).P (h ⟨i, by omega⟩).1 (h ⟨i, by omega⟩).2 s' : ℝ) * f s'
        ∂(nsMeasure M s₁ π T) := by
  have h1 : (∫ h, f (h ⟨i + 1, hi⟩).1 ∂(nsMeasure M s₁ π T)) =
      ∫ h', f (h' (Fin.last (i + 1))).1 ∂(nsMeasure M s₁ π (i + 1 + 1)) := by
    rw [← eq23_prefix M s₁ π (i + 1 + 1) T (by omega),
      integral_map (eq23_meas_restr _).aemeasurable
        (measurable_of_countable _).aestronglyMeasurable]
    rfl
  have h2 : (∫ h, ∑ s', ((M i).P (h ⟨i, by omega⟩).1 (h ⟨i, by omega⟩).2 s' : ℝ) * f s'
        ∂(nsMeasure M s₁ π T)) =
      ∫ h', ∑ s', ((M i).P (h' (Fin.last i)).1 (h' (Fin.last i)).2 s' : ℝ) * f s'
        ∂(nsMeasure M s₁ π (i + 1)) := by
    rw [← eq23_prefix M s₁ π (i + 1) T (by omega),
      integral_map (eq23_meas_restr _).aemeasurable
        (measurable_of_countable _).aestronglyMeasurable]
    rfl
  rw [h1, h2, eq23_step_integral]
  apply integral_congr_ae
  filter_upwards with h
  simp only [Fin.snoc_last]
  rw [eq23_inner_fst M s₁ π (i + 1) h f, eq23_state_kernel_succ, eq23_trans_integral]
  rfl

theorem eq23_allowed_ae {S A : ℕ} (M : ℕ → FiniteMDP S A) (s₁ : Fin S) (π : MDPPolicy S A)
    (As : Fin S → Finset (Fin A)) (hπ : IsAllowedPolicy As π)
    (T i : ℕ) (hi : i < T) :
    ∀ᵐ h ∂(nsMeasure M s₁ π T), (h ⟨i, hi⟩).2 ∈ As (h ⟨i, hi⟩).1 := by
  rw [ae_iff]
  have hset : {h : MDPTrajectory S A T | ¬ (h ⟨i, hi⟩).2 ∈ As (h ⟨i, hi⟩).1} =
      (fun h (j : Fin (i + 1)) => h (Fin.castLE (show i + 1 ≤ T by omega) j)) ⁻¹'
        {h' : MDPTrajectory S A (i + 1) | (h' (Fin.last i)).2 ∉ As (h' (Fin.last i)).1} := by
    ext h; rfl
  rw [hset, ← Measure.map_apply (eq23_meas_restr _) (Set.toFinite _).measurableSet,
    eq23_prefix, nsMeasure,
    Measure.map_apply measurable_mdpTrajectorySnoc (Set.toFinite _).measurableSet,
    Measure.compProd_apply (Set.toFinite _).measurableSet]
  have hz : ∀ h : MDPTrajectory S A i,
      nsStepKernel M s₁ π i h
        (Prod.mk h ⁻¹' ((fun p : MDPTrajectory S A i × (Fin S × Fin A) =>
          Fin.snoc (α := fun _ => Fin S × Fin A) p.1 p.2) ⁻¹'
          {h' : MDPTrajectory S A (i + 1) | (h' (Fin.last i)).2 ∉ As (h' (Fin.last i)).1})) = 0 := by
    intro h
    have hpre : (Prod.mk h ⁻¹' ((fun p : MDPTrajectory S A i × (Fin S × Fin A) =>
          Fin.snoc (α := fun _ => Fin S × Fin A) p.1 p.2) ⁻¹'
          {h' : MDPTrajectory S A (i + 1) | (h' (Fin.last i)).2 ∉ As (h' (Fin.last i)).1})) =
        {p : Fin S × Fin A | p.2 ∉ As p.1} := by
      ext p; simp [Fin.snoc_last]
    rw [hpre, nsStepKernel, Kernel.compProd_apply (Set.toFinite _).measurableSet]
    exact (lintegral_congr (fun b => hπ i h b)).trans lintegral_zero
  simp_rw [hz]
  exact lintegral_zero

theorem eq23_rewardDrift_nonneg {S A : ℕ} (M : ℕ → FiniteMDP S A)
    (As : Fin S → Finset (Fin A)) (q : ℕ) : 0 ≤ rewardDrift M As q := by
  unfold rewardDrift
  apply Real.sSup_nonneg
  rintro d ⟨s, a, -, rfl⟩
  exact abs_nonneg _

theorem eq23_transDrift_nonneg {S A : ℕ} (M : ℕ → FiniteMDP S A)
    (As : Fin S → Finset (Fin A)) (q : ℕ) : 0 ≤ transDrift M As q := by
  unfold transDrift
  apply Real.sSup_nonneg
  rintro d ⟨s, a, -, rfl⟩
  exact Finset.sum_nonneg (fun _ _ => abs_nonneg _)

theorem eq23_filter_sum {T : ℕ} (t W : ℕ) (hEnd : t + W ≤ T) (g : ℕ → ℝ) :
    ∑ τ ∈ (Finset.univ.filter fun τ : Fin T => t ≤ (τ : ℕ) ∧ (τ : ℕ) < t + W), g τ =
      ∑ i ∈ Finset.Ico t (t + W), g i := by
  refine Finset.sum_bij (fun (τ : Fin T) _ => (τ : ℕ)) ?_ ?_ ?_ ?_
  · intro τ hτ
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hτ
    simpa [Finset.mem_Ico] using hτ
  · intro a _ b _ hab; exact Fin.ext hab
  · intro i hi
    simp only [Finset.mem_Ico] at hi
    exact ⟨⟨i, by omega⟩, by simp [hi.1, hi.2], rfl⟩
  · intro τ _; rfl

theorem eq23_telescope (X Y : ℕ → ℝ) (t : ℕ) :
    ∀ W, 1 ≤ W → (∀ i, t ≤ i → i + 1 < t + W → X i = Y (i + 1)) →
      ∑ i ∈ Finset.Ico t (t + W), (X i - Y i) = X (t + W - 1) - Y t := by
  intro W hW
  induction W, hW using Nat.le_induction with
  | base => intro _; simp
  | succ n hn ih =>
    intro hXY
    rw [show t + (n + 1) = (t + n) + 1 by omega, Finset.sum_Ico_succ_top (by omega),
      ih (fun i h1 h2 => hXY i h1 (by omega))]
    have := hXY (t + n - 1) (by omega) (by omega)
    rw [show t + n - 1 + 1 = t + n by omega] at this
    rw [show t + n + 1 - 1 = t + n by omega, show t + n - 1 = t + n - 1 from rfl, this]
    ring

end NonstatRL.Oracle

open NonstatRL.Oracle

theorem solution {S A : ℕ} (M : ℕ → FiniteMDP S A)
    (As : Fin S → Finset (Fin A)) (hS : 0 < S)
    (hAs : ∀ s, (As s).Nonempty) (T : ℕ) (Dmax : ℝ)
    (hD : ∀ u, u < T → diameter (M u) As ≤ ENNReal.ofReal Dmax)
    (s₁ : Fin S) (π : MDPPolicy S A) (hπ : IsAllowedPolicy As π)
    (t W : ℕ) (hW : 0 < W) (hEnd : t + W ≤ T) :
    (∫ h, ∑ τ ∈ (Finset.univ.filter fun τ : Fin T =>
        t ≤ (τ : ℕ) ∧ (τ : ℕ) < t + W),
        (M τ).r (h τ).1 (h τ).2 ∂(nsMeasure M s₁ π T)) -
      2 * Dmax - 2 * (W : ℝ) *
        (∑ q ∈ Finset.Ico t (min (t + W) (T - 1)),
          (rewardDrift M As q + 2 * Dmax * transDrift M As q)) ≤
      ∑ τ ∈ Finset.Ico t (t + W), optGain (M τ) As := by
  obtain ⟨γ, hγ, hγb⟩ := exists_bounded_optimal_dual (M t) As hS hAs Dmax (hD t (by omega))
  have hDnn : 0 ≤ Dmax := by
    have := hγb ⟨0, hS⟩; linarith [this.1, this.2]
  set μ := nsMeasure M s₁ π T with hμ
  set dr : ℕ → ℝ := fun q => rewardDrift M As q + 2 * Dmax * transDrift M As q with hdr
  have hdr0 : ∀ q, 0 ≤ dr q := fun q => by
    have := eq23_rewardDrift_nonneg M As q
    have := eq23_transDrift_nonneg M As q
    simp only [hdr]; positivity
  set Δ := ∑ q ∈ Finset.Ico t (min (t + W) (T - 1)), dr q with hΔ
  -- pointwise key inequality
  have key : ∀ i, t ≤ i → i < t + W → ∀ s a, a ∈ As s →
      (M i).r s a ≤ optGain (M i) As + 2 * Δ -
        ((∑ s' : Fin S, ((M i).P s a s' : ℝ) * γ s') - γ s) := by
    intro i hti hiW s a ha
    have hiT : i < T := by omega
    have h19 := eq19_dual_drift M As hS hAs T Dmax hD t i hti hiT γ hγ hγb s a ha
    have h18 := eq18_optGain_drift M As hS hAs T Dmax hD t i hti hiT
    have hsub : ∑ q ∈ Finset.Ico t i, dr q ≤ Δ := by
      apply Finset.sum_le_sum_of_subset_of_nonneg
      · intro q hq; simp only [Finset.mem_Ico] at hq ⊢; omega
      · intro q _ _; exact hdr0 q
    simp only [hdr] at hsub h19 h18
    linarith
  -- a.e. allowedness
  have hae : ∀ᵐ h ∂μ, ∀ τ : Fin T, (h τ).2 ∈ As (h τ).1 := by
    rw [ae_all_iff]; intro τ
    exact eq23_allowed_ae M s₁ π As hπ T τ τ.isLt
  set filt := (Finset.univ.filter fun τ : Fin T => t ≤ (τ : ℕ) ∧ (τ : ℕ) < t + W) with hfilt
  have hmono : (∫ h, ∑ τ ∈ filt, (M τ).r (h τ).1 (h τ).2 ∂μ) ≤
      ∫ h, ∑ τ ∈ filt, ((optGain (M τ) As + 2 * Δ) -
        ((∑ s' : Fin S, ((M τ).P (h τ).1 (h τ).2 s' : ℝ) * γ s') - γ (h τ).1)) ∂μ := by
    apply integral_mono_ae Integrable.of_finite Integrable.of_finite
    filter_upwards [hae] with h hh
    apply Finset.sum_le_sum; intro τ hτ
    simp only [hfilt, Finset.mem_filter, Finset.mem_univ, true_and] at hτ
    exact key τ hτ.1 hτ.2 _ _ (hh τ)
  -- compute RHS
  set Xn : ℕ → ℝ := fun i => if hi : i < T then
    ∫ h, ∑ s' : Fin S, ((M i).P (h ⟨i, hi⟩).1 (h ⟨i, hi⟩).2 s' : ℝ) * γ s' ∂μ else 0 with hXn
  set Yn : ℕ → ℝ := fun i => if hi : i < T then ∫ h, γ (h ⟨i, hi⟩).1 ∂μ else 0 with hYn
  have hRHS : (∫ h, ∑ τ ∈ filt, ((optGain (M τ) As + 2 * Δ) -
        ((∑ s' : Fin S, ((M τ).P (h τ).1 (h τ).2 s' : ℝ) * γ s') - γ (h τ).1)) ∂μ) =
      ∑ i ∈ Finset.Ico t (t + W), (optGain (M i) As + 2 * Δ) -
        ∑ i ∈ Finset.Ico t (t + W), (Xn i - Yn i) := by
    rw [integral_finsetSum _ (fun _ _ => Integrable.of_finite)]
    rw [← eq23_filter_sum t W hEnd, ← eq23_filter_sum t W hEnd, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl; intro τ _
    rw [integral_sub Integrable.of_finite Integrable.of_finite, integral_const,
      integral_sub Integrable.of_finite Integrable.of_finite]
    simp only [hXn, hYn, dif_pos τ.isLt, probReal_univ, one_smul]
  have htel : ∑ i ∈ Finset.Ico t (t + W), (Xn i - Yn i) = Xn (t + W - 1) - Yn t := by
    apply eq23_telescope Xn Yn t W hW
    intro i _ hi
    have hi1 : i + 1 < T := by omega
    simp only [hXn, hYn, dif_pos hi1, dif_pos (show i < T by omega)]
    exact (eq23_next_state M s₁ π T i hi1 γ).symm
  have hX0 : 0 ≤ Xn (t + W - 1) := by
    simp only [hXn, dif_pos (show t + W - 1 < T by omega)]
    apply integral_nonneg; intro h
    apply Finset.sum_nonneg; intro s' _
    exact mul_nonneg (NNReal.coe_nonneg _) (hγb s').1
  have hY : Yn t ≤ 2 * Dmax := by
    simp only [hYn, dif_pos (show t < T by omega)]
    calc ∫ h, γ (h ⟨t, _⟩).1 ∂μ ≤ ∫ h, (2 * Dmax) ∂μ :=
          integral_mono Integrable.of_finite Integrable.of_finite (fun h => (hγb _).2)
      _ = 2 * Dmax := by simp
  have hsumc : ∑ i ∈ Finset.Ico t (t + W), (optGain (M i) As + 2 * Δ) =
      ∑ i ∈ Finset.Ico t (t + W), optGain (M i) As + 2 * (W : ℝ) * Δ := by
    rw [Finset.sum_add_distrib, Finset.sum_const, Nat.card_Ico]
    simp; ring
  have hfinal := hmono
  rw [hRHS, htel, hsumc] at hfinal
  linarith
