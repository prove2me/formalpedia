-- Prove2me | solution 1 for NetworkControl.CapacityRegion.lemma_necessary_condition_strong_stability_v2
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-22T02:16:22.256963+00:00
-- url     : https://prove2.me/submissions/1c9c109c-321f-4c10-a965-0fcb459fde30

import Mathlib
import Definitions.Def_NetworkControl_CapacityRegion_QueueBacklog
import Definitions.Def_NetworkControl_CapacityRegion_StronglyStable



namespace NetworkControl.CapacityRegion

open MeasureTheory

lemma h26_sum_lower (u : ℕ → ℝ) (hu : ∀ t, 0 ≤ u t) (a k : ℕ) (L : ℝ)
    (hL : ∀ τ ∈ Finset.Ico a (a + k), L ≤ u τ) :
    (k : ℝ) * L ≤ ∑ τ ∈ Finset.range (a + k), u τ := by
  have h1 : ∑ τ ∈ Finset.Ico a (a + k), L ≤ ∑ τ ∈ Finset.Ico a (a + k), u τ :=
    Finset.sum_le_sum hL
  have h2 : ∑ τ ∈ Finset.Ico a (a + k), u τ ≤ ∑ τ ∈ Finset.range (a + k), u τ := by
    apply Finset.sum_le_sum_of_subset_of_nonneg
    · intro x hx
      simp only [Finset.mem_Ico, Finset.mem_range] at hx ⊢
      omega
    · intro i _ _; exact hu i
  have h3 : ∑ τ ∈ Finset.Ico a (a + k), L = (k : ℝ) * L := by
    simp
  linarith

lemma h26_key (u : ℕ → ℝ) (hu : ∀ t, 0 ≤ u t) (M c : ℝ) (hc : 0 < c)
    (hM : ∀ t : ℕ, 1 / (t : ℝ) * ∑ τ ∈ Finset.range t, u τ ≤ M)
    (h : (∀ t, u (t + 1) ≤ u t + c) ∨ (∀ t, u t ≤ u (t + 1) + c)) :
    Filter.Tendsto (fun t : ℕ => u t / (t : ℝ)) Filter.atTop (nhds 0) := by
  have hM0 : 0 ≤ M := by
    have := hM 1
    simp at this
    linarith [hu 0]
  have hS : ∀ t : ℕ, 1 ≤ t → ∑ τ ∈ Finset.range t, u τ ≤ M * t := by
    intro t ht
    have := hM t
    have htpos : (0 : ℝ) < t := by exact_mod_cast ht
    rw [one_div, inv_mul_le_iff₀ htpos] at this
    linarith
  have claim : ∀ ε : ℝ, 0 < ε → ε ≤ c → ∀ t : ℕ, 1 ≤ t → ε * t ≤ u t →
      ε * t / (2 * c) < 4 * M / ε + 1 := by
    intro ε hε hεc t ht hut
    have htpos : (0 : ℝ) < t := by exact_mod_cast ht
    set k : ℕ := ⌊ε * t / (2 * c)⌋₊ with hkdef
    have hk1 : (k : ℝ) ≤ ε * t / (2 * c) := Nat.floor_le (by positivity)
    have hk2 : ε * t / (2 * c) < k + 1 := Nat.lt_floor_add_one _
    have hk3 : (k : ℝ) * (2 * c) ≤ ε * t := by
      rwa [le_div_iff₀ (by positivity)] at hk1
    have hk4 : (k : ℝ) ≤ t / 2 := by
      have : ε * t / (2 * c) ≤ t / 2 := by
        rw [div_le_div_iff₀ (by positivity) (by positivity)]
        nlinarith
      linarith
    have hkt : k ≤ t := by
      have : (k : ℝ) ≤ t := by linarith
      exact_mod_cast this
    suffices hk : (k : ℝ) * ε ≤ 4 * M by
      have : (k : ℝ) ≤ 4 * M / ε := by rw [le_div_iff₀ hε]; exact hk
      linarith
    rcases h with h | h
    · -- upward steps bounded: look backwards
      have hstep : ∀ τ s : ℕ, u (τ + s) ≤ u τ + s * c := by
        intro τ s
        induction s with
        | zero => simp
        | succ s ih =>
          have := h (τ + s)
          rw [← add_assoc]
          push_cast
          linarith
      have hlow := h26_sum_lower u hu (t - k) k (ε * t / 2) (by
        intro τ hτ
        simp only [Finset.mem_Ico] at hτ
        have := hstep τ (t - τ)
        have hτt : τ + (t - τ) = t := by omega
        rw [hτt] at this
        have hsk : ((t - τ : ℕ) : ℝ) ≤ k := by
          have : t - τ ≤ k := by omega
          exact_mod_cast this
        nlinarith)
      have hsum := hS (t - k + k) (by omega)
      have e : t - k + k = t := by omega
      rw [e] at hlow hsum
      have : (k : ℝ) * (ε * t / 2) ≤ M * t := le_trans hlow hsum
      nlinarith
    · have hstep : ∀ τ s : ℕ, u τ ≤ u (τ + s) + s * c := by
        intro τ s
        induction s with
        | zero => simp
        | succ s ih =>
          have := h (τ + s)
          rw [← add_assoc]
          push_cast
          linarith
      have hlow := h26_sum_lower u hu t k (ε * t / 2) (by
        intro τ hτ
        simp only [Finset.mem_Ico] at hτ
        obtain ⟨s, rfl⟩ : ∃ s, τ = t + s := ⟨τ - t, by omega⟩
        have := hstep t s
        have hsk : (s : ℝ) ≤ k := by
          have : s ≤ k := by omega
          exact_mod_cast this
        nlinarith)
      have hsum := hS (t + k) (by omega)
      have hk5 : ((t + k : ℕ) : ℝ) ≤ 2 * t := by
        push_cast; linarith
      have : (k : ℝ) * (ε * t / 2) ≤ M * (2 * t) := by
        calc _ ≤ _ := hlow
          _ ≤ M * ((t + k : ℕ) : ℝ) := hsum
          _ ≤ M * (2 * t) := mul_le_mul_of_nonneg_left hk5 hM0
      nlinarith
  rw [Metric.tendsto_atTop]
  intro ε' hε'
  set ε := min ε' c with hεdef
  have hεpos : 0 < ε := lt_min hε' hc
  have hεc : ε ≤ c := min_le_right _ _
  have hεε' : ε ≤ ε' := min_le_left _ _
  -- choose N with ε * N / (2c) ≥ 4M/ε + 1
  obtain ⟨N, hN⟩ := exists_nat_ge ((4 * M / ε + 1) * (2 * c) / ε + 1)
  refine ⟨N + 1, fun t ht => ?_⟩
  have htpos : (0 : ℝ) < t := by
    have : (1 : ℝ) ≤ t := by exact_mod_cast (by omega : 1 ≤ t)
    linarith
  rw [Real.dist_eq, sub_zero, abs_of_nonneg (div_nonneg (hu t) htpos.le)]
  by_contra hcon
  push_neg at hcon
  have hut : ε * t ≤ u t := by
    have : ε' ≤ u t / t := hcon
    rw [le_div_iff₀ htpos] at this
    nlinarith
  have := claim ε hεpos hεc t (by omega) hut
  have htN : (N : ℝ) ≤ t := by exact_mod_cast (by omega : N ≤ t)
  have h2 : (4 * M / ε + 1) * (2 * c) / ε < t := by linarith
  rw [div_lt_iff₀ hεpos] at h2
  rw [div_lt_iff₀ (by positivity)] at this
  nlinarith

lemma h26_QB_nonneg {Ω : Type*} (A svc : ℕ → Ω → ℝ) (U0 : Ω → ℝ)
    (hAnn : ∀ t ω, 0 ≤ A t ω) (hU0nn : ∀ ω, 0 ≤ U0 ω) :
    ∀ t ω, 0 ≤ QueueBacklog A svc U0 t ω := by
  intro t
  induction t with
  | zero => intro ω; exact hU0nn ω
  | succ t ih =>
    intro ω
    simp only [QueueBacklog]
    exact add_nonneg (le_max_right _ _) (hAnn t ω)

lemma h26_QB_int {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    (A svc : ℕ → Ω → ℝ) (U0 : Ω → ℝ)
    (hU0int : Integrable U0 P) (hAint : ∀ t, Integrable (A t) P)
    (hsvcint : ∀ t, Integrable (svc t) P) :
    ∀ t, Integrable (QueueBacklog A svc U0 t) P := by
  intro t
  induction t with
  | zero => exact hU0int
  | succ t ih =>
    have h1 : Integrable (fun ω => max (QueueBacklog A svc U0 t ω - svc t ω) 0) P :=
      (ih.sub (hsvcint t)).pos_part
    exact h1.add (hAint t)

theorem necessary_core
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    (A svc : ℕ → Ω → ℝ) (U0 : Ω → ℝ)
    (hAnn : ∀ t ω, 0 ≤ A t ω) (hsvcnn : ∀ t ω, 0 ≤ svc t ω) (hU0nn : ∀ ω, 0 ≤ U0 ω)
    (hU0int : Integrable U0 P) (hAint : ∀ t, Integrable (A t) P)
    (hsvcint : ∀ t, Integrable (svc t) P)
    (Amax Dmax : ℝ) (hAmax : 0 ≤ Amax) (hDmax : 0 ≤ Dmax)
    (hstable : StronglyStable (fun t : ℕ => ∫ ω, QueueBacklog A svc U0 t ω ∂P))
    (hbound : (∀ t : ℕ, ∫ ω, A t ω ∂P ≤ Amax) ∨
      (∀ t : ℕ, ∫ ω, (svc t ω - A t ω) ∂P ≤ Dmax)) :
    Filter.Tendsto (fun t : ℕ => (∫ ω, QueueBacklog A svc U0 t ω ∂P) / (t : ℝ))
      Filter.atTop (nhds 0) := by
  have hnn := h26_QB_nonneg A svc U0 hAnn hU0nn
  have hint := h26_QB_int (P := P) A svc U0 hU0int hAint hsvcint
  obtain ⟨M, hM⟩ := hstable
  rcases hbound with hb | hb
  · refine h26_key (fun t : ℕ => ∫ ω, QueueBacklog A svc U0 t ω ∂P)
      (fun t => integral_nonneg (hnn t)) M (Amax + 1) (by linarith) hM (Or.inl ?_)
    intro t
    show ∫ ω, QueueBacklog A svc U0 (t+1) ω ∂P ≤ ∫ ω, QueueBacklog A svc U0 t ω ∂P + (Amax + 1)
    have e : ∫ ω, QueueBacklog A svc U0 (t+1) ω ∂P
        = ∫ ω, max (QueueBacklog A svc U0 t ω - svc t ω) 0 ∂P + ∫ ω, A t ω ∂P := by
      show ∫ ω, (max (QueueBacklog A svc U0 t ω - svc t ω) 0 + A t ω) ∂P = _
      exact integral_add ((hint t).sub (hsvcint t)).pos_part (hAint t)
    have hle : ∫ ω, max (QueueBacklog A svc U0 t ω - svc t ω) 0 ∂P
        ≤ ∫ ω, QueueBacklog A svc U0 t ω ∂P := by
      apply integral_mono ((hint t).sub (hsvcint t)).pos_part (hint t)
      intro ω
      have h1 := hnn t ω
      have h2 := hsvcnn t ω
      show max (QueueBacklog A svc U0 t ω - svc t ω) 0 ≤ QueueBacklog A svc U0 t ω
      exact max_le (by linarith) (by linarith)
    linarith [hb t]
  · refine h26_key (fun t : ℕ => ∫ ω, QueueBacklog A svc U0 t ω ∂P)
      (fun t => integral_nonneg (hnn t)) M (Dmax + 1) (by linarith) hM (Or.inr ?_)
    intro t
    show ∫ ω, QueueBacklog A svc U0 t ω ∂P ≤ ∫ ω, QueueBacklog A svc U0 (t+1) ω ∂P + (Dmax + 1)
    have hle : ∫ ω, (QueueBacklog A svc U0 t ω + (A t ω - svc t ω)) ∂P
        ≤ ∫ ω, QueueBacklog A svc U0 (t+1) ω ∂P := by
      apply integral_mono ((hint t).add ((hAint t).sub (hsvcint t))) (hint (t+1))
      intro ω
      show QueueBacklog A svc U0 t ω + (A t ω - svc t ω) ≤ max (QueueBacklog A svc U0 t ω - svc t ω) 0 + A t ω
      have := le_max_left (QueueBacklog A svc U0 t ω - svc t ω) 0
      linarith
    have e : ∫ ω, (QueueBacklog A svc U0 t ω + (A t ω - svc t ω)) ∂P
        = ∫ ω, QueueBacklog A svc U0 t ω ∂P - ∫ ω, (svc t ω - A t ω) ∂P := by
      have i1 := integral_add (hint t) ((hAint t).sub (hsvcint t))
      have i2 := integral_sub (hAint t) (hsvcint t)
      have i3 := integral_sub (hsvcint t) (hAint t)
      simp only [Pi.sub_apply] at i1 i2 i3
      rw [i1, i2, i3]
      ring
    linarith [hb t]

end NetworkControl.CapacityRegion

open NetworkControl.CapacityRegion
open NetworkControl.CapacityRegion MeasureTheory

theorem solution
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    (A svc : ℕ → Ω → ℝ) (U0 : Ω → ℝ)
    (hAnn : ∀ t ω, 0 ≤ A t ω) (hsvcnn : ∀ t ω, 0 ≤ svc t ω) (hU0nn : ∀ ω, 0 ≤ U0 ω)
    (hU0int : Integrable U0 P) (hAint : ∀ t, Integrable (A t) P)
    (hsvcint : ∀ t, Integrable (svc t) P)
    (Amax Dmax : ℝ) (hAmax : 0 ≤ Amax) (hDmax : 0 ≤ Dmax)
    (hstable : StronglyStable (fun t : ℕ => ∫ ω, QueueBacklog A svc U0 t ω ∂P))
    (hbound : (∀ t : ℕ, ∫ ω, A t ω ∂P ≤ Amax) ∨
      (∀ t : ℕ, ∫ ω, (svc t ω - A t ω) ∂P ≤ Dmax)) :
    Filter.Tendsto (fun t : ℕ => (∫ ω, QueueBacklog A svc U0 t ω ∂P) / (t : ℝ))
      Filter.atTop (nhds 0) := by
  exact necessary_core A svc U0 hAnn hsvcnn hU0nn hU0int hAint hsvcint Amax Dmax hAmax hDmax hstable hbound
