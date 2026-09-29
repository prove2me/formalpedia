-- Prove2me | solution 1 for GoldbergTarjan.Generic.run_label_monotone
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-09-28T05:40:07.823675+00:00
-- url     : https://prove2.me/submissions/3becfe4c-6872-42f2-9244-ba021cf900fa

import Mathlib
import Definitions.Def_GoldbergTarjan_Generic_Run

open GoldbergTarjan.Generic

variable {V : Type} [Fintype V] [DecidableEq V]

/-- In `ℕ∞`, `a < b + 1` implies `a ≤ b`. -/
private theorem enat_le_of_lt_succ {a b : ℕ∞} (h : a < b + 1) : a ≤ b := by
  rcases eq_or_ne b ⊤ with hb | hb
  · rw [hb]; exact le_top
  · exact (ENat.lt_add_one_iff hb).mp h

/-- In `ℕ∞`, a finite value is strictly below its successor. -/
private theorem enat_lt_succ {a : ℕ∞} (ha : a ≠ ⊤) : a < a + 1 :=
  (ENat.add_one_le_iff ha).mp (le_refl _)

/-- No self-loops in the residual graph. -/
private theorem residual_self (N : Network V) (f : V → V → ℝ) (hf : IsPreflow N f) (v : V) :
    residualCap N f v v = 0 := by
  have h1 : f v v = -f v v := hf.2.1 v v
  have h2 : f v v = 0 := by linarith
  rw [residualCap, N.cap_self, h2, sub_zero]

/-- Lemma 2.1: some basic operation applies to an active vertex. -/
private theorem push_or_relabel (N : Network V) (f : V → V → ℝ) (d : V → ℕ∞) (v : V)
    (hf : IsPreflow N f) (hd : IsValidLabeling N f d) (hv : IsActive N f d v) :
    (∃ w, PushApplicable N f d v w) ∨ RelabelApplicable N f d v := by
  by_cases hex : ∃ w, 0 < residualCap N f v w ∧ d v = d w + 1
  · obtain ⟨w, hw1, hw2⟩ := hex
    exact Or.inl ⟨w, hv, hw1, hw2⟩
  · refine Or.inr ⟨hv, fun w hw => ?_⟩
    have h1 : d v ≤ d w + 1 := hd.2.2 v w hw
    have h2 : d v ≠ d w + 1 := fun hc => hex ⟨w, hw, hc⟩
    exact enat_le_of_lt_succ (lt_of_le_of_ne h1 h2)

/-- The initial preflow of Fig. 2 is a preflow. -/
private theorem init_preflow (N : Network V) : IsPreflow N (initialFlow N) := by
  refine ⟨?_, ?_, ?_⟩
  · intro v w
    simp only [initialFlow]
    by_cases hv : v = N.s
    · rw [if_pos hv, hv]
    · rw [if_neg hv]
      by_cases hw : w = N.s
      · rw [if_pos hw, hw]
        have h1 := N.cap_nonneg N.s v
        have h2 := N.cap_nonneg v N.s
        linarith
      · rw [if_neg hw]
        exact N.cap_nonneg v w
  · intro v w
    simp only [initialFlow]
    by_cases hv : v = N.s <;> by_cases hw : w = N.s <;> simp [hv, hw, N.cap_self]
  · intro v hv
    have hsum : excess (initialFlow N) v = N.c N.s v := by
      unfold excess
      rw [Finset.sum_eq_single N.s]
      · simp [initialFlow]
      · intro u _ hu
        simp [initialFlow, hu, hv]
      · intro h; exact absurd (Finset.mem_univ N.s) h
    rw [hsum]
    exact N.cap_nonneg _ _

/-- The simple initial labelling is valid for the initial preflow. -/
private theorem init_valid (N : Network V) :
    IsValidLabeling N (initialFlow N) (initialLabel N) := by
  refine ⟨by simp [initialLabel], ?_, ?_⟩
  · simp [initialLabel, N.source_ne_sink.symm]
  · intro v w he
    by_cases hv : v = N.s
    · exfalso
      have h0 : residualCap N (initialFlow N) v w = 0 := by
        simp [residualCap, initialFlow, hv]
      rw [IsResidualEdge, h0] at he
      exact lt_irrefl 0 he
    · simp only [initialLabel, if_neg hv]
      exact zero_le

/-- The pushed amount is nonnegative and bounded by the excess and the residual capacity. -/
private theorem push_amount_bounds (N : Network V) (f : V → V → ℝ) (d : V → ℕ∞) (v w : V)
    (happ : PushApplicable N f d v w) :
    0 ≤ pushAmount N f v w ∧ pushAmount N f v w ≤ excess f v ∧
      pushAmount N f v w ≤ residualCap N f v w := by
  refine ⟨?_, min_le_left _ _, min_le_right _ _⟩
  exact le_min happ.1.2.2.2.le happ.2.1.le

private theorem push_ne (N : Network V) (f : V → V → ℝ) (d : V → ℕ∞) (v w : V)
    (hf : IsPreflow N f) (happ : PushApplicable N f d v w) : v ≠ w := by
  intro h
  have h0 := happ.2.1
  rw [h, residual_self N f hf w] at h0
  exact lt_irrefl 0 h0

private theorem pushFlow_vw (N : Network V) (f : V → V → ℝ) (v w : V) :
    pushFlow N f v w v w = f v w + pushAmount N f v w := by
  simp [pushFlow]

private theorem pushFlow_wv (N : Network V) (f : V → V → ℝ) (v w : V) (hvw : v ≠ w) :
    pushFlow N f v w w v = f w v - pushAmount N f v w := by
  have h1 : ¬(w = v ∧ v = w) := fun hc => hvw hc.2
  simp [pushFlow, h1]

private theorem pushFlow_other (N : Network V) (f : V → V → ℝ) (v w x y : V)
    (h1 : ¬(x = v ∧ y = w)) (h2 : ¬(x = w ∧ y = v)) :
    pushFlow N f v w x y = f x y := by
  simp only [pushFlow, if_neg h1, if_neg h2]

private theorem excess_push_w (N : Network V) (f : V → V → ℝ) (v w : V) (hvw : v ≠ w) :
    excess (pushFlow N f v w) w = excess f w + pushAmount N f v w := by
  have h : excess (pushFlow N f v w) w - excess f w
      = ∑ x : V, (pushFlow N f v w x w - f x w) := by
    unfold excess; rw [← Finset.sum_sub_distrib]
  have hs : ∑ x : V, (pushFlow N f v w x w - f x w) = pushAmount N f v w := by
    rw [Finset.sum_eq_single v]
    · rw [pushFlow_vw]; ring
    · intro x _ hx
      rw [pushFlow_other N f v w x w (fun hc => hx hc.1) (fun hc => hvw hc.2.symm)]
      ring
    · intro hcon; exact absurd (Finset.mem_univ v) hcon
  rw [hs] at h; linarith

private theorem excess_push_v (N : Network V) (f : V → V → ℝ) (v w : V) (hvw : v ≠ w) :
    excess (pushFlow N f v w) v = excess f v - pushAmount N f v w := by
  have h : excess (pushFlow N f v w) v - excess f v
      = ∑ x : V, (pushFlow N f v w x v - f x v) := by
    unfold excess; rw [← Finset.sum_sub_distrib]
  have hs : ∑ x : V, (pushFlow N f v w x v - f x v) = -pushAmount N f v w := by
    rw [Finset.sum_eq_single w]
    · rw [pushFlow_wv N f v w hvw]; ring
    · intro x _ hx
      rw [pushFlow_other N f v w x v (fun hc => hvw hc.2) (fun hc => hx hc.1)]
      ring
    · intro hcon; exact absurd (Finset.mem_univ w) hcon
  rw [hs] at h; linarith

private theorem excess_push_other (N : Network V) (f : V → V → ℝ) (v w u : V)
    (huv : u ≠ v) (huw : u ≠ w) :
    excess (pushFlow N f v w) u = excess f u := by
  unfold excess
  refine Finset.sum_congr rfl fun x _ => ?_
  exact pushFlow_other N f v w x u (fun hc => huw hc.2) (fun hc => huv hc.2)

private theorem push_preflow (N : Network V) (f : V → V → ℝ) (d : V → ℕ∞) (v w : V)
    (hf : IsPreflow N f) (happ : PushApplicable N f d v w) :
    IsPreflow N (pushFlow N f v w) := by
  obtain ⟨hδ0, hδe, hδr⟩ := push_amount_bounds N f d v w happ
  have hvw : v ≠ w := push_ne N f d v w hf happ
  refine ⟨?_, ?_, ?_⟩
  · intro x y
    by_cases h1 : x = v ∧ y = w
    · obtain ⟨hx, hy⟩ := h1
      rw [hx, hy, pushFlow_vw]
      rw [residualCap] at hδr
      linarith
    · by_cases h2 : x = w ∧ y = v
      · obtain ⟨hx, hy⟩ := h2
        rw [hx, hy, pushFlow_wv N f v w hvw]
        have := hf.1 w v
        linarith
      · rw [pushFlow_other N f v w x y h1 h2]
        exact hf.1 x y
  · intro x y
    by_cases h1 : x = v ∧ y = w
    · obtain ⟨hx, hy⟩ := h1
      rw [hx, hy, pushFlow_vw, pushFlow_wv N f v w hvw]
      have := hf.2.1 v w
      linarith
    · by_cases h2 : x = w ∧ y = v
      · obtain ⟨hx, hy⟩ := h2
        rw [hx, hy, pushFlow_wv N f v w hvw, pushFlow_vw]
        have := hf.2.1 w v
        linarith
      · have h3 : ¬(y = v ∧ x = w) := fun hc => h2 ⟨hc.2, hc.1⟩
        have h4 : ¬(y = w ∧ x = v) := fun hc => h1 ⟨hc.2, hc.1⟩
        rw [pushFlow_other N f v w x y h1 h2, pushFlow_other N f v w y x h3 h4]
        exact hf.2.1 x y
  · intro u hu
    by_cases huw : u = w
    · rw [huw, excess_push_w N f v w hvw]
      have := hf.2.2 w (by rw [← huw]; exact hu)
      linarith
    · by_cases huv : u = v
      · rw [huv, excess_push_v N f v w hvw]
        have hex : 0 < excess f v := happ.1.2.2.2
        linarith
      · rw [excess_push_other N f v w u huv huw]
        exact hf.2.2 u hu

private theorem push_valid (N : Network V) (f : V → V → ℝ) (d : V → ℕ∞) (v w : V)
    (hf : IsPreflow N f) (hd : IsValidLabeling N f d) (happ : PushApplicable N f d v w) :
    IsValidLabeling N (pushFlow N f v w) d := by
  obtain ⟨hδ0, hδe, hδr⟩ := push_amount_bounds N f d v w happ
  have hvw : v ≠ w := push_ne N f d v w hf happ
  refine ⟨hd.1, hd.2.1, ?_⟩
  intro x y he
  by_cases h2 : x = w ∧ y = v
  · obtain ⟨hx, hy⟩ := h2
    rw [hx, hy]
    calc d w ≤ d w + 1 := le_self_add
      _ = d v := happ.2.2.symm
      _ ≤ d v + 1 := le_self_add
  · have hmono : residualCap N (pushFlow N f v w) x y ≤ residualCap N f x y := by
      by_cases h1 : x = v ∧ y = w
      · obtain ⟨hx, hy⟩ := h1
        rw [hx, hy, residualCap, residualCap, pushFlow_vw]
        linarith
      · rw [residualCap, residualCap, pushFlow_other N f v w x y h1 h2]
    exact hd.2.2 x y (lt_of_lt_of_le he hmono)

/-- The relabelled value strictly exceeds the old label. -/
private theorem relabel_ge (N : Network V) (f : V → V → ℝ) (d : V → ℕ∞) (v : V)
    (happ : RelabelApplicable N f d v) : d v + 1 ≤ relabelValue N f d v := by
  unfold relabelValue
  refine le_iInf fun w => le_iInf fun hw => ?_
  exact add_le_add (happ.2 w hw) (le_refl 1)

private theorem relabel_valid (N : Network V) (f : V → V → ℝ) (d : V → ℕ∞) (v : V)
    (hf : IsPreflow N f) (hd : IsValidLabeling N f d) (happ : RelabelApplicable N f d v) :
    IsValidLabeling N f (Function.update d v (relabelValue N f d v)) := by
  have hge : d v ≤ relabelValue N f d v :=
    le_trans le_self_add (relabel_ge N f d v happ)
  have hvs : v ≠ N.s := happ.1.1
  have hvt : v ≠ N.t := happ.1.2.1
  refine ⟨?_, ?_, ?_⟩
  · rw [Function.update_of_ne (Ne.symm hvs)]; exact hd.1
  · rw [Function.update_of_ne (Ne.symm hvt)]; exact hd.2.1
  · intro x y he
    by_cases hx : x = v
    · have hyx : y ≠ v := by
        intro h
        rw [hx, h, IsResidualEdge, residual_self N f hf v] at he
        exact lt_irrefl 0 he
      rw [hx, Function.update_of_ne hyx, Function.update_self]
      have : relabelValue N f d v ≤ d y + 1 := by
        unfold relabelValue
        refine iInf_le_of_le y ?_
        exact iInf_le (fun _ => d y + 1) (by rw [← hx]; exact he)
      exact this
    · rw [Function.update_of_ne hx]
      by_cases hy : y = v
      · rw [hy, Function.update_self]
        exact le_trans (hd.2.2 x y he) (add_le_add (by rw [hy] at *; exact hge) (le_refl 1))
      · rw [Function.update_of_ne hy]
        exact hd.2.2 x y he

/-- Invariant of a run: the state is always a preflow with a valid labelling. -/
private theorem run_inv (N : Network V) (σ : ℕ → State V) (K : ℕ) (hrun : IsRun N σ K) :
    ∀ k ≤ K, IsPreflow N (σ k).1 ∧ IsValidLabeling N (σ k).1 (σ k).2 := by
  intro k
  induction k with
  | zero =>
    intro _
    rw [hrun.1]
    exact ⟨init_preflow N, init_valid N⟩
  | succ m ih =>
    intro hm
    obtain ⟨hp, hv⟩ := ih (by omega)
    rcases hrun.2 m (by omega) with ⟨a, b, happ, hf1, hf2⟩ | ⟨a, happ, hf1, hf2⟩
    · rw [hf1, hf2]
      exact ⟨push_preflow N _ _ a b hp happ, push_valid N _ _ a b hp hv happ⟩
    · rw [hf1, hf2]
      exact ⟨hp, relabel_valid N _ _ a hp hv happ⟩

/-- One step never decreases a label. -/
private theorem step_label_le (N : Network V) (p q : State V) (hstep : BasicStep N p q) (v : V) :
    p.2 v ≤ q.2 v := by
  rcases hstep with ⟨a, b, _, _, hf2⟩ | ⟨a, happ, _, hf2⟩
  · rw [hf2]
  · rw [hf2]
    by_cases hv : v = a
    · rw [hv, Function.update_self]
      exact le_trans le_self_add (relabel_ge N p.1 p.2 a happ)
    · rw [Function.update_of_ne hv]

theorem solution {V : Type} [Fintype V] [DecidableEq V]
    (N : Network V) (σ : ℕ → State V) (K : ℕ) (hrun : IsRun N σ K) :
    (∀ (v : V) (k l : ℕ), k ≤ l → l ≤ K → (σ k).2 v ≤ (σ l).2 v) ∧
      (∀ (v : V) (k : ℕ), k < K → RelabelStep N (σ k) (σ (k + 1)) v →
        (σ k).2 v < (σ (k + 1)).2 v) := by
  refine ⟨?_, ?_⟩
  · intro v k l hkl hlK
    -- chain the one-step bound along `k, k+1, …, l`
    obtain ⟨j, hj⟩ : ∃ j, l = k + j := ⟨l - k, by omega⟩
    subst hj
    induction j with
    | zero => exact le_refl _
    | succ m ih =>
      have hm : k + m ≤ K := by omega
      refine le_trans (ih (by omega) (by omega)) ?_
      have hstep := hrun.2 (k + m) (by omega)
      have hstep2 := step_label_le N (σ (k + m)) (σ (k + m + 1)) hstep v
      have heq : k + (m + 1) = k + m + 1 := by omega
      rw [heq]
      exact hstep2
  · intro v k hk hrel
    have hact := hrel.1.1
    have hne : (σ k).2 v ≠ ⊤ := ne_of_lt hact.2.2.1
    have hlt : (σ k).2 v < (σ k).2 v + 1 := enat_lt_succ hne
    have hge : (σ k).2 v + 1 ≤ relabelValue N (σ k).1 (σ k).2 v :=
      relabel_ge N (σ k).1 (σ k).2 v hrel.1
    rw [hrel.2.2, Function.update_self]
    exact lt_of_lt_of_le hlt hge
