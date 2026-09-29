-- Prove2me | solution 1 for GoldbergTarjan.Generic.terminated_run_is_max_flow
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-09-28T05:49:41.619981+00:00
-- url     : https://prove2.me/submissions/4ba2f1a5-c725-4dc2-9da8-df9c49306c87

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
/-- `Rch N f k u`: `u` is reachable from the source by at most `k` residual edges. -/
private def Rch (N : Network V) (f : V → V → ℝ) : ℕ → V → Prop
  | 0 => fun u => u = N.s
  | (k + 1) => fun u => Rch N f k u ∨ ∃ v, Rch N f k v ∧ IsResidualEdge N f v u

/-- `Lv j u`: the shortest residual path from the source to `u` has exactly `j` edges. -/
private def Lv (N : Network V) (f : V → V → ℝ) (j : ℕ) (u : V) : Prop :=
  Rch N f j u ∧ ∀ i < j, ¬ Rch N f i u

private theorem rch_mono (N : Network V) (f : V → V → ℝ) :
    ∀ k u, Rch N f k u → Rch N f (k + 1) u := fun _ _ h => Or.inl h

private theorem rch_le (N : Network V) (f : V → V → ℝ) :
    ∀ i k u, i ≤ k → Rch N f i u → Rch N f k u := by
  intro i k u hik h
  induction k with
  | zero =>
    have hi : i = 0 := by omega
    subst hi
    exact h
  | succ m ih =>
    rcases Nat.lt_or_ge i (m + 1) with hlt | hge
    · exact rch_mono N f m u (ih (by omega))
    · have : i = m + 1 := by omega
      subst this
      exact h

private theorem rch_exists_lv (N : Network V) (f : V → V → ℝ) :
    ∀ k u, Rch N f k u → ∃ j, j ≤ k ∧ Lv N f j u := by
  classical
  intro k u hk
  have hex : ∃ j, Rch N f j u := ⟨k, hk⟩
  refine ⟨Nat.find hex, ?_, Nat.find_spec hex, ?_⟩
  · exact Nat.find_le hk
  · intro i hi
    exact Nat.find_min hex hi

private theorem lv_pred (N : Network V) (f : V → V → ℝ) :
    ∀ j u, Lv N f (j + 1) u → ∃ v, Lv N f j v ∧ IsResidualEdge N f v u := by
  intro j u hu
  obtain ⟨hr, hmin⟩ := hu
  rcases hr with hr | ⟨v, hv, he⟩
  · exact absurd hr (hmin j (by omega))
  · obtain ⟨i, hij, hlv⟩ := rch_exists_lv N f j v hv
    refine ⟨v, ?_, he⟩
    have hij' : i = j := by
      by_contra hne
      have hlt : i < j := by omega
      have : Rch N f (i + 1) u := Or.inr ⟨v, hlv.1, he⟩
      exact hmin (i + 1) (by omega) this
    exact hij' ▸ hlv

private theorem lv_down (N : Network V) (f : V → V → ℝ) (k₀ : ℕ) (t : V)
    (ht : Lv N f k₀ t) : ∀ i, i ≤ k₀ → ∃ u, Lv N f (k₀ - i) u := by
  intro i
  induction i with
  | zero => intro _; exact ⟨t, by simpa using ht⟩
  | succ m ih =>
    intro hm
    obtain ⟨u, hu⟩ := ih (by omega)
    have heq : k₀ - m = (k₀ - (m + 1)) + 1 := by omega
    rw [heq] at hu
    obtain ⟨v, hv, -⟩ := lv_pred N f (k₀ - (m + 1)) u hu
    exact ⟨v, hv⟩

private theorem lv_unique (N : Network V) (f : V → V → ℝ) :
    ∀ j j' u, Lv N f j u → Lv N f j' u → j = j' := by
  intro j j' u h h'
  by_contra hne
  rcases Nat.lt_or_ge j j' with hlt | hge
  · exact h'.2 j hlt h.1
  · have : j' < j := by omega
    exact h.2 j' this h'.1

private theorem rch_label (N : Network V) (f : V → V → ℝ) (d : V → ℕ∞)
    (hd : IsValidLabeling N f d) :
    ∀ k u, Rch N f k u → d N.s ≤ d u + (k : ℕ∞) := by
  intro k
  induction k with
  | zero =>
    intro u hu
    simp only [Rch] at hu
    subst hu
    simp
  | succ m ih =>
    intro u hu
    rcases hu with hu | ⟨v, hv, he⟩
    · refine le_trans (ih u hu) ?_
      have hstep : ((m : ℕ∞)) ≤ ((m + 1 : ℕ) : ℕ∞) := by
        exact_mod_cast Nat.le_succ m
      exact add_le_add (le_refl (d u)) hstep
    · have h1 := ih v hv
      have h2 : d v ≤ d u + 1 := hd.2.2 v u he
      have : d N.s ≤ (d u + 1) + (m : ℕ∞) :=
        le_trans h1 (add_le_add h2 (le_refl ((m : ℕ∞))))
      refine le_trans this ?_
      have hc : ((m + 1 : ℕ) : ℕ∞) = (m : ℕ∞) + 1 := by push_cast; ring
      rw [hc]
      rw [add_assoc, add_comm (1 : ℕ∞) (m : ℕ∞)]

/-- A valid labelling forbids a residual path from the source to the sink. -/
private theorem no_st_path (N : Network V) (f : V → V → ℝ) (d : V → ℕ∞)
    (hf : IsPreflow N f) (hd : IsValidLabeling N f d) :
    ¬ ResidualReachable N f N.s N.t := by
  classical
  intro hreach
  -- the sink is reachable in finitely many steps
  have key : ∀ w, ResidualReachable N f N.s w → ∃ k, Rch N f k w := by
    intro w hw
    induction hw with
    | refl => exact ⟨0, rfl⟩
    | tail hab hbc ih =>
      obtain ⟨k, hk⟩ := ih
      exact ⟨k + 1, Or.inr ⟨_, hk, hbc⟩⟩
  obtain ⟨k, hk⟩ := key N.t hreach
  obtain ⟨k₀, -, hlv⟩ := rch_exists_lv N f k N.t hk
  -- every level `0, …, k₀` is realised by some vertex, and levels are unique
  have hchoice : ∀ j : Fin (k₀ + 1), ∃ u, Lv N f (j : ℕ) u := by
    intro j
    have hj : k₀ - (k₀ - (j : ℕ)) = (j : ℕ) := by omega
    obtain ⟨u, hu⟩ := lv_down N f k₀ N.t hlv (k₀ - (j : ℕ)) (by omega)
    exact ⟨u, by rwa [hj] at hu⟩
  choose F hF using hchoice
  have hinj : Function.Injective F := by
    intro a b hab
    have h1 := hF a
    have h2 := hF b
    rw [hab] at h1
    have := lv_unique N f (a : ℕ) (b : ℕ) (F b) h1 h2
    exact Fin.ext this
  have hcard : k₀ + 1 ≤ Fintype.card V := by
    have := Fintype.card_le_of_injective F hinj
    simpa using this
  -- but the labelling forces `k₀ ≥ card V`
  have hlab := rch_label N f d hd k₀ N.t hlv.1
  rw [hd.1, hd.2.1, zero_add] at hlab
  have : (Fintype.card V : ℕ) ≤ k₀ := by exact_mod_cast hlab
  omega

/-- A doubly-indexed antisymmetric sum over a square index set vanishes. -/
private theorem sum_self_anti (g : V → V → ℝ) (hanti : ∀ x y, g x y = -g y x) (T : Finset V) :
    ∑ u ∈ T, ∑ x ∈ T, g x u = 0 := by
  have key : ∑ u ∈ T, ∑ x ∈ T, g x u = -∑ u ∈ T, ∑ x ∈ T, g x u := by
    calc ∑ u ∈ T, ∑ x ∈ T, g x u = ∑ u ∈ T, ∑ x ∈ T, (-g u x) := by
          exact Finset.sum_congr rfl fun u _ => Finset.sum_congr rfl fun x _ => hanti x u
      _ = -∑ u ∈ T, ∑ x ∈ T, g u x := by
          rw [← Finset.sum_neg_distrib]
          refine Finset.sum_congr rfl fun u _ => ?_
          rw [← Finset.sum_neg_distrib]
      _ = -∑ u ∈ T, ∑ x ∈ T, g x u := by rw [Finset.sum_comm]
  linarith

/-- Max-flow/min-cut, easy direction: a flow with no residual `s`–`t` path is maximum. -/
private theorem maxflow_of_no_path (N : Network V) (f : V → V → ℝ) (hf : IsFlow N f)
    (hno : ¬ ResidualReachable N f N.s N.t) : IsMaxFlow N f := by
  classical
  set S : Finset V := Finset.univ.filter (fun u => ResidualReachable N f N.s u) with hSdef
  have hmemS : ∀ u, u ∈ S ↔ ResidualReachable N f N.s u := by intro u; simp [hSdef]
  have hsS : N.s ∈ S := (hmemS _).mpr Relation.ReflTransGen.refl
  have htS : N.t ∉ S := fun h => hno ((hmemS _).mp h)
  have hsat : ∀ x ∈ S, ∀ u ∈ Sᶜ, f x u = N.c x u := by
    intro x hx u hu
    have hxr := (hmemS x).mp hx
    have hnotedge : ¬ (0 < residualCap N f x u) := by
      intro he
      exact (Finset.mem_compl.mp hu) ((hmemS u).mpr (hxr.tail he))
    have h1 : N.c x u - f x u ≤ 0 := by
      have := not_lt.mp hnotedge
      rwa [residualCap] at this
    have h2 : f x u ≤ N.c x u := hf.1 x u
    linarith
  have hsplit : ∀ g : V → V → ℝ, ∑ u ∈ Sᶜ, excess g u
      = ∑ u ∈ Sᶜ, ∑ x ∈ S, g x u + ∑ u ∈ Sᶜ, ∑ x ∈ Sᶜ, g x u := by
    intro g
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun u _ => ?_
    rw [excess, ← Finset.sum_add_sum_compl S (fun x => g x u)]
  have hexc : ∀ g : V → V → ℝ, IsFlow N g → ∑ u ∈ Sᶜ, excess g u = value N g := by
    intro g hg
    rw [Finset.sum_eq_single N.t]
    · rw [value, excess]
    · intro u hu hut
      refine hg.2.2 u ?_ hut
      intro h
      exact (Finset.mem_compl.mp hu) (h ▸ hsS)
    · intro h; exact absurd (Finset.mem_compl.mpr htS) h
  have hcut : ∀ g : V → V → ℝ, IsFlow N g → value N g = ∑ u ∈ Sᶜ, ∑ x ∈ S, g x u := by
    intro g hg
    have h1 := hexc g hg
    have h2 := hsplit g
    have h3 : ∑ u ∈ Sᶜ, ∑ x ∈ Sᶜ, g x u = 0 := sum_self_anti g hg.2.1 Sᶜ
    rw [h3, add_zero] at h2
    rw [← h1, h2]
  refine ⟨hf, fun g hg => ?_⟩
  rw [hcut g hg, hcut f hf]
  refine Finset.sum_le_sum fun u hu => Finset.sum_le_sum fun x hx => ?_
  rw [hsat x hx u hu]
  exact hg.1 x u

theorem solution {V : Type} [Fintype V] [DecidableEq V]
    (N : Network V) (σ : ℕ → State V) (K : ℕ) (hrun : IsRun N σ K)
    (hterm : NoBasicOpApplicable N (σ K)) (hfin : ∀ v : V, (σ K).2 v < ⊤) :
    IsMaxFlow N (σ K).1 := by
  obtain ⟨hp, hd⟩ := run_inv N σ K hrun K (le_refl K)
  -- no vertex is active at termination
  have hnoact : ∀ v : V, ¬ IsActive N (σ K).1 (σ K).2 v := by
    intro v hv
    rcases push_or_relabel N (σ K).1 (σ K).2 v hp hd hv with ⟨w, hw⟩ | hr
    · exact hterm.1 v w hw
    · exact hterm.2 v hr
  -- hence the preflow is a flow
  have hflow : IsFlow N (σ K).1 := by
    refine ⟨hp.1, hp.2.1, ?_⟩
    intro v hvs hvt
    have hle : ¬ (0 < excess (σ K).1 v) := by
      intro hpos
      exact hnoact v ⟨hvs, hvt, hfin v, hpos⟩
    have h1 : excess (σ K).1 v ≤ 0 := not_lt.mp hle
    have h2 : 0 ≤ excess (σ K).1 v := hp.2.2 v hvs
    linarith
  exact maxflow_of_no_path N (σ K).1 hflow (no_st_path N (σ K).1 (σ K).2 hp hd)
