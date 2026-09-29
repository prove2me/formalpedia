-- Prove2me | solution 1 for GoldbergTarjan.Generic.run_label_le
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-09-28T06:18:39.905272+00:00
-- url     : https://prove2.me/submissions/7f136cb8-e93f-418f-804e-cea22fd48fa2

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

/-- `RchTo N f k u`: the source is reachable from `u` by at most `k` residual edges. -/
private def RchTo (N : Network V) (f : V → V → ℝ) : ℕ → V → Prop
  | 0 => fun u => u = N.s
  | (k + 1) => fun u => RchTo N f k u ∨ ∃ w, IsResidualEdge N f u w ∧ RchTo N f k w

private theorem rchto_le (N : Network V) (f : V → V → ℝ) :
    ∀ i k u, i ≤ k → RchTo N f i u → RchTo N f k u := by
  intro i k u hik h
  induction k with
  | zero =>
    have hi : i = 0 := by omega
    subst hi; exact h
  | succ m ih =>
    rcases Nat.lt_or_ge i (m + 1) with hlt | hge
    · exact Or.inl (ih (by omega))
    · have : i = m + 1 := by omega
      subst this; exact h

/-- `LvTo N f j u`: the shortest residual path from `u` to the source has exactly `j` edges. -/
private def LvTo (N : Network V) (f : V → V → ℝ) (j : ℕ) (u : V) : Prop :=
  RchTo N f j u ∧ ∀ i < j, ¬ RchTo N f i u

private theorem rchto_exists_lv (N : Network V) (f : V → V → ℝ) :
    ∀ k u, RchTo N f k u → ∃ j, j ≤ k ∧ LvTo N f j u := by
  classical
  intro k u hk
  have hex : ∃ j, RchTo N f j u := ⟨k, hk⟩
  exact ⟨Nat.find hex, Nat.find_le hk, Nat.find_spec hex, fun i hi => Nat.find_min hex hi⟩

private theorem lvto_pred (N : Network V) (f : V → V → ℝ) :
    ∀ j u, LvTo N f (j + 1) u → ∃ w, IsResidualEdge N f u w ∧ LvTo N f j w := by
  intro j u hu
  obtain ⟨hr, hmin⟩ := hu
  rcases hr with hr | ⟨w, he, hw⟩
  · exact absurd hr (hmin j (by omega))
  · obtain ⟨i, hij, hlv⟩ := rchto_exists_lv N f j w hw
    refine ⟨w, he, ?_⟩
    have hij' : i = j := by
      by_contra hne
      have hlt : i < j := by omega
      have : RchTo N f (i + 1) u := Or.inr ⟨w, he, hlv.1⟩
      exact hmin (i + 1) (by omega) this
    exact hij' ▸ hlv

private theorem lvto_down (N : Network V) (f : V → V → ℝ) (k₀ : ℕ) (u₀ : V)
    (ht : LvTo N f k₀ u₀) : ∀ i, i ≤ k₀ → ∃ u, LvTo N f (k₀ - i) u := by
  intro i
  induction i with
  | zero => intro _; exact ⟨u₀, by simpa using ht⟩
  | succ m ih =>
    intro hm
    obtain ⟨u, hu⟩ := ih (by omega)
    have heq : k₀ - m = (k₀ - (m + 1)) + 1 := by omega
    rw [heq] at hu
    obtain ⟨w, -, hw⟩ := lvto_pred N f (k₀ - (m + 1)) u hu
    exact ⟨w, hw⟩

private theorem lvto_unique (N : Network V) (f : V → V → ℝ) :
    ∀ j j' u, LvTo N f j u → LvTo N f j' u → j = j' := by
  intro j j' u h h'
  by_contra hne
  rcases Nat.lt_or_ge j j' with hlt | hge
  · exact h'.2 j hlt h.1
  · exact h.2 j' (by omega) h'.1

private theorem lvto_card (N : Network V) (f : V → V → ℝ) (k₀ : ℕ) (u₀ : V)
    (ht : LvTo N f k₀ u₀) : k₀ + 1 ≤ Fintype.card V := by
  classical
  have hchoice : ∀ j : Fin (k₀ + 1), ∃ u, LvTo N f (j : ℕ) u := by
    intro j
    have hj : k₀ - (k₀ - (j : ℕ)) = (j : ℕ) := by omega
    obtain ⟨u, hu⟩ := lvto_down N f k₀ u₀ ht (k₀ - (j : ℕ)) (by omega)
    exact ⟨u, by rwa [hj] at hu⟩
  choose F hF using hchoice
  have hinj : Function.Injective F := by
    intro a b hab
    have h1 := hF a
    have h2 := hF b
    rw [hab] at h1
    exact Fin.ext (lvto_unique N f (a : ℕ) (b : ℕ) (F b) h1 h2)
  have := Fintype.card_le_of_injective F hinj
  simpa using this

private theorem rchto_label (N : Network V) (f : V → V → ℝ) (d : V → ℕ∞)
    (hd : IsValidLabeling N f d) :
    ∀ k u, RchTo N f k u → d u ≤ d N.s + (k : ℕ∞) := by
  intro k
  induction k with
  | zero =>
    intro u hu
    simp only [RchTo] at hu
    subst hu
    simp
  | succ m ih =>
    intro u hu
    rcases hu with hu | ⟨w, he, hw⟩
    · refine le_trans (ih u hu) ?_
      have hstep : ((m : ℕ∞)) ≤ ((m + 1 : ℕ) : ℕ∞) := by exact_mod_cast Nat.le_succ m
      exact add_le_add (le_refl (d N.s)) hstep
    · have h1 := ih w hw
      have h2 : d u ≤ d w + 1 := hd.2.2 u w he
      have h3 : d u ≤ (d N.s + (m : ℕ∞)) + 1 := le_trans h2 (add_le_add h1 (le_refl 1))
      refine le_trans h3 ?_
      have hc : ((m + 1 : ℕ) : ℕ∞) = (m : ℕ∞) + 1 := by push_cast; ring
      rw [hc, add_assoc]

/-- Excess at a non-source vertex forces a residual path back to the source. -/
private theorem reaches_source (N : Network V) (f : V → V → ℝ) (v : V)
    (hf : IsPreflow N f) (hv : 0 < excess f v) : ResidualReachable N f v N.s := by
  classical
  by_contra hcon
  set T : Finset V := Finset.univ.filter (fun u => ¬ ResidualReachable N f u N.s) with hT
  have hmemT : ∀ u : V, u ∈ T ↔ ¬ ResidualReachable N f u N.s := by
    intro u; simp [hT]
  have hvT : v ∈ T := (hmemT v).mpr hcon
  have hsT : N.s ∉ T := by
    rw [hmemT]
    exact fun h => h Relation.ReflTransGen.refl
  have hnores : ∀ u ∈ T, ∀ w ∈ Tᶜ, f w u ≤ 0 := by
    intro u hu w hw
    rw [hmemT] at hu
    have hws : ResidualReachable N f w N.s := by
      by_contra h
      exact (Finset.mem_compl.mp hw) ((hmemT w).mpr h)
    have hnotedge : ¬ IsResidualEdge N f u w := fun he =>
      hu (Relation.ReflTransGen.head he hws)
    have h1 : N.c u w - f u w ≤ 0 := by
      have := not_lt.mp hnotedge
      rwa [residualCap] at this
    have h2 : (0:ℝ) ≤ N.c u w := N.cap_nonneg u w
    have h3 : f w u = -f u w := hf.2.1 w u
    linarith
  have hanti : ∑ u ∈ T, ∑ w ∈ T, f w u = 0 := by
    have key : ∑ u ∈ T, ∑ w ∈ T, f w u = -∑ u ∈ T, ∑ w ∈ T, f w u := by
      calc ∑ u ∈ T, ∑ w ∈ T, f w u
          = ∑ u ∈ T, ∑ w ∈ T, (-f u w) := by
            exact Finset.sum_congr rfl fun u _ => Finset.sum_congr rfl fun w _ => hf.2.1 w u
        _ = -∑ u ∈ T, ∑ w ∈ T, f u w := by
            rw [← Finset.sum_neg_distrib]
            refine Finset.sum_congr rfl fun u _ => ?_
            rw [← Finset.sum_neg_distrib]
        _ = -∑ u ∈ T, ∑ w ∈ T, f w u := by rw [Finset.sum_comm]
    linarith
  have houter : ∑ u ∈ T, ∑ w ∈ Tᶜ, f w u ≤ 0 :=
    Finset.sum_nonpos fun u hu => Finset.sum_nonpos fun w hw => hnores u hu w hw
  have hsplit : ∑ u ∈ T, excess f u
      = (∑ u ∈ T, ∑ w ∈ T, f w u) + ∑ u ∈ T, ∑ w ∈ Tᶜ, f w u := by
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun u _ => ?_
    rw [excess, ← Finset.sum_add_sum_compl T (fun w => f w u)]
  have hle : ∑ u ∈ T, excess f u ≤ 0 := by rw [hsplit, hanti]; linarith
  have hpos : 0 < ∑ u ∈ T, excess f u := by
    refine Finset.sum_pos' (fun u hu => ?_) ⟨v, hvT, hv⟩
    refine hf.2.2 u ?_
    intro h
    exact hsT (h ▸ hu)
  linarith

theorem solution {V : Type} [Fintype V] [DecidableEq V]
    (N : Network V) (σ : ℕ → State V) (K : ℕ) (hrun : IsRun N σ K) :
    ∀ k ≤ K, ∀ v : V, (σ k).2 v ≤ ((2 * Fintype.card V - 1 : ℕ) : ℕ∞) := by
  have hcard : 1 ≤ Fintype.card V := Fintype.card_pos_iff.mpr ⟨N.s⟩
  intro k
  induction k with
  | zero =>
    intro _ v
    rw [hrun.1]
    show initialLabel N v ≤ ((2 * Fintype.card V - 1 : ℕ) : ℕ∞)
    by_cases hv : v = N.s
    · rw [initialLabel, if_pos hv]
      exact_mod_cast (by omega : Fintype.card V ≤ 2 * Fintype.card V - 1)
    · rw [initialLabel, if_neg hv]
      exact zero_le
  | succ m ih =>
    intro hm v
    have hle := ih (by omega)
    obtain ⟨hp, hd⟩ := run_inv N σ K hrun m (by omega)
    rcases hrun.2 m (by omega) with ⟨a, b, happ, hf1, hf2⟩ | ⟨a, happ, hf1, hf2⟩
    · rw [hf2]; exact hle v
    · rw [hf2]
      by_cases hva : v = a
      · rw [hva, Function.update_self]
        have hact := happ.1
        have hexc : 0 < excess (σ m).1 a := hact.2.2.2
        have hreach : ResidualReachable N (σ m).1 a N.s := reaches_source N (σ m).1 a hp hexc
        have hex : ∃ j, RchTo N (σ m).1 j a := by
          refine Relation.ReflTransGen.head_induction_on hreach ⟨0, rfl⟩ ?_
          intro x y hxy hys ihy
          obtain ⟨j, hj⟩ := ihy
          exact ⟨j + 1, Or.inr ⟨y, hxy, hj⟩⟩
        obtain ⟨k0, hk0⟩ := hex
        obtain ⟨j, hjk, hlv⟩ := rchto_exists_lv N (σ m).1 k0 a hk0
        have hjcard : j + 1 ≤ Fintype.card V := lvto_card N (σ m).1 j a hlv
        have hj1 : 1 ≤ j := by
          rcases Nat.eq_zero_or_pos j with h0 | h0
          · exfalso
            rw [h0] at hlv
            exact hact.1 hlv.1
          · exact h0
        obtain ⟨j', hj'⟩ : ∃ j', j = j' + 1 := ⟨j - 1, by omega⟩
        rw [hj'] at hlv hjcard
        obtain ⟨w, hew, hlvw⟩ := lvto_pred N (σ m).1 j' a hlv
        have hdw : (σ m).2 w ≤ (σ m).2 N.s + (j' : ℕ∞) :=
          rchto_label N (σ m).1 (σ m).2 hd j' w hlvw.1
        rw [hd.1] at hdw
        have hrv : relabelValue N (σ m).1 (σ m).2 a ≤ (σ m).2 w + 1 := by
          unfold relabelValue
          exact iInf_le_of_le w (iInf_le _ hew)
        refine le_trans hrv (le_trans (add_le_add hdw (le_refl 1)) ?_)
        have hcast : ((Fintype.card V : ℕ∞)) + (j' : ℕ∞) + 1
            = ((Fintype.card V + j' + 1 : ℕ) : ℕ∞) := by push_cast; ring
        rw [hcast]
        exact_mod_cast (by omega : Fintype.card V + j' + 1 ≤ 2 * Fintype.card V - 1)
      · rw [Function.update_of_ne hva]
        exact hle v
