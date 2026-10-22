-- Prove2me | solution 1 for MDPComplexity.AverageCost.closed_walk_mean
-- status  : ACCEPTED   (prove)
-- author  : @Ethan Cheung
-- created : 2026-10-21T17:41:20.232869+00:00
-- url     : https://prove2.me/submissions/5f1c58bd-a5fa-4b79-8dc1-e4ff29c8b3d9

import Mathlib
import Definitions.Def_MDPComplexity_AverageCost_Model

open MDPComplexity.AverageCost

variable {S : Type*} [Fintype S] [DecidableEq S]

def mpTr (M : DetMDP S) {s s' : S} (e : s = s') (x : M.D s) : M.D s' := e ▸ x

theorem mpTr_next (M : DetMDP S) {s s' : S} (e : s = s') (x : M.D s) :
    M.next s' (mpTr M e x) = M.next s x := by subst e; rfl

theorem mpTr_c (M : DetMDP S) {s s' : S} (e : s = s') (x : M.D s) :
    M.c s' (mpTr M e x) = M.c s x := by subst e; rfl

def mpInit (M : DetMDP S) {k : ℕ} (W : M.Walk (k+1)) : M.Walk k where
  v := fun j => W.v j.castSucc
  d := fun j => W.d j.castSucc
  step := fun j => W.step j.castSucc

def mpSnocV (M : DetMDP S) {k : ℕ} (W : M.Walk k) (d : M.D W.finish) (j : Fin (k+2)) : S :=
  if h : (j : ℕ) < k + 1 then W.v ⟨j, h⟩ else M.next W.finish d

theorem mpSnocV_lt (M : DetMDP S) {k : ℕ} (W : M.Walk k) (d : M.D W.finish) (j : Fin (k+2))
    (h : (j : ℕ) < k + 1) : mpSnocV M W d j = W.v ⟨j, h⟩ := by
  simp [mpSnocV, h]

theorem mpSnocV_ge (M : DetMDP S) {k : ℕ} (W : M.Walk k) (d : M.D W.finish) (j : Fin (k+2))
    (h : ¬ (j : ℕ) < k + 1) : mpSnocV M W d j = M.next W.finish d := by
  simp [mpSnocV, h]

def mpSnoc (M : DetMDP S) {k : ℕ} (W : M.Walk k) (d : M.D W.finish) : M.Walk (k+1) where
  v := mpSnocV M W d
  d := fun j => if h : (j : ℕ) < k then
      mpTr M (mpSnocV_lt M W d j.castSucc (by simp; omega)).symm (W.d ⟨j, h⟩)
    else
      mpTr M ((congrArg W.v (Fin.ext (by have := j.isLt; simp; omega))).trans
        (mpSnocV_lt M W d j.castSucc (by have := j.isLt; simp; omega)).symm) d
  step := by
    intro j
    by_cases h : (j : ℕ) < k
    · simp only [dif_pos h, mpTr_next]
      refine (W.step ⟨j, h⟩).trans ?_
      rw [mpSnocV_lt M W d j.succ (by simp; omega)]
      rfl
    · simp only [dif_neg h, mpTr_next]
      rw [mpSnocV_ge M W d j.succ (by simp; omega)]
      exact mpTr_next M _ _

theorem mpSnoc_start (M : DetMDP S) {k : ℕ} (W : M.Walk k) (d : M.D W.finish) :
    (mpSnoc M W d).start = W.start := by
  simp only [DetMDP.Walk.start, mpSnoc]
  rw [mpSnocV_lt M W d _ (by simp)]

theorem mpSnoc_finish (M : DetMDP S) {k : ℕ} (W : M.Walk k) (d : M.D W.finish) :
    (mpSnoc M W d).finish = M.next W.finish d := by
  simp only [DetMDP.Walk.finish, mpSnoc]
  rw [mpSnocV_ge M W d _ (by simp)]
  rfl

theorem mpSnoc_cost (M : DetMDP S) {k : ℕ} (W : M.Walk k) (d : M.D W.finish) :
    (mpSnoc M W d).cost = W.cost + M.c W.finish d := by
  unfold DetMDP.Walk.cost
  rw [Fin.sum_univ_castSucc]
  congr 1
  · apply Finset.sum_congr rfl
    intro i _
    show M.c (mpSnocV M W d _) (dite _ _ _) = _
    rw [dif_pos (show ((i.castSucc : Fin (k+1)) : ℕ) < k from i.isLt), mpTr_c]
    rfl
  · show M.c (mpSnocV M W d _) (dite _ _ _) = _
    rw [dif_neg (show ¬ ((Fin.last k : Fin (k+1)) : ℕ) < k by simp)]
    exact mpTr_c M _ d


theorem cw_reach_step (M : DetMDP S) (s₀ x : S) (d : M.D x) (h : M.Reachable s₀ x) :
    M.Reachable s₀ (M.next x d) := by
  obtain ⟨len, W, hs, hf⟩ := h
  subst hf
  exact ⟨len + 1, mpSnoc M W d, by rw [mpSnoc_start, hs], mpSnoc_finish M W d⟩

def NW (M : DetMDP S) (k : ℕ) (w : ℕ → S) (e : (t : ℕ) → M.D (w t)) : Prop :=
  ∀ t < k, M.next (w t) (e t) = w (t + 1)

def ncost (M : DetMDP S) (k : ℕ) (w : ℕ → S) (e : (t : ℕ) → M.D (w t)) : ℝ :=
  ∑ t ∈ Finset.range k, M.c (w t) (e t)

theorem cw_reach_all (M : DetMDP S) (s₀ : S) (k : ℕ) (w : ℕ → S) (e : (t : ℕ) → M.D (w t))
    (hw : NW M k w e) (h0 : M.Reachable s₀ (w 0)) : ∀ t ≤ k, M.Reachable s₀ (w t) := by
  intro t
  induction t with
  | zero => intro _; exact h0
  | succ t ih =>
    intro ht
    rw [← hw t (by omega)]
    exact cw_reach_step M s₀ _ _ (ih (by omega))

theorem cw_closed (M : DetMDP S) (s₀ : S) (μ : ℝ)
    (hμ : ∀ C : M.Cycle, M.Reachable s₀ C.base → μ ≤ C.mean) :
    ∀ k, 1 ≤ k → ∀ (w : ℕ → S) (e : (t : ℕ) → M.D (w t)), NW M k w e → w k = w 0 →
      M.Reachable s₀ (w 0) → (k : ℝ) * μ ≤ ncost M k w e := by
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
  intro hk w e hw hcl hr
  by_cases hdist : ∀ a < k, ∀ b < k, w a = w b → a = b
  · let C : M.Cycle :=
      { len := k
        positive := hk
        v := fun j => w j
        d := fun j => e j
        distinct := fun i j hij => Fin.ext (hdist i i.isLt j j.isLt hij)
        step := by
          intro j
          show M.next (w j) (e j) = w ((j.val + 1) % k)
          rw [hw j j.isLt]
          by_cases hj : j.val + 1 < k
          · rw [Nat.mod_eq_of_lt hj]
          · have : j.val + 1 = k := by have := j.isLt; omega
            rw [this, Nat.mod_self, hcl] }
    have h1 := hμ C hr
    have hmean : C.mean = ncost M k w e / k := by
      unfold DetMDP.Cycle.mean ncost
      congr 1
      exact Fin.sum_univ_eq_sum_range (fun t => M.c (w t) (e t)) k
    rw [hmean, le_div_iff₀ (by exact_mod_cast hk)] at h1
    linarith
  · push_neg at hdist
    obtain ⟨a0, ha0, b0, hb0, hab0, hne0⟩ := hdist
    -- order them
    obtain ⟨a, b, hab, hb, hwab⟩ : ∃ a b, a < b ∧ b < k ∧ w a = w b := by
      rcases Nat.lt_or_gt_of_ne hne0 with h | h
      · exact ⟨a0, b0, h, hb0, hab0⟩
      · exact ⟨b0, a0, h, ha0, hab0.symm⟩
    set δ := b - a with hδ
    set r := k - b with hr'
    have hk' : k = a + δ + r := by omega
    -- inner walk
    let w1 : ℕ → S := fun t => w (a + t)
    let e1 : (t : ℕ) → M.D (w1 t) := fun t => e (a + t)
    have hw1 : NW M δ w1 e1 := fun t ht => by
      show M.next (w (a + t)) (e (a + t)) = w (a + (t + 1))
      exact (hw (a + t) (by omega)).trans (congrArg w (by ring))
    have hcl1 : w1 δ = w1 0 := by
      show w (a + δ) = w (a + 0)
      rw [show a + δ = b by omega, Nat.add_zero, hwab]
    have hr1 : M.Reachable s₀ (w1 0) := cw_reach_all M s₀ k w e hw hr (a + 0) (by omega)
    have i1 := ih δ (by omega) (by omega) w1 e1 hw1 hcl1 hr1
    -- outer walk
    let w2 : ℕ → S := fun t => if t ≤ a then w t else w (t + δ)
    have hw2a : ∀ t, t < a → w t = w2 t := fun t ht => (if_pos ht.le).symm
    have hw2b : ∀ t, a ≤ t → w (t + δ) = w2 t := by
      intro t ht
      by_cases h : t ≤ a
      · have : t = a := by omega
        subst this
        show w (t + δ) = if t ≤ t then w t else w (t + δ)
        rw [if_pos le_rfl, show t + δ = b by omega, hwab]
      · exact (if_neg h).symm
    let e2 : (t : ℕ) → M.D (w2 t) := fun t =>
      if h : t < a then mpTr M (hw2a t h) (e t) else mpTr M (hw2b t (by omega)) (e (t + δ))
    have hw2 : NW M (a + r) w2 e2 := by
      intro t ht
      by_cases h : t < a
      · simp only [e2, dif_pos h, mpTr_next]
        rw [hw t (by omega)]
        exact (if_pos (by omega)).symm
      · simp only [e2, dif_neg h, mpTr_next]
        rw [hw (t + δ) (by omega)]
        rw [show t + δ + 1 = (t + 1) + δ by ring]
        exact (if_neg (by omega)).symm
    have hcl2 : w2 (a + r) = w2 0 := by
      show (if a + r ≤ a then w (a + r) else w (a + r + δ)) = if 0 ≤ a then w 0 else w (0 + δ)
      by_cases hr0 : r = 0
      · omega
      · rw [if_neg (by omega), if_pos (by omega), show a + r + δ = k by omega, hcl]
    have hr2 : M.Reachable s₀ (w2 0) := by
      show M.Reachable s₀ (if 0 ≤ a then w 0 else w (0 + δ))
      rw [if_pos (by omega)]; exact hr
    have i2 := ih (a + r) (by omega) (by omega) w2 e2 hw2 hcl2 hr2
    -- cost split
    have hsplit : ncost M k w e = ncost M (a + r) w2 e2 + ncost M δ w1 e1 := by
      unfold ncost
      rw [hk', Finset.sum_range_add, Finset.sum_range_add, Finset.sum_range_add]
      have hA : ∑ t ∈ Finset.range a, M.c (w2 t) (e2 t) = ∑ t ∈ Finset.range a, M.c (w t) (e t) := by
        apply Finset.sum_congr rfl
        intro t ht
        rw [Finset.mem_range] at ht
        simp only [e2, dif_pos ht, mpTr_c]
      have hB : ∑ t ∈ Finset.range r, M.c (w2 (a + t)) (e2 (a + t)) =
          ∑ t ∈ Finset.range r, M.c (w (a + δ + t)) (e (a + δ + t)) := by
        apply Finset.sum_congr rfl
        intro t _
        simp only [e2, dif_neg (show ¬ (a + t < a) by omega), mpTr_c]
        exact congrArg (fun s => M.c (w s) (e s)) (by ring)
      rw [hA, hB]
      ring
    rw [hsplit]
    have hcast : ((a + r : ℕ) : ℝ) + (δ : ℝ) = (k : ℝ) := by
      rw [hk']; push_cast; ring
    rw [← hcast]
    linarith

def cwW (M : DetMDP S) {k : ℕ} (W : M.Walk k) : ℕ → S := fun t => W.v ⟨min t k, by omega⟩

noncomputable def cwE (M : DetMDP S) {k : ℕ} (W : M.Walk k) : (t : ℕ) → M.D (cwW M W t) := fun t =>
  if h : t < k then
    mpTr M (show W.v (⟨t, h⟩ : Fin k).castSucc = cwW M W t from
      congrArg W.v (Fin.ext (by simp; omega))) (W.d ⟨t, h⟩)
  else Classical.arbitrary _

theorem cw_conv_nw (M : DetMDP S) {k : ℕ} (W : M.Walk k) : NW M k (cwW M W) (cwE M W) := by
  intro t ht
  simp only [cwE, dif_pos ht, mpTr_next]
  rw [W.step ⟨t, ht⟩]
  exact congrArg W.v (Fin.ext (by simp; omega))

theorem cw_conv_cost (M : DetMDP S) {k : ℕ} (W : M.Walk k) :
    ncost M k (cwW M W) (cwE M W) = W.cost := by
  unfold ncost DetMDP.Walk.cost
  rw [← Fin.sum_univ_eq_sum_range]
  apply Finset.sum_congr rfl
  intro j _
  simp only [cwE, dif_pos j.isLt, mpTr_c]

theorem cw_conv_0 (M : DetMDP S) {k : ℕ} (W : M.Walk k) : cwW M W 0 = W.start :=
  congrArg W.v (Fin.ext (by simp))

theorem cw_conv_k (M : DetMDP S) {k : ℕ} (W : M.Walk k) : cwW M W k = W.finish :=
  congrArg W.v (Fin.ext (by simp))

theorem cw_walk_bound (M : DetMDP S) (s₀ : S) (μ : ℝ)
    (hμ : ∀ C : M.Cycle, M.Reachable s₀ C.base → μ ≤ C.mean)
    {k : ℕ} (hk : 1 ≤ k) (W : M.Walk k) (u : S) (hu : M.Reachable s₀ u)
    (hs : W.start = u) (hf : W.finish = u) : (k : ℝ) * μ ≤ W.cost := by
  rw [← cw_conv_cost]
  apply cw_closed M s₀ μ hμ k hk _ _ (cw_conv_nw M W)
  · rw [cw_conv_0, cw_conv_k, hs, hf]
  · rw [cw_conv_0, hs]; exact hu

def cwCyc (M : DetMDP S) (C : M.Cycle) : M.Walk C.len where
  v := fun j => C.v ⟨j.val % C.len, Nat.mod_lt _ C.positive⟩
  d := fun j => mpTr M (congrArg C.v (Fin.ext (Nat.mod_eq_of_lt j.isLt).symm))
    (C.d j)
  step := by
    intro j
    rw [mpTr_next, C.step j]
    exact congrArg C.v (Fin.ext (by simp))

theorem cwCyc_cost (M : DetMDP S) (C : M.Cycle) :
    (cwCyc M C).cost = ∑ j : Fin C.len, M.c (C.v j) (C.d j) := by
  unfold DetMDP.Walk.cost
  apply Finset.sum_congr rfl
  intro j _
  exact mpTr_c M _ _

theorem cwCyc_start (M : DetMDP S) (C : M.Cycle) : (cwCyc M C).start = C.base :=
  congrArg C.v (Fin.ext (by simp))

theorem cwCyc_finish (M : DetMDP S) (C : M.Cycle) : (cwCyc M C).finish = C.base :=
  congrArg C.v (Fin.ext (by simp [DetMDP.Cycle.base]))
theorem solution (M : DetMDP S) (s₀ : S) :
    ∀ C₀ : M.Cycle, M.Reachable s₀ C₀.base →
      (∀ C : M.Cycle, M.Reachable s₀ C.base → C₀.mean ≤ C.mean) →
      IsLeast {μ : ℝ | ∃ (u : S) (k : ℕ) (W : M.Walk k),
        M.Reachable s₀ u ∧ 1 ≤ k ∧ k ≤ Fintype.card S ∧
        W.start = u ∧ W.finish = u ∧ μ = W.cost / k} C₀.mean := by
  intro C₀ hr hmin
  constructor
  · refine ⟨C₀.base, C₀.len, cwCyc M C₀, hr, C₀.positive, ?_, cwCyc_start M C₀,
      cwCyc_finish M C₀, ?_⟩
    · have := Fintype.card_le_of_injective C₀.v C₀.distinct
      simpa using this
    · rw [cwCyc_cost]; rfl
  · rintro μ ⟨u, k, W, hu, hk, -, hs, hf, rfl⟩
    have := cw_walk_bound M s₀ C₀.mean hmin hk W u hu hs hf
    rw [le_div_iff₀ (by exact_mod_cast hk)]
    linarith
