-- Prove2me | solution 1 for MDPComplexity.AverageCost.no_better_policy
-- status  : ACCEPTED   (prove)
-- author  : @Ethan Cheung Wang
-- created : 2026-10-21T17:43:26.138455+00:00
-- url     : https://prove2.me/submissions/6f80905b-1d54-4e81-a880-df43ff733168

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

theorem cw_split (M : DetMDP S) (a δ r : ℕ) (hδ : 1 ≤ δ) (w : ℕ → S) (e : (t : ℕ) → M.D (w t))
    (hw : NW M (a + δ + r) w e) (hwab : w a = w (a + δ)) :
    ∃ (w2 : ℕ → S) (e2 : (t : ℕ) → M.D (w2 t)), NW M (a + r) w2 e2 ∧ w2 0 = w 0 ∧
      w2 (a + r) = w (a + δ + r) ∧
      ncost M (a + δ + r) w e = ncost M (a + r) w2 e2 + ncost M δ (fun t => w (a + t)) (fun t => e (a + t)) ∧
      NW M δ (fun t => w (a + t)) (fun t => e (a + t)) ∧ w (a + δ) = w (a + 0) := by
  let w2 : ℕ → S := fun t => if t ≤ a then w t else w (t + δ)
  have hw2a : ∀ t, t < a → w t = w2 t := fun t ht => (if_pos ht.le).symm
  have hw2b : ∀ t, a ≤ t → w (t + δ) = w2 t := by
    intro t ht
    by_cases h : t ≤ a
    · have : t = a := by omega
      subst this
      show w (t + δ) = if t ≤ t then w t else w (t + δ)
      rw [if_pos le_rfl, hwab]
    · exact (if_neg h).symm
  let e2 : (t : ℕ) → M.D (w2 t) := fun t =>
    if h : t < a then mpTr M (hw2a t h) (e t) else mpTr M (hw2b t (by omega)) (e (t + δ))
  refine ⟨w2, e2, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro t ht
    by_cases h : t < a
    · simp only [e2, dif_pos h, mpTr_next]
      rw [hw t (by omega)]
      exact (if_pos (by omega)).symm
    · simp only [e2, dif_neg h, mpTr_next]
      rw [hw (t + δ) (by omega)]
      rw [show t + δ + 1 = (t + 1) + δ by ring]
      exact (if_neg (by omega)).symm
  · show (if 0 ≤ a then w 0 else w (0 + δ)) = w 0
    rw [if_pos (by omega)]
  · rw [← hw2b (a + r) (by omega)]
    exact congrArg w (by ring)
  · unfold ncost
    rw [Finset.sum_range_add, Finset.sum_range_add, Finset.sum_range_add]
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
  · intro t ht
    show M.next (w (a + t)) (e (a + t)) = w (a + (t + 1))
    exact (hw (a + t) (by omega)).trans (congrArg w (by ring))
  · rw [Nat.add_zero, hwab]

theorem cw_open (M : DetMDP S) (s₀ : S) (μ cm : ℝ)
    (hμ : ∀ C : M.Cycle, M.Reachable s₀ C.base → μ ≤ C.mean)
    (hcm : ∀ s d, |M.c s d| ≤ cm) :
    ∀ T (w : ℕ → S) (e : (t : ℕ) → M.D (w t)), NW M T w e →
      M.Reachable s₀ (w 0) →
      (T : ℝ) * μ - (Fintype.card S) * (cm + |μ|) ≤ ncost M T w e := by
  intro T
  induction T using Nat.strong_induction_on with
  | _ T ih =>
  intro w e hw hr
  have hcm0 : 0 ≤ cm := (abs_nonneg _).trans (hcm (w 0) (Classical.arbitrary _))
  by_cases hrep : ∃ a b, a < b ∧ b ≤ T ∧ w a = w b
  · obtain ⟨a, b, hab, hbT, hwab⟩ := hrep
    obtain ⟨w2, e2, hw2, h20, -, hsplit, hw1, hcl1⟩ :=
      cw_split M a (b - a) (T - b) (by omega) w e
        (by rw [show a + (b - a) + (T - b) = T by omega]; exact hw)
        (by rw [show a + (b - a) = b by omega]; exact hwab)
    have hr1 : M.Reachable s₀ (w (a + 0)) := cw_reach_all M s₀ T w e hw hr (a + 0) (by omega)
    have i1 := cw_closed M s₀ μ hμ (b - a) (by omega) _ _ hw1 hcl1 hr1
    have i2 := ih (a + (T - b)) (by omega) w2 e2 hw2 (by rw [h20]; exact hr)
    rw [show T = a + (b - a) + (T - b) by omega, hsplit]
    have hcast : ((a + (b - a) + (T - b) : ℕ) : ℝ) = ((a + (T - b) : ℕ) : ℝ) + ((b - a : ℕ) : ℝ) := by
      push_cast; ring
    rw [hcast]
    linarith
  · push_neg at hrep
    have hinj : Function.Injective (fun t : Fin (T + 1) => w t) := by
      intro i j hij
      by_contra hne
      rcases Nat.lt_or_gt_of_ne (Fin.val_ne_of_ne hne) with h | h
      · exact hrep i j h (by omega) hij
      · exact hrep j i h (by omega) hij.symm
    have hT : T + 1 ≤ Fintype.card S := by
      have := Fintype.card_le_of_injective _ hinj; simpa using this
    have hlow : -(T : ℝ) * cm ≤ ncost M T w e := by
      unfold ncost
      have : ∀ t ∈ Finset.range T, -cm ≤ M.c (w t) (e t) := fun t _ => by
        have := hcm (w t) (e t); rw [abs_le] at this; linarith
      have := Finset.sum_le_sum this
      simp at this
      linarith
    have hTr : (T : ℝ) ≤ Fintype.card S := by exact_mod_cast (by omega : T ≤ Fintype.card S)
    have h1 : (T : ℝ) * μ ≥ -(T : ℝ) * |μ| := by
      have := neg_abs_le μ; nlinarith [(Nat.cast_nonneg T : (0:ℝ) ≤ T)]
    have h2 : (T : ℝ) * μ ≤ (T : ℝ) * |μ| := by
      have := le_abs_self μ; nlinarith [(Nat.cast_nonneg T : (0:ℝ) ≤ T)]
    nlinarith [abs_nonneg μ, (Nat.cast_nonneg T : (0:ℝ) ≤ T)]

theorem cw_reach_self (M : DetMDP S) (s₀ : S) : M.Reachable s₀ s₀ :=
  ⟨0, ⟨fun _ => s₀, fun j => j.elim0, fun j => j.elim0⟩, rfl, rfl⟩

theorem solution (M : DetMDP S) (s₀ : S) :
    ∀ (δ : M.Policy) (C₀ : M.Cycle),
      M.Reachable s₀ C₀.base →
      (∀ C : M.Cycle, M.Reachable s₀ C.base → C₀.mean ≤ C.mean) →
      C₀.mean ≤ Filter.liminf (M.average s₀ δ) Filter.atTop := by
  intro δ C₀ _ hmin
  set μ := C₀.mean
  set cm : ℝ := ∑ p : (Σ s : S, M.D s), |M.c p.1 p.2|
  have hcm : ∀ s d, |M.c s d| ≤ cm := fun s d =>
    Finset.single_le_sum (f := fun p : (Σ s : S, M.D s) => |M.c p.1 p.2|)
      (fun _ _ => abs_nonneg _) (Finset.mem_univ ⟨s, d⟩)
  set K : ℝ := (Fintype.card S) * (cm + |μ|)
  let w : ℕ → S := M.path s₀ δ
  let e : (t : ℕ) → M.D (w t) := fun t => δ (w t) t
  have hw : ∀ T, NW M T w e := fun T t _ => rfl
  have hsum : ∀ T, ∑ t ∈ Finset.range (T + 1), M.stageCost s₀ δ t = ncost M (T + 1) w e :=
    fun T => rfl
  have hlow : ∀ T, ((T + 1 : ℕ) : ℝ) * μ - K ≤ ncost M (T + 1) w e := fun T =>
    cw_open M s₀ μ cm hmin hcm (T + 1) w e (hw _) (cw_reach_self M s₀)
  have hup : ∀ T, ncost M (T + 1) w e ≤ ((T + 1 : ℕ) : ℝ) * cm := by
    intro T
    unfold ncost
    have := Finset.sum_le_sum (s := Finset.range (T + 1))
      (fun t _ => (le_abs_self _).trans (hcm (w t) (e t)))
    simpa using this
  have hcm0 : 0 ≤ cm := (abs_nonneg _).trans (hcm s₀ (Classical.arbitrary _))
  have hcob : Filter.IsCoboundedUnder (· ≥ ·) Filter.atTop (M.average s₀ δ) := by
    apply Filter.isCoboundedUnder_ge_of_eventually_le Filter.atTop (x := 2 * cm)
    filter_upwards [Filter.eventually_ge_atTop 1] with T hT
    have hTp : (0:ℝ) < T := by exact_mod_cast hT
    unfold DetMDP.average
    rw [hsum, div_le_iff₀ hTp]
    have := hup T
    have h1 : (1:ℝ) ≤ T := by exact_mod_cast hT
    push_cast at this
    nlinarith
  apply le_of_forall_pos_le_add
  intro ε hε
  obtain ⟨N, hN⟩ := exists_nat_gt ((|μ| + K) / ε)
  have : μ - ε ≤ Filter.liminf (M.average s₀ δ) Filter.atTop := by
    apply Filter.le_liminf_of_le hcob
    filter_upwards [Filter.eventually_ge_atTop (max N 1)] with T hT
    have hT1 : (1:ℝ) ≤ T := by exact_mod_cast le_of_max_le_right hT
    have hTN : (N:ℝ) ≤ T := by exact_mod_cast le_of_max_le_left hT
    have hTp : (0:ℝ) < T := by linarith
    unfold DetMDP.average
    rw [hsum, le_div_iff₀ hTp]
    have h1 := hlow T
    push_cast at h1
    have h2 : (|μ| + K) / ε < T := lt_of_lt_of_le hN hTN
    rw [div_lt_iff₀ hε] at h2
    have h3 := neg_abs_le μ
    nlinarith
  linarith
