-- Prove2me | solution 1 for MDPComplexity.AverageCost.min_plus_walks
-- status  : ACCEPTED   (prove)
-- author  : @Ethan Cheung Wang
-- created : 2026-10-21T17:24:04.040725+00:00
-- url     : https://prove2.me/submissions/4532ee3c-202c-4428-8d5a-5e6eda4e97e0

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

theorem mp_A_le (M : DetMDP S) (w v : S) (d : M.D w) (h : M.next w d = v) :
    M.A w v ≤ (M.c w d : WithTop ℝ) := by
  unfold DetMDP.A
  refine (Finset.inf_le (Finset.mem_univ d)).trans ?_
  simp [h]

theorem mp_le (M : DetMDP S) : ∀ (k : ℕ) (W : M.Walk k),
    M.minPlusPow k W.start W.finish ≤ (W.cost : WithTop ℝ) := by
  intro k
  induction k with
  | zero =>
    intro W
    simp [DetMDP.minPlusPow, DetMDP.Walk.cost, DetMDP.Walk.start, DetMDP.Walk.finish]
  | succ k ih =>
    intro W
    have h1 := ih (mpInit M W)
    have hc : W.cost = (mpInit M W).cost + M.c (W.v (Fin.last k).castSucc) (W.d (Fin.last k)) := by
      unfold DetMDP.Walk.cost
      rw [Fin.sum_univ_castSucc]
      rfl
    rw [hc, WithTop.coe_add]
    show Finset.univ.inf _ ≤ _
    refine (Finset.inf_le (Finset.mem_univ (mpInit M W).finish)).trans ?_
    exact add_le_add h1 (mp_A_le M _ _ _ (W.step (Fin.last k)))

theorem mp_ex (M : DetMDP S) : ∀ (k : ℕ) (u v : S), M.minPlusPow k u v ≠ ⊤ →
    ∃ W : M.Walk k, W.start = u ∧ W.finish = v ∧ M.minPlusPow k u v = (W.cost : WithTop ℝ) := by
  intro k
  induction k with
  | zero =>
    intro u v h
    have huv : u = v := by
      by_contra hne; simp [DetMDP.minPlusPow, hne] at h
    subst huv
    refine ⟨⟨fun _ => u, fun j => j.elim0, fun j => j.elim0⟩, rfl, rfl, ?_⟩
    simp [DetMDP.minPlusPow, DetMDP.Walk.cost]
  | succ k ih =>
    intro u v h
    have : Nonempty S := ⟨u⟩
    have hdef : M.minPlusPow (k+1) u v =
        Finset.univ.inf (fun w : S => M.minPlusPow k u w + M.A w v) := rfl
    obtain ⟨w, -, hw⟩ := Finset.exists_mem_eq_inf Finset.univ Finset.univ_nonempty
      (fun w : S => M.minPlusPow k u w + M.A w v)
    rw [hdef, hw] at h ⊢
    have h1 : M.minPlusPow k u w ≠ ⊤ := fun e => h (by simp [e])
    have h2 : M.A w v ≠ ⊤ := fun e => h (by simp [e])
    obtain ⟨W, hs, hf, hW⟩ := ih u w h1
    obtain ⟨d, -, hd⟩ := Finset.exists_mem_eq_inf (Finset.univ : Finset (M.D w))
      Finset.univ_nonempty (fun d : M.D w => if M.next w d = v then (M.c w d : WithTop ℝ) else ⊤)
    have hA : M.A w v = if M.next w d = v then (M.c w d : WithTop ℝ) else ⊤ := hd
    have hnd : M.next w d = v := by
      by_contra hn; rw [hA, if_neg hn] at h2; exact h2 rfl
    rw [hA, if_pos hnd, hW]
    subst hf
    refine ⟨mpSnoc M W d, by rw [mpSnoc_start, hs], by rw [mpSnoc_finish, hnd], ?_⟩
    rw [mpSnoc_cost, WithTop.coe_add]

theorem solution (M : DetMDP S) (k : ℕ) (u v : S) :
    (M.minPlusPow k u v = ⊤ ↔
      ¬ ∃ W : M.Walk k, W.start = u ∧ W.finish = v) ∧
    (∀ W : M.Walk k, W.start = u → W.finish = v →
      ∃ r : ℝ, M.minPlusPow k u v = (r : WithTop ℝ) ∧
        IsLeast {x : ℝ | ∃ W' : M.Walk k,
          W'.start = u ∧ W'.finish = v ∧ x = W'.cost} r) := by
  constructor
  · constructor
    · rintro htop ⟨W, hs, hf⟩
      have := mp_le M k W
      rw [hs, hf, htop] at this
      exact absurd this (WithTop.not_top_le_coe _)
    · intro hn
      by_contra hne
      obtain ⟨W, hs, hf, -⟩ := mp_ex M k u v hne
      exact hn ⟨W, hs, hf⟩
  · intro W hs hf
    have hle := mp_le M k W
    rw [hs, hf] at hle
    have hne : M.minPlusPow k u v ≠ ⊤ := ne_top_of_le_ne_top WithTop.coe_ne_top hle
    obtain ⟨W', hs', hf', heq⟩ := mp_ex M k u v hne
    refine ⟨W'.cost, heq, ⟨W', hs', hf', rfl⟩, ?_⟩
    rintro x ⟨W'', h1, h2, rfl⟩
    have := mp_le M k W''
    rw [h1, h2, heq] at this
    exact WithTop.coe_le_coe.1 this
