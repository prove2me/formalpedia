-- Prove2me | solution 1 for MDPComplexity.Discounted.B_cheapest_walk
-- status  : ACCEPTED   (prove)
-- author  : @Ethan Cheung
-- created : 2026-10-21T17:38:26.79999+00:00
-- url     : https://prove2.me/submissions/fa2a8d80-26af-4a9c-a843-7a1137b23269

import Mathlib
import Definitions.Def_MDPComplexity_Discounted_Model

open MDPComplexity.Discounted Tropical

section
variable {S : Type} [Fintype S] [DecidableEq S]

def bwTr (M : DetMDP S) {s s' : S} (e : s = s') (x : M.D s) : M.D s' := e ▸ x

theorem bwTr_next (M : DetMDP S) {s s' : S} (e : s = s') (x : M.D s) :
    M.next s' (bwTr M e x) = M.next s x := by subst e; rfl

theorem bwTr_c (M : DetMDP S) {s s' : S} (e : s = s') (x : M.D s) :
    M.c s' (bwTr M e x) = M.c s x := by subst e; rfl

theorem bw_untropA (M : DetMDP S) (w v : S) :
    untrop (M.A w v) = Finset.univ.inf (fun i : M.D w =>
      if M.next w i = v then ((M.c w i : ℝ) : WithTop ℝ) else ⊤) := by
  unfold DetMDP.A
  rw [Finset.untrop_sum']
  congr 1
  funext i
  simp only [Function.comp]
  split_ifs <;> simp

theorem bw_B0 (M : DetMDP S) (β : ℝ) (u v : S) :
    untrop (M.B β 0 u v) = if u = v then 0 else ⊤ := by
  show untrop ((1 : Matrix S S (Tropical (WithTop ℝ))) u v) = _
  rw [Matrix.one_apply]
  split_ifs <;> simp

theorem bw_Bsucc (M : DetMDP S) (β : ℝ) (j : ℕ) (u v : S) :
    untrop (M.B β (j + 1) u v) = Finset.univ.inf (fun w : S =>
      untrop (M.B β j u w) + untrop (M.scaledA (β ^ j) w v)) := by
  show untrop ((M.B β j * M.scaledA (β ^ j)) u v) = _
  rw [Matrix.mul_apply, Finset.untrop_sum']
  rfl

theorem bw_scaled_le (M : DetMDP S) (r : ℝ) (hr : 0 ≤ r) (w v : S) (d : M.D w)
    (h : M.next w d = v) : untrop (M.scaledA r w v) ≤ ((r * M.c w d : ℝ) : WithTop ℝ) := by
  have h1 : untrop (M.A w v) ≤ ((M.c w d : ℝ) : WithTop ℝ) := by
    rw [bw_untropA]
    refine (Finset.inf_le (Finset.mem_univ d)).trans ?_
    simp [h]
  unfold DetMDP.scaledA
  rw [untrop_trop]
  generalize untrop (M.A w v) = a at h1
  cases a with
  | top => exact absurd h1 (by simp)
  | coe y =>
    simp only [WithTop.map_coe, WithTop.coe_le_coe] at h1 ⊢
    exact mul_le_mul_of_nonneg_left h1 hr

theorem bw_scaled_ex (M : DetMDP S) (r : ℝ) (w v : S) (hne : untrop (M.scaledA r w v) ≠ ⊤) :
    ∃ d : M.D w, M.next w d = v ∧ untrop (M.scaledA r w v) = ((r * M.c w d : ℝ) : WithTop ℝ) := by
  unfold DetMDP.scaledA at hne ⊢
  rw [untrop_trop] at hne ⊢
  obtain ⟨d, -, hd⟩ := Finset.exists_mem_eq_inf (Finset.univ : Finset (M.D w))
    Finset.univ_nonempty (fun i : M.D w => if M.next w i = v then ((M.c w i : ℝ) : WithTop ℝ) else ⊤)
  have hA : untrop (M.A w v) = if M.next w d = v then ((M.c w d : ℝ) : WithTop ℝ) else ⊤ := by
    rw [bw_untropA]; exact hd
  rw [hA] at hne ⊢
  by_cases hn : M.next w d = v
  · rw [if_pos hn]
    exact ⟨d, hn, by simp⟩
  · rw [if_neg hn] at hne; exact absurd rfl hne

theorem bw_le (M : DetMDP S) (β : ℝ) (hβ : 0 < β) : ∀ (j : ℕ) (u v : S) (W : M.Walk j u v),
    untrop (M.B β j u v) ≤ ((W.cost β : ℝ) : WithTop ℝ) := by
  intro j
  induction j with
  | zero =>
    intro u v W
    rw [bw_B0, if_pos (W.start.symm.trans W.finish)]
    simp [DetMDP.Walk.cost]
  | succ j ih =>
    intro u v W
    let W' : M.Walk j u (W.w j) := ⟨W.w, W.e, W.start, rfl, fun t ht => W.step t (by omega)⟩
    have h1 := ih u (W.w j) W'
    have hc : W.cost β = W'.cost β + β ^ j * M.c (W.w j) (W.e j) := by
      unfold DetMDP.Walk.cost; rw [Finset.sum_range_succ]
    rw [bw_Bsucc, hc, WithTop.coe_add]
    refine (Finset.inf_le (Finset.mem_univ (W.w j))).trans ?_
    exact add_le_add h1 (bw_scaled_le M _ (by positivity) _ _ _
      ((W.step j (by omega)).trans W.finish))

theorem bw_ex (M : DetMDP S) (β : ℝ) : ∀ (j : ℕ) (u v : S), untrop (M.B β j u v) ≠ ⊤ →
    ∃ W : M.Walk j u v, untrop (M.B β j u v) = ((W.cost β : ℝ) : WithTop ℝ) := by
  intro j
  induction j with
  | zero =>
    intro u v h
    rw [bw_B0] at h ⊢
    have huv : u = v := by by_contra hn; rw [if_neg hn] at h; exact h rfl
    subst huv
    refine ⟨⟨fun _ => u, fun _ => Classical.arbitrary _, rfl, rfl, fun t ht => absurd ht (by omega)⟩, ?_⟩
    simp [DetMDP.Walk.cost]
  | succ j ih =>
    intro u v h
    have : Nonempty S := ⟨u⟩
    rw [bw_Bsucc] at h ⊢
    obtain ⟨w, -, hw⟩ := Finset.exists_mem_eq_inf Finset.univ Finset.univ_nonempty
      (fun w : S => untrop (M.B β j u w) + untrop (M.scaledA (β ^ j) w v))
    rw [hw] at h ⊢
    have h1 : untrop (M.B β j u w) ≠ ⊤ := fun e => h (by simp [e])
    have h2 : untrop (M.scaledA (β ^ j) w v) ≠ ⊤ := fun e => h (by simp [e])
    obtain ⟨W, hW⟩ := ih u w h1
    obtain ⟨d, hdn, hd⟩ := bw_scaled_ex M _ w v h2
    let ww : ℕ → S := fun t => if t ≤ j then W.w t else v
    have hle : ∀ t, t ≤ j → W.w t = ww t := fun t ht => (if_pos ht).symm
    have hwj : w = ww j := W.finish.symm.trans (hle j le_rfl)
    let ee : (t : ℕ) → M.D (ww t) := fun t =>
      if h : t < j then bwTr M (hle t h.le) (W.e t)
      else if h' : t = j then bwTr M (hwj.trans (congrArg ww h'.symm)) d
      else Classical.arbitrary _
    have hstep : ∀ t < j + 1, M.next (ww t) (ee t) = ww (t + 1) := by
      intro t ht
      by_cases h3 : t < j
      · simp only [ee, dif_pos h3, bwTr_next]
        rw [W.step t h3]; exact hle (t+1) (by omega)
      · have h4 : t = j := by omega
        simp only [ee, dif_neg h3, dif_pos h4, bwTr_next]
        rw [hdn]; exact (if_neg (by omega)).symm
    let V : M.Walk (j + 1) u v :=
      ⟨ww, ee, by rw [← hle 0 (by omega)]; exact W.start, if_neg (by omega), hstep⟩
    refine ⟨V, ?_⟩
    have hcost : V.cost β = W.cost β + β ^ j * M.c w d := by
      unfold DetMDP.Walk.cost
      rw [Finset.sum_range_succ]
      congr 1
      · apply Finset.sum_congr rfl
        intro t ht
        rw [Finset.mem_range] at ht
        show β ^ t * M.c (ww t) (ee t) = _
        simp only [ee, dif_pos ht, bwTr_c]
      · show β ^ j * M.c (ww j) (ee j) = _
        simp only [ee, lt_irrefl, dif_neg, not_false_eq_true, dif_pos, bwTr_c]
    rw [hcost, hW, hd, WithTop.coe_add]
end

theorem solution {S : Type} [Fintype S] [DecidableEq S] (M : DetMDP S)
    (β : ℝ) (hβ : 0 < β ∧ β < 1) (j : ℕ) (u v : S) :
    (M.B β j u v = Tropical.trop (⊤ : WithTop ℝ) ↔ IsEmpty (M.Walk j u v)) ∧
    ∀ W : M.Walk j u v, ∃ x : ℝ, M.B β j u v = Tropical.trop (x : WithTop ℝ) ∧
      IsLeast (Set.range fun W' : M.Walk j u v => W'.cost β) x := by
  have key : M.B β j u v = Tropical.trop (⊤ : WithTop ℝ) ↔ untrop (M.B β j u v) = ⊤ := by
    constructor
    · intro h; rw [h, untrop_trop]
    · intro h; rw [← h, trop_untrop]
  constructor
  · rw [key]
    constructor
    · intro h
      refine ⟨fun W => ?_⟩
      have := bw_le M β hβ.1 j u v W
      rw [h] at this
      exact absurd this (by simp)
    · intro h
      by_contra hne
      obtain ⟨W, -⟩ := bw_ex M β j u v hne
      exact h.false W
  · intro W
    have hne : untrop (M.B β j u v) ≠ ⊤ :=
      ne_top_of_le_ne_top WithTop.coe_ne_top (bw_le M β hβ.1 j u v W)
    obtain ⟨W', hW'⟩ := bw_ex M β j u v hne
    refine ⟨W'.cost β, by rw [← hW', trop_untrop], ⟨W', rfl⟩, ?_⟩
    rintro _ ⟨W'', rfl⟩
    have := bw_le M β hβ.1 j u v W''
    rw [hW'] at this
    exact WithTop.coe_le_coe.1 this
