-- Prove2me | solution 1 for GoldbergTarjan.Generic.valid_labeling_sink_unreachable
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-09-28T02:47:25.958076+00:00
-- url     : https://prove2.me/submissions/6b480bdc-6d3c-47be-b179-19d6f5c1a787

import Mathlib
import Definitions.Def_GoldbergTarjan_Generic_Labeling

open GoldbergTarjan.Generic

variable {V : Type} [Fintype V]

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

theorem solution {V : Type} [Fintype V]
    (N : Network V) (f : V → V → ℝ) (d : V → ℕ∞)
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
