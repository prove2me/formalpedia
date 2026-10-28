-- Prove2me | solution 1 for MDPComplexity.StationaryHorizon.horizon_walk
-- status  : ACCEPTED   (prove)
-- author  : @Ethan Cheung Wang
-- created : 2026-10-21T17:36:47.990046+00:00
-- url     : https://prove2.me/submissions/a999cdef-3006-41f6-841a-1104a0109aa2

import Mathlib
import Definitions.Def_MDPComplexity_StationaryHorizon_Model

open MDPComplexity.StationaryHorizon

section
variable {S : Type} [Fintype S]

def hwTr (M : DetMDP S) {s s' : S} (e : s = s') (x : M.D s) : M.D s' := e ▸ x

theorem hwTr_next (M : DetMDP S) {s s' : S} (e : s = s') (x : M.D s) :
    M.next s' (hwTr M e x) = M.next s x := by subst e; rfl

theorem hwTr_c (M : DetMDP S) {s s' : S} (e : s = s') (x : M.D s) :
    M.c s' (hwTr M e x) = M.c s x := by subst e; rfl

def hwPathWalk (M : DetMDP S) (s₀ : S) (δ : M.Policy) (T : ℕ) : M.Walk T where
  x := fun t => M.path s₀ δ t
  e := fun t => δ (M.path s₀ δ t) t
  valid := fun t => rfl

theorem hwPathWalk_cost (M : DetMDP S) (s₀ : S) (δ : M.Policy) (T : ℕ) :
    (hwPathWalk M s₀ δ T).cost = M.horizonCost s₀ δ T := by
  unfold DetMDP.Walk.cost DetMDP.horizonCost
  rw [← Fin.sum_univ_eq_sum_range]
  rfl

open Classical in
noncomputable def hwPol (M : DetMDP S) {T : ℕ} (W : M.Walk T) : M.Policy := fun s t =>
  if h1 : t < T then
    (if h : W.x ⟨t, by omega⟩ = s then hwTr M h (W.e ⟨t, h1⟩) else Classical.arbitrary _)
  else Classical.arbitrary _

theorem hwPol_spec (M : DetMDP S) {T : ℕ} (W : M.Walk T) (t : ℕ) (h1 : t < T) :
    M.next (W.x ⟨t, by omega⟩) (hwPol M W (W.x ⟨t, by omega⟩) t) = W.x ⟨t + 1, by omega⟩ ∧
    M.c (W.x ⟨t, by omega⟩) (hwPol M W (W.x ⟨t, by omega⟩) t) = M.c (W.x ⟨t, by omega⟩) (W.e ⟨t, h1⟩) := by
  unfold hwPol
  rw [dif_pos h1, dif_pos rfl, hwTr_next, hwTr_c]
  exact ⟨W.valid ⟨t, h1⟩, rfl⟩

theorem hwPol_path (M : DetMDP S) (s₀ : S) {T : ℕ} (W : M.Walk T) (hs : W.x 0 = s₀) :
    ∀ t (ht : t ≤ T), M.path s₀ (hwPol M W) t = W.x ⟨t, by omega⟩ := by
  intro t
  induction t with
  | zero => intro _; rw [← hs]; rfl
  | succ t ih =>
    intro ht
    show M.next (M.path s₀ (hwPol M W) t) (hwPol M W (M.path s₀ (hwPol M W) t) t) = _
    rw [ih (by omega)]
    exact (hwPol_spec M W t (by omega)).1

theorem hwPol_cost (M : DetMDP S) (s₀ : S) {T : ℕ} (W : M.Walk T) (hs : W.x 0 = s₀) :
    M.horizonCost s₀ (hwPol M W) T = W.cost := by
  unfold DetMDP.horizonCost DetMDP.Walk.cost
  rw [← Fin.sum_univ_eq_sum_range]
  apply Finset.sum_congr rfl
  intro t _
  unfold DetMDP.stageCost
  rw [hwPol_path M s₀ W hs t (by omega)]
  exact (hwPol_spec M W t t.isLt).2

theorem hw_finite (M : DetMDP S) (s₀ : S) (T : ℕ) :
    {y : ℝ | ∃ W : M.Walk T, W.x 0 = s₀ ∧ y = W.cost}.Finite := by
  apply (Set.finite_range (fun f : Fin T → (Σ s : S, M.D s) =>
    ∑ t : Fin T, M.c (f t).1 (f t).2)).subset
  rintro y ⟨W, _, rfl⟩
  exact ⟨fun t => ⟨W.x t.castSucc, W.e t⟩, rfl⟩
end

theorem solution {S : Type} [Fintype S] (M : DetMDP S) (s₀ : S) (T : ℕ) :
    IsLeast {y : ℝ | ∃ W : M.Walk T, W.x 0 = s₀ ∧ y = W.cost}
      (M.optHorizon s₀ T) := by
  set A := {y : ℝ | ∃ W : M.Walk T, W.x 0 = s₀ ∧ y = W.cost}
  have hne : A.Nonempty := by
    let δ : M.Policy := fun s _ => Classical.arbitrary _
    exact ⟨_, hwPathWalk M s₀ δ T, rfl, rfl⟩
  obtain ⟨m, hmA, hmin⟩ := (hw_finite M s₀ T).exists_minimal hne
  have hlow : ∀ y ∈ A, m ≤ y := by
    intro y hy
    by_contra hlt
    push_neg at hlt
    exact absurd (hmin hy hlt.le) (by intro h; linarith)
  obtain ⟨W, hW0, rfl⟩ := hmA
  have hpol : ∀ δ : M.Policy, W.cost ≤ M.horizonCost s₀ δ T := by
    intro δ
    rw [← hwPathWalk_cost]
    exact hlow _ ⟨_, rfl, rfl⟩
  have hbdd : BddBelow (Set.range fun δ : M.Policy => M.horizonCost s₀ δ T) :=
    ⟨W.cost, by rintro _ ⟨δ, rfl⟩; exact hpol δ⟩
  have heq : M.optHorizon s₀ T = W.cost := by
    unfold DetMDP.optHorizon
    apply le_antisymm
    · exact (ciInf_le hbdd (hwPol M W)).trans (le_of_eq (hwPol_cost M s₀ W hW0))
    · haveI : Nonempty M.Policy := ⟨fun s _ => Classical.arbitrary _⟩
      exact le_ciInf hpol
  rw [heq]
  exact ⟨⟨W, hW0, rfl⟩, hlow⟩
