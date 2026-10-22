-- Prove2me | solution 1 for LostSalesOldNew.StateReduction.reaches_Xs
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-21T07:05:29.733577+00:00
-- url     : https://prove2.me/submissions/f2e806a3-a4c2-4469-b9ec-ece90076b805

import Mathlib
import Definitions.Def_LostSalesOldNew_StateReduction_Model

set_option autoImplicit false
open LostSalesOldNew.StateReduction

lemma LSS_next_apply {L : ℕ} (hL : 0 < L) (x : Fin L → ℝ) (z d : ℝ) (i : Fin L) :
    next x z d i = (if (i : ℕ) = 0 then max (x ⟨0, hL⟩ - d) 0 else 0) +
      (Fin.snoc (α := fun _ => ℝ) x z) i.succ := by
  unfold next shift
  by_cases h : (i : ℕ) = 0
  · have h0 : (Fin.snoc (α := fun _ => ℝ) x z) (0 : Fin (L + 1)) = x ⟨0, hL⟩ := by
      have : (0 : Fin (L + 1)) = Fin.castSucc ⟨0, hL⟩ := Fin.ext rfl
      rw [this, Fin.snoc_castSucc]
    simp [h, h0]
  · simp [h]

lemma LSS_snoc_succ {L : ℕ} (x : Fin L → ℝ) (z : ℝ) (m : Fin L) :
    (Fin.snoc (α := fun _ => ℝ) x z) m.succ =
      if h : (m : ℕ) + 1 < L then x ⟨(m : ℕ) + 1, h⟩ else z := by
  by_cases h : (m : ℕ) + 1 < L
  · have : m.succ = Fin.castSucc (⟨(m : ℕ) + 1, h⟩ : Fin L) := Fin.ext rfl
    rw [this, Fin.snoc_castSucc]
    simp [h]
  · have : m.succ = Fin.last L := Fin.ext (by simp; omega)
    rw [this, Fin.snoc_last]
    simp [h]

theorem solution {L : ℕ} (hL : 0 < L)
    (s : Fin (L + 1) → ℝ) (hs : IsLevelVector s)
    (z : (Fin L → ℝ) → ℝ) (hz : z ∈ Zs s) (x : Fin L → ℝ) (hx : ∀ i, 0 ≤ x i)
    (ds : ℕ → ℝ) (hds : ∀ t, 0 ≤ ds t)
    (hdiv : Filter.Tendsto (fun n => ∑ t ∈ Finset.range n, ds t) Filter.atTop Filter.atTop) :
    ∃ t, traj z x ds t ∈ Xs s := by
  by_contra hcon
  push_neg at hcon
  obtain ⟨hz0, hz1, hz2⟩ := hz
  have hnn : ∀ t i, 0 ≤ traj z x ds t i := by
    intro t
    induction t with
    | zero => exact hx
    | succ t ih =>
      intro i
      show 0 ≤ next (traj z x ds t) (z (traj z x ds t)) (ds t) i
      rw [LSS_next_apply hL, LSS_snoc_succ]
      have h1 : 0 ≤ max (traj z x ds t ⟨0, hL⟩ - ds t) 0 := le_max_right _ _
      have h2 := hz0 _ ih
      split_ifs <;> first | linarith | exact add_nonneg (by linarith) (ih _)
  have hzero : ∀ t, z (traj z x ds t) = 0 := fun t => hz1 _ (hnn t) (hcon t)
  have hstep : ∀ t, traj z x ds (t + 1) = next (traj z x ds t) 0 (ds t) := by
    intro t
    show next (traj z x ds t) (z (traj z x ds t)) (ds t) = _
    rw [hzero t]
  have htail : ∀ t (m : Fin L), 1 ≤ (m : ℕ) → L ≤ (m : ℕ) + t → traj z x ds t m = 0 := by
    intro t
    induction t with
    | zero => intro m _ h; have := m.isLt; omega
    | succ t ih =>
      intro m hm h
      rw [hstep, LSS_next_apply hL, LSS_snoc_succ, if_neg (by omega), zero_add]
      by_cases h' : (m : ℕ) + 1 < L
      · rw [dif_pos h']
        exact ih _ (by simp) (by simp; omega)
      · rw [dif_neg h']
  have hy : ∀ t, L ≤ t → traj z x ds (t + 1) ⟨0, hL⟩ = max (traj z x ds t ⟨0, hL⟩ - ds t) 0 := by
    intro t ht
    rw [hstep, LSS_next_apply hL, LSS_snoc_succ]
    simp only [if_true]
    by_cases h' : 1 < L
    · rw [dif_pos (by simpa using h')]
      have := htail t ⟨1, h'⟩ (by simp) (by simp; omega)
      simp [this]
    · rw [dif_neg (by simpa using h')]
      simp
  have hyn : ∀ n, traj z x ds (L + n) ⟨0, hL⟩ =
      max (traj z x ds L ⟨0, hL⟩ - ∑ u ∈ Finset.range n, ds (L + u)) 0 := by
    intro n
    induction n with
    | zero => simp [le_of_lt, max_eq_left (hnn L _)]
    | succ n ih =>
      rw [← add_assoc, hy (L + n) (by omega), ih, Finset.sum_range_succ]
      have := hds (L + n)
      rcases le_total (traj z x ds L ⟨0, hL⟩ - ∑ u ∈ Finset.range n, ds (L + u)) 0 with h | h
      · rw [max_eq_right h, max_eq_right (by linarith), max_eq_right (by linarith)]
      · rw [max_eq_left h]
        rcases le_total (traj z x ds L ⟨0, hL⟩ - ∑ u ∈ Finset.range n, ds (L + u) - ds (L + n)) 0 with h2 | h2
        · rw [max_eq_right h2, max_eq_right (by linarith)]
        · rw [max_eq_left h2, max_eq_left (by linarith)]
          ring_nf
  set C : ℝ := traj z x ds L ⟨0, hL⟩ + ∑ t ∈ Finset.range L, ds t with hC
  obtain ⟨M, hM⟩ := Filter.eventually_atTop.1 (Filter.tendsto_atTop.1 hdiv C)
  have hsum := hM (L + M) (by omega)
  rw [Finset.sum_range_add] at hsum
  have hy0 : traj z x ds (L + M) ⟨0, hL⟩ = 0 := by
    rw [hyn]
    apply max_eq_right
    linarith
  apply hcon (L + M)
  have hall : ∀ m : Fin L, traj z x ds (L + M) m = 0 := by
    intro m
    by_cases hm : (m : ℕ) = 0
    · have : m = ⟨0, hL⟩ := Fin.ext hm
      rw [this]; exact hy0
    · exact htail _ m (by omega) (by omega)
  refine ⟨hnn _, ?_⟩
  intro l
  have hv : v (traj z x ds (L + M)) l = 0 := by
    unfold v
    apply Finset.sum_eq_zero
    intro m _
    rw [hall m]
    simp
  rw [hv]
  have := hs.1 (Fin.le_last l.castSucc)
  linarith [hs.2]
