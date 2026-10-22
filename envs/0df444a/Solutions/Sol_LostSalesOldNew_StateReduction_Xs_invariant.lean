-- Prove2me | solution 1 for LostSalesOldNew.StateReduction.Xs_invariant
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-21T06:50:34.498468+00:00
-- url     : https://prove2.me/submissions/3dc0407f-b4cc-4269-9a33-9784d7872103

import Mathlib
import Definitions.Def_LostSalesOldNew_StateReduction_Model

set_option autoImplicit false
open LostSalesOldNew.StateReduction

lemma LSS_snoc_tail {L : ℕ} (x : Fin L → ℝ) (z : ℝ) (l : Fin L) :
    ∑ m : Fin L, (if (l : ℕ) ≤ (m : ℕ) then (Fin.snoc (α := fun _ => ℝ) x z) m.succ else 0)
      = v x ((l : ℕ) + 1) + z := by
  have h1 : ∑ m' : Fin (L + 1), (if (l : ℕ) + 1 ≤ (m' : ℕ) then (Fin.snoc (α := fun _ => ℝ) x z) m' else 0)
      = v x ((l : ℕ) + 1) + z := by
    rw [Fin.sum_univ_castSucc]
    simp only [Fin.val_castSucc, Fin.snoc_castSucc, Fin.snoc_last, Fin.val_last, v]
    have : (l : ℕ) + 1 ≤ L := l.isLt
    simp [this]
  rw [← h1, Fin.sum_univ_succ]
  simp only [Fin.val_zero, Fin.val_succ]
  simp

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

theorem solution {L : ℕ} (hL : 0 < L)
    (s : Fin (L + 1) → ℝ) (hs : IsLevelVector s)
    (z : (Fin L → ℝ) → ℝ) (hz : z ∈ Zs s) (x : Fin L → ℝ) (hx : x ∈ Xs s)
    (d : ℝ) (hd : 0 ≤ d) :
    next x (z x) d ∈ Xs s := by
  obtain ⟨hz0, hz1, hz2⟩ := hz
  obtain ⟨hx0, hx1⟩ := hx
  have hzx : 0 ≤ z x := hz0 x hx0
  have hy : ∀ i : Fin (L + 1), 0 ≤ (Fin.snoc (α := fun _ => ℝ) x (z x)) i := by
    intro i
    refine Fin.lastCases ?_ (fun j => ?_) i
    · simpa using hzx
    · simpa using hx0 j
  have hxs : x ∈ Xs s := ⟨hx0, hx1⟩
  have hM : 0 ≤ max (x ⟨0, hL⟩ - d) 0 := le_max_right _ _
  refine ⟨?_, ?_⟩
  · intro i
    rw [LSS_next_apply hL]
    have := hy i.succ
    split_ifs <;> linarith
  · intro l
    have key : v (next x (z x) d) (l : ℕ) =
        (if (l : ℕ) = 0 then max (x ⟨0, hL⟩ - d) 0 else 0) + (v x ((l : ℕ) + 1) + z x) := by
      rw [← LSS_snoc_tail x (z x) l]
      unfold v
      have e : ∀ m : Fin L, (if (l : ℕ) ≤ (m : ℕ) then next x (z x) d m else 0) =
          (if m = ⟨0, hL⟩ then (if (l : ℕ) = 0 then max (x ⟨0, hL⟩ - d) 0 else 0) else 0) +
          (if (l : ℕ) ≤ (m : ℕ) then (Fin.snoc (α := fun _ => ℝ) x (z x)) m.succ else 0) := by
        intro m
        rw [LSS_next_apply hL]
        by_cases hm : m = ⟨0, hL⟩
        · have hm' : (m : ℕ) = 0 := by rw [hm]
          by_cases hl : (l : ℕ) = 0
          · simp [hm, hl]
          · simp [hm, hl]
        · have hm' : (m : ℕ) ≠ 0 := fun h => hm (Fin.ext h)
          simp [hm, hm']
      simp only [e, Finset.sum_add_distrib, Finset.sum_ite_eq', Finset.mem_univ, if_true]
    rw [key]
    have hl1 : (l : ℕ) + 1 < L + 1 + 1 := by omega
    by_cases hl : (l : ℕ) = 0
    · rw [if_pos hl]
      have h0 := hz2 x hxs ⟨0, by omega⟩
      have hv0 : v x 0 = v x 1 + x ⟨0, hL⟩ := by
        unfold v
        have e : ∀ m : Fin L, (if 0 ≤ (m : ℕ) then x m else 0) =
            (if 1 ≤ (m : ℕ) then x m else 0) + (if m = ⟨0, hL⟩ then x m else 0) := by
          intro m
          by_cases hm : m = ⟨0, hL⟩
          · have hm' : (m : ℕ) = 0 := by rw [hm]
            simp [hm, hm']
          · have hm' : (m : ℕ) ≠ 0 := fun h => hm (Fin.ext h)
            have : 1 ≤ (m : ℕ) := by omega
            simp [hm, this]
        simp only [e, Finset.sum_add_distrib, Finset.sum_ite_eq', Finset.mem_univ, if_true]
      have hv1 : (l : ℕ) + 1 = 1 := by omega
      have hlc : l.castSucc = (⟨0, by omega⟩ : Fin (L + 1)) := Fin.ext hl
      rw [hv1, hlc]
      have hxx : max (x ⟨0, hL⟩ - d) 0 ≤ x ⟨0, hL⟩ := max_le (by linarith) (hx0 _)
      linarith
    · rw [if_neg hl]
      have := hz2 x hxs ⟨(l : ℕ) + 1, by omega⟩
      have hanti := hs.1 (show l.castSucc ≤ (⟨(l : ℕ) + 1, by omega⟩ : Fin (L + 1)) from by
        simp [Fin.le_def])
      simp only at this
      linarith
