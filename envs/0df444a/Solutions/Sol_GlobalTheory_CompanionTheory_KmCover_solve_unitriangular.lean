-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.KmCover.solve_unitriangular
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T12:42:15.979607+00:00
-- url     : https://prove2.me/submissions/b2cb68b8-193f-4d03-a768-7c198c9941cf

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_ExistsUdlOfIsUnit
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_SolveUnitriangular
import Theorems.Thm_GlobalTheory_CompanionTheory_KmCover_mul_congr_one

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.KmCover
open Matrix
variable {R : Type*} [CommRing R] {n : ℕ}
namespace GlobalTheory.CompanionTheory.KmCover
theorem _root_.solution (J : Ideal R) (T V : Fin n → Fin n → Set R)
    (hdec : ∀ i j, i < j → ∀ c ∈ J, ∃ t v : R, t ∈ T i j ∧ v ∈ V i j ∧ t ∈ J ∧ v ∈ J ∧ c = t + v)
    (u : Matrix (Fin n) (Fin n) R)
    (hu : ∀ i j, u i j - (1 : Matrix (Fin n) (Fin n) R) i j ∈ J)
    (hlow : ∀ i j, j < i → u i j = 0) (hdiag : ∀ i, u i i = 1) :
    ∃ r w : Matrix (Fin n) (Fin n) R,
      (∀ i j, j < i → r i j = 0) ∧ (∀ i, r i i = 1) ∧ (∀ i j, i < j → r i j ∈ T i j) ∧
      (∀ i j, j < i → w i j = 0) ∧ (∀ i, w i i = 1) ∧ (∀ i j, i < j → w i j ∈ V i j) ∧
      u = r * w := by
  have key : ∀ d : ℕ, ∃ r w : Matrix (Fin n) (Fin n) R,
      (∀ i j, j < i → r i j = 0) ∧ (∀ i, r i i = 1) ∧
      (∀ i j, j < i → w i j = 0) ∧ (∀ i, w i i = 1) ∧
      (∀ i j, i < j → j.val ≤ i.val + d → r i j ∈ T i j ∧ w i j ∈ V i j) ∧
      (∀ i j, i.val + d < j.val → r i j = 0 ∧ w i j = 0) ∧
      (∀ i j, r i j - (1 : Matrix (Fin n) (Fin n) R) i j ∈ J) ∧
      (∀ i j, w i j - (1 : Matrix (Fin n) (Fin n) R) i j ∈ J) ∧
      (∀ i j, j.val ≤ i.val + d → (r * w) i j = u i j) := by
    intro d
    induction d with
    | zero =>
      refine ⟨1, 1, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · intro i j h
        exact Matrix.one_apply_ne (ne_of_gt h)
      · intro i
        exact Matrix.one_apply_eq i
      · intro i j h
        exact Matrix.one_apply_ne (ne_of_gt h)
      · intro i
        exact Matrix.one_apply_eq i
      · intro i j h h2
        have : i.val < j.val := h
        omega
      · intro i j h
        have : i ≠ j := by
          intro e
          subst e
          omega
        exact ⟨Matrix.one_apply_ne this, Matrix.one_apply_ne this⟩
      · intro i j
        simp
      · intro i j
        simp
      · intro i j h
        rw [mul_one]
        rcases Nat.lt_or_ge j.val i.val with h1 | h1
        · rw [hlow i j h1]
          exact Matrix.one_apply_ne (by
            intro e
            subst e
            omega)
        · have : i = j := Fin.ext (by omega)
          subst this
          rw [hdiag i]
          exact Matrix.one_apply_eq i
    | succ d ih =>
      obtain ⟨r, w, hrl, hrd, hwl, hwd, hin, hout, hrJ, hwJ, hp⟩ := ih
      have hc : ∀ i j, i < j → u i j - (r * w) i j ∈ J := by
        intro i j h
        have h1 := mul_congr_one hrJ hwJ i j
        have h2 := hu i j
        have := J.sub_mem h2 h1
        simpa using this
      have hex : ∀ i j, ∃ t v : R, i < j → t ∈ T i j ∧ v ∈ V i j ∧ t ∈ J ∧ v ∈ J ∧
          u i j - (r * w) i j = t + v := by
        intro i j
        by_cases h : i < j
        · obtain ⟨t, v, h1⟩ := hdec i j h _ (hc i j h)
          exact ⟨t, v, fun _ => h1⟩
        · exact ⟨0, 0, fun h' => absurd h' h⟩
      choose t v htv using hex
      obtain ⟨r', hr'⟩ : ∃ r' : Matrix (Fin n) (Fin n) R,
          ∀ i j, r' i j = if j.val = i.val + d + 1 then t i j else r i j :=
        ⟨fun i j => if j.val = i.val + d + 1 then t i j else r i j, fun _ _ => rfl⟩
      obtain ⟨w', hw'⟩ : ∃ w' : Matrix (Fin n) (Fin n) R,
          ∀ i j, w' i j = if j.val = i.val + d + 1 then v i j else w i j :=
        ⟨fun i j => if j.val = i.val + d + 1 then v i j else w i j, fun _ _ => rfl⟩
      have hr'l : ∀ i j, j < i → r' i j = 0 := by
        intro i j h
        have h' : j.val < i.val := h
        rw [hr', if_neg (by omega), hrl i j h]
      have hw'l : ∀ i j, j < i → w' i j = 0 := by
        intro i j h
        have h' : j.val < i.val := h
        rw [hw', if_neg (by omega), hwl i j h]
      have hr'd : ∀ i, r' i i = 1 := by
        intro i
        rw [hr', if_neg (by omega), hrd i]
      have hw'd : ∀ i, w' i i = 1 := by
        intro i
        rw [hw', if_neg (by omega), hwd i]
      refine ⟨r', w', hr'l, hr'd, hw'l, hw'd, ?_, ?_, ?_, ?_, ?_⟩
      · intro i j h h2
        rw [hr', hw']
        by_cases e : j.val = i.val + d + 1
        · rw [if_pos e, if_pos e]
          exact ⟨(htv i j h).1, (htv i j h).2.1⟩
        · rw [if_neg e, if_neg e]
          exact hin i j h (by omega)
      · intro i j h
        rw [hr', hw', if_neg (by omega), if_neg (by omega)]
        exact hout i j (by omega)
      · intro i j
        rw [hr']
        by_cases e : j.val = i.val + d + 1
        · have hij : i < j := by
            rw [Fin.lt_def]
            omega
          rw [if_pos e, Matrix.one_apply_ne (ne_of_lt hij), sub_zero]
          exact (htv i j hij).2.2.1
        · rw [if_neg e]
          exact hrJ i j
      · intro i j
        rw [hw']
        by_cases e : j.val = i.val + d + 1
        · have hij : i < j := by
            rw [Fin.lt_def]
            omega
          rw [if_pos e, Matrix.one_apply_ne (ne_of_lt hij), sub_zero]
          exact (htv i j hij).2.2.2.1
        · rw [if_neg e]
          exact hwJ i j
      · intro i j h
        by_cases e : j.val = i.val + d + 1
        · have hij : i < j := by
            rw [Fin.lt_def]
            omega
          have hneq : i ≠ j := ne_of_lt hij
          have hold := hout i j (by omega)
          have hsum : (r' * w') i j = (r * w) i j + t i j + v i j := by
            have hterm : ∀ k, r' i k * w' k j =
                r i k * w k j + (if k = j then t i j else 0) + (if k = i then v i j else 0) := by
              intro k
              by_cases kj : k = j
              · subst kj
                rw [if_pos rfl, if_neg (Ne.symm hneq), hw'd, hwd, hold.1, hr', if_pos e]
                ring
              · by_cases ki : k = i
                · subst ki
                  rw [if_neg kj, if_pos rfl, hr'd, hrd, hold.2, hw', if_pos e]
                  ring
                · rw [if_neg kj, if_neg ki]
                  rcases lt_or_gt_of_ne ki with h1 | h1
                  · rw [hr'l i k h1, hrl i k h1]
                    ring
                  · rcases lt_or_gt_of_ne kj with h2 | h2
                    · have a1 : i.val < k.val := h1
                      have a2 : k.val < j.val := h2
                      rw [hr', hw', if_neg (by omega), if_neg (by omega)]
                      ring
                    · rw [hw'l k j h2, hwl k j h2]
                      ring
            rw [Matrix.mul_apply, Finset.sum_congr rfl (fun k _ => hterm k),
              Finset.sum_add_distrib, Finset.sum_add_distrib, Matrix.mul_apply]
            simp
          rw [hsum]
          have := (htv i j hij).2.2.2.2
          linear_combination -this
        · have hle : j.val ≤ i.val + d := by omega
          rw [← hp i j hle, Matrix.mul_apply, Matrix.mul_apply]
          refine Finset.sum_congr rfl fun k _ => ?_
          by_cases h1 : k.val = i.val + d + 1
          · have : j < k := by
              rw [Fin.lt_def]
              omega
            rw [hw'l k j this, hwl k j this]
            ring
          · by_cases h2 : j.val = k.val + d + 1
            · have : k < i := by
                rw [Fin.lt_def]
                omega
              rw [hr'l i k this, hrl i k this]
              ring
            · rw [hr', hw', if_neg h1, if_neg h2]
  obtain ⟨r, w, hrl, hrd, hwl, hwd, hin, -, -, -, hp⟩ := key n
  refine ⟨r, w, hrl, hrd, ?_, hwl, hwd, ?_, ?_⟩
  · intro i j h
    exact (hin i j h (by omega)).1
  · intro i j h
    exact (hin i j h (by omega)).2
  · ext i j
    exact (hp i j (by omega)).symm
end GlobalTheory.CompanionTheory.KmCover
