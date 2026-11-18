-- Prove2me | solution 1 for Kyprianou.Ch06.finiteOrderedTimeGridCountTelescoping
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-17T07:17:03.678091+00:00
-- url     : https://prove2.me/submissions/d0a33ca3-a514-4753-b60f-0121b1d07f6b

import Mathlib
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open scoped NNReal
set_option autoImplicit false

theorem solution
    (k : Nat) (grid : Fin (k + 1) → NNReal)
    (hGrid : Monotone grid) (hZero : grid 0 = 0)
    (F : NNReal → Nat) (hF : Monotone F) (hFZero : F 0 = 0)
    (r : Nat) (hr : r ≤ k) :
    F (grid ⟨r, Nat.lt_succ_of_le hr⟩) =
      ∑ j ∈ (Finset.univ.filter (fun j : Fin k => j.val < r)),
        (F (grid j.succ) - F (grid j.castSucc)) := by
  classical
  have hAll : ∀ (n : Nat) (hn : n ≤ k),
      F (grid ⟨n, Nat.lt_succ_of_le hn⟩) =
        ∑ j ∈ (Finset.univ.filter
          (fun j : Fin k => j.val < n)),
          (F (grid j.succ) - F (grid j.castSucc)) := by
    intro n
    induction n with
    | zero =>
        intro _
        simp [hZero, hFZero]
    | succ n ih =>
        intro hn
        have hnk : n < k := by omega
        let j : Fin k := ⟨n, hnk⟩
        have hj : j ∉ (Finset.univ.filter
            (fun t : Fin k => t.val < n)) := by
          simp [j]
        have hFilter :
            (Finset.univ.filter
              (fun t : Fin k => t.val < n + 1)) =
            insert j (Finset.univ.filter
              (fun t : Fin k => t.val < n)) := by
          ext t
          simp only [Finset.mem_filter, Finset.mem_univ,
            true_and, Finset.mem_insert]
          change t.val < n + 1 ↔ t = j ∨ t.val < n
          constructor
          · intro ht
            by_cases heq : t.val = n
            · left
              exact Fin.ext heq
            · right
              omega
          · rintro (ht | ht)
            · subst t
              change n < n + 1
              omega
            · omega
        rw [hFilter, Finset.sum_insert hj]
        have ih' := ih (by omega : n ≤ k)
        have hStep : F (grid ⟨n, by omega⟩) ≤
            F (grid ⟨n + 1, by omega⟩) := by
          apply hF
          apply hGrid
          exact Fin.mk_le_mk.mpr (by omega)
        change F (grid ⟨n + 1, by omega⟩) =
          (F (grid ⟨n + 1, by omega⟩) -
            F (grid ⟨n, by omega⟩)) +
            ∑ t ∈ (Finset.univ.filter
              (fun t : Fin k => t.val < n)),
              (F (grid t.succ) - F (grid t.castSucc))
        rw [← ih']
        omega
  exact hAll r hr
