-- Prove2me | solution 1 for KSATSingleFlip.Connect.insertion_implies_replacement
-- status  : ACCEPTED   (prove)
-- author  : @wcysai
-- created : 2026-11-13T09:37:16.499632+00:00
-- url     : https://prove2.me/submissions/63d8a9d0-032e-49b1-bd79-a709ccefcf8a

import Mathlib
set_option autoImplicit false

theorem solution {A : Type} (j : ℕ) (F : List A → ℝ) (L : ℝ)
    (hins : ∀ (xs : List A) (i : ℕ) (a : A), |F (xs.insertIdx i a) - F xs| ≤ L)
    (x : Fin j → A) (i : Fin j) (a : A) :
    |F (List.ofFn x) - F (List.ofFn (Function.update x i a))| ≤ 2*L := by
  classical
  let l := List.ofFn x
  have hi : i.val < l.length := by simp [l, i.isLt]
  have hupdate : List.ofFn (Function.update x i a) = l.set i.val a := by
    apply List.ext_getElem
    · simp [l]
    · intro k hk hk'
      simp only [List.getElem_ofFn, List.getElem_set]
      by_cases h : i.val = k
      · subst k
        simp
      · have hfin : (⟨k, by simpa [l] using hk⟩ : Fin j) ≠ i := by
          intro he
          have := congrArg Fin.val he
          exact h this.symm
        simp [Function.update_of_ne hfin, h, l]
  let b := l.eraseIdx i.val
  have horig : b.insertIdx i.val (x i) = l := by
    simpa [b, l] using (List.insertIdx_eraseIdx_getElem hi)
  have hnew : b.insertIdx i.val a = List.ofFn (Function.update x i a) := by
    rw [hupdate]
    exact List.insertIdx_eraseIdx_self (Nat.ne_of_lt hi) a
  have h₁ := hins b i.val (x i)
  have h₂ := hins b i.val a
  rw [horig] at h₁
  rw [hnew] at h₂
  calc
    |F (List.ofFn x) - F (List.ofFn (Function.update x i a))|
        ≤ |F (List.ofFn x) - F b| + |F b - F (List.ofFn (Function.update x i a))| := abs_sub_le _ _ _
    _ ≤ L + L := by rw [abs_sub_comm (F b)]; exact add_le_add h₁ h₂
    _ = 2*L := by ring
