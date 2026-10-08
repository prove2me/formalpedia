-- Prove2me | solution 1 for MatousekLP.SparseRecovery.two_r_le_m
-- status  : ACCEPTED   (prove)
-- author  : @moona3k
-- created : 2026-10-05T03:57:18.975729+00:00
-- url     : https://prove2.me/submissions/b91bd8c5-cd39-4dc3-a669-49ddb896d240

import Definitions.Def_MatousekLP_SparseRecovery_BasisPursuit
import Mathlib

open Matrix

theorem solution {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (r : ℕ) (hmn : m < n)
    (hii : ∀ S : Finset (Fin n), S.card ≤ 2 * r →
      LinearIndependent ℝ (fun j : S => Aᵀ (j : Fin n))) :
    2 * r ≤ m := by
  by_contra h
  push_neg at h
  -- a set of `m + 1` columns
  obtain ⟨S, -, hS⟩ := Finset.exists_subset_card_eq (s := (Finset.univ : Finset (Fin n)))
    (n := m + 1) (by simpa using hmn)
  have hli := hii S (by omega)
  have := hli.fintype_card_le_finrank
  simp [hS] at this
