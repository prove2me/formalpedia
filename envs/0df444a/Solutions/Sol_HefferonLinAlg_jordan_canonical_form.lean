-- Prove2me | solution 1 for HefferonLinAlg.jordan_canonical_form
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-08-07T14:03:20.216817+00:00
-- url     : https://prove2.me/submissions/925ed2d9-9958-4086-b927-51a1bd5c8882

import Definitions.Def_HefferonLinAlg_jordan
import Theorems.Thm_HefferonLinAlg_jordan_form_exists
import Theorems.Thm_HefferonLinAlg_jordanBlocks_unique

open Matrix
open HefferonLinAlg

theorem solution {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ) :
    ∃! B : Multiset (ℕ × ℂ),
      ∃ (k : ℕ) (sz : Fin k → ℕ) (lam : Fin k → ℂ),
        IsJordanFormOf A sz lam ∧ jordanBlocks sz lam = B := by
  obtain ⟨k, sz, lam, hJ⟩ := HefferonLinAlg.jordan_form_exists A
  refine ⟨jordanBlocks sz lam, ⟨k, sz, lam, hJ, rfl⟩, ?_⟩
  rintro B ⟨k', sz', lam', hJ', rfl⟩
  exact HefferonLinAlg.jordanBlocks_unique hJ' hJ
