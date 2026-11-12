-- Prove2me | solution 1 for HararySachs.Hyper.lemma_4
-- status  : ACCEPTED   (prove)
-- author  : @milia
-- created : 2026-11-12T03:37:22.050439+00:00
-- url     : https://prove2.me/submissions/b513ef14-50b2-400b-95a1-2c9d2ced5383

import Mathlib
import Definitions.Def_HararySachs_Hyper_Operators
import Theorems.Thm_HararySachs_Hyper_coeff_eq_numTours
import Theorems.Thm_HararySachs_Hyper_numTours_pos_iff

open HararySachs.Hyper

theorem solution {n L : ℕ} (hL : 0 < L) (m : ArcMult n)
    (hm : (∑ u : Fin n, ∑ v : Fin n, m u v) = L) :
    (MvPolynomial.coeff 0 (diffMonomial m (trPow n L)) ≠ 0 ↔ IsEulerian m) ∧
      (IsEulerian m →
        MvPolynomial.coeff 0 (diffMonomial m (trPow n L)) =
          (numTours m hL : ℚ)) := by
  rw [coeff_eq_numTours hL m hm]
  refine ⟨?_, fun _ => rfl⟩
  rw [← numTours_pos_iff hL m hm, Nat.cast_ne_zero, Nat.pos_iff_ne_zero]
