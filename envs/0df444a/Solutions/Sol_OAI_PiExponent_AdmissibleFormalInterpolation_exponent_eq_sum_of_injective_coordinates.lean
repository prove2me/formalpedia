-- Prove2me | solution 1 for OAI.PiExponent.AdmissibleFormalInterpolation.exponent_eq_sum_of_injective_coordinates
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-19T10:21:51.630134+00:00
-- url     : https://prove2.me/submissions/485bff90-5a27-490d-918b-e2da53d20f85

import Definitions.Def_OAI_PiExponent_FormalJetShear
import Mathlib.Algebra.BigOperators.Finsupp.Basic

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open scoped BigOperators

theorem solution
    {σ : Type*} [DecidableEq σ] {m : ℕ}
    (v : Fin m → σ) (x0 : σ)
    (hv : Function.Injective v)
    (hdisj : ∀ i : Fin m, v i ≠ x0)
    (e : Fin m → ℕ) (d : σ →₀ ℕ)
    (hbase : d x0 = 0)
    (hcoord : ∀ i : Fin m, d (v i) = e i)
    (hout : ∀ x : σ, x ≠ x0 → (∀ i : Fin m, v i ≠ x) → d x = 0) :
    d = ∑ i : Fin m, Finsupp.single (v i) (e i) := by
  classical
  ext x
  rw [Finsupp.finset_sum_apply]
  simp only [Finsupp.single_apply]
  by_cases hx0 : x = x0
  · subst x
    simp [hbase, hdisj]
  · by_cases hcoordx : ∃ i : Fin m, v i = x
    · obtain ⟨i, hi⟩ := hcoordx
      have hsum : (∑ j : Fin m, (if v j = x then e j else 0)) = e i := by
        rw [Finset.sum_eq_single i]
        · simp [hi]
        · intro j hj hji
          have hneq : v j ≠ x := by
            intro h
            apply hji
            exact hv (h.trans hi.symm)
          simp [hneq]
        · intro hnot
          exact False.elim (hnot (Finset.mem_univ i))
      rw [hsum, ← hi, hcoord]
    · have hzero : (∑ i : Fin m, (if v i = x then e i else 0)) = 0 := by
        apply Finset.sum_eq_zero
        intro i hi
        have hneq : v i ≠ x := by
          intro h
          exact hcoordx ⟨i, h⟩
        simp [hneq]
      rw [hzero]
      exact hout x hx0 (fun i h => hcoordx ⟨i, h⟩)
