-- Prove2me | solution 1 for OAI.PiExponent.eventualLogJetSurjective_transverseForSpatialVolume_360483bd
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-24T08:44:37.602716+00:00
-- url     : https://prove2.me/submissions/161a5f2a-5fc7-43e2-ad56-d3c969a8d95f

import Mathlib
import Definitions.Def_PiExponent_DeterminantSetup
import Definitions.Def_eventualTransverseJetSurjectiveForSpatialVolume_360483bd

open scoped BigOperators

namespace S108LJ

open MvPolynomial

lemma eval_cases {n : ℕ} (a : MvPolynomial (Fin n) ℂ) (f : MvPolynomial (Fin (n + 1)) ℂ) :
    aeval (Fin.cases a X : Fin (n + 1) → MvPolynomial (Fin n) ℂ) f =
      Polynomial.eval a (finSuccEquiv ℂ n f) := by
  induction f using MvPolynomial.induction_on with
  | C r => simp [finSuccEquiv_apply]
  | add p q hp hq => rw [map_add, map_add, Polynomial.eval_add, hp, hq]
  | mul_X p i hp =>
    rw [map_mul, map_mul, Polynomial.eval_mul, hp, aeval_X]
    congr 1
    cases i using Fin.cases with
    | zero => simp [finSuccEquiv_X_zero]
    | succ j => simp [finSuccEquiv_X_succ]

lemma coeff_eval_zero {n : ℕ} (f : MvPolynomial (Fin (n + 1)) ℂ) (e : Fin n →₀ ℕ) :
    coeff e (aeval (Fin.cases 0 X : Fin (n + 1) → MvPolynomial (Fin n) ℂ) f) =
      coeff (e.cons 0) f := by
  rw [eval_cases, ← Polynomial.coeff_zero_eq_eval_zero, finSuccEquiv_coeff_coeff]

lemma coeff_eval_one_ne {n : ℕ} (f : MvPolynomial (Fin (n + 1)) ℂ) (e : Fin n →₀ ℕ)
    (h : coeff e (aeval (Fin.cases 1 X : Fin (n + 1) → MvPolynomial (Fin n) ℂ) f) ≠ 0) :
    ∃ k : ℕ, coeff (e.cons k) f ≠ 0 := by
  rw [eval_cases, Polynomial.eval_eq_sum_range, coeff_sum] at h
  obtain ⟨k, -, hk⟩ := Finset.exists_ne_zero_of_sum_ne_zero h
  refine ⟨k, ?_⟩
  simpa [finSuccEquiv_coeff_coeff] using hk

end S108LJ

open S108LJ MvPolynomial in
theorem solution
    (m K : Nat) (w0 v0 alpha : Rat)
    (hw0 : 0 < w0) (hv0 : 0 < v0) (halpha : 0 < alpha)
    (w : Fin m → Nat) (hw : ∀ i, 0 < w i)
    (c : Fin K → Fin m → Complex)
    (hjet : OAI.PiExponent.eventualLogJetSurjective m K w0 v0 alpha w c) :
    OAI.PiExponent.eventualTransverseJetSurjectiveForSpatialVolume_360483bd m K alpha w c := by
  classical
  obtain ⟨D, hD, H0, hH⟩ := hjet
  refine ⟨D, hD, H0, fun H hH0 hDH J => ?_⟩
  have h := hH H hH0 hDH
  unfold OAI.PiExponent.logJetSurjective at h
  obtain ⟨P, hPdeg, hPjet⟩ := h (fun j d => if d 0 = 0 then J j d.tail else 0)
  refine ⟨aeval (Fin.cases 1 X : Fin (m + 1) → MvPolynomial (Fin m) ℂ) P, ?_, ?_⟩
  · intro e he
    rw [mem_support_iff] at he
    obtain ⟨k, hk⟩ := coeff_eval_one_ne P e he
    have := hPdeg _ (mem_support_iff.2 hk)
    simp only [Finsupp.cons_zero, Finsupp.cons_succ] at this
    have hw0' : (0 : ℝ) ≤ (w0 : ℝ) * (k : ℝ) := by
      have : (0 : ℝ) < (w0 : ℝ) := by exact_mod_cast hw0
      positivity
    linarith
  · intro j e he
    have h1 := hPjet j (e.cons 0) (by simpa using he)
    simp only [Finsupp.cons_zero, if_true, Finsupp.tail_cons] at h1
    rw [← h1, ← coeff_eval_zero]
    congr 1
    rw [comp_aeval_apply, comp_aeval_apply]
    congr 1
    congr 1
    funext k
    cases k using Fin.cases with
    | zero => simp
    | succ i =>
      simp only [Fin.cases_succ, map_add, aeval_C, aeval_X, algebraMap_eq, map_sum]
      simp
      apply Finset.sum_eq_zero
      intro k _
      split_ifs with hk
      · simp
      · simp [hk]
