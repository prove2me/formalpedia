-- Prove2me | solution 1 for OAI.PiExponent.FormalInterpolation.fibreContact_word_jet_vanishing
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-23T17:34:05.88424+00:00
-- url     : https://prove2.me/submissions/24f8ddf6-2141-4134-a492-613aa1b663e1

import Definitions.Def_OAI_PiExponent_FibreContactAuxiliaryData
import Mathlib
import Mathlib.Algebra.MvPolynomial.PDeriv

section

open OAI.PiExponent.FormalInterpolation

namespace PiL19

lemma pderiv_bound {m : Nat} (W : Fin m → Rat) (N : Nat)
    (F : MvPolynomial (Fin m) Complex) (hF : fibreContactSupportBound W N F)
    (i : Fin m) (hW : ∀ i, 0 ≤ (W i : Real)) :
    fibreContactSupportBound W N (MvPolynomial.pderiv i F) := by
  classical
  intro b hb
  rw [MvPolynomial.mem_support_iff, MvPolynomial.coeff_pderiv] at hb
  have hmem : b + Finsupp.single i 1 ∈ F.support := by
    rw [MvPolynomial.mem_support_iff]; intro h; rw [h, zero_mul] at hb; exact hb rfl
  have h1 := hF _ hmem
  have : ∑ k : Fin m, (((b + Finsupp.single i 1 : Fin m →₀ ℕ) k : ℕ) : Real) * (W k : Real) =
      (∑ k : Fin m, (b k : Real) * (W k : Real)) + W i := by
    simp only [Finsupp.add_apply, Nat.cast_add, add_mul, Finset.sum_add_distrib, Finsupp.single_apply]
    congr 1
    rw [Finset.sum_eq_single i]
    · simp
    · intro k _ hk; simp [Ne.symm hk]
    · simp
  rw [this] at h1
  linarith [hW i]

theorem chain {σ R S : Type*} [CommSemiring R] [CommSemiring S] [Algebra R S] [DecidableEq σ] (D : Derivation R S S) (g : σ → S) (p : MvPolynomial σ R) (i : σ) (hg : ∀ j, D (g j) = if j = i then 1 else 0) : MvPolynomial.aeval g (MvPolynomial.pderiv i p) = D (MvPolynomial.aeval g p) := by
  induction p using MvPolynomial.induction_on with
  | C a => simp
  | add p q hp hq => simp [hp, hq]
  | mul_X p j hp =>
    have e1 : MvPolynomial.pderiv i (p * MvPolynomial.X j) =
        p * MvPolynomial.pderiv i (MvPolynomial.X j) + MvPolynomial.X j * MvPolynomial.pderiv i p := by
      rw [Derivation.leibniz, smul_eq_mul, smul_eq_mul]
    have e2 : D (MvPolynomial.aeval g p * g j) =
        MvPolynomial.aeval g p * D (g j) + g j * D (MvPolynomial.aeval g p) := by
      rw [Derivation.leibniz, smul_eq_mul, smul_eq_mul]
    rw [e1, map_add, map_mul, map_mul, hp, map_mul, MvPolynomial.aeval_X, e2, hg j]
    by_cases h : j = i
    · subst h; simp [MvPolynomial.pderiv_X_self]
    · simp [MvPolynomial.pderiv_X_of_ne h, h]

lemma transl_pderiv {m : ℕ} (c : Fin m → ℂ) (i : Fin m) (p : MvPolynomial (Fin m) ℂ) :
    MvPolynomial.aeval (fun k => MvPolynomial.C (c k) + MvPolynomial.X k) (MvPolynomial.pderiv i p) =
      MvPolynomial.pderiv i (MvPolynomial.aeval (fun k => MvPolynomial.C (c k) + MvPolynomial.X k) p) := by
  classical
  refine chain (MvPolynomial.pderiv i) _ p i fun j => ?_
  by_cases h : j = i
  · subst h; simp [MvPolynomial.pderiv_X_self]
  · simp [MvPolynomial.pderiv_X_of_ne h, h]

lemma weight_add {m : ℕ} (V : Fin m → ℚ) (a : Fin m →₀ ℕ) (i : Fin m) :
    ∑ k : Fin m, (((a + Finsupp.single i 1 : Fin m →₀ ℕ) k : ℕ) : Real) * (V k : Real) =
      (∑ k : Fin m, (a k : Real) * (V k : Real)) + V i := by
  classical
  simp only [Finsupp.add_apply, Nat.cast_add, add_mul, Finset.sum_add_distrib, Finsupp.single_apply]
  congr 1
  rw [Finset.sum_eq_single i]
  · simp
  · intro k _ hk; simp [Ne.symm hk]
  · simp

theorem word_jet {m K : Nat} (c : Fin K → Fin m → Complex)
    (V : Fin m → Rat) (sigma : Rat) (N : Nat)
    (F : MvPolynomial (Fin m) Complex)
    (hjet : fibreContactJetVanishing c V ((1 + 3 * (sigma : Real)) * (N : Real)) F)
    (word : List (Fin m))
    (hword : fibreContactWordCost V word ≤ (sigma : Real) * (N : Real)) :
    fibreContactJetVanishing c V ((1 + 2 * (sigma : Real)) * (N : Real))
      (fibreContactWord word F) := by
  classical
  have key : ∀ (w : List (Fin m)) (j : Fin K) (a : Fin m →₀ ℕ),
      (∑ k : Fin m, (a k : Real) * (V k : Real)) + fibreContactWordCost V w <
        (1 + 3 * (sigma : Real)) * (N : Real) →
      (MvPolynomial.aeval (fun i => MvPolynomial.C (c j i) + MvPolynomial.X i)
        (fibreContactWord w F)).coeff a = 0 := by
    intro w
    induction w with
    | nil =>
      intro j a ha
      simp only [fibreContactWordCost, List.map_nil, List.sum_nil, add_zero] at ha
      simpa [fibreContactWord] using hjet j a ha
    | cons i w ih =>
      intro j a ha
      have hw : fibreContactWord (i :: w) F = MvPolynomial.pderiv i (fibreContactWord w F) := by
        simp [fibreContactWord]
      rw [hw, transl_pderiv, MvPolynomial.coeff_pderiv, ih j _ ?_, zero_mul]
      rw [weight_add]
      simp only [fibreContactWordCost, List.map_cons, List.sum_cons] at ha
      simp only [fibreContactWordCost]
      linarith
  intro j a ha
  exact key word j a (by linarith)

theorem supp_pderiv {m : Nat} (W : Fin m → Rat) (N : Nat)
    (F : MvPolynomial (Fin m) Complex)
    (hF : fibreContactSupportBound W N F)
    (i : Fin m)
    (hW : ∀ j, 0 ≤ (W j : Real)) :
    fibreContactSupportBound W N (MvPolynomial.pderiv i F) := pderiv_bound W N F hF i hW

end PiL19

end

open OAI OAI.PiExponent OAI.PiExponent.FormalInterpolation

open scoped BigOperators
open OAI.PiExponent.FormalInterpolation

theorem solution
    {m K : Nat} (c : Fin K → Fin m → Complex)
    (V : Fin m → Rat) (sigma : Rat) (N : Nat)
    (F : MvPolynomial (Fin m) Complex)
    (hjet : fibreContactJetVanishing c V ((1 + 3 * (sigma : Real)) * (N : Real)) F)
    (word : List (Fin m))
    (hword : fibreContactWordCost V word ≤ (sigma : Real) * (N : Real)) :
    fibreContactJetVanishing c V ((1 + 2 * (sigma : Real)) * (N : Real))
      (fibreContactWord word F) := by
  apply PiL19.word_jet <;> assumption
