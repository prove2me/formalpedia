-- Prove2me | solution 1 for OAI.PiExponent.FormalInterpolation.truncatedPolynomialJet_separating_coordinate_selectors
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-18T22:51:12.392205+00:00
-- url     : https://prove2.me/submissions/6aa959cd-cb5d-4d5d-95e7-0a2c7c08b73c

import Theorems.Thm_OAI_PiExponent_FormalInterpolation_truncatedPolynomialJet_logIdeal_coeff_congr
import Theorems.Thm_OAI_PiExponent_FormalInterpolation_logarithmicCenterIdeals_pairwise_comaximal_of_separating_coordinate
import Theorems.Thm_OAI_PiExponent_FormalInterpolation_finite_comaximal_ideal_selectors
import Definitions.Def_OAI_PiExponent_TruncatedPolynomialJets
import Mathlib.RingTheory.Ideal.Quotient.Operations

open OAI.PiExponent OAI.PiExponent.FormalInterpolation
theorem solution
    {m : Nat} (K : Nat) (T : Fin m → Nat)
    (c : Fin K → Fin m → Complex)
    (S : Fin (m + 1) → Nat)
    (hsep : K = 0 ∨ ∃ i : Fin m, Function.Injective (fun j : Fin K => c j i)) :
    ∃ E : Fin K → MvPolynomial (Fin (m + 1)) Complex,
      ∀ (j k : Fin K)
        (a : {a : Fin (m + 1) → Nat // ∀ i, a i < S i}),
        (truncatedPolynomialJet (c j) T (E k)).coeff
            (InterpolationMatrix.exponentVector a.1) =
          if j = k ∧ a.1 = 0 then 1 else 0 := by
  classical
  by_cases hK : K = 0
  · subst K
    exact ⟨Fin.elim0, by intro j; exact Fin.elim0 j⟩
  · have hcoord : ∃ i : Fin m, Function.Injective (fun j : Fin K => c j i) :=
      hsep.resolve_left hK
    obtain ⟨i, hi⟩ := hcoord
    let I : Fin K → Ideal (MvPolynomial (Fin (m + 1)) Complex) :=
      fun j => logarithmicCenterIdeal (c j) T S
    have hI : ∀ j k : Fin K, j ≠ k → I j ⊔ I k = ⊤ := by
      intro j k hjk
      exact OAI.PiExponent.FormalInterpolation.logarithmicCenterIdeals_pairwise_comaximal_of_separating_coordinate
        T S c i hi j k hjk
    obtain ⟨E, hE⟩ :=
      OAI.PiExponent.FormalInterpolation.finite_comaximal_ideal_selectors I hI
    refine ⟨E, ?_⟩
    intro j k a
    have hcong :=
      OAI.PiExponent.FormalInterpolation.truncatedPolynomialJet_logIdeal_coeff_congr
        (c j) T S (E k) (if j = k then 1 else 0) (hE j k)
    have hzero :
        (0 : Fin (m + 1) →₀ Nat) = InterpolationMatrix.exponentVector a.1 ↔
          a.1 = 0 := by
      constructor
      · intro h
        funext t
        have ht := congrArg (fun d : Fin (m + 1) →₀ Nat => d t) h
        exact ht.symm
      · intro h
        apply Finsupp.ext
        intro t
        change 0 = a.1 t
        exact (congrArg (fun f : Fin (m + 1) → Nat => f t) h).symm
    calc
      (truncatedPolynomialJet (c j) T (E k)).coeff
          (InterpolationMatrix.exponentVector a.1) =
          (truncatedPolynomialJet (c j) T (if j = k then 1 else 0)).coeff
            (InterpolationMatrix.exponentVector a.1) := hcong a
      _ = if j = k ∧ a.1 = 0 then 1 else 0 := by
        by_cases hjk : j = k
        · simp [hjk, MvPolynomial.coeff_one, hzero]
        · simp [hjk]