-- Prove2me | solution 1 for OAI.PiExponent.FormalInterpolation.truncate_polynomial_representations
-- status  : ACCEPTED   (disprove)
-- author  : @Eyal1990
-- created : 2026-10-23T08:54:44.228791+00:00
-- url     : https://prove2.me/submissions/9acc52fe-16ea-48bf-91d8-9cdcee4ada88

import Definitions.Def_OAI_PiExponent_WeightedIdealCurveCriterion
import Mathlib.RingTheory.MvPolynomial.WeightedHomogeneous
import Mathlib.Data.Real.Archimedean

open scoped BigOperators
open OAI.PiExponent.FormalInterpolation

/-- The hypotheses permit the bottom ideal, whose positive powers force an exact representative. -/
theorem solution :
    ¬ (∀ {d : Nat} (I : Ideal (MvPolynomial (Fin d) Complex))
      (w : Fin d → Rat) (rho : Rat) (eps : Real)
      (s : Nat) (hs : 0 < s) (D : Nat)
      (hD : (D : Real) < (s : Real) * ((rho : Real) + eps))
      (m : Nat) (g : Fin m → MvPolynomial (Fin d) Complex)
      (hg : ∀ j, g j ∈ I ^ s)
      (hdeg : ∀ j, ∀ a ∈ (g j).support,
        ∑ k, (w k : Real) * (a k : Real) ≤ (D : Real))
      (hrepr : ∀ q : MvPolynomial (Fin d) Complex,
        ∃ t : Nat, ∃ b : Fin t → MvPolynomial (Fin d) Complex,
          ∃ F : Fin t → MvPolynomial (Fin m) Complex,
            q = ∑ i : Fin t, MvPolynomial.aeval g (F i) * b i),
      ∃ C : Real, 0 ≤ C ∧ ∃ N : Nat, ∀ n : Nat, N ≤ n →
        ∀ q : MvPolynomial (Fin d) Complex, ∃ p : MvPolynomial (Fin d) Complex,
          q - p ∈ I ^ n ∧
          ∀ a ∈ p.support,
            ∑ k, (w k : Real) * (a k : Real) ≤
              (n : Real) * ((rho : Real) + eps) + C) := by
  intro h
  let I : Ideal (MvPolynomial (Fin 1) Complex) := ⊥
  let w : Fin 1 → Rat := fun _ => 1
  let rho : Rat := 0
  let eps : Real := 1
  let g : Fin 1 → MvPolynomial (Fin 1) Complex := fun _ => 0
  have hg : ∀ j, g j ∈ I ^ 1 := by
    intro j
    simp [I, g]
  have hdeg : ∀ j, ∀ a ∈ (g j).support,
      ∑ k, (w k : Real) * (a k : Real) ≤ ((0 : Nat) : Real) := by
    intro j a ha
    simp [g] at ha
  have hrepr : ∀ q : MvPolynomial (Fin 1) Complex,
      ∃ t : Nat, ∃ b : Fin t → MvPolynomial (Fin 1) Complex,
        ∃ F : Fin t → MvPolynomial (Fin 1) Complex,
          q = ∑ i : Fin t, MvPolynomial.aeval g (F i) * b i := by
    intro q
    refine ⟨1, (fun _ => q), (fun _ => 1), ?_⟩
    simp [g]
  have hres := h (d := 1) I w rho eps 1 (by norm_num) (D := 0)
    (by norm_num) 1 g hg hdeg hrepr
  rcases hres with ⟨C, hC, N, hN⟩
  let n : Nat := max N 1
  have hnN : N ≤ n := by
    dsimp [n]
    exact Nat.le_max_left _ _
  have hn0 : n ≠ 0 := by
    dsimp [n]
    omega
  obtain ⟨K, hK⟩ := exists_nat_gt ((n : Real) + C)
  let q : MvPolynomial (Fin 1) Complex := MvPolynomial.X 0 ^ K
  obtain ⟨p, hqp, hpbound⟩ := hN n hnN q
  have hpq : p = q := by
    have hzero : q - p = 0 := by
      have hmem : q - p ∈ (⊥ : Ideal (MvPolynomial (Fin 1) Complex)) := by
        simpa [I, Ideal.bot_pow hn0] using hqp
      simpa using hmem
    exact (sub_eq_zero.mp hzero).symm
  have hmono : Finsupp.single (0 : Fin 1) K ∈ p.support := by
    rw [hpq]
    simp [q, MvPolynomial.support_X_pow]
  have hweight := hpbound (Finsupp.single (0 : Fin 1) K) hmono
  have hKbound : (K : Real) ≤ (n : Real) + C := by
    simpa [w, rho, eps, Finsupp.single_apply] using hweight
  linarith