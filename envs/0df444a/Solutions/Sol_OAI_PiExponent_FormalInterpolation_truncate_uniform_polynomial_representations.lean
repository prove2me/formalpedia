-- Prove2me | solution 1 for OAI.PiExponent.FormalInterpolation.truncate_uniform_polynomial_representations
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-23T09:11:35.527982+00:00
-- url     : https://prove2.me/submissions/4a03cf33-14ca-467c-a6e6-7957af2a2399

import Definitions.Def_OAI_PiExponent_WeightedIdealCurveCriterion
import Mathlib.RingTheory.MvPolynomial.WeightedHomogeneous
import Theorems.Thm_OAI_PiExponent_FormalInterpolation_exists_nonnegative_uniform_support_weight_bound
import Theorems.Thm_OAI_PiExponent_FormalInterpolation_truncate_one_polynomial_mod_power
import Theorems.Thm_OAI_PiExponent_FormalInterpolation_sum_truncation_errors_in_ideal_power
import Theorems.Thm_OAI_PiExponent_FormalInterpolation_weighted_degree_of_truncated_generator_sum

open scoped BigOperators
open OAI.PiExponent.FormalInterpolation

 theorem solution
    {d : Nat} (I : Ideal (MvPolynomial (Fin d) Complex))
    (w : Fin d → Rat) (rho : Rat) (eps : Real)
    (s : Nat) (hs : 0 < s) (D : Nat)
    (hD : (D : Real) < (s : Real) * ((rho : Real) + eps))
    (m : Nat) (g : Fin m → MvPolynomial (Fin d) Complex)
    (hg : ∀ j, g j ∈ I ^ s)
    (hdeg : ∀ j, ∀ a ∈ (g j).support,
      ∑ k, (w k : Real) * (a k : Real) ≤ (D : Real))
    (t : Nat) (b : Fin t → MvPolynomial (Fin d) Complex)
    (hrepr : ∀ q : MvPolynomial (Fin d) Complex,
      ∃ F : Fin t → MvPolynomial (Fin m) Complex,
        q = ∑ i : Fin t, MvPolynomial.aeval g (F i) * b i) :
    ∃ C : Real, 0 ≤ C ∧ ∃ N : Nat, ∀ n : Nat, N ≤ n →
      ∀ q : MvPolynomial (Fin d) Complex, ∃ p : MvPolynomial (Fin d) Complex,
        q - p ∈ I ^ n ∧
        ∀ a ∈ p.support,
          ∑ k, (w k : Real) * (a k : Real) ≤
            (n : Real) * ((rho : Real) + eps) + C := by
  obtain ⟨C, hC, hb⟩ :=
    OAI.PiExponent.FormalInterpolation.exists_nonnegative_uniform_support_weight_bound
      w b
  refine ⟨C, hC, 1, ?_⟩
  intro n hn q
  have hn0 : 0 < n := by exact lt_of_lt_of_le Nat.zero_lt_one hn
  obtain ⟨F, hq⟩ := hrepr q
  have htrunc : ∀ i : Fin t,
      ∃ G : MvPolynomial (Fin m) Complex,
        (∀ u ∈ G.support, s * (∑ j, u j) < n) ∧
        MvPolynomial.aeval g (F i - G) ∈ I ^ n := by
    intro i
    exact OAI.PiExponent.FormalInterpolation.truncate_one_polynomial_mod_power
      I s n hs hn0 g hg (F i)
  let G : Fin t → MvPolynomial (Fin m) Complex :=
    fun i => Classical.choose (htrunc i)
  have hG : ∀ i : Fin t,
      (∀ u ∈ (G i).support, s * (∑ j, u j) < n) ∧
      MvPolynomial.aeval g (F i - G i) ∈ I ^ n := by
    intro i
    exact Classical.choose_spec (htrunc i)
  let p : MvPolynomial (Fin d) Complex :=
    ∑ i : Fin t, MvPolynomial.aeval g (G i) * b i
  have hmod :
      (∑ i : Fin t, MvPolynomial.aeval g (F i) * b i) - p ∈ I ^ n := by
    exact OAI.PiExponent.FormalInterpolation.sum_truncation_errors_in_ideal_power
      I n g b F G (fun i => (hG i).2)
  have hweight :=
    OAI.PiExponent.FormalInterpolation.weighted_degree_of_truncated_generator_sum
      w rho eps s hs D hD g hdeg b C hb n F G (fun i => (hG i).1)
  refine ⟨p, ?_, hweight⟩
  rw [hq]
  simpa [p] using hmod
