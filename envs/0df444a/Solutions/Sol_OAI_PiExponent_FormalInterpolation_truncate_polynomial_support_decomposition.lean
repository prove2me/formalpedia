-- Prove2me | solution 1 for OAI.PiExponent.FormalInterpolation.truncate_polynomial_support_decomposition
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-23T09:27:29.408113+00:00
-- url     : https://prove2.me/submissions/5a962c4b-4e17-4a3d-baa1-c03914315796

import Definitions.Def_OAI_PiExponent_WeightedIdealCurveCriterion
import Mathlib.RingTheory.MvPolynomial.WeightedHomogeneous

open scoped BigOperators
open OAI.PiExponent.FormalInterpolation

theorem solution
    {m : Nat} (s n : Nat) (F : MvPolynomial (Fin m) Complex) :
    ∃ G : MvPolynomial (Fin m) Complex,
      (∀ u ∈ G.support, s * (∑ j : Fin m, u j) < n) ∧
      F - G =
        ∑ u ∈ F.support.filter (fun u => ¬ s * (∑ j : Fin m, u j) < n),
          MvPolynomial.monomial u (F.coeff u) := by
  classical
  let p : (Fin m →₀ Nat) → Prop := fun u => s * (∑ j : Fin m, u j) < n
  let low : Finset (Fin m →₀ Nat) := F.support.filter p
  let G : MvPolynomial (Fin m) Complex :=
    ∑ u ∈ low, MvPolynomial.monomial u (F.coeff u)
  refine ⟨G, ?_, ?_⟩
  · intro u hu
    have hu' : u ∈ low.biUnion (fun v => (MvPolynomial.monomial v (F.coeff v)).support) :=
      MvPolynomial.support_sum hu
    obtain ⟨v, hv, huv⟩ := Finset.mem_biUnion.mp hu'
    have huv' : u ∈ ({v} : Finset (Fin m →₀ Nat)) :=
      MvPolynomial.support_monomial_subset huv
    have huv_eq : u = v := Finset.mem_singleton.mp huv'
    subst u
    exact (Finset.mem_filter.mp hv).2
  · let H : MvPolynomial (Fin m) Complex :=
      ∑ u ∈ F.support.filter (fun u => ¬ p u),
        MvPolynomial.monomial u (F.coeff u)
    have hsplit : F = G + H := by
      dsimp [G, low, H]
      calc
        F = ∑ u ∈ F.support, MvPolynomial.monomial u (F.coeff u) :=
          MvPolynomial.as_sum F
        _ = (∑ u ∈ F.support.filter p, MvPolynomial.monomial u (F.coeff u)) +
              ∑ u ∈ F.support.filter (fun u => ¬ p u),
                MvPolynomial.monomial u (F.coeff u) := by
          simpa [p] using
            (Finset.sum_filter_add_sum_filter_not F.support p
              (fun u => MvPolynomial.monomial u (F.coeff u))).symm
    calc
      F - G = H := (sub_eq_iff_eq_add).2 (by simpa [add_comm] using hsplit)
      _ = ∑ u ∈ F.support.filter (fun u => ¬ s * (∑ j : Fin m, u j) < n),
            MvPolynomial.monomial u (F.coeff u) := by
        simp [H, p]