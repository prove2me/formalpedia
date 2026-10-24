-- Prove2me | solution 1 for OAI.PiExponent.DeterminantContradiction.weighted_support_sum_eq_column_sum
-- status  : ACCEPTED   (disprove)
-- author  : @Eyal1990
-- created : 2026-10-23T08:15:40.111785+00:00
-- url     : https://prove2.me/submissions/5bbca8ae-1783-4574-adad-a9af0c44de69

import Definitions.Def_OAI_PiExponent_TruncatedPolynomialJets
open OAI.PiExponent OAI.PiExponent.DeterminantContradiction OAI.PiExponent.FormalInterpolation
open Classical
open scoped BigOperators
noncomputable section

theorem solution :
    ¬ (∀ {m : Nat} (w0 : Real) (w : Fin m → Real) (H : Real)
        (P : MvPolynomial (Fin (m + 1)) Complex)
        (f : (Fin (m + 1) →₀ Nat) → Complex)
        (hP : ∀ a ∈ P.support,
          ∑ i, InterpolationMatrix.columnWeights w0 w i * (a i : Real) ≤ H),
        (∑ a ∈ P.support, f a) =
          ∑ c : InterpolationMatrix.Column w0 w H,
            f (InterpolationMatrix.exponentVector c.1)) := by
  intro h
  let S : Finset (Fin 1 → Nat) :=
    {a ∈ ({fun i : Fin 1 => 0} : Finset (Fin 1 → Nat)) |
      ∑ i, Fin.cases 1 (fun i => i.elim0) i * (a i : Real) ≤ 0}
  have hbad := h (m := 0) (1 : Real) (fun i => Fin.elim0 i) (0 : Real)
      (0 : MvPolynomial (Fin 1) Complex)
      (fun _ => (1 : Complex))
      (by
        intro a ha
        simp at ha)
  norm_num [InterpolationMatrix.Column, OAI.PiExponent.realWeightedSimplex,
    InterpolationMatrix.columnWeights, InterpolationMatrix.exponentVector] at hbad
  have hmem : (fun _ : Fin 1 => 0) ∈ S := by
    simp [S]
  have hcard : 0 < S.card := Finset.card_pos.mpr ⟨_, hmem⟩
  have hcast : (S.card : Complex) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.ne_of_gt hcard)
  have hzero : (S.card : Complex) = 0 := by simpa [S] using hbad.symm
  exact hcast hzero