-- Prove2me | solution 1 for OAI.PiExponent.FormalInterpolation.formalJet_box_coefficients
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-08T18:34:37.731266+00:00
-- url     : https://prove2.me/submissions/69f56e62-6c69-4a87-8a40-1ba336166cda
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Theorems.Thm_OAI_PiExponent_FormalInterpolation_formalJet_finite_coefficients
open OAI.PiExponent

theorem solution
    {m : Nat} (c : Fin m → Complex) (N : Nat)
    (Q : MvPolynomial (Fin (m + 1)) Complex) :
    ∃ P : MvPolynomial (Fin (m + 1)) Complex,
      ∀ a : Fin (m + 1) → Nat, (∀ i, a i ≤ N) →
        MvPowerSeries.coeff (InterpolationMatrix.exponentVector a)
          (FormalInterpolation.formalJet c P) =
        MvPowerSeries.coeff (InterpolationMatrix.exponentVector a)
          (Q : MvPowerSeries (Fin (m + 1)) Complex) := by
  classical
  let S : Finset (Fin (m + 1) → Nat) :=
    Finset.univ.image
      (fun b : (Fin (m + 1) → Fin (N + 1)) => fun i => (b i).val)
  obtain ⟨P, hP⟩ :=
    OAI.PiExponent.FormalInterpolation.formalJet_finite_coefficients c S Q
  refine ⟨P, ?_⟩
  intro a ha
  apply hP a
  have haS : a ∈ S := by
    change a ∈ (Finset.univ.image
      (fun b : (Fin (m + 1) → Fin (N + 1)) => fun i => (b i).val))
    rw [Finset.mem_image]
    refine ⟨fun i => ⟨a i, Nat.lt_succ_of_le (ha i)⟩, Finset.mem_univ _, ?_⟩
    funext i
    rfl
  exact haS
