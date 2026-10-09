-- Prove2me | solution 1 for OAI.PiExponent.FormalInterpolation.finite_formalJet_polynomial_approximation
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-08T17:10:41.756139+00:00
-- url     : https://prove2.me/submissions/7d40e918-74c8-4407-b81e-e5c6f26d686a
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_OAI_PiExponent_FormalInterpolationPackets
import Theorems.Thm_OAI_PiExponent_FormalInterpolation_formalJet_box_coefficients
open OAI.PiExponent

theorem solution
    {m : ℕ} (c : Fin m → ℂ) (S : Finset (Fin (m + 1) → ℕ))
    (Q : MvPolynomial (Fin (m + 1)) ℂ) :
    ∃ P : MvPolynomial (Fin (m + 1)) ℂ,
      ∀ a : { a // a ∈ S },
        MvPowerSeries.coeff (InterpolationMatrix.exponentVector a.val)
          (FormalInterpolation.formalJet c P) =
        MvPowerSeries.coeff (InterpolationMatrix.exponentVector a.val)
          (Q : MvPowerSeries (Fin (m + 1)) ℂ) := by
  classical
  let N : ℕ := S.sup (fun b => Finset.univ.sup (fun i => b i))
  obtain ⟨P, hP⟩ :=
    OAI.PiExponent.FormalInterpolation.formalJet_box_coefficients c N Q
  refine ⟨P, ?_⟩
  intro a
  apply hP
  intro i
  have ha : a.val ∈ S := a.property
  dsimp [N]
  exact (Finset.le_sup (f := fun j => a.val j) (Finset.mem_univ i)).trans
    (Finset.le_sup
      (f := fun b => Finset.univ.sup (fun j => b j)) ha)
