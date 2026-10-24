-- Prove2me | solution 1 for OAI.PiExponent.DeterminantContradiction.linearMap_finitePi_coordinate_representation_e43f5331
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-23T08:06:22.028062+00:00
-- url     : https://prove2.me/submissions/9e163a64-bb94-41b0-9770-841a317ee927

import Definitions.Def_OAI_PiExponent_TruncatedPolynomialJets
open OAI.PiExponent
open OAI.PiExponent.DeterminantContradiction
open OAI.PiExponent.FormalInterpolation
open scoped BigOperators

theorem solution
    {β : Type*} [Fintype β]
    (L : (β → Complex) →ₗ[Complex] Complex) :
    ∃ a : β → Complex, ∀ v : β → Complex,
      L v = ∑ b, a b * v b := by
  classical
  let a : β → Complex := fun b => L (Pi.single b (1 : Complex))
  refine ⟨a, ?_⟩
  intro v
  have hdecomp : v = ∑ b : β, v b • Pi.single b (1 : Complex) := by
    ext x
    simp [Pi.single_apply]
  calc
    L v = L (∑ b : β, v b • Pi.single b (1 : Complex)) := by
      rw [← hdecomp]
    _ = ∑ b : β, v b • L (Pi.single b (1 : Complex)) := by
      simp only [map_sum, map_smul]
    _ = ∑ b : β, a b * v b := by
      simp [a, smul_eq_mul, mul_comm]
