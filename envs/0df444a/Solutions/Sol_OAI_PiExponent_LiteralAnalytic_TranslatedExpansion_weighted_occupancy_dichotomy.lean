-- Prove2me | solution 1 for OAI.PiExponent.LiteralAnalytic.TranslatedExpansion.weighted_occupancy_dichotomy
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-17T09:55:52.224436+00:00
-- url     : https://prove2.me/submissions/f8989aea-d4ed-43b1-8819-c41666e6398e

import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Theorems.Thm_OAI_PiExponent_LiteralAnalytic_TranslatedExpansion_weighted_occupancy_dichotomy_low_mass
import Theorems.Thm_OAI_PiExponent_LiteralAnalytic_TranslatedExpansion_weighted_occupancy_dichotomy_collision
open scoped BigOperators

theorem solution
    {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
    (group : ι → κ) (weight : κ → ℝ)
    {H A eta N bbar : ℝ}
    (hH : 0 < H) (hA : 0 ≤ A) (heta : 0 ≤ eta) (hN : 0 < N)
    (hweight : ∀ a, 0 ≤ weight a)
    (hmean : (Fintype.card ι : ℝ) * H * bbar ≤ ∑ i : ι, weight (group i))
    (hcapacity : (((Finset.univ : Finset κ).filter (fun a => weight a ≤ A * H)).card : ℝ) ≤ N) :
    (eta ^ 2 * (Fintype.card ι : ℝ) ^ 2 / N ≤
      ∑ a : κ, (((Finset.univ : Finset ι).filter (fun i => group i = a)).card : ℝ) ^ 2) ∨
    ((Fintype.card ι : ℝ) * H * (A * (1 - eta) - bbar) ≤
      (∑ i : ι, weight (group i)) - (Fintype.card ι : ℝ) * H * bbar) := by
  let low : Finset κ := (Finset.univ : Finset κ).filter (fun a => weight a ≤ A * H)
  have hlowcap : (low.card : ℝ) ≤ N := by
    simpa [low] using hcapacity
  by_cases hs :
      (Fintype.card ι : ℝ) * H * (A * (1 - eta) - bbar) ≤
        (∑ i : ι, weight (group i)) - (Fintype.card ι : ℝ) * H * bbar
  · exact Or.inr hs
  · have hlow :=
      OAI.PiExponent.LiteralAnalytic.TranslatedExpansion.weighted_occupancy_dichotomy_low_mass
        group weight hH hA heta hweight hs
    have hcollision :=
      OAI.PiExponent.LiteralAnalytic.TranslatedExpansion.weighted_occupancy_dichotomy_collision
        group low heta hN hlowcap hlow
    exact Or.inl hcollision
