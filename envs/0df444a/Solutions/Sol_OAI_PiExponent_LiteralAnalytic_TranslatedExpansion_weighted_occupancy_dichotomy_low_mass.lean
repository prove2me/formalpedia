-- Prove2me | solution 1 for OAI.PiExponent.LiteralAnalytic.TranslatedExpansion.weighted_occupancy_dichotomy_low_mass
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-18T03:02:44.217977+00:00
-- url     : https://prove2.me/submissions/d718106b-28d3-4c2a-9fb5-726b75ec8eb9

import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Theorems.Thm_OAI_PiExponent_LiteralAnalytic_TranslatedExpansion_weighted_occupancy_from_total_weight_bound
open scoped BigOperators

theorem solution
    {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
    (group : ι → κ) (weight : κ → ℝ)
    {H A eta bbar : ℝ}
    (hH : 0 < H) (hA : 0 ≤ A) (heta : 0 ≤ eta)
    (hweight : ∀ a, 0 ≤ weight a)
    (hsurplus :
      ¬ ((Fintype.card ι : ℝ) * H * (A * (1 - eta) - bbar) ≤
        (∑ i : ι, weight (group i)) - (Fintype.card ι : ℝ) * H * bbar)) :
    eta * (Fintype.card ι : ℝ) ≤
      ∑ a ∈ ((Finset.univ : Finset κ).filter (fun a => weight a ≤ A * H)),
        (((Finset.univ : Finset ι).filter (fun i => group i = a)).card : ℝ) := by
  have hstrict :
      (∑ i : ι, weight (group i)) - (Fintype.card ι : ℝ) * H * bbar <
        (Fintype.card ι : ℝ) * H * (A * (1 - eta) - bbar) :=
    not_le.mp hsurplus
  have hsum :
      (∑ i : ι, weight (group i)) <
        (Fintype.card ι : ℝ) * H * (A * (1 - eta)) := by
    calc
      (∑ i : ι, weight (group i)) =
          ((∑ i : ι, weight (group i)) - (Fintype.card ι : ℝ) * H * bbar) +
            (Fintype.card ι : ℝ) * H * bbar := by
        exact (sub_add_cancel _ _).symm
      _ < (Fintype.card ι : ℝ) * H * (A * (1 - eta) - bbar) +
            (Fintype.card ι : ℝ) * H * bbar := add_lt_add_left hstrict _
      _ = (Fintype.card ι : ℝ) * H *
            ((A * (1 - eta) - bbar) + bbar) := by rw [← mul_add]
      _ = (Fintype.card ι : ℝ) * H * (A * (1 - eta)) := by rw [sub_add_cancel]
  exact OAI.PiExponent.LiteralAnalytic.TranslatedExpansion.weighted_occupancy_from_total_weight_bound
    group weight hH hA heta hweight hsum