-- Prove2me | solution 1 for OAI.PiExponent.LiteralAnalytic.TranslatedExpansion.generic_product_bound
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-17T09:41:22.905664+00:00
-- url     : https://prove2.me/submissions/2ac79985-ef5d-4736-a7c7-329c10f6694a

import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Theorems.Thm_OAI_PiExponent_LiteralAnalytic_TranslatedExpansion_weighted_occupancy_dichotomy
import Theorems.Thm_OAI_PiExponent_LiteralAnalytic_TranslatedExpansion_product_bound_of_rates

open scoped BigOperators

theorem solution
    {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
    (group : ι → κ) (weight : κ → ℝ) (scalar determinant : ℂ)
    {H A eta nu c N bbar Etr Ehol rho : ℝ}
    (hH : 0 < H) (hA : 0 ≤ A) (heta : 0 ≤ eta) (hnu : 0 ≤ nu)
    (hc : 0 ≤ c) (hN : 0 < N)
    (hweight : ∀ a, 0 ≤ weight a)
    (hmean : (Fintype.card ι : ℝ) * H * bbar ≤ ∑ i : ι, weight (group i))
    (hcapacity : (((Finset.univ : Finset κ).filter (fun a => weight a ≤ A * H)).card : ℝ) ≤ N)
    (hscalar : ‖scalar‖ ≤ Real.exp
      (-nu * ((∑ i : ι, weight (group i)) - (Fintype.card ι : ℝ) * H * bbar) +
        (Fintype.card ι : ℝ) * H * Etr))
    (hdet : ‖determinant‖ ≤ Real.exp
      (-c * (∑ a : κ,
        (((Finset.univ : Finset ι).filter (fun i => group i = a)).card : ℝ) ^ 2) +
        (Fintype.card ι : ℝ) * H * (Ehol + rho))) :
    ‖scalar * determinant‖ ≤ Real.exp ((Fintype.card ι : ℝ) * H *
      (Etr + Ehol + rho + max (-c * eta ^ 2 * (Fintype.card ι : ℝ) / (H * N))
        (-nu * (A * (1 - eta) - bbar)))) := by
  have hocc := OAI.PiExponent.LiteralAnalytic.TranslatedExpansion.weighted_occupancy_dichotomy
    group weight hH hA heta hN hweight hmean hcapacity
  have hcoll : 0 ≤ ∑ a : κ,
      (((Finset.univ : Finset ι).filter (fun i => group i = a)).card : ℝ) ^ 2 := by
    apply Finset.sum_nonneg
    intro a ha
    positivity
  exact OAI.PiExponent.LiteralAnalytic.TranslatedExpansion.product_bound_of_rates
    group weight scalar determinant hH hA heta hnu hc hN hmean hcoll hocc hscalar hdet