-- Prove2me | solution 1 for OAI.PiExponent.LiteralAnalytic.TranslatedExpansion.product_bound_of_rates
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-19T09:00:07.016976+00:00
-- url     : https://prove2.me/submissions/9c0d358a-d4a1-4792-83e7-0a092a897ad5

import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic

import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open scoped BigOperators

theorem solution
    {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
    (group : ι → κ) (weight : κ → ℝ) (scalar determinant : ℂ)
    {H A eta nu c N bbar Etr Ehol rho : ℝ}
    (hH : 0 < H) (hA : 0 ≤ A) (heta : 0 ≤ eta) (hnu : 0 ≤ nu)
    (hc : 0 ≤ c) (hN : 0 < N)
    (hmean : (Fintype.card ι : ℝ) * H * bbar ≤ ∑ i : ι, weight (group i))
    (hcoll : 0 ≤ ∑ a : κ,
      (((Finset.univ : Finset ι).filter (fun i => group i = a)).card : ℝ) ^ 2)
    (hrates : (eta ^ 2 * (Fintype.card ι : ℝ) ^ 2 / N ≤
      ∑ a : κ, (((Finset.univ : Finset ι).filter (fun i => group i = a)).card : ℝ) ^ 2) ∨
      ((Fintype.card ι : ℝ) * H * (A * (1 - eta) - bbar) ≤
      (∑ i : ι, weight (group i)) - (Fintype.card ι : ℝ) * H * bbar))
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
  let m : ℝ := Fintype.card ι
  let excess : ℝ := (∑ i : ι, weight (group i)) - m * H * bbar
  let collisions : ℝ := ∑ a : κ,
    (((Finset.univ : Finset ι).filter (fun i => group i = a)).card : ℝ) ^ 2
  let rcol : ℝ := -c * eta ^ 2 * m / (H * N)
  let rapp : ℝ := -nu * (A * (1 - eta) - bbar)
  have hm : 0 ≤ m := Nat.cast_nonneg _
  have hscale : 0 ≤ m * H := mul_nonneg hm hH.le
  have hexcess : 0 ≤ excess := sub_nonneg.mpr hmean
  have hs0 : -nu * excess ≤ 0 :=
    mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hnu) hexcess
  have hd0 : -c * collisions ≤ 0 :=
    mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hc) hcoll
  have hpen : -nu * excess + -c * collisions ≤ m * H * max rcol rapp := by
    rcases hrates with hr | hr
    · have hcr : -c * collisions ≤ -c * (eta ^ 2 * m ^ 2 / N) :=
        mul_le_mul_of_nonpos_left hr (neg_nonpos.mpr hc)
      have hcancel : -c * (eta ^ 2 * m ^ 2 / N) = m * H * rcol := by
        dsimp [rcol]
        field_simp [hH.ne', hN.ne'] <;> ring
      calc
        -nu * excess + -c * collisions ≤ 0 + -c * (eta ^ 2 * m ^ 2 / N) :=
          add_le_add hs0 hcr
        _ = m * H * rcol := by rw [zero_add, hcancel]
        _ ≤ m * H * max rcol rapp :=
          mul_le_mul_of_nonneg_left (le_max_left rcol rapp) hscale
    · have hsr : -nu * excess ≤ -nu * (m * H * (A * (1 - eta) - bbar)) :=
        mul_le_mul_of_nonpos_left hr (neg_nonpos.mpr hnu)
      calc
        -nu * excess + -c * collisions ≤
            -nu * (m * H * (A * (1 - eta) - bbar)) + 0 := add_le_add hsr hd0
        _ = m * H * rapp := by dsimp [rapp]; ring
        _ ≤ m * H * max rcol rapp :=
          mul_le_mul_of_nonneg_left (le_max_right rcol rapp) hscale
  change ‖scalar * determinant‖ ≤
    Real.exp (m * H * (Etr + Ehol + rho + max rcol rapp))
  calc
    ‖scalar * determinant‖ = ‖scalar‖ * ‖determinant‖ := norm_mul _ _
    _ ≤ Real.exp (-nu * excess + m * H * Etr) *
        Real.exp (-c * collisions + m * H * (Ehol + rho)) :=
      mul_le_mul hscalar hdet (norm_nonneg _) (Real.exp_nonneg _)
    _ = Real.exp ((-nu * excess + m * H * Etr) +
        (-c * collisions + m * H * (Ehol + rho))) := (Real.exp_add _ _).symm
    _ ≤ Real.exp (m * H * (Etr + Ehol + rho + max rcol rapp)) := by
      apply Real.exp_le_exp.mpr
      calc
        (-nu * excess + m * H * Etr) + (-c * collisions + m * H * (Ehol + rho)) =
            m * H * (Etr + Ehol + rho) + (-nu * excess + -c * collisions) := by ring
        _ ≤ m * H * (Etr + Ehol + rho) + m * H * max rcol rapp :=
          add_le_add_right hpen _
        _ = m * H * (Etr + Ehol + rho + max rcol rapp) := by ring
