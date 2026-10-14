-- Prove2me | solution 1 for OAI.PiExponent.DeterminantAnalyticBound.translated_summand_bound
-- status  : ACCEPTED   (prove)
-- author  : @Yuxuan Xu
-- created : 2026-10-11T19:20:37.009443+00:00
-- url     : https://prove2.me/submissions/6f3fb375-a5ab-4052-a59d-90a06cba315e

import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Tactic
import Definitions.Def_OAI_NumberTheory_PiExponent_Analysis_CollisionCombinatorics_Multiplicity
import Theorems.Thm_OAI_PiExponent_Collision_sum_weight_ge_of_low_count_le


namespace OAI.PiExponent.Collision
section
open scoped BigOperators

theorem sum_multiplicity_eq_card_filter {ι κ : Type*} [DecidableEq κ]
    (rows : Finset ι) (groups : Finset κ) (group : ι → κ) :
    ∑ a ∈ groups, multiplicity rows group a =
      (rows.filter fun i => group i ∈ groups).card := by
  exact Finset.sum_card_fiberwise_eq_card_filter rows groups group

end
end OAI.PiExponent.Collision

namespace OAI.PiExponent.Collision
section
open scoped BigOperators
variable {G : Type*}

theorem sum_sq_le_card_mul_sum_sq (S : Finset G) (n : G → ℝ) :
    (∑ a ∈ S, n a) ^ 2 ≤ (S.card : ℝ) * ∑ a ∈ S, n a ^ 2 := by
  simpa using Finset.sum_mul_sq_le_sq_mul_sq S (fun _ : G => (1 : ℝ)) n

end
end OAI.PiExponent.Collision

namespace OAI.PiExponent.Collision
section
open scoped BigOperators
variable {G : Type*}

theorem sum_sq_le_card_mul_total_sq (S U : Finset G) (hSU : S ⊆ U)
    (n : G → ℝ) :
    (∑ a ∈ S, n a) ^ 2 ≤ (S.card : ℝ) * ∑ a ∈ U, n a ^ 2 := by
  apply (sum_sq_le_card_mul_sum_sq S n).trans
  apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg _)
  exact Finset.sum_le_sum_of_subset_of_nonneg hSU (fun a _ _ => sq_nonneg (n a))

end
end OAI.PiExponent.Collision

namespace OAI.PiExponent.Collision
section
open scoped BigOperators
variable {G : Type*}
variable [Fintype G]

theorem sum_sq_le_card_mul_univ_sq (S : Finset G) (n : G → ℝ) :
    (∑ a ∈ S, n a) ^ 2 ≤ (S.card : ℝ) * ∑ a, n a ^ 2 := by
  exact sum_sq_le_card_mul_total_sq S Finset.univ (Finset.subset_univ S) n

end
end OAI.PiExponent.Collision

namespace OAI.PiExponent.DeterminantAnalyticBound
section
open scoped BigOperators

theorem two_alternative_exponent
    {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
    (group : ι → κ) (weight : κ → ℝ)
    {H A eta nu c N bbar E : ℝ}
    (hH : 0 < H) (hA : 0 ≤ A) (heta : 0 ≤ eta) (hnu : 0 ≤ nu)
    (hc : 0 ≤ c) (hN : 0 < N) (hw : ∀ a, 0 ≤ weight a)
    (hbeta : (Fintype.card ι : ℝ) * H * bbar ≤ ∑ i, weight (group i))
    (hcap : (((Finset.univ : Finset κ).filter (fun a => weight a ≤ A * H)).card : ℝ) ≤ N) :
    -nu * ((∑ i, weight (group i)) - (Fintype.card ι : ℝ) * H * bbar) -
      c * (∑ a, (Collision.multiplicity Finset.univ group a : ℝ) ^ 2) +
      (Fintype.card ι : ℝ) * H * E ≤
    (Fintype.card ι : ℝ) * H *
      (E + max (-c * eta ^ 2 * (Fintype.card ι : ℝ) / (H * N))
        (-nu * (A * (1 - eta) - bbar))) := by
  classical
  let S := (Finset.univ : Finset κ).filter (fun a => weight a ≤ A * H)
  let M : ℝ := Fintype.card ι
  let Z : ℝ := ∑ a, (Collision.multiplicity Finset.univ group a : ℝ) ^ 2
  have hM : 0 ≤ M := Nat.cast_nonneg _
  have hZ : 0 ≤ Z := Finset.sum_nonneg fun _ _ => sq_nonneg _
  have hmass : (∑ a ∈ S, (Collision.multiplicity Finset.univ group a : ℝ)) =
      (((Finset.univ : Finset ι).filter (fun i => weight (group i) ≤ A * H)).card : ℝ) := by
    have hn := Collision.sum_multiplicity_eq_card_filter (Finset.univ : Finset ι) S group
    have hn' : (∑ a ∈ S, Collision.multiplicity Finset.univ group a) =
        ((Finset.univ : Finset ι).filter (fun i => weight (group i) ≤ A * H)).card := by
      simpa only [S, Finset.mem_filter, Finset.mem_univ, true_and] using hn
    exact_mod_cast hn'
  by_cases hlow : eta * M ≤ ∑ a ∈ S, (Collision.multiplicity Finset.univ group a : ℝ)
  · have hsq : eta ^ 2 * M ^ 2 ≤ N * Z := by
      calc
        _ = (eta * M) ^ 2 := by ring
        _ ≤ (∑ a ∈ S, (Collision.multiplicity Finset.univ group a : ℝ)) ^ 2 :=
          pow_le_pow_left₀ (mul_nonneg heta hM) hlow 2
        _ ≤ (S.card : ℝ) * Z := Collision.sum_sq_le_card_mul_univ_sq S _
        _ ≤ N * Z := mul_le_mul_of_nonneg_right hcap hZ
    have hcollision : -c * Z ≤ M * H * (-c * eta ^ 2 * M / (H * N)) := by
      have hz : eta ^ 2 * M ^ 2 / N ≤ Z := (div_le_iff₀ hN).mpr (by nlinarith [hsq])
      have hh := mul_le_mul_of_nonneg_left hz hc
      have he : M * H * (-c * eta ^ 2 * M / (H * N)) = -c * (eta ^ 2 * M ^ 2 / N) := by
        field_simp
      rw [he]
      nlinarith [hh]
    have hscalar : -nu * ((∑ i, weight (group i)) - M * H * bbar) ≤ 0 := by
      have hp := mul_nonneg hnu (sub_nonneg.mpr hbeta)
      nlinarith [hp]
    have hmax := mul_le_mul_of_nonneg_left
      (le_max_left (-c * eta ^ 2 * M / (H * N)) (-nu * (A * (1 - eta) - bbar)))
      (mul_nonneg hM hH.le)
    change -nu * ((∑ i, weight (group i)) - M * H * bbar) - c * Z + M * H * E ≤ _
    change _ ≤ M * H * (E + max (-c * eta ^ 2 * M / (H * N)) (-nu * (A * (1 - eta) - bbar)))
    nlinarith
  · have hl : (((Finset.univ : Finset ι).filter (fun i => weight (group i) ≤ A * H)).card : ℝ) ≤
        eta * (Finset.univ : Finset ι).card := by
      rw [← hmass]
      exact (le_of_not_ge hlow)
    have hwgt := Collision.sum_weight_ge_of_low_count_le (Finset.univ : Finset ι)
      (fun i => weight (group i)) (mul_nonneg hA hH.le) (fun i _ => hw _) hl
    have hwgt' : A * H * (1 - eta) * M ≤ ∑ i, weight (group i) := by
      simpa only [Finset.card_univ, M] using hwgt
    have hmul := mul_le_mul_of_nonneg_left hwgt' hnu
    have hscalar : -nu * ((∑ i, weight (group i)) - M * H * bbar) ≤
        M * H * (-nu * (A * (1 - eta) - bbar)) := by nlinarith [hmul]
    have hcollision : -c * Z ≤ 0 := by nlinarith [mul_nonneg hc hZ]
    have hmax := mul_le_mul_of_nonneg_left
      (le_max_right (-c * eta ^ 2 * M / (H * N)) (-nu * (A * (1 - eta) - bbar)))
      (mul_nonneg hM hH.le)
    change -nu * ((∑ i, weight (group i)) - M * H * bbar) - c * Z + M * H * E ≤ _
    change _ ≤ M * H * (E + max (-c * eta ^ 2 * M / (H * N)) (-nu * (A * (1 - eta) - bbar)))
    nlinarith

end
end OAI.PiExponent.DeterminantAnalyticBound

open scoped BigOperators
open OAI.PiExponent OAI.PiExponent.DeterminantAnalyticBound

theorem solution
    {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
    (group : ι → κ) (weight : κ → ℝ) (scalar determinant : ℂ)
    {H A eta nu c N bbar Etr Ehol rho : ℝ}
    (hH : 0 < H) (hA : 0 ≤ A) (heta : 0 ≤ eta) (hnu : 0 ≤ nu)
    (hc : 0 ≤ c) (hN : 0 < N) (hw : ∀ a, 0 ≤ weight a)
    (hbeta : (Fintype.card ι : ℝ) * H * bbar ≤ ∑ i, weight (group i))
    (hcap : (((Finset.univ : Finset κ).filter (fun a => weight a ≤ A * H)).card : ℝ) ≤ N)
    (hscalar : ‖scalar‖ ≤ Real.exp
      (-nu * ((∑ i, weight (group i)) - (Fintype.card ι : ℝ) * H * bbar) +
        (Fintype.card ι : ℝ) * H * Etr))
    (hdet : ‖determinant‖ ≤ Real.exp
      (-c * (∑ a, (Collision.multiplicity Finset.univ group a : ℝ) ^ 2) +
        (Fintype.card ι : ℝ) * H * (Ehol + rho))) :
    ‖scalar * determinant‖ ≤ Real.exp ((Fintype.card ι : ℝ) * H *
      (Etr + Ehol + rho + max (-c * eta ^ 2 * (Fintype.card ι : ℝ) / (H * N))
        (-nu * (A * (1 - eta) - bbar)))) := by
  rw [norm_mul]
  apply (mul_le_mul hscalar hdet (norm_nonneg _) (Real.exp_pos _).le).trans
  rw [← Real.exp_add]
  apply Real.exp_le_exp.mpr
  have h := two_alternative_exponent group weight hH hA heta hnu hc hN hw hbeta hcap
    (E := Etr + Ehol + rho)
  nlinarith [h]
