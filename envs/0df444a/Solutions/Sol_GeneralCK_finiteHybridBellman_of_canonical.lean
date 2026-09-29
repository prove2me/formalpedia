-- Prove2me | solution 1 for GeneralCK.finiteHybridBellman_of_canonical
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-09-24T23:03:36.698907+00:00
-- url     : https://prove2.me/submissions/41b0bd5d-c71e-441b-bf53-c35727e90d28

import Definitions.Def_GeneralCK_bellman
import Definitions.Def_GeneralCK_finite_law_regional
import Definitions.Def_GeneralCK_statement
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Convex.Jensen
import Mathlib.Analysis.SpecialFunctions.BinaryEntropy
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Theorems.Thm_GeneralCK_B_complement

namespace GeneralCK
open scoped BigOperators





















theorem H_complement (p : ℝ) : H (1 - p) = H p := by simp [H]







end GeneralCK

namespace GeneralCK
open scoped BigOperators



namespace InteriorLaw
variable {ι : Type*} [Fintype ι]









@[simp] theorem avg_const (μ : InteriorLaw ι) (c : ℝ) : μ.avg (fun _ => c) = c := by
  simp only [avg, ← Finset.sum_mul, μ.weight_sum, one_mul]



theorem avg_sub (μ : InteriorLaw ι) (v w : ι → ℝ) :
    μ.avg (fun i => v i - w i) = μ.avg v - μ.avg w := by
  simp [avg, mul_sub, Finset.sum_sub_distrib]






















@[simp] theorem swap_a (μ : InteriorLaw ι) : μ.swap.a = μ.b := rfl
@[simp] theorem swap_b (μ : InteriorLaw ι) : μ.swap.b = μ.a := rfl
@[simp] theorem swap_e (μ : InteriorLaw ι) : μ.swap.e = μ.f := rfl
@[simp] theorem swap_f (μ : InteriorLaw ι) : μ.swap.f = μ.e := rfl
@[simp] theorem complement_a (μ : InteriorLaw ι) : μ.complement.a = 1 - μ.a := by
  change μ.avg (fun i => 1 - μ.left i) = 1 - μ.a
  rw [μ.avg_sub, μ.avg_const]; rfl
@[simp] theorem complement_b (μ : InteriorLaw ι) : μ.complement.b = 1 - μ.b := by
  change μ.avg (fun i => 1 - μ.right i) = 1 - μ.b
  rw [μ.avg_sub, μ.avg_const]; rfl
@[simp] theorem complement_e (μ : InteriorLaw ι) : μ.complement.e = μ.e := by
  simp [e, avg, complement, Function.comp_apply, H_complement]
@[simp] theorem complement_f (μ : InteriorLaw ι) : μ.complement.f = μ.f := by
  simp [f, avg, complement, Function.comp_apply, H_complement]

end InteriorLaw

theorem J_complement (v : ℝ) : J (1 - v) = -J v := by
  unfold J
  rw [sub_sub_cancel, show v / (1 - v) = ((1 - v) / v)⁻¹ from (inv_div _ _).symm,
    Real.log_inv, neg_div]

theorem interiorCost_comm (u v : ℝ) : interiorCost u v = interiorCost v u := by
  unfold interiorCost; ring

theorem interiorCost_complement (u v : ℝ) :
    interiorCost (1 - u) (1 - v) = interiorCost u v := by
  simp only [interiorCost, J_complement]; ring

namespace InteriorLaw
variable {ι : Type*} [Fintype ι]

@[simp] theorem swap_cost (μ : InteriorLaw ι) : μ.swap.cost = μ.cost := by
  simp only [cost, avg, swap, interiorCost_comm (μ.right _) (μ.left _)]
@[simp] theorem complement_cost (μ : InteriorLaw ι) : μ.complement.cost = μ.cost := by
  simp only [cost, avg, complement, interiorCost_complement]
@[simp] theorem swap_gap (μ : InteriorLaw ι) : μ.swap.gap = μ.gap := by
  simp only [gap, swap_a, swap_b, swap_e, swap_f, add_comm]
@[simp] theorem complement_gap (μ : InteriorLaw ι) : μ.complement.gap = μ.gap := by
  simp only [gap, complement_a, complement_b, complement_e, complement_f]
  rw [show (1 - μ.a + (1 - μ.b)) / 2 = 1 - (μ.a + μ.b) / 2 by ring]
  simp only [B_complement]

/-- The genuine symmetries produce the exact canonical domain consumed by the cover. -/
theorem exists_canonical (μ : InteriorLaw ι) :
    ∃ ν : InteriorLaw ι, ν.a ≤ ν.b ∧ ν.a + ν.b ≤ 1 ∧
      ν.gap = μ.gap ∧ ν.cost = μ.cost := by
  by_cases hab : μ.a ≤ μ.b
  · by_cases hs : μ.a + μ.b ≤ 1
    · exact ⟨μ, hab, hs, rfl, rfl⟩
    · refine ⟨μ.complement.swap, ?_, ?_, ?_, ?_⟩
      · simp only [swap_a, swap_b, complement_a, complement_b]; linarith
      · simp only [swap_a, swap_b, complement_a, complement_b]; linarith
      · simp
      · simp
  · by_cases hs : μ.a + μ.b ≤ 1
    · refine ⟨μ.swap, ?_, ?_, ?_, ?_⟩
      · simp only [swap_a, swap_b]; linarith
      · simp only [swap_a, swap_b]; linarith
      · simp
      · simp
    · refine ⟨μ.complement, ?_, ?_, ?_, ?_⟩
      · simp only [complement_a, complement_b]; linarith
      · simp only [complement_a, complement_b]; linarith
      · simp
      · simp

end InteriorLaw

/-- Canonical finite-law inequalities suffice, with feasibility supplied by the law itself. -/
theorem _root_.solution
    (hc : ∀ (k : ℕ) (μ : InteriorLaw (Fin k)),
      μ.a ≤ μ.b → μ.a + μ.b ≤ 1 → μ.gap ≤ μ.cost) : FiniteHybridBellman := by
  intro k w u v hw hsum hu hv
  let μ : InteriorLaw (Fin k) := ⟨w, u, v, hw, hsum, hu, hv⟩
  obtain ⟨ν, hab, hs, hg, hj⟩ := μ.exists_canonical
  have h := hc k ν hab hs
  rw [hg, hj] at h
  exact sub_le_iff_le_add'.mp h

end GeneralCK
