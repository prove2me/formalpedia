-- Prove2me | solution 1 for HighDimCLT.MultBoot.eq_21
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-21T11:14:00.876516+00:00
-- url     : https://prove2.me/submissions/c68b62a6-4ff9-4f2f-bc7c-31d8ec636a20

import Mathlib
import Definitions.Def_HighDimCLT_MultBoot_Setting
set_option autoImplicit false
open MeasureTheory ProbabilityTheory HighDimCLT.MultBoot

theorem solution (p : ℕ) (hp : 3 ≤ p) (β : ℝ) (hβ : 0 < β) (y w : EuclideanSpace ℝ (Fin p)) :
    0 ≤ Fβ β y w - (⨆ j : Fin p, (w j - y j)) ∧
    Fβ β y w - (⨆ j : Fin p, (w j - y j)) ≤ β⁻¹ * Real.log p := by
  have hp0 : 0 < p := by omega
  have : Nonempty (Fin p) := ⟨⟨0, hp0⟩⟩
  set M : ℝ := ⨆ j : Fin p, (w j - y j) with hM
  have hle : ∀ j, w j - y j ≤ M := fun j => le_ciSup (f := fun j : Fin p => w j - y j) (Set.finite_range _).bddAbove j
  obtain ⟨j0, hj0⟩ : ∃ j0, w j0 - y j0 = M := exists_eq_ciSup_of_finite
  have hlow : Real.exp (β * M) ≤ ∑ j, Real.exp (β * (w j - y j)) := by
    rw [← hj0]
    exact Finset.single_le_sum (f := fun j => Real.exp (β * (w j - y j)))
      (fun j _ => (Real.exp_pos _).le) (Finset.mem_univ j0)
  have hup : ∑ j, Real.exp (β * (w j - y j)) ≤ p * Real.exp (β * M) := by
    calc ∑ j, Real.exp (β * (w j - y j)) ≤ ∑ _j : Fin p, Real.exp (β * M) :=
          Finset.sum_le_sum (fun j _ => Real.exp_le_exp.2 (by nlinarith [hle j]))
      _ = p * Real.exp (β * M) := by simp
  have hpos : 0 < ∑ j, Real.exp (β * (w j - y j)) := lt_of_lt_of_le (Real.exp_pos _) hlow
  have hF : Fβ β y w = β⁻¹ * Real.log (∑ j, Real.exp (β * (w j - y j))) := rfl
  refine ⟨?_, ?_⟩
  · rw [hF]
    have h1 : β * M ≤ Real.log (∑ j, Real.exp (β * (w j - y j))) := by
      rw [← Real.log_exp (β * M)]
      exact Real.log_le_log (Real.exp_pos _) hlow
    have : M ≤ β⁻¹ * Real.log (∑ j, Real.exp (β * (w j - y j))) := by
      rw [le_inv_mul_iff₀ hβ]; linarith
    linarith
  · rw [hF]
    have h1 : Real.log (∑ j, Real.exp (β * (w j - y j))) ≤ Real.log p + β * M := by
      have : Real.log (p * Real.exp (β * M)) = Real.log p + β * M := by
        rw [Real.log_mul (by positivity) (Real.exp_pos _).ne', Real.log_exp]
      rw [← this]
      exact Real.log_le_log hpos hup
    have : β⁻¹ * Real.log (∑ j, Real.exp (β * (w j - y j))) ≤ β⁻¹ * Real.log p + M := by
      have e : β⁻¹ * (Real.log p + β * M) = β⁻¹ * Real.log p + M := by
        field_simp
      calc _ ≤ β⁻¹ * (Real.log p + β * M) := mul_le_mul_of_nonneg_left h1 (inv_nonneg.2 hβ.le)
        _ = _ := e
    linarith
