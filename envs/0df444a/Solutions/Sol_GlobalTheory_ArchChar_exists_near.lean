-- Prove2me | solution 1 for GlobalTheory.ArchChar.exists_near
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T11:59:04.81583+00:00
-- url     : https://prove2.me/submissions/171bd65f-5f17-495b-9910-ac8b2757bccd

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SatakeParameters_ContinuousCharUnitsComplexStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SatakeParameters_CharConstOnTranslatesTrivial
import Theorems.Thm_GlobalTheory_ArchChar_eq_of_tendsto
import Theorems.Thm_GlobalTheory_ArchChar_tendsto_div
import Theorems.Thm_GlobalTheory_ArchChar_abs_coord_le
import Theorems.Thm_GlobalTheory_ArchChar_tendsto_succ
import Theorems.Thm_GlobalTheory_ArchChar_succ_pos
import Theorems.Thm_GlobalTheory_ArchChar_real_trivial

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Filter Topology
open GlobalTheory GlobalTheory.ArchChar
variable {ι : Type} [Fintype ι] [DecidableEq ι]
namespace GlobalTheory.ArchChar
theorem _root_.solution (ψ : (ι → ℂˣ) →* ℂˣ) (hψ : Continuous ψ) (θ : ι → ℂ) (hθ : ∀ i, (θ i).im ≠ 0)
    (T : Set (ι → ℝ)) (C : ℝ) (hT : ∀ y : ι → ℝ, ∃ a ∈ T, ‖a - y‖ ≤ C)
    (hc : ∀ a ∈ T, ψ (shift θ hθ a) = 1) (i : ι) (R : ℝ) :
    ∃ t : ℝ, |t - R| ≤ C ∧ ψ (Pi.mulSingle i (Units.mk0 _ (add_ne (hθ i) t))) = 1 := by
  let y : ℕ → ι → ℝ := fun m j => if j = i then R else ((m : ℝ) + 1) * 1
  choose A hA hAd using fun m => hT (y m)
  have hAi : ∀ m, A m i ∈ Set.Icc (R - C) (R + C) := by
    intro m
    have h : |A m i - R| ≤ C := by simpa [y] using abs_coord_le (hAd m) i
    rw [abs_le] at h
    constructor <;> linarith [h.1, h.2]
  obtain ⟨t, ht, φ, hφ, hlim⟩ := isCompact_Icc.tendsto_subseq hAi
  refine ⟨t, ?_, ?_⟩
  · rw [abs_le]
    constructor <;> linarith [ht.1, ht.2]
  · let D : ℕ → ι → ℂˣ := fun m => realUnits (fun j => if j = i then 1 else (m : ℝ) + 1)
      (fun j => by split_ifs <;> [exact one_pos; exact succ_pos m])
    have hD : ∀ m, ψ (D m) = 1 := fun m => real_trivial ψ hψ θ hθ T C 1 hT hc _ _
    have hconv : ∀ j, Tendsto (fun m => ((shift θ hθ (A (φ m)) * (D (φ m))⁻¹) j : ℂ)) atTop
        (𝓝 ((Pi.mulSingle i (Units.mk0 _ (add_ne (hθ i) t)) : ι → ℂˣ) j : ℂ)) := by
      intro j
      by_cases hj : j = i
      · subst hj
        simp [shift, D, realUnits]
        exact ((Complex.continuous_ofReal.tendsto t).comp hlim).add_const _
      · have h1 := tendsto_div (θ j) 1 C tendsto_succ (a := fun m => A m j) (fun m => by
            simpa [y, hj] using abs_coord_le (hAd m) j)
        have h2 := h1.comp hφ.tendsto_atTop
        convert h2 using 1
        · funext m
          simp [shift, D, realUnits, hj, div_eq_mul_inv]
        · simp [hj]
    have heq := eq_of_tendsto ψ hψ (X' := fun _ => 1) (w' := 1)
      (fun m => by rw [map_mul, map_inv, hc _ (hA _), hD, inv_one, mul_one, map_one]) hconv
      (fun j => by simp)
    rw [heq, map_one]
end GlobalTheory.ArchChar
