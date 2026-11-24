-- Prove2me | solution 1 for GlobalTheory.ArchChar.const_eq_one
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T11:59:03.909611+00:00
-- url     : https://prove2.me/submissions/fb9aeae1-42f2-42c6-a34b-78c5d0043424

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
    (T : Set (ι → ℝ)) (C : ℝ) (c : ℂˣ) (hT : ∀ y : ι → ℝ, ∃ a ∈ T, ‖a - y‖ ≤ C)
    (hc : ∀ a ∈ T, ψ (shift θ hθ a) = c) : c = 1 := by
  have hD : ∀ m : ℕ, ψ (realUnits (fun _ : ι => (m : ℝ) + 1) (fun _ => succ_pos m)) = 1 :=
    fun m => real_trivial ψ hψ θ hθ T C c hT hc _ _
  choose A hA hAd using fun m : ℕ => hT (fun _ : ι => ((m : ℝ) + 1) * 1)
  obtain ⟨a₀, ha₀, -⟩ := hT 0
  have hlim : ∀ i, Tendsto (fun m => ((shift θ hθ (A m) *
      (realUnits (fun _ : ι => (m : ℝ) + 1) (fun _ => succ_pos m))⁻¹) i : ℂ)) atTop
      (𝓝 ((1 : ι → ℂˣ) i : ℂ)) := by
    intro i
    have := tendsto_div (θ i) 1 C tendsto_succ (a := fun m => A m i)
      (fun m => abs_coord_le (hAd m) i)
    convert this using 1
    · funext m
      simp [shift, realUnits, div_eq_mul_inv]
    · simp
  have heq := eq_of_tendsto ψ hψ (X' := fun _ => shift θ hθ a₀) (w' := shift θ hθ a₀)
    (fun m => by rw [map_mul, map_inv, hD, hc _ (hA m), hc _ ha₀, inv_one, mul_one]) hlim
    (fun i => tendsto_const_nhds)
  rw [map_one, hc _ ha₀] at heq
  exact heq.symm
end GlobalTheory.ArchChar
