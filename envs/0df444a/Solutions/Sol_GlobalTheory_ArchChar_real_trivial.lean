-- Prove2me | solution 1 for GlobalTheory.ArchChar.real_trivial
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T05:39:56.734205+00:00
-- url     : https://prove2.me/submissions/b695aef3-9b20-4264-93ec-6dc2fc2ffe97

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SatakeParameters_ContinuousCharUnitsComplexStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SatakeParameters_CharConstOnTranslatesTrivial
import Theorems.Thm_GlobalTheory_ArchChar_eq_of_tendsto
import Theorems.Thm_GlobalTheory_ArchChar_tendsto_div
import Theorems.Thm_GlobalTheory_ArchChar_abs_coord_le
import Theorems.Thm_GlobalTheory_ArchChar_tendsto_succ
import Theorems.Thm_GlobalTheory_ArchChar_succ_pos

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
    (hc : ∀ a ∈ T, ψ (shift θ hθ a) = c) (r : ι → ℝ) (hr : ∀ i, 0 < r i) :
    ψ (realUnits r hr) = 1 := by
  let D : ℕ → ι → ℂˣ := fun m => realUnits (fun _ => (m : ℝ) + 1) (fun _ => succ_pos m)
  have key : ∀ (q : ι → ℝ) (hq : ∀ i, 0 < q i), ∃ X : ℕ → ι → ℂˣ,
      (∀ m, ψ (X m) = c * (ψ (D m))⁻¹) ∧
      ∀ i, Tendsto (fun m => (X m i : ℂ)) atTop (𝓝 (realUnits q hq i : ℂ)) := by
    intro q hq
    choose A hA hAd using fun m : ℕ => hT (fun i => ((m : ℝ) + 1) * q i)
    refine ⟨fun m => shift θ hθ (A m) * (D m)⁻¹, fun m => ?_, fun i => ?_⟩
    · rw [map_mul, map_inv, hc _ (hA m)]
    · have := tendsto_div (θ i) (q i) C tendsto_succ (a := fun m => A m i)
        (fun m => abs_coord_le (hAd m) i)
      convert this using 1
      · funext m
        simp [shift, realUnits, D, div_eq_mul_inv]
      · simp [realUnits]
  obtain ⟨X, hX, hXl⟩ := key r hr
  obtain ⟨X', hX', hX'l⟩ := key (fun _ => 1) (fun _ => one_pos)
  have heq := eq_of_tendsto ψ hψ (fun m => (hX m).trans (hX' m).symm) hXl hX'l
  rw [heq]
  have h1 : realUnits (fun _ : ι => (1 : ℝ)) (fun _ => one_pos) = 1 := by
    funext i
    ext
    simp [realUnits]
  rw [h1, map_one]
end GlobalTheory.ArchChar
