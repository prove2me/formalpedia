-- Prove2me | solution 1 for NemytskiiLebesgue.IsCaratheodory.memLp_nemytskii_volume_iff_growth
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T18:39:33.966018+00:00
-- url     : https://prove2.me/submissions/d11e857e-10ac-445c-b32f-9f585e5eb58c

module
public import Mathlib.MeasureTheory.Integral.DominatedConvergence
public import Definitions.Def_LeanPool_NemytskiiLebesgue_Continuity
public import Definitions.Def_LeanPool_NemytskiiLebesgue_ConverseImplication
public import Theorems.Thm_NemytskiiLebesgue_IsCaratheodory_growth_of_memLp_nemytskii_volume
public import Theorems.Thm_NemytskiiLebesgue_IsCaratheodory_memLp_nemytskii_of_growth_real


set_option autoImplicit true
@[expose] public section
public section
open NemytskiiLebesgue
open scoped NemytskiiLebesgue
open MeasureTheory _root_.Filter TopologicalSpace
open scoped NNReal ENNReal Topology
namespace NemytskiiLebesgue
namespace IsCaratheodory
theorem _root_.solution
    {m k : ℕ} {f : ℝ → ℝ^m → ℝ^k} (hf : IsCaratheodory f volume)
    {p : ℝ≥0∞} (h1p : 1 ≤ p) (hp : p < ⊤)
    {q : ℝ≥0∞} (h1q : 1 ≤ q) (hq : q < ⊤) :
    (∀ u : ℝ → ℝ^m, MemLp u p volume → MemLp (fun x : ℝ => f x (u x)) q volume) ↔
    (∃ a : ℝ → ℝ, MemLp a q volume ∧ ∃ C : ℝ, 0 ≤ C ∧
      ∀ᵐ x : ℝ ∂volume, ∀ ξ : ℝ^m, ‖f x ξ‖ ≤ |a x| + C * ‖ξ‖ ^ (p / q).toReal) :=
  ⟨hf.growth_of_memLp_nemytskii_volume h1p hp h1q hq,
  fun ⟨_, ha, _, hC, haCpq⟩ _ => hf.memLp_nemytskii_of_growth_real h1p hp h1q hq ha hC haCpq⟩
end IsCaratheodory
end NemytskiiLebesgue
