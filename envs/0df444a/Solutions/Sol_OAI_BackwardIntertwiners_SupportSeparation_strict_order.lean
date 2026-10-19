-- Prove2me | solution 1 for OAI.BackwardIntertwiners.SupportSeparation.strict_order
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-18T03:02:26.669835+00:00
-- url     : https://prove2.me/submissions/e71a2e6f-8691-496f-a6d5-e1a1574b8ee3

-- Generated from openai/math@1581d4c lean/OAI/Analysis/BackwardIntertwiners/FiberTails.lean:L49-L72
-- (upload_full_project.md Phase 4): solution for node OAI.BackwardIntertwiners.SupportSeparation.strict_order. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` has its type (`type_of%`) and is proved by it.
import Mathlib
import Definitions.Def_BackwardIntertwiners
import Definitions.Def_OAI_Analysis_BackwardIntertwiners_ConvexEnvelope
import Definitions.Def_OAI_Analysis_BackwardIntertwiners_ConvolutionBounds
import Definitions.Def_OAI_Analysis_BackwardIntertwiners_CoefficientSupport
import Definitions.Def_OAI_Analysis_BackwardIntertwiners_WeightSeparation
import Definitions.Def_OAI_Analysis_BackwardIntertwiners_FiberTails
import Theorems.Thm_OAI_BackwardIntertwiners_SupportSeparation_of_bounded

-- ---- from OAI.Analysis.BackwardIntertwiners.FiberTails ----
namespace OAI

namespace BackwardIntertwiners
open Filter
open scoped Topology
noncomputable section

lemma SupportSeparation.strict_order {w : ℤ → ℝ} (hsep : SupportSeparation w)
    {b c : ℤ → ℂ} (hbn : ∃ j, b j ≠ 0) (hcn : ∃ j, c j ≠ 0)
    {B C : ℝ} (hB : 0 < B) (hC : 0 < C)
    (hb : ∀ j, ‖b j‖ ≤ B*w j) (hc : ∀ j, ‖c j‖*w j ≤ C)
    (hz : ∀ r : ℕ, (∑' j : ℤ, b j * c (j-r)) = 0)
    {i j : ℤ} (hbi : b i ≠ 0) (hcj : c j ≠ 0) : i < j := by
  obtain ⟨t, h, hbt, hch, hbmax, hcmin, hth⟩ :=
    hsep.of_bounded hbn hcn hB hC hb hc (fun r _ => hz r)
  have hit : i ≤ t := by by_contra! hh; exact hbi (hbmax i hh)
  have hhj : h ≤ j := by by_contra! hh; exact hcj (hcmin j hh)
  have hstrict : t < h := by
    by_contra! hht
    have he : t = h := le_antisymm hth hht
    have hsingle : (∑' k : ℤ, b k*c k) = b t*c h := by
      rw [tsum_eq_single t, he]
      intro k hk
      by_cases hkt : t < k
      · simp [hbmax k hkt]
      · rw [hcmin k (by omega), mul_zero]
    have hzero := hz 0
    simp only [Nat.cast_zero, sub_zero] at hzero
    rw [hsingle] at hzero
    exact (mul_ne_zero hbt hch) hzero
  omega

end
end BackwardIntertwiners

end OAI

-- ---- platform node ----
open OAI OAI.BackwardIntertwiners
open Filter
open scoped Topology


theorem solution : type_of% @_root_.OAI.BackwardIntertwiners.SupportSeparation.strict_order := @_root_.OAI.BackwardIntertwiners.SupportSeparation.strict_order
