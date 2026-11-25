-- Prove2me | solution 1 for GlobalTheory.T.infinite_product_renormalization
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T18:23:29.315356+00:00
-- url     : https://prove2.me/submissions/b04df08d-d308-43e7-9862-2f8b87979cd1

import Mathlib
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_InfiniteProductRenormalization
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_InfiniteProductRenormalizationStatement
import Theorems.Thm_GlobalTheory_CompanionTheory_SW_TailConst_exists_const_mul_tail


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Topology
open scoped ENNReal NNReal Matrix
set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ (ι : Type) [DecidableEq ι] (a : ι → ℝ) (c : Finset ι → ℝ≥0) (S₁ : Finset ι), (∀ v, 0 ≤ a v) → Summable (fun v => |a v - 1|) → (∀ S, S₁ ⊆ S → ∀ v, v ∉ S → (c S : ℝ) = c (insert v S) * a v) → ∃ (c₀ : ℝ≥0) (S₀ : Finset ι), S₁ ⊆ S₀ ∧ ∀ S, S₀ ⊆ S → (0 < ∏' v : {v // v ∉ S}, a v.1) ∧ (c S : ℝ) = c₀ * ∏' v : {v // v ∉ S}, a v.1 := by
  first | exact @GlobalTheory.CompanionTheory.SW.TailConst.exists_const_mul_tail | exact GlobalTheory.CompanionTheory.SW.TailConst.exists_const_mul_tail | (intros; apply GlobalTheory.CompanionTheory.SW.TailConst.exists_const_mul_tail <;> assumption)
end _root_.GlobalTheory.T
