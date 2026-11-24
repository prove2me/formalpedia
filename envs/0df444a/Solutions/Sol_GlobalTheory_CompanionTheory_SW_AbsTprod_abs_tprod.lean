-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.SW.AbsTprod.abs_tprod
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T13:30:57.180346+00:00
-- url     : https://prove2.me/submissions/0c98c139-cf74-4852-b392-32fbc9093856

import Mathlib
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_InfiniteProductMultipliable
import Theorems.Thm_GlobalTheory_CompanionTheory_SW_AbsTprod_multipliable_of_summable_abs_sub_one
import Theorems.Thm_GlobalTheory_CompanionTheory_SW_AbsTprod_tprod_nonneg_of_nonneg
import Theorems.Thm_GlobalTheory_CompanionTheory_SW_AbsTprod_tprod_ne_zero_of_summable
import Theorems.Thm_GlobalTheory_CompanionTheory_SW_AbsTprod_tprod_eq_prod_mul_tprod_compl

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
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.SW GlobalTheory.CompanionTheory.SW.AbsTprod
namespace GlobalTheory.CompanionTheory.SW.AbsTprod
theorem _root_.solution : ∀ (ι : Type) (a : ι → ℝ), Summable (fun v => |a v - 1|) → Multipliable a ∧ (∀ S : Finset ι, Multipliable (fun v : {v // v ∉ S} => a v.1) ∧ ∏' v, a v = (∏ v ∈ S, a v) * ∏' v : {v // v ∉ S}, a v.1) ∧ ((∀ v, 0 < a v) → 0 < ∏' v, a v) ∧ ((∀ v, 0 ≤ a v) → 0 ≤ ∏' v, a v) := by
  intro ι a h
  have hm := GlobalTheory.CompanionTheory.SW.AbsTprod.multipliable_of_summable_abs_sub_one h
  refine ⟨hm, fun S => GlobalTheory.CompanionTheory.SW.AbsTprod.tprod_eq_prod_mul_tprod_compl h S, fun hpos => ?_,
    fun h0 => GlobalTheory.CompanionTheory.SW.AbsTprod.tprod_nonneg_of_nonneg hm h0⟩
  exact lt_of_le_of_ne (GlobalTheory.CompanionTheory.SW.AbsTprod.tprod_nonneg_of_nonneg hm fun v => (hpos v).le)
    (GlobalTheory.CompanionTheory.SW.AbsTprod.tprod_ne_zero_of_summable h fun v => (hpos v).ne').symm
end GlobalTheory.CompanionTheory.SW.AbsTprod
