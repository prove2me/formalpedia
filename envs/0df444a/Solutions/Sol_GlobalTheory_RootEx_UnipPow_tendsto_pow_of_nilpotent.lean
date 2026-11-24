-- Prove2me | solution 1 for GlobalTheory.RootEx.UnipPow.tendsto_pow_of_nilpotent
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T22:32:49.554749+00:00
-- url     : https://prove2.me/submissions/4e3c7c0f-6816-438a-b638-da06ed5d84e0

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_TwistedDiscreteSeries_FramePositiveSum
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_SimpleSumRowCol
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_RootExchangeUnipotentExistsResidueCardPowMemNhds
import Theorems.Thm_GlobalTheory_RootEx_UnipPow_tendsto_choose
import Theorems.Thm_GlobalTheory_RootEx_UnipPow_add_one_pow_eq
import Theorems.Thm_GlobalTheory_StepData_IntM_add
import Theorems.Thm_GlobalTheory_StepData_MaxM_add


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory ValuativeRel Matrix Topology GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.IndefiniteRowSideFullHecke.FramePositiveSum
open GlobalTheory GlobalTheory.RootEx GlobalTheory.RootEx.UnipPow
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
namespace GlobalTheory.RootEx.UnipPow
theorem _root_.solution {ι : Type} [Fintype ι] [DecidableEq ι] (hq : (resCard k).Prime)
    {g : Matrix ι ι k} {d : ℕ} (ha : (g - 1) ^ (d + 1) = 0) :
    Filter.Tendsto (fun m : ℕ => g ^ (resCard k ^ m)) Filter.atTop (𝓝 1) := by
  have hexp : ∀ m : ℕ, g ^ (resCard k ^ m) =
      ∑ i ∈ Finset.range (d + 1), (((resCard k ^ m).choose i : ℕ) : k) • (g - 1) ^ i := by
    intro m
    have h := add_one_pow_eq ha (resCard k ^ m)
    rw [sub_add_cancel] at h
    rw [h]
    exact Finset.sum_congr rfl fun i _ => (Nat.cast_smul_eq_nsmul k _ _).symm
  have hlim := (tendsto_finsetSum (Finset.range d) fun i _ =>
    (tendsto_choose hq (Nat.succ_ne_zero i)).smul_const ((g - 1) ^ (i + 1))).add
    (tendsto_const_nhds (x := (1 : Matrix ι ι k)))
  simp only [zero_smul, Finset.sum_const_zero, zero_add] at hlim
  refine hlim.congr fun m => ?_
  rw [hexp, Finset.sum_range_succ']
  simp
end GlobalTheory.RootEx.UnipPow
