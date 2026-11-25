-- Prove2me | solution 1 for GlobalTheory.SW.prod_pow_le_prod_of_mono
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T00:09:54.288582+00:00
-- url     : https://prove2.me/submissions/cb053080-0cb8-4adb-92ae-e002591c0ee8

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SpanningFamilies_IsHeatZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_ExistsNeZeroNormSqLeMulCovolumeRpow
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_ExistsLinearIndependentOfRatIndependent
import Theorems.Thm_GlobalTheory_spanCovol_bot
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.spanCovol_bot



set_option autoImplicit false
open Matrix Complex NumberField GlobalTheory.SW Filter Topology
open ReciprocityTheory.ChartRestriction.G.FD (cc herm)
open scoped ComplexConjugate ComplexOrder Real
open GlobalTheory GlobalTheory.SW
namespace GlobalTheory.SW
theorem _root_.solution (l : ℕ → ℝ) (hl : ∀ i, 0 ≤ l i) (d N : ℕ)
    (hm : ∀ i j, i ≤ j → j ≤ d * N → l i ≤ l j) :
    ∏ i ∈ Finset.range N, l (d * i + 1) ^ d ≤ ∏ j ∈ Finset.range (d * N), l (j + 1) := by
  induction N with
  | zero => simp
  | succ N ih =>
    rw [Finset.prod_range_succ, mul_add, mul_one, Finset.prod_range_add]
    refine mul_le_mul (ih fun i j hij hj => hm i j hij (by nlinarith)) ?_ (pow_nonneg (hl _) _)
      (Finset.prod_nonneg fun _ _ => hl _)
    calc l (d * N + 1) ^ d = ∏ _j ∈ Finset.range d, l (d * N + 1) := by simp
      _ ≤ _ := Finset.prod_le_prod (fun _ _ => hl _) fun j hj => hm _ _ (by omega) (by
          have := Finset.mem_range.1 hj
          rw [mul_add]; omega)
end GlobalTheory.SW
