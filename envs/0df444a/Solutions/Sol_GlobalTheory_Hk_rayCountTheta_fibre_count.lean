-- Prove2me | solution 1 for GlobalTheory.Hk.rayCountTheta_fibre_count
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T17:35:04.920081+00:00
-- url     : https://prove2.me/submissions/dfd750d3-3d29-4422-ae74-588a383ebd81

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_GlobalTwisting_LamIdealOfNotPrimePow
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_QFormCountStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_ThetaQFormStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_RayClassIdealCountEqNcardShiftedBinaryFormStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_RayCountThetaFibreCount

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Complex ArithmeticFunction MeasureTheory Filter Topology NumberField GlobalTheory.Hk GlobalTheory.Mem
open scoped Classical
open GlobalTheory GlobalTheory.Hk
namespace GlobalTheory.Hk
theorem _root_.solution {ι : Type} (Q : ι → ℝ) (q : ι → ℕ) (hq1 : ∀ v, 1 ≤ q v) (hq : ∀ v, Q v = q v)
    (y : ℝ) (hy : 1 ≤ y) (hfin : {v | Q v ≤ y}.Finite) :
    ∑ n ∈ Finset.Icc 1 ⌊y⌋₊, (({v | Q v = (n : ℕ)}.ncard : ℕ) : ℝ) = (({v | Q v ≤ y}.ncard : ℕ) : ℝ) := by
  have hmaps : ∀ v ∈ hfin.toFinset, q v ∈ Finset.Icc 1 ⌊y⌋₊ := by
    intro v hv
    rw [Set.Finite.mem_toFinset, Set.mem_ofPred_eq, hq] at hv
    exact Finset.mem_Icc.mpr ⟨hq1 v, Nat.le_floor hv⟩
  have hfib : ∀ n ∈ Finset.Icc 1 ⌊y⌋₊,
      {v | Q v = (n : ℕ)}.ncard = (hfin.toFinset.filter fun v => q v = n).card := by
    intro n hn
    rw [← Set.ncard_coe_finset]
    congr 1
    ext v
    simp only [Set.mem_ofPred_eq, Finset.coe_filter, Set.Finite.mem_toFinset, hq, Nat.cast_inj]
    constructor
    · rintro rfl
      exact ⟨le_trans (Nat.cast_le.mpr (Finset.mem_Icc.mp hn).2) (Nat.floor_le (by linarith)), rfl⟩
    · exact fun h => h.2
  rw [show (∑ n ∈ Finset.Icc 1 ⌊y⌋₊, (({v | Q v = (n : ℕ)}.ncard : ℕ) : ℝ)) =
      ∑ n ∈ Finset.Icc 1 ⌊y⌋₊, (((hfin.toFinset.filter fun v => q v = n).card : ℕ) : ℝ) from
    Finset.sum_congr rfl fun n hn => by rw [hfib n hn]]
  rw [← Nat.cast_sum, ← Finset.card_eq_sum_card_fiberwise hmaps, ← Set.ncard_coe_finset,
    Set.Finite.coe_toFinset]
end GlobalTheory.Hk
