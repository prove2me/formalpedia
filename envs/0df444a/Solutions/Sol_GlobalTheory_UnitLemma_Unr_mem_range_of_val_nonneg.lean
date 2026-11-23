-- Prove2me | solution 1 for GlobalTheory.UnitLemma.Unr.mem_range_of_val_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T21:00:34.007281+00:00
-- url     : https://prove2.me/submissions/5ceacbe0-4bde-41f8-be16-be9661886f83

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_OverExtAlgebraMap
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_MemRangeOfValNonneg

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.UnitLemma GlobalTheory.UnitLemma.Unr
open GlobalTheory.UnitLemma
namespace GlobalTheory.UnitLemma.Unr
theorem _root_.solution (K : UQ) (z : K.E) (h : 0 ≤ val K.O z) :
    ∃ a : K.O, algebraMap K.O K.E a = z := by
  by_cases hz : z = 0
  · exact ⟨0, by simp [hz]⟩
  have h0 : (IsDiscreteValuationRing.maximalIdeal K.O).valuation K.E z ≠ 0 := by simpa using hz
  have hle : (IsDiscreteValuationRing.maximalIdeal K.O).valuation K.E z ≤ 1 := by
    unfold val at h
    rw [← WithZero.exp_log h0, ← WithZero.exp_zero, WithZero.exp_le_exp]
    omega
  obtain ⟨a, ha⟩ := IsDiscreteValuationRing.exists_lift_of_le_one hle
  exact ⟨a, ha⟩
end GlobalTheory.UnitLemma.Unr
