-- Prove2me | solution 1 for GlobalTheory.UnitLemma.Unr.valuation_map_eq_of_unr
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T22:01:41.95466+00:00
-- url     : https://prove2.me/submissions/f5db82f3-501f-459a-b0e1-c2c976d37fa1

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_OverExtAlgebraMap
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_MemRangeOfValNonneg
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ExistsIntegerSpanningFamilyOfUnramifiedExt

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
open GlobalTheory.UnitLemma IsDedekindDomain IsLocalRing
variable {K K' : UQ} {d : ℕ} {φ : K.E →+* K'.E}
namespace GlobalTheory.UnitLemma.Unr
theorem _root_.solution (hU : IsUnrExt K K' d φ) (x : K.E) :
    (IsDiscreteValuationRing.maximalIdeal K'.O).valuation K'.E (φ x) =
      (IsDiscreteValuationRing.maximalIdeal K.O).valuation K.E x := by
  by_cases hx : x = 0
  · simp [hx]
  have h := hU.2.2.1 x
  unfold val at h
  have h0 : (IsDiscreteValuationRing.maximalIdeal K.O).valuation K.E x ≠ 0 := by simpa using hx
  have h0' : (IsDiscreteValuationRing.maximalIdeal K'.O).valuation K'.E (φ x) ≠ 0 := by simpa using hx
  rw [← WithZero.exp_log h0, ← WithZero.exp_log h0']
  congr 1
  omega
end GlobalTheory.UnitLemma.Unr
