-- Prove2me | solution 1 for GlobalTheory.Hk.LogDeriv.hasDerivAt_of_conv
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T07:40:33.94051+00:00
-- url     : https://prove2.me/submissions/4f572fec-6554-4dae-a622-a4c5792b2988

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_GlobalTwisting_LamIdealOfNotPrimePow
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_RayClassLFunctionFamilyContinuationGrowth
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_TsumOneDivRpowLe
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_RayClassFamilyLogDerivReGtOne
import Theorems.Thm_GlobalTheory_Hk_LogDeriv_absc_lt

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
open GlobalTheory GlobalTheory.Hk GlobalTheory.Hk.LogDeriv
open LSeries
open scoped LSeries.notation
namespace GlobalTheory.Hk.LogDeriv
theorem _root_.solution {a l : ℕ → ℂ} (ha : ∀ s : ℂ, 1 < s.re → LSeriesSummable a s)
    (hl : ∀ s : ℂ, 1 < s.re → LSeriesSummable l s)
    (hc : ∀ n : ℕ, n ≠ 0 → Complex.log n * a n = (l ⍟ a) n) {s : ℂ} (hs : 1 < s.re) :
    HasDerivAt (LSeries a) (-(LSeries l s * LSeries a s)) s := by
  have h := LSeries_hasDerivAt (absc_lt ha hs)
  have hlog : LSeries (logMul a) s = LSeries (l ⍟ a) s := LSeries_congr (fun {n} hn => hc n hn) s
  rwa [hlog, LSeries_convolution' (hl s hs) (ha s hs)] at h
end GlobalTheory.Hk.LogDeriv
