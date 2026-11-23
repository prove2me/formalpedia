-- Prove2me | solution 1 for GlobalTheory.Hk.LogDeriv.absc_lt
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T07:37:48.897509+00:00
-- url     : https://prove2.me/submissions/78b129b8-c5ca-4caf-b3a5-d1cbfb08a061

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_GlobalTwisting_LamIdealOfNotPrimePow
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_RayClassLFunctionFamilyContinuationGrowth
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_TsumOneDivRpowLe
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_RayClassFamilyLogDerivReGtOne

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
theorem _root_.solution {a : ℕ → ℂ} (ha : ∀ s : ℂ, 1 < s.re → LSeriesSummable a s) {s : ℂ} (hs : 1 < s.re) :
    abscissaOfAbsConv a < s.re := by
  have h : abscissaOfAbsConv a ≤ ((1 : ℝ) : EReal) :=
    LSeries.abscissaOfAbsConv_le_of_forall_lt_LSeriesSummable fun y hy =>
      ha (y : ℂ) (by simpa using hy)
  exact lt_of_le_of_lt h (EReal.coe_lt_coe_iff.mpr hs)
end GlobalTheory.Hk.LogDeriv
