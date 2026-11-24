-- Prove2me | solution 1 for GlobalTheory.UnitDiscAlg.QuotAlg.eq_one_of_mul_eq_one
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T21:49:48.743076+00:00
-- url     : https://prove2.me/submissions/4dc2adb6-8c4e-4529-92f5-e9eecfe9dd89

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_CommOfBezout
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_NormDetLeOneOfEntriesNormLeOne
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_IsUnitAndIntegInvOfNormDetEqOne
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_UltrametricNormDetOneAddSmulStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_QuotientIntegralUnit

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.UnitDiscAlg
open GlobalTheory GlobalTheory.UnitDiscAlg GlobalTheory.UnitDiscAlg.QuotAlg
namespace GlobalTheory.UnitDiscAlg.QuotAlg
theorem _root_.solution {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (ha1 : a ≤ 1) (hb1 : b ≤ 1)
    (hab : a * b = 1) : a = 1 := by nlinarith
end GlobalTheory.UnitDiscAlg.QuotAlg
