-- Prove2me | solution 1 for GlobalTheory.UnitDiscAlg.QuotAlg.cm_mul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T21:49:44.379804+00:00
-- url     : https://prove2.me/submissions/3a1d5bd8-ba95-4998-a195-4cb16ba5768f

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
variable {R : Type*} [CommRing R]
namespace GlobalTheory.UnitDiscAlg.QuotAlg
theorem _root_.solution {e x y α β : R} (hx : x * e = α * e) (hy : y * e = β * e) :
    x * y * e = α * β * e := by
  linear_combination y * hx + α * hy
end GlobalTheory.UnitDiscAlg.QuotAlg
