-- Prove2me | solution 1 for GlobalTheory.UnitDiscAlg.QuotAlg.eq_of_comp
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T21:49:47.82761+00:00
-- url     : https://prove2.me/submissions/40e24150-4802-44f9-939a-0c7382608c60

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
theorem _root_.solution {e₁ e₂ e₃ x y : R} (hs : e₁ + e₂ + e₃ = 1)
    (h1 : x * e₁ = y * e₁) (h2 : x * e₂ = y * e₂) (h3 : x * e₃ = y * e₃) : x = y := by
  linear_combination h1 + h2 + h3 - (x - y) * hs
end GlobalTheory.UnitDiscAlg.QuotAlg
