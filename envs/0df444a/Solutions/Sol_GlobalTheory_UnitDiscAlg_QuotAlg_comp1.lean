-- Prove2me | solution 1 for GlobalTheory.UnitDiscAlg.QuotAlg.comp1
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T21:49:45.409259+00:00
-- url     : https://prove2.me/submissions/e61e84c3-17ea-4910-972e-c3ac427004ad

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
theorem _root_.solution {e₁ e₂ e₃ : R} (h11 : e₁ * e₁ = e₁) (h12 : e₁ * e₂ = 0) (h13 : e₁ * e₃ = 0)
    (α β γ : R) : (α * e₁ + β * e₂ + γ * e₃) * e₁ = α * e₁ := by
  linear_combination α * h11 + β * h12 + γ * h13
end GlobalTheory.UnitDiscAlg.QuotAlg
