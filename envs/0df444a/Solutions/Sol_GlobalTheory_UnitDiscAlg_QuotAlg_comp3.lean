-- Prove2me | solution 1 for GlobalTheory.UnitDiscAlg.QuotAlg.comp3
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T21:49:46.840977+00:00
-- url     : https://prove2.me/submissions/0a989acf-6381-4f98-8505-36819a20a18a

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
theorem _root_.solution {e₁ e₂ e₃ : R} (h13 : e₁ * e₃ = 0) (h23 : e₂ * e₃ = 0) (h33 : e₃ * e₃ = e₃)
    (α β γ : R) : (α * e₁ + β * e₂ + γ * e₃) * e₃ = γ * e₃ := by
  linear_combination α * h13 + β * h23 + γ * h33
end GlobalTheory.UnitDiscAlg.QuotAlg
