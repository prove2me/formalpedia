-- Prove2me | solution 1 for GlobalTheory.UnitDiscAlg.QuotAlg.comp2
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T21:49:46.161459+00:00
-- url     : https://prove2.me/submissions/b71cad5b-1516-44b4-8878-6662a814e86c

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
theorem _root_.solution {e₁ e₂ e₃ : R} (h12 : e₁ * e₂ = 0) (h22 : e₂ * e₂ = e₂) (h23 : e₂ * e₃ = 0)
    (α β γ : R) : (α * e₁ + β * e₂ + γ * e₃) * e₂ = β * e₂ := by
  linear_combination α * h12 + β * h22 + γ * h23
end GlobalTheory.UnitDiscAlg.QuotAlg
