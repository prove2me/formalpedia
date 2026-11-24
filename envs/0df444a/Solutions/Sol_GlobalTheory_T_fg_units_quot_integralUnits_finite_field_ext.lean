-- Prove2me | solution 1 for GlobalTheory.T.fg_units_quot_integralUnits_finite_field_ext
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T21:08:06.731867+00:00
-- url     : https://prove2.me/submissions/5bc17aa0-2ef0-4a9b-9cb7-d466ef0ca397

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_FgUnitsQuotIntegralUnitsFiniteFieldExt
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_UnitLemmaGroup
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_FgUnitsQuotIntegralUnitsFiniteFieldExtStatement
import Theorems.Thm_GlobalTheory_FieldUnitsQuotFG_fg_units_quot


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.UnitLemma Polynomial
set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ (K : UQ) (L : Type) [Field L] [Algebra K.O L] [Algebra K.E L] [IsScalarTower K.O K.E L] [FiniteDimensional K.E L], Group.FG (Lˣ ⧸ intUnits K.O L) := by
  first | exact @GlobalTheory.FieldUnitsQuotFG.fg_units_quot | exact GlobalTheory.FieldUnitsQuotFG.fg_units_quot | (intros; apply GlobalTheory.FieldUnitsQuotFG.fg_units_quot <;> assumption)
end _root_.GlobalTheory.T
