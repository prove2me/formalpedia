-- Prove2me | solution 1 for GlobalTheory.T.localModel_modulus_properties_on_units
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T22:05:22.745994+00:00
-- url     : https://prove2.me/submissions/cd16f89e-dfff-475a-b2c4-e1a8f6eea4f0

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_LocalModelModulusPropertiesOnUnits
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_IsTermOver
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_LocalModelModulusPropertiesOnUnitsStatement
import Theorems.Thm_GlobalTheory_ModuleUnits_modK_units


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ValuativeRel Formalism.MainNotions.S Formalism.MainNotions.S.Loc
open scoped Pointwise ENNReal Classical
set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E] (M : Model F E), M.OK → (∀ x y : E, IsUnit x → IsUnit y → M.modK (x * y) = M.modK x * M.modK y) ∧ (∀ x : E, IsUnit x → 0 < M.modK x ∧ M.modK (M.L.cj x) = M.modK x) ∧ ∀ x : E, x ∈ M.L.O → (∃ y ∈ M.L.O, x * y = 1) → M.modK x = 1 := by
  first | exact @GlobalTheory.ModuleUnits.modK_units | exact GlobalTheory.ModuleUnits.modK_units | (intros; apply GlobalTheory.ModuleUnits.modK_units <;> assumption)
end _root_.GlobalTheory.T
