-- Prove2me | solution 1 for GlobalTheory.T.typeFn_period_exist_moduli_nonempty
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T15:21:54.426007+00:00
-- url     : https://prove2.me/submissions/a64ebcb8-358f-47e6-9bb9-6ec9c45c5795

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_TypeFnPeriodExistModuliNonempty
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_Signature
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_TypeFnPeriodExistModuliNonemptyStatement
import Theorems.Thm_GlobalTheory_PeriodExists_typeFn_period_exist


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField Matrix
open scoped nonZeroDivisors
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H), (∃ (g : ℕ) (ty : Fin g → (E →+* ℂ)), IsTypeFn H D.p D.q ty) ∧ (∀ (g : ℕ) (ty : Fin g → (E →+* ℂ)), IsTypeFn H D.p D.q ty → g = Module.finrank ℚ E / 2 * (D.p + D.q) ∧ ∃ P, IsPeriod D ty P) ∧ (N1c → 1 ≤ D.p + D.q → ∀ (l : Level H) (Xo : Moduli D l) (c : Coeff l), Nonempty (Xo.XF c)) := by
  first | exact @GlobalTheory.PeriodExists.typeFn_period_exist | exact GlobalTheory.PeriodExists.typeFn_period_exist | (intros; apply GlobalTheory.PeriodExists.typeFn_period_exist <;> assumption)
end _root_.GlobalTheory.T
