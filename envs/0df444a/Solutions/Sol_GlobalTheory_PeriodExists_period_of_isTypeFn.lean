-- Prove2me | solution 1 for GlobalTheory.PeriodExists.period_of_isTypeFn
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T14:31:28.236798+00:00
-- url     : https://prove2.me/submissions/00acbd13-62e2-4d43-9d03-2acb8b7f46b8

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_Signature
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_ExistsHermCoordOfDatum
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_SignatureHermitianModelOfDatumStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_HermFormConjDiag
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_TypeFnPeriodExistModuliNonempty
import Theorems.Thm_GlobalTheory_PeriodExists_exists_equiv_of_isTypeFn
import Theorems.Thm_GlobalTheory_PeriodExists_exists_isPeriod_of_equiv
import Theorems.Thm_GlobalTheory_PeriodExists_exists_typeFn_period

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField Matrix
open scoped nonZeroDivisors ComplexConjugate
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.PeriodExists
variable {E : Type} [Field E] [NumberField E] [IsCMField E]
namespace GlobalTheory.PeriodExists
theorem _root_.solution (H : Host E) (D : Datum H) (g : ℕ) (ty : Fin g → (E →+* ℂ))
    (h : IsTypeFn H D.p D.q ty) :
    g = Module.finrank ℚ E / 2 * (D.p + D.q) ∧ ∃ P, IsPeriod D ty P := by
  obtain ⟨g', ty', h', hg, P, hP⟩ := exists_typeFn_period H D
  obtain ⟨e, he⟩ := exists_equiv_of_isTypeFn h h'
  exact ⟨(Fin.equiv_iff_eq.1 ⟨e⟩).trans hg, exists_isPeriod_of_equiv e he hP⟩
end GlobalTheory.PeriodExists
