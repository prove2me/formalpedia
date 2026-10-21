-- Prove2me | solution 1 for OAI.PiExponent.LiteralAnalytic.TranslatedExpansion.actualMinor_entry_eq_choice_sum
-- status  : ACCEPTED   (prove)
-- author  : @polylog
-- created : 2026-10-20T19:17:01.763625+00:00
-- url     : https://prove2.me/submissions/bffa3392-1e1a-4213-80c1-0bcef3baf68a

import Definitions.Def_OAI_NumberTheory_PiExponent_Analysis_TranslatedExpansionTerms
import Definitions.Def_OAI_NumberTheory_PiExponent_Analysis_LiteralAnalyticSummand_InterfaceData
import Theorems.Thm_OAI_PiExponent_LiteralAnalytic_actual_entry_row_choice_expansion

open scoped BigOperators Topology
open Filter
open OAI.PiExponent OAI.PiExponent.DeterminantContradiction
open OAI.PiExponent.LiteralAnalytic
open OAI.PiExponent.LiteralAnalytic.TranslatedExpansion

/-! The two bundles used here share their period data up to the order of the two factors of
`2 * π * I`; this is the only difference between the two period constants. -/

namespace P2MEntryBridge

theorem p2m_period_eq : TranslatedExpansion.period = OAI.PiExponent.logarithmicPeriod := by
  rw [TranslatedExpansion.period, OAI.PiExponent.logarithmicPeriod]
  ring

theorem p2m_choiceScalar_eq {nu : ℝ} (d : FixedData nu) {H : ℝ}
    (r : Row d H) (t : TranslatedExpansion.RowChoice d H r) :
    TranslatedExpansion.choiceScalar d r t = LiteralAnalytic.choiceScalar d r t := by
  simp only [TranslatedExpansion.choiceScalar]
  rw [p2m_period_eq]
  simp only [LiteralAnalytic.choiceScalar, RowTranslation.rowScalar, RowTranslation.tail,
    LiteralAnalytic.beta, InterpolationMatrix.exponentVector,
    Finsupp.coe_equivFunOnFinite_symm]

theorem p2m_periodMonomial_eq {m : ℕ} (j h : ℕ) (a : Fin m → ℕ) :
    TranslatedExpansion.periodMonomial j h a =
      MatrixTranslation.periodMonomial j OAI.PiExponent.logarithmicPeriod h a := by
  simp only [TranslatedExpansion.periodMonomial, MatrixTranslation.periodMonomial,
    MatrixTranslation.periodCoordinate]
  rw [p2m_period_eq]

/-- Entry expansion of the selected minor in the translated-expansion bundle. -/
theorem p2m_entry {nu : ℝ} (d : FixedData nu) {H : ℝ}
    (selection : Row d H → Column d H) (r c : Row d H) :
    actualMinor d H selection r c =
      ∑ t : TranslatedExpansion.RowChoice d H r,
        TranslatedExpansion.choiceScalar d r t *
          PowerSeries.coeff (r.2.1 0 - t.2.2)
            ((TranslatedExpansion.periodMonomial r.1.val
              ((selection c).1 0) (fun i => (selection c).1 i.succ)).coeff t.1.1) := by
  have h1 : actualMinor d H selection r c = actualMatrix d H r (selection c) := rfl
  rw [h1]
  rw [LiteralAnalytic.actual_entry_row_choice_expansion d r (selection c)]
  apply Finset.sum_congr rfl
  intro t _
  rw [p2m_choiceScalar_eq d r t, p2m_periodMonomial_eq]

end P2MEntryBridge

/-- Every selected matrix entry is the finite weighted sum of its translated row-choice
contributions. -/
theorem solution
    {nu : ℝ} (d : FixedData nu) {H : ℝ} (hH : 0 < H)
    (selection : Row d H → Column d H) (f : TranslatedExpansion.ChoiceFamily d H)
    (r c : Row d H) :
    actualMinor d H selection r c =
      ∑ t : TranslatedExpansion.RowChoice d H r,
        TranslatedExpansion.choiceScalar d r t *
          TranslatedExpansion.choiceMatrix d selection (Function.update f r t) r c := by
  rw [P2MEntryBridge.p2m_entry d selection r c]
  apply Finset.sum_congr rfl
  intro t _
  congr 1
  simp only [TranslatedExpansion.choiceMatrix]
  rw [show (Function.update f r t) r = t from Function.update_self r t f]
