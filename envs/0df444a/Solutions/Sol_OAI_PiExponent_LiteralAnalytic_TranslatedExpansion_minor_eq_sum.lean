-- Prove2me | solution 1 for OAI.PiExponent.LiteralAnalytic.TranslatedExpansion.minor_eq_sum
-- status  : ACCEPTED   (prove)
-- author  : @polylog
-- created : 2026-10-20T19:19:29.111755+00:00
-- url     : https://prove2.me/submissions/a2199d59-933b-4b9f-a9e5-26734ecf66ad

import Definitions.Def_OAI_NumberTheory_PiExponent_Analysis_TranslatedExpansionTerms
import Definitions.Def_OAI_NumberTheory_PiExponent_Analysis_LiteralAnalyticSummand_InterfaceData
import Theorems.Thm_OAI_PiExponent_LiteralAnalytic_actual_entry_row_choice_expansion

open scoped BigOperators Topology
open Filter
open OAI.PiExponent OAI.PiExponent.DeterminantContradiction
open OAI.PiExponent.LiteralAnalytic
open OAI.PiExponent.LiteralAnalytic.TranslatedExpansion

/-! ### Bridging the two period bundles

The translated-expansion bundle and the row-translation bundle share their period data up to the
order of the two factors of `2 * π * I`; the row-choice scalar of the translated-expansion bundle
is the expanded form of the general `rowScalar`. -/

namespace P2MMinorBridge

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

/-- Determinant of a matrix whose rows are finite sums over row-dependent index sets. -/
theorem p2m_det_dependent_row_sum {ι : Type*} [Fintype ι] [DecidableEq ι]
    {δ : ι → Type*} [∀ i, Fintype (δ i)]
    (B : ∀ i, δ i → ℂ) (C : ∀ i, δ i → ι → ℂ) :
    Matrix.det (fun i j => ∑ t, B i t * C i t j) =
      ∑ f : (∀ i, δ i), (∏ i, B i (f i)) * Matrix.det (fun i j => C i (f i) j) := by
  classical
  have hm := (Matrix.detRowAlternating : (ι → ℂ) [⋀^ι]→ₗ[ℂ] ℂ).toMultilinearMap.map_sum
    (fun i t => B i t • C i t)
  calc
    _ = Matrix.det (fun i => ∑ t, B i t • C i t) := by
      congr 1
      funext i j
      simp
    _ = ∑ f : (∀ i, δ i), Matrix.det (fun i => B i (f i) • C i (f i)) := hm
    _ = _ := by
      apply Finset.sum_congr rfl
      intro f _
      exact Matrix.det_mul_column (fun i => B i (f i)) (fun i j => C i (f i) j)

end P2MMinorBridge

/-- The actual minor determinant equals the sum over all row-choice families of the corresponding
sheared scalar product times period-matrix determinant. -/
theorem solution
    {nu : ℝ} (d : FixedData nu) {H : ℝ} (hH : 0 < H)
    (selection : Row d H → Column d H) :
    (actualMinor d H selection).det
      = ∑ f : TranslatedExpansion.ChoiceFamily d H,
          TranslatedExpansion.summand d selection f := by
  have hdet := P2MMinorBridge.p2m_det_dependent_row_sum
    (ι := Row d H) (δ := fun r : Row d H => TranslatedExpansion.RowChoice d H r)
    (B := fun r t => TranslatedExpansion.choiceScalar d r t)
    (C := fun r t c =>
      PowerSeries.coeff (r.2.1 0 - t.2.2)
        ((TranslatedExpansion.periodMonomial r.1.val
          ((selection c).1 0) (fun i => (selection c).1 i.succ)).coeff t.1.1))
  have hentry : (fun r c => actualMinor d H selection r c) =
      (fun r c => ∑ t : TranslatedExpansion.RowChoice d H r,
        TranslatedExpansion.choiceScalar d r t *
          PowerSeries.coeff (r.2.1 0 - t.2.2)
            ((TranslatedExpansion.periodMonomial r.1.val
              ((selection c).1 0) (fun i => (selection c).1 i.succ)).coeff t.1.1)) := by
    funext r c
    exact P2MMinorBridge.p2m_entry d selection r c
  change Matrix.det (fun r c => actualMinor d H selection r c) =
    ∑ f : TranslatedExpansion.ChoiceFamily d H, TranslatedExpansion.summand d selection f
  rw [hentry, hdet]
  apply Finset.sum_congr rfl
  intro f _
  rw [TranslatedExpansion.summand]
  congr 1
