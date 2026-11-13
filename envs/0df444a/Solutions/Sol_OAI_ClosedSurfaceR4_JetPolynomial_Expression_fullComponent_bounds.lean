-- Prove2me | solution 1 for OAI.ClosedSurfaceR4.JetPolynomial.Expression.fullComponent_bounds
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-12T12:33:33.896411+00:00
-- url     : https://prove2.me/submissions/74c63144-b4a7-479f-897b-05a3f7b412fa

import Mathlib
import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
import Definitions.Def_OAIQ249SI007

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Correction_JetPolynomialAlgebra
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Finite polynomials in actual coordinate jets, with coefficients smooth in
position, the second jet, and the periodic variable. -/
noncomputable section
open scoped ContDiff

namespace ClosedSurfaceR4.JetPolynomial

namespace Expression

lemma order_mul_le (e f : Expression) : (e.mul f).order ≤ max e.order f.order := by
  induction e with
  | coeff c => simp only [mul, order_mapCoeff, order]; exact le_max_right _ _
  | atom w a e ih => simp only [mul, order] at *; omega
  | add e g ihe ihg => simp only [mul, order] at *; omega

lemma loss_mul_le (e f : Expression) : (e.mul f).loss ≤ e.loss + f.loss := by
  induction e with
  | coeff c => simp only [mul, loss_mapCoeff, loss, zero_add, le_refl]
  | atom w a e ih => simp only [mul, loss] at *; omega
  | add e g ihe ihg => simp only [mul, loss] at *; omega

end Expression
end ClosedSurfaceR4.JetPolynomial

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Correction_JetPolynomialDerivative
attribute [-simp] _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.eval_neg _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.eval_sub _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.loss_angle _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.loss_covariance _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.loss_fluct _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.loss_liftOperator _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.loss_mean _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.loss_neg _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.loss_primitive _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.loss_scale _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.loss_sub _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.order_angle _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.order_covariance _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.order_fluct _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.order_liftOperator _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.order_mean _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.order_neg _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.order_primitive _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.order_scale _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.order_sub _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_C _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_J _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_e _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_lowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_variationLowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowPosition_lowJet _root_.OAI.ClosedSurfaceR4.PeriodicExpansion.Family.slow_apply _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_one _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_zero _root_.OAI.ClosedSurfaceR4.SurfaceVelocityFamily.Loop.withSpatialAmplitude_amplitude
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Differentiation preserves finite polynomial dependence on higher jets.
The proof is for actual derivatives, including the low-jet chain rule. -/
noncomputable section
open scoped ContDiff BigOperators

namespace ClosedSurfaceR4.JetPolynomial
open SmoothPeriodicCalculus

namespace Expression

lemma order_sumList_le {ι : Type*} (l : List ι) (f : ι → Expression) (N : ℕ)
    (hN : 2 ≤ N) (hf : ∀ i ∈ l, (f i).order ≤ N) : (sumList l f).order ≤ N := by
  induction l with
  | nil => exact hN
  | cons i l ih =>
    exact max_le (hf i (List.mem_cons_self ..))
      (ih (fun j hj => hf j (List.mem_cons_of_mem _ hj)))

lemma loss_sumList_le {ι : Type*} (l : List ι) (f : ι → Expression) (N : ℕ)
    (hf : ∀ i ∈ l, (f i).loss ≤ N) : (sumList l f).loss ≤ N := by
  induction l with
  | nil => exact Nat.zero_le _
  | cons i l ih =>
    exact max_le (hf i (List.mem_cons_self ..))
      (ih (fun j hj => hf j (List.mem_cons_of_mem _ hj)))

lemma order_lowFactor (v : Fin 2) (i : LowIndex) : (lowFactor v i).order ≤ 3 := by
  cases i with
  | inl i => simp [lowFactor, order]
  | inr i =>
    obtain ⟨w, a⟩ := i
    have h : (lowWord w).length ≤ 2 := by fin_cases w <;> simp [lowWord]
    simp only [lowFactor, order, List.length_cons]
    omega

lemma loss_lowFactor (v : Fin 2) (i : LowIndex) : (lowFactor v i).loss ≤ 1 := by
  cases i with
  | inl i => simp [lowFactor, loss]
  | inr i =>
    obtain ⟨w, a⟩ := i
    have h : (lowWord w).length ≤ 2 := by fin_cases w <;> simp [lowWord]
    simp only [lowFactor, loss, List.length_cons]
    omega

lemma order_slow_le (v : Fin 2) (e : Expression) :
    (e.slow v).order ≤ max 3 (e.order + 1) := by
  induction e with
  | coeff c =>
    apply order_sumList_le _ _ _ (by simp [order])
    intro i _
    exact (order_mul_le _ _).trans (max_le (order_lowFactor v i) (by simp [order]))
  | atom w a e ih => simp only [slow, order, List.length_cons] at *; omega
  | add e f ihe ihf => simp only [slow, order] at *; omega

lemma loss_slow_le (v : Fin 2) (e : Expression) : (e.slow v).loss ≤ e.loss + 1 := by
  induction e with
  | coeff c =>
    apply loss_sumList_le
    intro i _
    exact (loss_mul_le _ _).trans (by simpa only [loss, add_zero] using loss_lowFactor v i)
  | atom w a e ih => simp only [slow, loss, List.length_cons] at *; omega
  | add e f ihe ihf => simp only [slow, loss] at *; omega

end Expression
end ClosedSurfaceR4.JetPolynomial

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Correction_JetPolynomialFullCorrector
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Polynomial construction for every component of the complete periodic
corrector. Only the transverse derivative increases the highest jet order. -/
noncomputable section
open scoped ContDiff

namespace ClosedSurfaceR4.JetPolynomial
open PeriodicCorrector CovarianceCorrector

variable {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [CompleteSpace E] [FiniteDimensional ℝ E]

namespace Expression

omit [CompleteSpace E] [FiniteDimensional ℝ E] in
lemma order_spanTerm_le (Y C : LowJet → E) (L : E →L[ℝ] ℝ) (H K : Expression) :
    (spanTerm Y C L H K).order ≤ max 2 (max H.order K.order) := by
  exact max_le ((order_mul_le _ _).trans (by simp only [order]; omega))
    ((order_mul_le _ _).trans (by simp only [order]; omega))

omit [CompleteSpace E] [FiniteDimensional ℝ E] in
lemma loss_spanTerm_le (Y C : LowJet → E) (L : E →L[ℝ] ℝ) (H K : Expression) :
    (spanTerm Y C L H K).loss ≤ max H.loss K.loss := by
  exact max_le ((loss_mul_le _ _).trans (by simp only [loss, zero_add]; omega))
    ((loss_mul_le _ _).trans (by simp only [loss, zero_add]; omega))

omit [CompleteSpace E] [FiniteDimensional ℝ E] in
lemma order_angularSource_le (Y C X₀ : LowJet → E) (V : LowJet → C(Period, E))
    (h K e : Expression) :
    (angularSource Y C X₀ V h K e).order ≤ max 2 (max h.order (max K.order e.order)) := by
  unfold angularSource
  rw [order_sub, order_fluct]
  exact max_le (by omega) (max_le
    ((order_mul_le _ _).trans (by simp only [order]; omega))
    ((order_mul_le _ _).trans (by simp only [order, order_angle]; omega)))

omit [CompleteSpace E] [FiniteDimensional ℝ E] in
lemma loss_angularSource_le (Y C X₀ : LowJet → E) (V : LowJet → C(Period, E))
    (h K e : Expression) :
    (angularSource Y C X₀ V h K e).loss ≤ max h.loss (max K.loss e.loss) := by
  unfold angularSource
  rw [loss_sub, loss_fluct]
  exact max_le (by omega) (max_le
    ((loss_mul_le _ _).trans (by simp only [loss, zero_add]; omega))
    ((loss_mul_le _ _).trans (by simp only [loss, zero_add, loss_angle]; omega)))

omit [CompleteSpace E] [FiniteDimensional ℝ E] in
/-- One full periodic solve raises the jet order and scale loss by at most one. -/
theorem fullComponent_bounds_oai (Y C X₀ : LowJet → E) (V : LowJet → C(Period, E))
    (q : LowJet → ℝ) (L : E →L[ℝ] ℝ) (v : Fin 2) (h j e : Expression)
    (N R : ℕ) (hN : 2 ≤ N) (hh : h.order ≤ N) (hj : j.order ≤ N) (he : e.order ≤ N)
    (lh : h.loss ≤ R) (lj : j.loss ≤ R) (le : e.loss ≤ R) :
    (fullComponent Y C X₀ V q L v h j e).order ≤ N + 1 ∧
      (fullComponent Y C X₀ V q L v h j e).loss ≤ R + 1 := by
  have ho := order_slow_le v h.primitive
  have hl := loss_slow_le v h.primitive
  have hos := order_spanTerm_le Y C L h.primitive ((h.primitive.slow v).sub j)
  have hls := loss_spanTerm_le Y C L h.primitive ((h.primitive.slow v).sub j)
  have hor := order_angularSource_le Y C X₀ V h ((h.primitive.slow v).sub j) e
  have hlr := loss_angularSource_le Y C X₀ V h ((h.primitive.slow v).sub j) e
  simp only [order_primitive, order_sub, loss_primitive, loss_sub] at ho hl hos hls hor hlr
  constructor
  · change max (spanTerm Y C L h.primitive ((h.primitive.slow v).sub j)).order _ ≤ _
    rw [order_primitive, order_covariance]
    omega
  · change max (spanTerm Y C L h.primitive ((h.primitive.slow v).sub j)).loss _ ≤ _
    rw [loss_primitive, loss_covariance]
    omega

end Expression
end ClosedSurfaceR4.JetPolynomial

end

end OAI
end

theorem solution : type_of% @OAI.ClosedSurfaceR4.JetPolynomial.Expression.fullComponent_bounds_oai := @OAI.ClosedSurfaceR4.JetPolynomial.Expression.fullComponent_bounds_oai
