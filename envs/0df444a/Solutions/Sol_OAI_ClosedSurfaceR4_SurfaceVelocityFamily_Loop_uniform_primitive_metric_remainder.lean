-- Prove2me | solution 1 for OAI.ClosedSurfaceR4.SurfaceVelocityFamily.Loop.uniform_primitive_metric_remainder
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-12T12:51:05.365979+00:00
-- url     : https://prove2.me/submissions/6b2a3110-4960-4a1e-a3af-c61ecbaf13c8

import Mathlib
import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
import Mathlib.Analysis.Calculus.BumpFunction.Normed
import Mathlib.Analysis.Calculus.ContDiff.Convolution
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Geometry.Manifold.PartitionOfUnity
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.LinearAlgebra.Vandermonde
import Mathlib.MeasureTheory.Measure.Haar.NormedSpace
import Definitions.Def_SurfaceImmersion
import Definitions.Def_OAIQ249SI012
import Theorems.Thm_OAI_ClosedSurfaceR4_JetPolynomial_MetricPolynomial_coefficients_smooth
import Theorems.Thm_OAI_ClosedSurfaceR4_JetPolynomial_MetricPolynomial_compact_metric_error
import Theorems.Thm_OAI_ClosedSurfaceR4_SurfaceVelocityFamily_Loop_meanMetric_eq_meanOperator

section
-- module Solutions.OAIQ249_SI.Immersion_ClosedSurface_WeightedBounds
attribute [-instance] _root_.instVAddIntReal_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Complex Bundle Manifold
open scoped ContDiff Matrix Topology Manifold BigOperators

namespace ClosedSurfaceR4.WeightedEstimates

variable {E F G H : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [NormedAddCommGroup G] [NormedSpace ℝ G]
  [NormedAddCommGroup H] [NormedSpace ℝ H]




lemma WeightedBound.congr {U : Set E} {s C : ℝ} {m : ℕ} {f g : E → F}
    (hf : WeightedBound U s m C f) (he : EqOn g f U) : WeightedBound U s m C g := by
  intro j hj x hx
  rw [iteratedFDerivWithin_congr he hx]
  exact hf j hj x hx

end ClosedSurfaceR4.WeightedEstimates

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Correction_JetPolynomialAlgebra
attribute [-instance] _root_.instVAddIntReal_solutions
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

lemma smoothCoeffs_map {O : Set LowJet} (e : Expression) (f)
    (hf : ∀ c, ContDiffOn ℝ ∞ c (O ×ˢ Set.univ) → ContDiffOn ℝ ∞ (f c) (O ×ˢ Set.univ))
    (he : e.SmoothCoeffs O) : (e.mapCoeff f).SmoothCoeffs O := by
  induction e with
  | coeff c => exact hf c he
  | atom w a e ih => exact ih he
  | add e g ihe ihg => exact ⟨ihe he.1, ihg he.2⟩

lemma smoothCoeffs_mul {O : Set LowJet} {e f : Expression}
    (he : e.SmoothCoeffs O) (hf : f.SmoothCoeffs O) : (e.mul f).SmoothCoeffs O := by
  induction e with
  | coeff c => exact smoothCoeffs_map f _ (fun d hd => he.mul hd) hf
  | atom w a e ih => exact ih he
  | add e g ihe ihg => exact ⟨ihe he.1, ihg he.2⟩

end Expression
end ClosedSurfaceR4.JetPolynomial

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Correction_JetPolynomialDerivative
attribute [-instance] _root_.instMembershipProdContinuousLinearMapRealIdRelLoc _root_.instVAddIntReal_solutions
attribute [-simp] _root_.ContinuousLinearMap.comp_toSpanSingleton_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.eval_neg _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.eval_sub _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.loss_angle _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.loss_covariance _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.loss_fluct _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.loss_liftOperator _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.loss_mean _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.loss_neg _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.loss_primitive _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.loss_scale _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.loss_sub _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.order_angle _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.order_covariance _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.order_fluct _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.order_liftOperator _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.order_mean _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.order_neg _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.order_primitive _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.order_scale _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.order_sub _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_C _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_J _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_e _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_lowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_variationLowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowPosition_lowJet _root_.OAI.ClosedSurfaceR4.PeriodicExpansion.Family.slow_apply _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_one _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_zero _root_.OAI.ClosedSurfaceR4.SurfaceVelocityFamily.Loop.withSpatialAmplitude_amplitude _root_.Path.extend_div_self
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

lemma smoothCoeffs_sumList {ι : Type*} {O : Set LowJet} (l : List ι) (f : ι → Expression)
    (hf : ∀ i ∈ l, (f i).SmoothCoeffs O) : (sumList l f).SmoothCoeffs O := by
  induction l with
  | nil => exact contDiffOn_const
  | cons i l ih => exact ⟨hf i (List.mem_cons_self ..),
      ih (fun j hj => hf j (List.mem_cons_of_mem _ hj))⟩

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

lemma smoothCoeffs_lowFactor (O : Set LowJet) (v : Fin 2) (i : LowIndex) :
    (lowFactor v i).SmoothCoeffs O := by
  cases i with
  | inl i => exact contDiffOn_const
  | inr i => exact contDiffOn_const

lemma smoothCoeffs_slow {O : Set LowJet} (hO : IsOpen O) (v : Fin 2)
    {e : Expression} (he : e.SmoothCoeffs O) : (e.slow v).SmoothCoeffs O := by
  induction e with
  | coeff c =>
    apply smoothCoeffs_sumList
    intro i _
    exact smoothCoeffs_mul (smoothCoeffs_lowFactor O v i)
      (LocalPeriodicCalculus.slow_smooth hO he (lowBasis i))
  | atom w a e ih => exact ⟨he, ih he⟩
  | add e f ihe ihf => exact ⟨ihe he.1, ihf he.2⟩

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
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Correction_JetPolynomialIntegral
attribute [-instance] _root_.instMembershipProdContinuousLinearMapRealIdRelLoc _root_.instVAddIntReal_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Angular derivatives, averaging, and normalized primitives act only on
smooth low-jet coefficients, preserving polynomial jet order and scale loss. -/
noncomputable section
open MeasureTheory
open scoped ContDiff

namespace ClosedSurfaceR4.JetPolynomial
open SmoothPeriodicCalculus

namespace Expression

lemma smoothCoeffs_angle {O : Set LowJet} (hO : IsOpen O) {e : Expression}
    (he : e.SmoothCoeffs O) : e.angle.SmoothCoeffs O :=
  smoothCoeffs_map e _ (fun _ hc => LocalPeriodicCalculus.angle_smooth hO hc) he

lemma smoothCoeffs_mean {O : Set LowJet} (hO : IsOpen O) {e : Expression}
    (he : e.SmoothCoeffs O) : e.mean.SmoothCoeffs O := by
  apply smoothCoeffs_map e _ _ he
  intro c hc
  exact (SmoothParameterIntegral.contDiffOn_integral hO hc 0 1).comp contDiffOn_fst
    (fun _ hz => hz.1)

end Expression
end ClosedSurfaceR4.JetPolynomial

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Correction_JetPolynomialFullCorrector
attribute [-instance] _root_.instVAddIntReal_solutions
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
theorem fullComponent_bounds (Y C X₀ : LowJet → E) (V : LowJet → C(Period, E))
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

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Correction_JetPolynomialVector
attribute [-instance] _root_.instVAddIntReal_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Four coordinate polynomials represent the actual vector families used by
the metric recursion. Dot products and both derivatives preserve representation. -/
noncomputable section
open scoped ContDiff Topology BigOperators

namespace ClosedSurfaceR4.JetPolynomial
open LocalPeriodicExpansion SmoothPeriodicCalculus

namespace VectorExpression

lemma smoothCoeffs_dot {O : Set LowJet} {R T : VectorExpression}
    (hR : R.SmoothCoeffs O) (hT : T.SmoothCoeffs O) : (R.dot T).SmoothCoeffs O := by
  apply Expression.smoothCoeffs_sumList
  intro i _
  exact Expression.smoothCoeffs_mul (hR i) (hT i)

lemma order_dot_le {R T : VectorExpression} {N : ℕ} (hN : 2 ≤ N)
    (hR : ∀ i, (R i).order ≤ N) (hT : ∀ i, (T i).order ≤ N) : (R.dot T).order ≤ N := by
  apply Expression.order_sumList_le _ _ _ hN
  intro i _
  exact (Expression.order_mul_le _ _).trans (max_le (hR i) (hT i))

end VectorExpression
end ClosedSurfaceR4.JetPolynomial

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Correction_JetPolynomialScalar
attribute [-instance] _root_.instMembershipProdContinuousLinearMapRealIdRelLoc _root_.instVAddIntReal_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Scalar polynomial representations of the finite metric coefficients. -/
noncomputable section
open scoped BigOperators

namespace ClosedSurfaceR4.JetPolynomial.Expression
open LocalPeriodicExpansion CovarianceCorrector

lemma smoothCoeffs_sumFinset {ι : Type*} {O : Set LowJet} (a : Finset ι) (e : ι → Expression)
    (he : ∀ i ∈ a, (e i).SmoothCoeffs O) : (sumFinset a e).SmoothCoeffs O := by
  apply smoothCoeffs_sumList
  intro i hi
  exact he i (Finset.mem_toList.mp hi)

lemma order_sumFinset_le {ι : Type*} (a : Finset ι) (e : ι → Expression) (N : ℕ)
    (hN : 2 ≤ N) (he : ∀ i ∈ a, (e i).order ≤ N) : (sumFinset a e).order ≤ N := by
  apply order_sumList_le _ _ _ hN
  intro i hi
  exact he i (Finset.mem_toList.mp hi)

end ClosedSurfaceR4.JetPolynomial.Expression

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Correction_PolynomialMetricCoefficients
attribute [-instance] _root_.instMembershipProdContinuousLinearMapRealIdRelLoc _root_.instVAddIntReal_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Actual coordinate polynomial expressions for the metric coefficients in
the finite oscillatory recursion. Index zero denotes the first correction. -/
noncomputable section
open scoped ContDiff BigOperators

namespace ClosedSurfaceR4.JetPolynomial.MetricPolynomial

lemma order_xCoefficient {U : ℕ → VectorExpression} {r i : ℕ}
    (hi : 1 ≤ i) (hir : i < r)
    (hU : ∀ j < r, ∀ a, (U j a).order ≤ 2 * j + 2) (dx : Fin 2) (a : Fin 4) :
    (xCoefficient dx U i a).order ≤ 2 * i + 2 := by
  have hp := Expression.order_slow_le dx (U (i - 1) a)
  have hprev := hU (i - 1) (by omega) a
  have hcur := hU i hir a
  change max ((U (i - 1) a).slow dx).order ((U i a).angle).order ≤ _
  rw [Expression.order_angle]
  omega

lemma order_yCoefficient {U : ℕ → VectorExpression} {r i : ℕ}
    (hi : 1 ≤ i) (hir : i ≤ r)
    (hU : ∀ j < r, ∀ a, (U j a).order ≤ 2 * j + 2) (dy : Fin 2) (a : Fin 4) :
    (yCoefficient dy U i a).order ≤ 2 * i + 1 := by
  have hp := Expression.order_slow_le dy (U (i - 1) a)
  have hprev := hU (i - 1) (by omega) a
  exact hp.trans (by omega)

lemma order_xxQuadratic {U : ℕ → VectorExpression} {r : ℕ} (hr : 1 ≤ r)
    (hU : ∀ j < r, ∀ a, (U j a).order ≤ 2 * j + 2) (dx : Fin 2) :
    (xxQuadratic dx U r).order ≤ 2 * r := by
  apply Expression.order_sumFinset_le _ _ _ (by omega)
  intro i hi
  obtain ⟨hi, hir⟩ := Finset.mem_Ico.mp hi
  apply VectorExpression.order_dot_le (by omega)
  · intro a
    exact (order_xCoefficient hi hir hU dx a).trans (by omega)
  · intro a
    exact (order_xCoefficient (by omega) (by omega) hU dx a).trans (by omega)

lemma order_xyQuadratic {U : ℕ → VectorExpression} {r : ℕ} (hr : 1 ≤ r)
    (hU : ∀ j < r, ∀ a, (U j a).order ≤ 2 * j + 2) (dx dy : Fin 2) :
    (xyQuadratic dx dy U r).order ≤ 2 * r := by
  apply Expression.order_sumFinset_le _ _ _ (by omega)
  intro i hi
  obtain ⟨hi, hir⟩ := Finset.mem_Ico.mp hi
  apply VectorExpression.order_dot_le (by omega)
  · intro a
    exact (order_xCoefficient hi hir hU dx a).trans (by omega)
  · intro a
    exact (order_yCoefficient (by omega) (by omega) hU dy a).trans (by omega)

lemma order_yyQuadratic {U : ℕ → VectorExpression} {r : ℕ} (hr : 1 ≤ r)
    (hU : ∀ j < r, ∀ a, (U j a).order ≤ 2 * j + 2) (dy : Fin 2) :
    (yyQuadratic dy U (r + 1)).order ≤ 2 * r + 1 := by
  apply Expression.order_sumFinset_le _ _ _ (by omega)
  intro i hi
  obtain ⟨hi, hir⟩ := Finset.mem_Ico.mp hi
  apply VectorExpression.order_dot_le (by omega)
  · intro a
    exact (order_yCoefficient hi (by omega) hU dy a).trans (by omega)
  · intro a
    exact (order_yCoefficient (by omega) (by omega) hU dy a).trans (by omega)

end ClosedSurfaceR4.JetPolynomial.MetricPolynomial

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Correction_PolynomialMetricForcing
attribute [-instance] _root_.instVAddIntReal_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The right-hand sides of the finite triangular correction step are actual
higher-jet polynomials. Their maximal jet order is the preceding order plus one. -/
noncomputable section
open scoped ContDiff BigOperators

namespace ClosedSurfaceR4.JetPolynomial.MetricPolynomial

lemma smooth_xCoefficient {O : Set LowJet} (hO : IsOpen O) {U : ℕ → VectorExpression}
    (hU : ∀ j, (U j).SmoothCoeffs O) (dx : Fin 2) (i : ℕ) :
    (xCoefficient dx U i).SmoothCoeffs O := by
  intro a
  exact ⟨Expression.smoothCoeffs_slow hO dx (hU _ _),
    Expression.smoothCoeffs_angle hO (hU _ _)⟩

lemma smooth_yCoefficient {O : Set LowJet} (hO : IsOpen O) {U : ℕ → VectorExpression}
    (hU : ∀ j, (U j).SmoothCoeffs O) (dy : Fin 2) (i : ℕ) :
    (yCoefficient dy U i).SmoothCoeffs O := by
  intro a
  exact Expression.smoothCoeffs_slow hO dy (hU _ _)

lemma forcing_orders {U : ℕ → VectorExpression} {r : ℕ} (hr : 1 ≤ r)
    (hU : ∀ j < r, ∀ a, (U j a).order ≤ 2 * j + 2)
    {X Y : VectorExpression} (hX : ∀ a, (X a).order ≤ 2) (hY : ∀ a, (Y a).order ≤ 2)
    (dx dy : Fin 2) :
    (mixedForcing X Y dx dy U r).order ≤ 2 * r + 1 ∧
      (longitudinalForcing X dx U r).order ≤ 2 * r + 1 ∧
      (transverseForcing dy U r).order ≤ 2 * r + 1 := by
  have hprev : ∀ a, ((U (r - 1)).slow dx a).order ≤ 2 * r + 1 := by
    intro a
    have hd := Expression.order_slow_le dx (U (r - 1) a)
    have hp := hU (r - 1) (by omega) a
    exact hd.trans (by omega)
  have hXslow := VectorExpression.order_dot_le (by omega : 2 ≤ 2 * r + 1)
    (fun a => (hX a).trans (by omega)) hprev
  have hYslow := VectorExpression.order_dot_le (by omega : 2 ≤ 2 * r + 1)
    (fun a => (hY a).trans (by omega)) hprev
  have hXy := VectorExpression.order_dot_le (by omega : 2 ≤ 2 * r + 1)
    (fun a => (hX a).trans (by omega)) (order_yCoefficient hr (le_refl r) hU dy)
  have hxy := order_xyQuadratic hr hU dx dy
  have hxx := order_xxQuadratic hr hU dx
  have hyy := order_yyQuadratic hr hU dy
  refine ⟨?_, ?_, hyy⟩
  · change max (max _ _) _ ≤ _
    exact max_le (max_le hXy hYslow) (hxy.trans (by omega))
  · change max _ ((xxQuadratic dx U r).scale (1 / 2)).order ≤ _
    rw [Expression.order_scale]
    exact max_le hXslow (hxx.trans (by omega))

end ClosedSurfaceR4.JetPolynomial.MetricPolynomial

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Correction_PolynomialJetRecursion
attribute [-instance] _root_.instVAddIntReal_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Finite jet-order induction for the explicit periodic correction recursion. -/
noncomputable section
open scoped ContDiff

namespace ClosedSurfaceR4.JetPolynomial.MetricPolynomial
open Expression

lemma order_step {Y C X₀ : LowJet → R4} {V : LowJet → C(CovarianceCorrector.Period, R4)}
    {q : LowJet → ℝ} {dx dy : Fin 2} {U : ℕ → VectorExpression} {r : ℕ} (hr : 1 ≤ r)
    (hU : ∀ j < r, ∀ a, (U j a).order ≤ 2 * j + 2) (a : Fin 4) :
    (step Y C X₀ V q dx dy U r a).order ≤ 2 * r + 2 := by
  have hs := forcing_orders hr hU
    (X := longitudinal X₀ V) (Y := transverse Y) (fun _ => le_refl 2) (fun _ => le_refl 2) dx dy
  let h := (mixedForcing (longitudinal X₀ V) (transverse Y) dx dy U r).fluct.scale (-1)
  let j := (transverseForcing dy U r).fluct.scale (-1 / 2)
  let e := (longitudinalForcing (longitudinal X₀ V) dx U r).fluct.scale (-1)
  have hh : h.order ≤ 2 * r + 1 := by simpa only [h, order_scale, order_fluct] using hs.1
  have hj : j.order ≤ 2 * r + 1 := by simpa only [j, order_scale, order_fluct] using hs.2.2
  have he : e.order ≤ 2 * r + 1 := by simpa only [e, order_scale, order_fluct] using hs.2.1
  have hb := fullComponent_bounds Y C X₀ V q (EuclideanSpace.proj a) dy h j e
    (2 * r + 1) (max h.loss (max j.loss e.loss)) (by omega) hh hj he
    (le_max_left _ _) ((le_max_left _ _).trans (le_max_right _ _))
    ((le_max_right _ _).trans (le_max_right _ _))
  exact hb.1

/-- The expression for U_(i+1) uses jets of the base map through order 2i+2,
independently of how much further the finite recursion is continued. -/
theorem coefficients_order (Y C X₀ : LowJet → R4)
    (V : LowJet → C(CovarianceCorrector.Period, R4)) (q : LowJet → ℝ)
    (dx dy : Fin 2) (n i : ℕ) (a : Fin 4) :
    (coefficients Y C X₀ V q dx dy n i a).order ≤ 2 * i + 2 := by
  induction n generalizing i a with
  | zero =>
    change ((Expression.coeff _).fluct.primitive).order ≤ _
    simp only [order_primitive, order_fluct, order]
    omega
  | succ n ih =>
    by_cases hi : i = n + 1
    · subst i
      rw [coefficients, Function.update_self]
      exact order_step (by omega) (fun j _ a => ih j a) a
    · rw [coefficients, Function.update_of_ne hi]
      exact ih i a

end ClosedSurfaceR4.JetPolynomial.MetricPolynomial

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Correction_PolynomialJetSmoothness
attribute [-instance] _root_.instMembershipProdContinuousLinearMapRealIdRelLoc _root_.instVAddIntReal_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The finite correction expressions have coefficients smooth throughout
the admissible low-jet domain. No higher jets occur in coefficient inverses. -/
noncomputable section
open scoped ContDiff

namespace ClosedSurfaceR4.JetPolynomial.MetricPolynomial
open CovarianceCorrector

lemma smooth_longitudinal {O : Set LowJet} {X₀ : LowJet → R4} {V : LowJet → C(Period, R4)}
    (hX : ContDiffOn ℝ ∞ X₀ O)
    (hV : ContDiffOn ℝ ∞ (fun z : LowJet × ℝ => V z.1 (z.2 : Period)) (O ×ˢ Set.univ)) :
    (longitudinal X₀ V).SmoothCoeffs O := by
  intro a
  let L : R4 →L[ℝ] ℝ := EuclideanSpace.proj a
  exact L.contDiff.comp_contDiffOn
    ((hX.comp contDiffOn_fst (fun _ hz => hz.1)).add hV)

lemma smooth_transverse {O : Set LowJet} {Y : LowJet → R4} (hY : ContDiffOn ℝ ∞ Y O) :
    (transverse Y).SmoothCoeffs O := by
  intro a
  let L : R4 →L[ℝ] ℝ := EuclideanSpace.proj a
  have hi : ContDiffOn ℝ ∞ (fun Q => Y Q a) O :=
    L.contDiff.comp_contDiffOn hY
  exact hi.comp contDiffOn_fst (fun _ hz => hz.1)

end ClosedSurfaceR4.JetPolynomial.MetricPolynomial

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Correction_PolynomialGeometry
attribute [-instance] _root_.instMembershipProdContinuousLinearMapRealIdRelLoc _root_.instVAddIntReal_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Low-jet geometry and the initial primitive in the actual periodic family
are represented by the corresponding coordinate polynomial expressions. -/
noncomputable section
open scoped ContDiff

namespace ClosedSurfaceR4.JetPolynomial
open LocalPeriodicExpansion CovarianceCorrector

namespace MetricPolynomial

lemma represents_longitudinal {S : TopologicalSpace.Opens Base} {G : Base → Space}
    {v : Base} (g : Geometry (E := R4) S v) (X₀ : LowJet → R4) (V : LowJet → C(Period, R4))
    (hX : ∀ p ∈ S, g.X₀ p = X₀ (lowJet G p)) (hV : ∀ p ∈ S, g.V.val p = V (lowJet G p)) :
    VectorExpression.Represents G (longitudinal X₀ V) g.longitudinal := by
  intro i p hp t
  change (X₀ (lowJet G p) + V (lowJet G p) (t : Period)) i = _
  rw [Geometry.longitudinal, Family.add_apply, Family.constant_apply _ _ hp,
    hX p hp, hV p hp]

lemma represents_transverse {S : TopologicalSpace.Opens Base} {G : Base → Space}
    {v : Base} (g : Geometry (E := R4) S v) (Y : LowJet → R4)
    (hY : ∀ p ∈ S, g.Y p = Y (lowJet G p)) :
    VectorExpression.Represents G (transverse Y) g.transverse := by
  intro i p hp t
  change Y (lowJet G p) i = _
  rw [Geometry.transverse, Family.constant_apply _ _ hp, hY p hp]

end MetricPolynomial
end ClosedSurfaceR4.JetPolynomial

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Correction_PolynomialMetricRemainder
attribute [-instance] _root_.instVAddIntReal_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Actual jet-polynomial representations of every coefficient of the finite
pullback-metric remainder. -/
noncomputable section
open scoped ContDiff BigOperators

namespace ClosedSurfaceR4.JetPolynomial.MetricPolynomial
open LocalPeriodicExpansion

lemma smooth_finiteMetric {O : Set LowJet} {X Y : ℕ → VectorExpression}
    (hX : ∀ i, (X i).SmoothCoeffs O) (hY : ∀ i, (Y i).SmoothCoeffs O) (L r : ℕ) :
    (finiteMetric L r X Y).SmoothCoeffs O := by
  apply Expression.smoothCoeffs_sumFinset
  intro i _
  apply Expression.smoothCoeffs_sumFinset
  intro j _
  split_ifs
  · exact VectorExpression.smoothCoeffs_dot (hX i) (hY j)
  · exact contDiffOn_const

lemma smooth_xTangent {O : Set LowJet} (hO : IsOpen O) {X : VectorExpression}
    {U : ℕ → VectorExpression} (hX : X.SmoothCoeffs O) (hU : ∀ i, (U i).SmoothCoeffs O)
    (dx : Fin 2) (L i : ℕ) : (xTangent X dx U L i).SmoothCoeffs O := by
  unfold xTangent
  split_ifs
  · exact hX
  · intro a
    exact Expression.smoothCoeffs_slow hO dx (hU _ a)
  · exact smooth_xCoefficient hO hU dx i

lemma smooth_yTangent {O : Set LowJet} (hO : IsOpen O) {Y : VectorExpression}
    {U : ℕ → VectorExpression} (hY : Y.SmoothCoeffs O) (hU : ∀ i, (U i).SmoothCoeffs O)
    (dy : Fin 2) (i : ℕ) : (yTangent Y dy U i).SmoothCoeffs O := by
  unfold yTangent
  split_ifs
  · exact hY
  · exact smooth_yCoefficient hO hU dy i

end ClosedSurfaceR4.JetPolynomial.MetricPolynomial

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Primitive_LocalPeriodicFastEvaluation
attribute [-instance] _root_.instMembershipProdContinuousLinearMapRealIdRelLoc _root_.instVAddIntReal_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Actual fast-phase differentiation on an admissible chart domain. -/
noncomputable section
open scoped ContDiff

namespace ClosedSurfaceR4.LocalPeriodicExpansion.Family
open CovarianceCorrector SmoothPeriodicCalculus

variable {A E : Type} [NormedAddCommGroup A] [NormedSpace ℝ A]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] {O : TopologicalSpace.Opens A}

lemma fastValue_smooth (U : Family O E) (ℓ : A →L[ℝ] ℝ) (z : ℝ) :
    ContDiffOn ℝ ∞ (U.fastValue ℓ z) O :=
  U.smooth.comp (contDiffOn_id.prodMk (ℓ.contDiff.div_const z).contDiffOn)
    (fun _ hp => ⟨hp, Set.mem_univ _⟩)

end ClosedSurfaceR4.LocalPeriodicExpansion.Family

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Atlas_TangentMetricBounds
attribute [-instance] _root_.instVAddIntReal_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Apply the finite-tail estimate to the actual two tangent expansions. -/
noncomputable section
open scoped ContDiff

namespace ClosedSurfaceR4.JetPolynomial.MetricPolynomial
open LocalPeriodicExpansion WeightedEstimates

lemma smooth_tangentExpression {O : Set LowJet} (hO : IsOpen O)
    {X Y : VectorExpression} {R : ℕ → VectorExpression}
    (hX : X.SmoothCoeffs O) (hY : Y.SmoothCoeffs O) (hR : ∀ i, (R i).SmoothCoeffs O)
    (dx dy : Fin 2) (L : ℕ) (b : Bool) (i : ℕ) :
    (tangentExpression X Y R dx dy L b i).SmoothCoeffs O := by
  cases b
  · exact smooth_yTangent hO hY hR dy i
  · exact smooth_xTangent hO hX hR dx L i

end ClosedSurfaceR4.JetPolynomial.MetricPolynomial

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Primitive_LocalPeriodicFiniteAnsatz
attribute [-instance] _root_.instMembershipProdContinuousLinearMapRealIdRelLoc _root_.instVAddIntReal_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The finite oscillatory map and its actual first derivatives. -/

noncomputable section
open scoped ContDiff BigOperators

namespace ClosedSurfaceR4.LocalPeriodicExpansion

open CovarianceCorrector

variable {A E : Type} [NormedAddCommGroup A] [NormedSpace ℝ A]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] {O : TopologicalSpace.Opens A}

lemma finiteAnsatz_smooth {F : A → E} (hF : ContDiffOn ℝ ∞ F O)
    (U : ℕ → Family O E) (ℓ : A →L[ℝ] ℝ) (L : ℕ) (z : ℝ) :
    ContDiffOn ℝ ∞ (finiteAnsatz F U ℓ L z) O :=
  hF.add (ContDiffOn.sum fun i _ => contDiffOn_const.smul ((U i).fastValue_smooth ℓ z))

end ClosedSurfaceR4.LocalPeriodicExpansion

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Primitive_SurfaceVelocityFamily
attribute [-instance] _root_.instMembershipProdContinuousLinearMapRealIdRelLoc _root_.instVAddIntReal_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Convert a geometric second-jet velocity loop into the exact family of
Euclidean data used by the supported finite periodic recursion. -/
noncomputable section
open Set
open scoped ContDiff

namespace ClosedSurfaceR4.SurfaceVelocityFamily
open RealModes JetPolynomial JetVelocityCoordinates CovarianceCorrector
open LocalPeriodicExpansion LocalPeriodicCalculus
local notation "ι" => JetVelocityCoordinates.toEuclidean

namespace Loop
variable {O : TopologicalSpace.Opens LowJet} (l : Loop O)

lemma euclideanVelocity_mean {J : LowJet} (hJ : J ∈ O) :
    average (l.euclideanVelocity J) = ι (normal J) := by
  rw [average, ← PeriodicPrimitive.integral_lift_eq_haar]
  simp only [l.euclideanVelocity_apply hJ]
  have hi : IntervalIntegrable (fun t => l.velocity (J, t)) MeasureTheory.volume 0 1 :=
    (smooth_slice O.isOpen l.smoothVelocity hJ).continuous.intervalIntegrable 0 1
  exact (JetVelocityCoordinates.toEuclidean.toContinuousLinearMap.intervalIntegral_comp_comm hi).trans
    (congrArg ι (l.mean J hJ))

end Loop
end ClosedSurfaceR4.SurfaceVelocityFamily

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Primitive_SurfaceVelocityIdentities
attribute [-instance] _root_.instMembershipProdContinuousLinearMapRealIdRelLoc _root_.instMetricSpaceOneJet _root_.instVAddIntReal_solutions
attribute [-simp] _root_.ContinuousLinearMap.comp_toSpanSingleton_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.circularPhaseBoundaryCurve_carrier _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.directionJetLinearization_apply _root_.OAI.ClosedSurfaceR4.GeometryPreservation.boundaryProfileMap_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.eval_neg _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.eval_sub _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.loss_covariance _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.loss_liftOperator _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.loss_mapCoeff _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.order_covariance _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.order_liftOperator _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.order_mapCoeff _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_C _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_J _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_e _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_lowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_variationLowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowPosition_lowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.spatialAmplitude_lowJet _root_.OAI.ClosedSurfaceR4.LocalPeriodicExpansion.Geometry.xTangent_zero _root_.OAI.ClosedSurfaceR4.LocalPeriodicExpansion.Geometry.yTangent_zero _root_.OAI.ClosedSurfaceR4.RealModes.secondTensorFromJet_realTwoJet _root_.OAI.ClosedSurfaceR4.SurfaceVelocityFamily.Loop.withSpatialAmplitude_amplitude _root_.Path.extend_div_self
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The leading metric and support of the actual second-jet family. -/
noncomputable section
open Set
open scoped ContDiff Matrix

namespace ClosedSurfaceR4.SurfaceVelocityFamily
open RealModes JetPolynomial JetVelocityCoordinates CovarianceCorrector
open LocalPeriodicExpansion
local notation "ι" => JetVelocityCoordinates.toEuclidean

lemma first_slot {G : JetPolynomial.Base → JetPolynomial.Space}
    (hG : ContDiff ℝ ∞ G) (i : Fin 2) (p : JetPolynomial.Base) :
    slot (![1, 2] i) (lowJet G p) = fderiv ℝ G p (coordinateVector i) := by
  funext a
  have he := congrArg (fun L : JetPolynomial.Base →L[ℝ] ℝ => L (coordinateVector i))
    (fderiv_apply (hG.differentiable (by simp) p) a)
  calc
    _ = fderiv ℝ (fun q => G q a) p (coordinateVector i) := by fin_cases i <;> rfl
    _ = _ := he

lemma euclidean_first_derivative {G : JetPolynomial.Base → JetPolynomial.Space}
    (hG : ContDiff ℝ ∞ G) (i : Fin 2) (p : JetPolynomial.Base) :
    fderiv ℝ (fun q => ι (G q)) p (coordinateVector i) =
      ι (slot (![1, 2] i) (lowJet G p)) := by
  have hd := (JetVelocityCoordinates.toEuclidean.hasFDerivAt.comp p
    (hG.differentiable (by simp) p).hasFDerivAt).fderiv
  calc
    _ = ι (fderiv ℝ G p (coordinateVector i)) :=
      congrArg (fun L : JetPolynomial.Base →L[ℝ] Euclidean => L (coordinateVector i)) hd
    _ = _ := congrArg ι (first_slot hG i p).symm

namespace Loop
variable {O : TopologicalSpace.Opens LowJet} (l : Loop O)

variable {S : TopologicalSpace.Opens JetPolynomial.Base}
    {G : JetPolynomial.Base → JetPolynomial.Space} (hG : ContDiff ℝ ∞ G)
    (hGO : MapsTo (lowJet G) S O)

lemma geometry_velocity {p : JetPolynomial.Base} (hp : p ∈ S) :
    (l.geometry G hG hGO).V.val p = l.euclideanVelocity (lowJet G p) := by
  apply ContinuousMap.ext
  intro t
  change (Family.ofLocal (fun q => l.euclideanVelocity (lowJet G q)) _).val p t = _
  exact Family.ofLocal_apply _ _ hp t

lemma geometry_mean {p : JetPolynomial.Base} (hp : p ∈ S) :
    average ((l.geometry G hG hGO).V.val p) = ι (normal (lowJet G p)) := by
  rw [l.geometry_velocity hG hGO hp]
  exact l.euclideanVelocity_mean (hGO hp)

lemma geometry_dx {p : JetPolynomial.Base} (hp : p ∈ S) :
    fderiv ℝ (fun q => ι (G q)) p (coordinateVector 0) =
      (l.geometry G hG hGO).X₀ p + average ((l.geometry G hG hGO).V.val p) := by
  rw [euclidean_first_derivative hG, l.geometry_mean hG hGO hp]
  change ι (slot 1 (lowJet G p)) = ι (tangent (lowJet G p)) + ι (normal (lowJet G p))
  rw [← map_add]
  congr 1
  dsimp [tangent]
  abel

lemma geometry_dy (p : JetPolynomial.Base) :
    fderiv ℝ (fun q => ι (G q)) p (coordinateVector 1) = (l.geometry G hG hGO).Y p :=
  euclidean_first_derivative hG 1 p

end Loop
end ClosedSurfaceR4.SurfaceVelocityFamily

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Correction_BoundedSurfaceCorrection
attribute [-instance] _root_.instVAddIntReal_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Apply the finite periodic correction to the actual geometric second-jet
family, including global smooth extension and its uniform scale bound. -/
noncomputable section
open Set
open scoped ContDiff

namespace ClosedSurfaceR4.SurfaceVelocityFamily
open RealModes JetPolynomial JetVelocityCoordinates LocalPeriodicExpansion
open CovarianceCorrector WeightedEstimates

namespace Loop
variable {O : TopologicalSpace.Opens LowJet} (l : Loop O)

lemma yData_smooth : ContDiffOn ℝ ∞ yData O :=
  (JetVelocityCoordinates.toEuclidean.contDiff.comp (slot_smooth 2)).contDiffOn

lemma cData_smooth : ContDiffOn ℝ ∞ cData O :=
  (JetVelocityCoordinates.toEuclidean.contDiff.comp (slot_smooth 6)).contDiffOn

include l in
lemma xData_smooth : ContDiffOn ℝ ∞ xData O :=
  JetVelocityCoordinates.toEuclidean.contDiff.comp_contDiffOn l.smoothTangent

end Loop
end ClosedSurfaceR4.SurfaceVelocityFamily

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Correction_PolynomialPerturbationCalculus
attribute [-instance] _root_.instMembershipProdContinuousLinearMapRealIdRelLoc _root_.instVAddIntReal_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The perturbation operators and their actual first variations. -/
noncomputable section
open scoped ContDiff BigOperators

namespace ClosedSurfaceR4.JetPolynomial.Perturbation

variable {n : ℕ}

lemma eval_smooth {O : Set LowJet} {U : Set Base} {P : Fin n → Expression}
    (hP : ∀ l, (P l).SmoothCoeffs O) (ε : ℝ) {G : Base → Space}
    (hG : ContDiff ℝ ∞ G) (hQ : Set.MapsTo (lowJet G) U O) :
    ContDiffOn ℝ ∞ (eval P ε G) (U ×ˢ Set.univ) := by
  exact ContDiffOn.sum (fun l _ => contDiffOn_const.mul ((P l).eval_smooth hG hQ (hP l)))

end ClosedSurfaceR4.JetPolynomial.Perturbation

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Geometry_SurfaceMetricExpansion
attribute [-instance] _root_.instMembershipProdContinuousLinearMapRealIdRelLoc _root_.instVAddIntReal_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The finite metric expansion of the actual surface map, with its leading
primitive tensor identified and its fast remainder uniformly bounded. -/
noncomputable section
open Set
open scoped ContDiff BigOperators

namespace ClosedSurfaceR4.SurfaceVelocityFamily
open RealModes JetPolynomial JetVelocityCoordinates LocalPeriodicExpansion
open CovarianceCorrector WeightedEstimates
local notation "ι" => JetVelocityCoordinates.toEuclidean

namespace Loop
variable {O : TopologicalSpace.Opens LowJet} (l : Loop O)

/-- No derivative or leading-metric identities are additional assumptions:
they follow from the actual coordinate jet and the geometric loop. -/
theorem compact_surface_metric_error {S : TopologicalSpace.Opens JetPolynomial.Base}
    {K : Set LowJet} (hK : IsCompact K) (hKO : K ⊆ O)
    (n : ℕ) (b c : Bool) (ℓ : JetPolynomial.Base →L[ℝ] ℝ)
    (hℓx : ℓ (coordinateVector 0) = 1) (hℓy : ℓ (coordinateVector 1) = 0) :
    ∃ d : ℕ, ∀ (m : ℕ) (B : ℝ), 1 ≤ B → ∃ D : ℝ, 0 ≤ D ∧
      ∀ (G : JetPolynomial.Base → JetPolynomial.Space) (hG : ContDiff ℝ ∞ G)
        (hGK : MapsTo (lowJet G) S K) (s z : ℝ), 0 < z → z ≤ s → s ≤ 1 →
      WeightedBound S s (m + (2 * (n + 1) + 1)) B (lowJet G) →
      let g := l.geometry G hG (fun _ hp => hKO (hGK hp))
      ∀ U : ℕ → Family S Euclidean,
        (∀ i, VectorExpression.Represents G (l.coefficientExpressions n i) (U i)) →
        U 0 = g.initial → (g.yyCoefficient U 1).fluct = 0 →
        (∀ r, 1 ≤ r → r ≤ n →
          (g.xxCoefficient (coordinateVector 0) U r).fluct = 0 ∧
          (g.xyCoefficient (coordinateVector 0) U r).fluct = 0 ∧
          (g.yyCoefficient U (r + 1)).fluct = 0) →
        WeightedBound S z m (D * z ^ (n + 1) / s ^ d)
          (fun p => inner ℝ
            (fderiv ℝ (finiteAnsatz (fun q => ι (G q)) U ℓ (n + 1) z) p
              (MetricPolynomial.metricDirection (coordinateVector 0) (coordinateVector 1) b))
            (fderiv ℝ (finiteAnsatz (fun q => ι (G q)) U ℓ (n + 1) z) p
              (MetricPolynomial.metricDirection (coordinateVector 0) (coordinateVector 1) c)) -
            MetricPolynomial.meanMetric g (coordinateVector 0) U n b c z p) := by
  have hd : ∀ J ∈ O, PeriodicCorrector.gramDet (yData J) (cData J) ≠ 0 := by
    intro J hJ
    rw [yData, cData, gram_toEuclidean]
    exact l.gram_ne J hJ
  have hRs := MetricPolynomial.coefficients_smooth O.isOpen yData_smooth cData_smooth
    (xData_smooth l) l.euclideanVelocity_smooth hd l.smoothQ (fun _ hJ => l.q_pos hJ)
    (fun _ hJ => l.euclideanVelocity_length hJ) 0 1 n
  obtain ⟨d, hb⟩ := MetricPolynomial.compact_metric_error (S := S) O.isOpen hK hKO
    (MetricPolynomial.longitudinal xData l.euclideanVelocity) (MetricPolynomial.transverse yData)
    (l.coefficientExpressions n)
    (MetricPolynomial.smooth_longitudinal (xData_smooth l) l.euclideanVelocity_smooth)
    (MetricPolynomial.smooth_transverse yData_smooth) hRs n (fun _ => le_rfl) (fun _ => le_rfl)
    (fun j _ a => MetricPolynomial.coefficients_order _ _ _ _ _ 0 1 n j a)
    0 1 b c ℓ hℓx hℓy
  refine ⟨d, ?_⟩
  intro m B hB
  obtain ⟨D, hD, hbound⟩ := hb m B hB
  refine ⟨D, hD, ?_⟩
  intro G hG hGK s z hz hzs hs1 hGs g U hrep hinit hy hc
  exact hbound G s z hz hzs hs1 hG hGK hGs g U (fun q => ι (G q))
    (MetricPolynomial.represents_longitudinal g xData l.euclideanVelocity (fun _ _ => rfl)
      (fun _ hp => l.geometry_velocity hG (fun _ hp => hKO (hGK hp)) hp))
    (MetricPolynomial.represents_transverse g yData (fun _ _ => rfl))
    hrep hinit hy hc (JetVelocityCoordinates.toEuclidean.contDiff.comp hG).contDiffOn
    (fun _ hp => l.geometry_dx hG (fun _ hp => hKO (hGK hp)) hp)
    (fun p _ => l.geometry_dy hG (fun _ hp => hKO (hGK hp)) p)

end Loop
end ClosedSurfaceR4.SurfaceVelocityFamily

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Correction_SurfaceMeanPolynomial
attribute [-instance] _root_.instMembershipProdContinuousLinearMapRealIdRelLoc _root_.instVAddIntReal_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The finite mean correction is an actual higher-jet polynomial, so the
perturbed small-increment solver applies to the same metric expansion. -/
noncomputable section
open Set
open scoped ContDiff BigOperators
namespace ClosedSurfaceR4.SurfaceVelocityFamily
open RealModes JetPolynomial JetVelocityCoordinates LocalPeriodicExpansion CovarianceCorrector

namespace Loop
variable {O : TopologicalSpace.Opens LowJet} (l : Loop O)

lemma coefficientExpressions_smooth (n i : ℕ) :
    (l.coefficientExpressions n i).SmoothCoeffs O :=
  MetricPolynomial.coefficients_smooth O.isOpen yData_smooth cData_smooth
    (xData_smooth l) l.euclideanVelocity_smooth
    (fun J hJ => by rw [yData,cData,gram_toEuclidean]; exact l.gram_ne J hJ)
    l.smoothQ (fun _ hJ => l.q_pos hJ) (fun _ hJ => l.euclideanVelocity_length hJ) 0 1 n i

lemma meanPolynomial_smooth (n : ℕ) (b c : Bool) (r : Fin n) :
    (l.meanPolynomial n b c r).SmoothCoeffs O := by
  apply Expression.smoothCoeffs_mean O.isOpen
  apply MetricPolynomial.smooth_finiteMetric
  all_goals
    intro i
    exact MetricPolynomial.smooth_tangentExpression O.isOpen
      (MetricPolynomial.smooth_longitudinal (xData_smooth l) l.euclideanVelocity_smooth)
      (MetricPolynomial.smooth_transverse yData_smooth) (l.coefficientExpressions_smooth n)
      0 1 (n+1) _ i

end Loop
end ClosedSurfaceR4.SurfaceVelocityFamily

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Primitive_PeriodicFastEvaluation
attribute [-instance] _root_.instVAddIntReal_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Chain rule for substituting a fast linear phase in a smooth periodic family. -/

noncomputable section
open scoped ContDiff

namespace ClosedSurfaceR4.PeriodicExpansion

open CovarianceCorrector SmoothPeriodicCalculus

variable {A E : Type} [NormedAddCommGroup A] [NormedSpace ℝ A]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E]

namespace Family

lemma fastValue_smooth (U : Family A E) (ℓ : A →L[ℝ] ℝ) (z : ℝ) :
    ContDiff ℝ ∞ (U.fastValue ℓ z) :=
  U.smooth.comp (contDiff_id.prodMk (ℓ.contDiff.div_const z))

end Family
end ClosedSurfaceR4.PeriodicExpansion

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Primitive_PeriodicFiniteAnsatz
attribute [-instance] _root_.instMembershipProdContinuousLinearMapRealIdRelLoc _root_.instVAddIntReal_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The finite oscillatory map and its actual first derivatives. -/

noncomputable section
open scoped ContDiff BigOperators

namespace ClosedSurfaceR4.PeriodicExpansion

open CovarianceCorrector

variable {A E : Type} [NormedAddCommGroup A] [NormedSpace ℝ A]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E]

lemma finiteAnsatz_smooth {F : A → E} (hF : ContDiff ℝ ∞ F)
    (U : ℕ → Family A E) (ℓ : A →L[ℝ] ℝ) (L : ℕ) (z : ℝ) :
    ContDiff ℝ ∞ (finiteAnsatz F U ℓ L z) :=
  hF.add (ContDiff.sum fun i _ => contDiff_const.smul ((U i).fastValue_smooth ℓ z))

end ClosedSurfaceR4.PeriodicExpansion

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Primitive_SurfacePrimitiveError
attribute [-instance] _root_.instMembershipProdContinuousLinearMapRealIdRelLoc _root_.instVAddIntReal_solutions
attribute [-simp] _root_.ContinuousLinearMap.comp_toSpanSingleton_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.circularPhaseBoundaryCurve_carrier _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.directionJetLinearization_apply _root_.OAI.ClosedSurfaceR4.GeometryPreservation.boundaryProfileMap_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_C _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_J _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_e _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowPosition_lowJet _root_.OAI.ClosedSurfaceR4.RealModes.secondTensorFromJet_realTwoJet _root_.Path.extend_div_self
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The finite primitive's actual metric error is the sum of its solved mean
error and the fast finite tail. The prescribed amplitude is fixed in position. -/
noncomputable section
open Set
open scoped ContDiff
namespace ClosedSurfaceR4.SurfaceVelocityFamily.Loop
open RealModes JetPolynomial JetVelocityCoordinates LocalPeriodicExpansion CovarianceCorrector
open WeightedEstimates

variable {O : TopologicalSpace.Opens LowJet} (l : SurfaceVelocityFamily.Loop O)

lemma meanOperator_smooth {S : TopologicalSpace.Opens Base}
    {G : JetPolynomial.Base → JetPolynomial.Space} (hG : ContDiff ℝ ∞ G) (hGO : MapsTo (lowJet G) S O)
    (n : ℕ) (b c : Bool) (z : ℝ) : ContDiffOn ℝ ∞ (l.meanOperator n b c z G) S := by
  have hF := JetVelocityCoordinates.toEuclidean.contDiff.comp hG
  have hd := hF.fderiv_right (m := ∞) (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)
  apply ((hd.clm_apply contDiff_const).inner ℝ (hd.clm_apply contDiff_const)).contDiffOn.add
  have he := Perturbation.eval_smooth (fun r => l.meanPolynomial_smooth n b c r) z hG hGO
  exact he.comp (contDiff_id.prodMk contDiff_const).contDiffOn (fun p hp => ⟨hp,mem_univ _⟩)

/-- A solved mean equation controls the actual primitive metric at every
finite weighted order. The tail loss is chosen before the order or slow map. -/
theorem compact_primitive_error {a : Base → ℝ} (ha : ContDiff ℝ ∞ a)
    (hamp : l.HasSpatialAmplitude a) {S : TopologicalSpace.Opens Base}
    {K : Set LowJet} (hK : IsCompact K) (hKO : K ⊆ O)
    (n : ℕ) (b c : Bool) (ℓ : Base →L[ℝ] ℝ)
    (hℓx : ℓ (coordinateVector 0) = 1) (hℓy : ℓ (coordinateVector 1) = 0) :
    ∃ d : ℕ, ∀ (m : ℕ) (B : ℝ), 1 ≤ B → ∃ D : ℝ, 0 ≤ D ∧
      ∀ (G : JetPolynomial.Base → JetPolynomial.Space) (hG : ContDiff ℝ ∞ G) (hGK : MapsTo (lowJet G) S K)
        (s z : ℝ), 0 < z → z ≤ s → s ≤ 1 →
      WeightedBound S s (m+(2*(n+1)+1)) B (lowJet G) →
      let g := l.geometry G hG (fun _ hp => hKO (hGK hp))
      ∀ U : ℕ → Family S Euclidean,
        (∀ i, VectorExpression.Represents G (l.coefficientExpressions n i) (U i)) →
        U 0 = g.initial → (g.yyCoefficient U 1).fluct = 0 →
        (∀ r, 1 ≤ r → r ≤ n →
          (g.xxCoefficient (coordinateVector 0) U r).fluct = 0 ∧
          (g.xyCoefficient (coordinateVector 0) U r).fluct = 0 ∧
          (g.yyCoefficient U (r+1)).fluct = 0) →
      ∀ (H : Base → ℝ), ContDiffOn ℝ ∞ H S → ∀ E : ℝ,
      WeightedBound S s m E (l.meanOperator n b c z G-H) →
      WeightedBound S z m (D*z^(n+1)/s^d+E)
        (fun p => inner ℝ
          (fderiv ℝ (finiteAnsatz (fun q => JetVelocityCoordinates.toEuclidean (G q))
            U ℓ (n+1) z) p
            (MetricPolynomial.metricDirection (coordinateVector 0) (coordinateVector 1) b))
          (fderiv ℝ (finiteAnsatz (fun q => JetVelocityCoordinates.toEuclidean (G q))
            U ℓ (n+1) z) p
            (MetricPolynomial.metricDirection (coordinateVector 0) (coordinateVector 1) c)) -
          (H p+(if b && c then a p^2 else 0))) := by
  obtain ⟨d,hd⟩ := l.compact_surface_metric_error (S := S) hK hKO n b c ℓ hℓx hℓy
  refine ⟨d,?_⟩
  intro m B hB
  obtain ⟨D,hD,hbound⟩ := hd m B hB
  refine ⟨D,hD,?_⟩
  intro G hG hGK s z hz hzs hs1 hGb g U hU hinit hy hc H hH E hErr
  have hGO : MapsTo (lowJet G) S O := fun _ hp => hKO (hGK hp)
  have htail := hbound G hG hGK s z hz hzs hs1 hGb U hU hinit hy hc
  have hbase : ContDiffOn ℝ ∞ (fun q => JetVelocityCoordinates.toEuclidean (G q)) S :=
    (JetVelocityCoordinates.toEuclidean.contDiff.comp hG).contDiffOn
  have hfinite := finiteAnsatz_smooth hbase U ℓ (n+1) z
  have hfd := hfinite.fderiv_of_isOpen S.isOpen (m := ∞) (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)
  have hmetric : ContDiffOn ℝ ∞ (fun p => inner ℝ
      (fderiv ℝ (finiteAnsatz (fun q => JetVelocityCoordinates.toEuclidean (G q))
        U ℓ (n+1) z) p
        (MetricPolynomial.metricDirection (coordinateVector 0) (coordinateVector 1) b))
      (fderiv ℝ (finiteAnsatz (fun q => JetVelocityCoordinates.toEuclidean (G q))
        U ℓ (n+1) z) p
        (MetricPolynomial.metricDirection (coordinateVector 0) (coordinateVector 1) c))) S :=
    (hfd.clm_apply contDiffOn_const).inner ℝ (hfd.clm_apply contDiffOn_const)
  have hmean := l.meanOperator_smooth hG hGO n b c z
  have hAmp : ContDiffOn ℝ ∞ (fun p => if b && c then a p^2 else 0) S := by
    split_ifs
    · exact (ha.pow 2).contDiffOn
    · exact contDiffOn_const
  have hMeanMetric : ContDiffOn ℝ ∞
      (MetricPolynomial.meanMetric g (coordinateVector 0) U n b c z) S := by
    apply (hmean.add hAmp).congr
    intro p hp
    exact l.meanMetric_eq_meanOperator hamp hG hGO n b c z U hU hp
  have hsErr := hErr.shrink_scale hz.le hzs
  have hb := htail.add S.isOpen.uniqueDiffOn hz.le (hmetric.sub hMeanMetric)
    (hmean.sub hH) hsErr
  apply hb.congr
  intro p hp
  dsimp only [g]
  rw [l.meanMetric_eq_meanOperator hamp hG hGO n b c z U hU hp]
  ring

end ClosedSurfaceR4.SurfaceVelocityFamily.Loop

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Primitive_PeriodicMetricCoordinates
attribute [-instance] _root_.instMetricSpaceOneJet _root_.instVAddIntReal_solutions
attribute [-simp] _root_.ContinuousLinearMap.comp_toSpanSingleton_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.circularPhaseBoundaryCurve_carrier _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.exactCellCutoff_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.directionJetLinearization_apply _root_.OAI.ClosedSurfaceR4.GeometryPreservation.boundaryProfileMap_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_C _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_J _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_e _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.modeSupport_jetSupport _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.onModeSupport_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowPosition_lowJet _root_.OAI.ClosedSurfaceR4.PhaseGeometry.linearPhaseChart_apply _root_.OAI.ClosedSurfaceR4.PhaseGeometry.linearPhaseChart_source _root_.OAI.ClosedSurfaceR4.PhaseGeometry.linearPhaseChart_symm_apply _root_.OAI.ClosedSurfaceR4.PhaseGeometry.linearPhaseChart_target _root_.OAI.ClosedSurfaceR4.PhaseGeometry.phaseEquiv_apply _root_.OAI.ClosedSurfaceR4.PhaseGeometry.phaseEquiv_symm_apply _root_.OAI.ClosedSurfaceR4.PhasePartitions.CompactPhasePartition.coe_pieceSupport _root_.OAI.ClosedSurfaceR4.PhasePartitions.CompactPhasePartition.coe_supportCompact _root_.OAI.ClosedSurfaceR4.PhasePartitions.CompactPhasePartition.splitSupported_apply _root_.OAI.ClosedSurfaceR4.PhasePartitions.CompactPhasePartition.supportedWeight_apply _root_.OAI.ClosedSurfaceR4.RealModes.secondTensorFromJet_realTwoJet _root_.Path.extend_div_self
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Exact identification of the three coordinate metric entries of a
Euclidean periodic map in the primitive's product coordinates. -/
noncomputable section
open scoped ContDiff Matrix
namespace ClosedSurfaceR4.LocalPeriodicExpansion
open JetPolynomial JetPolynomial.Perturbation SmallModes

lemma metric_coordinate_pair {f : JetPolynomial.Base → ClosedSurfaceR4.Space}
    (hf : ContDiff ℝ ∞ f) (p : JetPolynomial.Base) (b c : Bool) :
    RealModes.realMetric (spaceCoordinates ∘ f ∘ planeCoordinateIsometry.symm)
      (if b then dx else dy) (if c then dx else dy) (planeCoordinateIsometry p) =
      inner ℝ
        (fderiv ℝ f p (MetricPolynomial.metricDirection (coordinateVector 0) (coordinateVector 1) b))
        (fderiv ℝ f p (MetricPolynomial.metricDirection (coordinateVector 0) (coordinateVector 1) c)) := by
  have he := euclidean_metric_coordinate_value (f ∘ planeCoordinateIsometry.symm)
    ((hf.comp planeCoordinateIsometry.symm.contDiff).differentiable (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top) (planeCoordinateIsometry p))
    (if b then dx else dy) (if c then dx else dy)
  rw [RealModes.evaluate_realMetricTensor] at he
  have hd (v : SmallModes.Base) :
      fderiv ℝ (f ∘ planeCoordinateIsometry.symm) (planeCoordinateIsometry p) v =
        fderiv ℝ f p (planeCoordinateIsometry.symm v) := by
    rw [fderiv_comp _ (hf.differentiable (by simp) _)
      planeCoordinateIsometry.symm.differentiableAt]
    simp only [ContinuousLinearMap.comp_apply,planeCoordinateIsometry.symm_apply_apply]
    change (fderiv ℝ f p)
      ((fderiv ℝ planeCoordinateIsometry.symm.toContinuousLinearEquiv.toContinuousLinearMap
        (planeCoordinateIsometry p)) v) = _
    rw [planeCoordinateIsometry.symm.toContinuousLinearEquiv.toContinuousLinearMap.fderiv]
    rfl
  have hdir (d : Bool) : planeCoordinateIsometry.symm (if d then dx else dy) =
      MetricPolynomial.metricDirection (coordinateVector 0) (coordinateVector 1) d := by
    cases d <;> ext i <;> fin_cases i <;> rfl
  simpa only [Function.comp_assoc,hd,hdir] using he

lemma metric_coordinate_tensor {f : JetPolynomial.Base → ClosedSurfaceR4.Space}
    (hf : ContDiff ℝ ∞ f) (p : JetPolynomial.Base) :
    RealModes.realMetricTensor (spaceCoordinates ∘ f ∘ planeCoordinateIsometry.symm)
      (planeCoordinateIsometry p) =
    ![inner ℝ (fderiv ℝ f p (coordinateVector 0)) (fderiv ℝ f p (coordinateVector 0)),
      inner ℝ (fderiv ℝ f p (coordinateVector 0)) (fderiv ℝ f p (coordinateVector 1)),
      inner ℝ (fderiv ℝ f p (coordinateVector 1)) (fderiv ℝ f p (coordinateVector 1))] := by
  ext k
  fin_cases k
  · exact metric_coordinate_pair hf p true true
  · exact metric_coordinate_pair hf p true false
  · exact metric_coordinate_pair hf p false false

end ClosedSurfaceR4.LocalPeriodicExpansion

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Primitive_UniformPrimitiveRemainder
attribute [-instance] _root_.instMembershipProdContinuousLinearMapRealIdRelLoc _root_.instVAddIntReal_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! One finite loss and one coefficient profile control all metric components
of the actual periodic primitive, before the slow map is selected. -/
noncomputable section
open Set
open scoped ContDiff BigOperators
namespace ClosedSurfaceR4.SurfaceVelocityFamily.Loop
open RealModes JetPolynomial JetVelocityCoordinates LocalPeriodicExpansion CovarianceCorrector WeightedEstimates
variable {O : TopologicalSpace.Opens LowJet} (l : SurfaceVelocityFamily.Loop O)

theorem uniform_primitive_remainder {a : JetPolynomial.Base → ℝ} (ha : ContDiff ℝ ∞ a)
    (hamp : l.HasSpatialAmplitude a) {S : TopologicalSpace.Opens JetPolynomial.Base}
    {K : Set LowJet} (hK : IsCompact K) (hKO : K ⊆ O)
    (n : ℕ) (ℓ : JetPolynomial.Base →L[ℝ] ℝ)
    (hℓx : ℓ (coordinateVector 0) = 1) (hℓy : ℓ (coordinateVector 1) = 0) :
    ∃ loss : ℕ, ∀ (m : ℕ) (B : ℝ), 1 ≤ B → ∃ D : ℝ, 0 ≤ D ∧
      ∀ (G : JetPolynomial.Base → JetPolynomial.Space) (hG : ContDiff ℝ ∞ G)
        (hGK : MapsTo (lowJet G) S K) (s z : ℝ), 0 < z → z ≤ s → s ≤ 1 →
      WeightedBound S s (m+(2*(n+1)+1)) B (lowJet G) →
      let g := l.geometry G hG (fun _ hp => hKO (hGK hp))
      ∀ U : ℕ → Family S Euclidean,
        (∀ i, VectorExpression.Represents G (l.coefficientExpressions n i) (U i)) →
        U 0 = g.initial → (g.yyCoefficient U 1).fluct = 0 →
        (∀ r, 1 ≤ r → r ≤ n →
          (g.xxCoefficient (coordinateVector 0) U r).fluct = 0 ∧
          (g.xyCoefficient (coordinateVector 0) U r).fluct = 0 ∧
          (g.yyCoefficient U (r+1)).fluct = 0) →
      ∀ b c : Bool, WeightedBound S z m (D*z^(n+1)/s^loss)
        (fun p => inner ℝ
          (fderiv ℝ (finiteAnsatz (fun q => JetVelocityCoordinates.toEuclidean (G q))
            U ℓ (n+1) z) p
            (MetricPolynomial.metricDirection (coordinateVector 0) (coordinateVector 1) b))
          (fderiv ℝ (finiteAnsatz (fun q => JetVelocityCoordinates.toEuclidean (G q))
            U ℓ (n+1) z) p
            (MetricPolynomial.metricDirection (coordinateVector 0) (coordinateVector 1) c))-
          (l.meanOperator n b c z G p+(if b && c then a p^2 else 0))) := by
  classical
  choose d hd using fun bc : Bool × Bool => l.compact_primitive_error ha hamp hK hKO n bc.1 bc.2 ℓ hℓx hℓy
  let loss := Finset.univ.sup d
  refine ⟨loss,?_⟩
  intro m B hB
  choose C hC hc using fun bc : Bool × Bool => hd bc m B hB
  let D := ∑ bc : Bool × Bool, C bc
  have hD : 0 ≤ D := Finset.sum_nonneg (fun bc _ => hC bc)
  have hCD (bc : Bool × Bool) : C bc ≤ D :=
    Finset.single_le_sum (fun bc _ => hC bc) (Finset.mem_univ _)
  refine ⟨D,hD,?_⟩
  intro G hG hGK s z hz hzs hs1 hGb g U hU hinit hy hcoeff b c
  have hs : 0 < s := hz.trans_le hzs
  have hmean := l.meanOperator_smooth hG (fun _ hp => hKO (hGK hp)) n b c z
  have hzero : WeightedBound S s m 0
      (l.meanOperator n b c z G-l.meanOperator n b c z G) := by
    have he : l.meanOperator n b c z G-l.meanOperator n b c z G = (fun _ => (0 : ℝ)) := by
      funext p
      exact sub_self _
    rw [he]
    exact weightedBound_zero (S : Set JetPolynomial.Base) s m (F := ℝ)
  have hb := hc (b,c) G hG hGK s z hz hzs hs1 hGb U hU hinit hy hcoeff
    (l.meanOperator n b c z G) hmean 0 hzero
  simp only [add_zero] at hb
  apply hb.mono_const
  have hdl : d (b,c) ≤ loss := Finset.le_sup (Finset.mem_univ _)
  have hp : s^loss ≤ s^d (b,c) := pow_le_pow_of_le_one hs.le hs1 hdl
  calc
    C (b,c)*z^(n+1)/s^d (b,c) ≤ D*z^(n+1)/s^d (b,c) :=
      div_le_div_of_nonneg_right
        (mul_le_mul_of_nonneg_right (hCD (b,c)) (pow_nonneg hz.le _)) (pow_nonneg hs.le _)
    _ ≤ D*z^(n+1)/s^loss := div_le_div_of_nonneg_left
      (mul_nonneg hD (pow_nonneg hz.le _)) (pow_pos hs _) hp

end ClosedSurfaceR4.SurfaceVelocityFamily.Loop

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Primitive_PrimitiveTensorRemainder
attribute [-instance] _root_.instMembershipProdContinuousLinearMapRealIdRelLoc _root_.instVAddIntReal_solutions
attribute [-simp] _root_.ContinuousLinearMap.comp_toSpanSingleton_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.circularPhaseBoundaryCurve_carrier _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.exactCellCutoff_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.directionJetLinearization_apply _root_.OAI.ClosedSurfaceR4.GeometryPreservation.boundaryProfileMap_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_C _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_J _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_e _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.modeSupport_jetSupport _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.onModeSupport_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowPosition_lowJet _root_.OAI.ClosedSurfaceR4.PhaseGeometry.linearPhaseChart_apply _root_.OAI.ClosedSurfaceR4.PhaseGeometry.linearPhaseChart_source _root_.OAI.ClosedSurfaceR4.PhaseGeometry.linearPhaseChart_symm_apply _root_.OAI.ClosedSurfaceR4.PhaseGeometry.linearPhaseChart_target _root_.OAI.ClosedSurfaceR4.PhaseGeometry.phaseEquiv_apply _root_.OAI.ClosedSurfaceR4.PhaseGeometry.phaseEquiv_symm_apply _root_.OAI.ClosedSurfaceR4.PhasePartitions.CompactPhasePartition.coe_pieceSupport _root_.OAI.ClosedSurfaceR4.PhasePartitions.CompactPhasePartition.coe_supportCompact _root_.OAI.ClosedSurfaceR4.PhasePartitions.CompactPhasePartition.splitSupported_apply _root_.OAI.ClosedSurfaceR4.PhasePartitions.CompactPhasePartition.supportedWeight_apply _root_.OAI.ClosedSurfaceR4.RealModes.secondTensorFromJet_realTwoJet _root_.Path.extend_div_self
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The three scalar remainder estimates control the actual full metric
tensor of the same finite periodic ansatz. -/
noncomputable section
open Set
open scoped ContDiff Matrix
namespace ClosedSurfaceR4.SurfaceVelocityFamily.Loop
open RealModes JetPolynomial JetVelocityCoordinates LocalPeriodicExpansion CovarianceCorrector WeightedEstimates
variable {O : TopologicalSpace.Opens LowJet} (l : SurfaceVelocityFamily.Loop O)

theorem uniform_primitive_metric_remainder_oai {a : JetPolynomial.Base → ℝ} (ha : ContDiff ℝ ∞ a)
    (hamp : l.HasSpatialAmplitude a) {S : TopologicalSpace.Opens JetPolynomial.Base}
    {K : Set LowJet} (hK : IsCompact K) (hKO : K ⊆ O)
    (n : ℕ) (ℓ : JetPolynomial.Base →L[ℝ] ℝ)
    (hℓx : ℓ (coordinateVector 0) = 1) (hℓy : ℓ (coordinateVector 1) = 0) :
    ∃ loss : ℕ, ∀ (m : ℕ) (B : ℝ), 1 ≤ B → ∃ D : ℝ, 0 ≤ D ∧
      ∀ (G : JetPolynomial.Base → JetPolynomial.Space) (hG : ContDiff ℝ ∞ G)
        (hGK : MapsTo (lowJet G) S K) (s z : ℝ), 0 < z → z ≤ s → s ≤ 1 →
      WeightedBound S s (m+(2*(n+1)+1)) B (lowJet G) →
      let g := l.geometry G hG (fun _ hp => hKO (hGK hp))
      ∀ U : ℕ → Family S Euclidean,
        (∀ i, VectorExpression.Represents G (l.coefficientExpressions n i) (U i)) →
        (∀ i, ContDiff ℝ ∞ (fun y : JetPolynomial.Base × ℝ => (U i).val y.1 (y.2 : Period))) →
        U 0 = g.initial → (g.yyCoefficient U 1).fluct = 0 →
        (∀ r, 1 ≤ r → r ≤ n →
          (g.xxCoefficient (coordinateVector 0) U r).fluct = 0 ∧
          (g.xyCoefficient (coordinateVector 0) U r).fluct = 0 ∧
          (g.yyCoefficient U (r+1)).fluct = 0) →
      WeightedBound S z m (D*z^(n+1)/s^loss)
        (fun p => RealModes.realMetricTensor
          (spaceCoordinates ∘ finiteAnsatz (fun q => JetVelocityCoordinates.toEuclidean (G q)) U ℓ (n+1) z ∘
            planeCoordinateIsometry.symm) (planeCoordinateIsometry p)-
          l.meanTensorOperator n z G (planeCoordinateIsometry p)-![a p^2,0,0]) := by
  obtain ⟨loss,hb⟩ := l.uniform_primitive_remainder ha hamp hK hKO n ℓ hℓx hℓy
  refine ⟨loss,?_⟩
  intro m B hB
  obtain ⟨D,hD,hd⟩ := hb m B hB
  refine ⟨D,hD,?_⟩
  intro G hG hGK s z hz hzs hs1 hGb g U hrep hU hinit hy hcoeff
  have hs : 0 < s := hz.trans_le hzs
  have hGO : MapsTo (lowJet G) S O := fun _ hp => hKO (hGK hp)
  let f := finiteAnsatz (fun q => JetVelocityCoordinates.toEuclidean (G q)) U ℓ (n+1) z
  have hf : ContDiff ℝ ∞ f := by
    exact PeriodicExpansion.finiteAnsatz_smooth (JetVelocityCoordinates.toEuclidean.contDiff.comp hG)
      (globalCoefficients U hU) ℓ (n+1) z
  let E : Bool → Bool → JetPolynomial.Base → ℝ := fun b c p =>
    inner ℝ
      (fderiv ℝ f p (MetricPolynomial.metricDirection (coordinateVector 0) (coordinateVector 1) b))
      (fderiv ℝ f p (MetricPolynomial.metricDirection (coordinateVector 0) (coordinateVector 1) c))-
      (l.meanOperator n b c z G p+(if b && c then a p^2 else 0))
  have hEs (b c : Bool) : ContDiffOn ℝ ∞ (E b c) S := by
    have hdf := hf.fderiv_right (m := ∞) (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)
    apply ((hdf.clm_apply contDiff_const).inner ℝ (hdf.clm_apply contDiff_const)).contDiffOn.sub
    apply (l.meanOperator_smooth hG hGO n b c z).add
    split_ifs
    · exact (ha.pow 2).contDiffOn
    · exact contDiffOn_const
  have hEb (b c : Bool) : WeightedBound S z m (D*z^(n+1)/s^loss) (E b c) :=
    hd G hG hGK s z hz hzs hs1 hGb U hrep hinit hy hcoeff b c
  let bf : Fin 3 → Bool := ![true,true,false]
  let cf : Fin 3 → Bool := ![true,false,false]
  have hbvec := WeightedBound.pi S.isOpen.uniqueDiffOn hz
    (div_nonneg (mul_nonneg hD (pow_nonneg hz.le _)) (pow_nonneg hs.le _))
    (fun k : Fin 3 => hEs (bf k) (cf k)) (fun k => hEb (bf k) (cf k))
  have heq : (fun p => RealModes.realMetricTensor
      (spaceCoordinates ∘ f ∘ planeCoordinateIsometry.symm) (planeCoordinateIsometry p)-
      l.meanTensorOperator n z G (planeCoordinateIsometry p)-![a p^2,0,0]) =
        (fun p k => E (bf k) (cf k) p) := by
    funext p k
    rw [metric_coordinate_tensor hf p]
    fin_cases k <;>
      simp [E,bf,cf,meanTensorOperator,MetricPolynomial.metricDirection]
    ring
  rw [heq]
  exact hbvec

end ClosedSurfaceR4.SurfaceVelocityFamily.Loop

end

end OAI
end

theorem solution : type_of% @OAI.ClosedSurfaceR4.SurfaceVelocityFamily.Loop.uniform_primitive_metric_remainder_oai := @OAI.ClosedSurfaceR4.SurfaceVelocityFamily.Loop.uniform_primitive_metric_remainder_oai
