-- Prove2me | solution 1 for OAI.ClosedSurfaceR4.SurfaceVelocityFamily.Loop.uniform_mixed_profile
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-12T12:50:40.241586+00:00
-- url     : https://prove2.me/submissions/7418ce27-75fa-4ea1-803e-fc25306c4473

import Mathlib
import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
import Mathlib.Geometry.Manifold.PartitionOfUnity
import Definitions.Def_OAIQ249SI012
import Theorems.Thm_OAI_ClosedSurfaceR4_JetPolynomial_Expression_fullComponent_bounds
import Theorems.Thm_OAI_ClosedSurfaceR4_JetPolynomial_MetricPolynomial_coefficients_smooth
import Theorems.Thm_OAI_ClosedSurfaceR4_JetPolynomial_VectorExpression_compact_coefficient_two_jets

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Primitive_LocalPeriodicCalculus
attribute [-instance] _root_.instMembershipProdContinuousLinearMapRealIdRelLoc _root_.instVAddIntReal_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Periodic differentiation and integration on an open parameter domain. -/

noncomputable section
open MeasureTheory
open scoped ContDiff Topology

namespace ClosedSurfaceR4.LocalPeriodicCalculus

open CovarianceCorrector SmoothPeriodicCalculus

variable {P E : Type} [NormedAddCommGroup P] [NormedSpace ℝ P]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E]

lemma slowOn_apply (F : P → C(Period, E)) (S : Set P) (hS : IsOpen S)
    (hF : ContDiffOn ℝ ∞ (fun z : P × ℝ => F z.1 (z.2 : Period)) (S ×ˢ Set.univ))
    (v : P) {p : P} (hp : p ∈ S) (t : ℝ) :
    slowOn F S hS hF v p (t : Period) =
      slowDerivative (fun z : P × ℝ => F z.1 (z.2 : Period)) v (p, t) :=
  bundleOn_apply _ _ _ _ _ hp t

end ClosedSurfaceR4.LocalPeriodicCalculus

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

lemma order_lowFactor (v : Fin 2) (i : LowIndex) : (lowFactor v i).order ≤ 3 := by
  cases i with
  | inl i => simp [lowFactor, order]
  | inr i =>
    obtain ⟨w, a⟩ := i
    have h : (lowWord w).length ≤ 2 := by fin_cases w <;> simp [lowWord]
    simp only [lowFactor, order, List.length_cons]
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

end Expression
end ClosedSurfaceR4.JetPolynomial

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Primitive_LocalPeriodicFamilies
attribute [-instance] _root_.instMembershipProdContinuousLinearMapRealIdRelLoc _root_.instVAddIntReal_solutions
attribute [-simp] _root_.ContinuousLinearMap.comp_toSpanSingleton_apply _root_.OAI.ClosedSurfaceR4.CollarVelocity.loopX_apply _root_.OAI.ClosedSurfaceR4.CollarVelocity.loopX_zero _root_.OAI.ClosedSurfaceR4.CollarVelocity.loopY_apply _root_.OAI.ClosedSurfaceR4.CollarVelocity.loopY_zero _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.loss_covariance _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.order_covariance _root_.OAI.ClosedSurfaceR4.LocalPeriodicExpansion.Family.fluct_apply _root_.OAI.ClosedSurfaceR4.LocalPeriodicExpansion.Family.global_apply _root_.OAI.ClosedSurfaceR4.LocalPeriodicExpansion.Family.mean_apply _root_.OAI.ClosedSurfaceR4.LocalPeriodicExpansion.Family.vectorMean_apply _root_.OAI.ClosedSurfaceR4.LocalPeriodicExpansion.Geometry.xTangent_zero _root_.OAI.ClosedSurfaceR4.LocalPeriodicExpansion.Geometry.yTangent_zero _root_.OAI.ClosedSurfaceR4.PeriodicExpansion.Family.add_apply _root_.OAI.ClosedSurfaceR4.PeriodicExpansion.Family.angle_apply _root_.OAI.ClosedSurfaceR4.PeriodicExpansion.Family.constant_apply _root_.OAI.ClosedSurfaceR4.PeriodicExpansion.Family.fluct_apply _root_.OAI.ClosedSurfaceR4.PeriodicExpansion.Family.inner_apply _root_.OAI.ClosedSurfaceR4.PeriodicExpansion.Family.mean_apply _root_.OAI.ClosedSurfaceR4.PeriodicExpansion.Family.neg_apply _root_.OAI.ClosedSurfaceR4.PeriodicExpansion.Family.slow_apply _root_.OAI.ClosedSurfaceR4.PeriodicExpansion.Family.smul_apply _root_.OAI.ClosedSurfaceR4.PeriodicExpansion.Family.sub_apply _root_.OAI.ClosedSurfaceR4.PeriodicExpansion.Family.sum_apply _root_.OAI.ClosedSurfaceR4.PeriodicExpansion.Family.zero_apply _root_.Path.extend_div_self
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Smooth periodic coefficient families on the actual open geometric domain.
Values outside that domain are fixed at zero, so equality only needs checking inside. -/
noncomputable section
open scoped ContDiff

namespace ClosedSurfaceR4.LocalPeriodicExpansion
open CovarianceCorrector LocalPeriodicCalculus

variable {A : Type} [NormedAddCommGroup A] [NormedSpace ℝ A]
variable (O : TopologicalSpace.Opens A) (E : Type) [NormedAddCommGroup E] [InnerProductSpace ℝ E]

variable {O E}
namespace Family

@[simp] lemma slow_apply (F : Family O E) (v : A) {p : A} (hp : p ∈ O) (t : ℝ) :
    (F.slow v).val p (t : Period) =
      SmoothPeriodicCalculus.slowDerivative (fun z : A × ℝ => F.val z.1 (z.2 : Period)) v (p, t) := by
  rw [slow, ofLocal_apply _ _ hp, slowOn_apply _ _ _ _ _ hp]

end Family
end ClosedSurfaceR4.LocalPeriodicExpansion

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

lemma angle_apply (F : Family O E) {p : A} (hp : p ∈ O) (t : ℝ) :
    F.angle.val p (t : Period) =
      angleDerivative (fun z : A × ℝ => F.val z.1 (z.2 : Period)) (p, t) := by
  rw [angle, ofLocal_apply _ _ hp]
  exact LocalPeriodicCalculus.bundleOn_apply _ _ _ _ _ hp t

end ClosedSurfaceR4.LocalPeriodicExpansion.Family

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

end Loop
end ClosedSurfaceR4.SurfaceVelocityFamily

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Primitive_PeriodicFastEvaluation
attribute [-instance] _root_.instVAddIntReal_solutions
attribute [-simp] _root_.ContinuousLinearMap.comp_toSpanSingleton_apply _root_.OAI.ClosedSurfaceR4.CollarVelocity.loopX_apply _root_.OAI.ClosedSurfaceR4.CollarVelocity.loopX_zero _root_.OAI.ClosedSurfaceR4.CollarVelocity.loopY_apply _root_.OAI.ClosedSurfaceR4.CollarVelocity.loopY_zero _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.loss_covariance _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.order_covariance _root_.OAI.ClosedSurfaceR4.LocalPeriodicExpansion.Family.add_apply _root_.OAI.ClosedSurfaceR4.LocalPeriodicExpansion.Family.constant_apply _root_.OAI.ClosedSurfaceR4.LocalPeriodicExpansion.Family.fluct_apply _root_.OAI.ClosedSurfaceR4.LocalPeriodicExpansion.Family.global_apply _root_.OAI.ClosedSurfaceR4.LocalPeriodicExpansion.Family.inner_apply _root_.OAI.ClosedSurfaceR4.LocalPeriodicExpansion.Family.mean_apply _root_.OAI.ClosedSurfaceR4.LocalPeriodicExpansion.Family.neg_apply _root_.OAI.ClosedSurfaceR4.LocalPeriodicExpansion.Family.ofLocal_apply _root_.OAI.ClosedSurfaceR4.LocalPeriodicExpansion.Family.slow_apply _root_.OAI.ClosedSurfaceR4.LocalPeriodicExpansion.Family.smul_apply _root_.OAI.ClosedSurfaceR4.LocalPeriodicExpansion.Family.sub_apply _root_.OAI.ClosedSurfaceR4.LocalPeriodicExpansion.Family.sum_apply _root_.OAI.ClosedSurfaceR4.LocalPeriodicExpansion.Family.vectorMean_apply _root_.OAI.ClosedSurfaceR4.LocalPeriodicExpansion.Family.zero_apply _root_.Path.extend_div_self
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

/-- Both slow and angular terms in the derivative of fast evaluation. -/
lemma fastValue_fderiv (U : Family A E) (ℓ : A →L[ℝ] ℝ) (z : ℝ) (p v : A) :
    fderiv ℝ (U.fastValue ℓ z) p v =
      (U.slow v).val p ((ℓ p / z : ℝ) : Period) +
        (ℓ v / z) • U.angle.val p ((ℓ p / z : ℝ) : Period) := by
  let T : A →L[ℝ] A × ℝ := (ContinuousLinearMap.id ℝ A).prod (z⁻¹ • ℓ)
  have hT (p : A) : T p = (p, ℓ p / z) := by
    simp [T, div_eq_mul_inv, mul_comm]
  have hEq : U.fastValue ℓ z =
      (fun w : A × ℝ => U.val w.1 (w.2 : Period)) ∘ T := by
    funext p
    simp only [Function.comp_apply, hT, fastValue]
  rw [hEq, fderiv_comp p (U.smooth.differentiable (by simp) (T p)) T.differentiableAt]
  simp only [ContinuousLinearMap.fderiv, ContinuousLinearMap.comp_apply, hT]
  change fderiv ℝ (fun w : A × ℝ => U.val w.1 (w.2 : Period)) (p, ℓ p / z) (v, ℓ v / z) = _
  have hv : (v, ℓ v / z) = (v, 0) + (ℓ v / z) • ((0 : A), (1 : ℝ)) := by
    simp
  rw [hv, map_add, map_smul]
  rfl

end Family
end ClosedSurfaceR4.PeriodicExpansion

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Geometry_CompactAnsatzAsymptotics
attribute [-instance] _root_.instMembershipProdContinuousLinearMapRealIdRelLoc _root_.instVAddIntReal_solutions
attribute [-simp] _root_.ContinuousLinearMap.comp_toSpanSingleton_apply _root_.OAI.ClosedSurfaceR4.CollarVelocity.loopX_apply _root_.OAI.ClosedSurfaceR4.CollarVelocity.loopX_zero _root_.OAI.ClosedSurfaceR4.CollarVelocity.loopY_apply _root_.OAI.ClosedSurfaceR4.CollarVelocity.loopY_zero _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.loss_covariance _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.order_covariance _root_.Path.extend_div_self
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Compact, fixed-coefficient asymptotics of the finite periodic ansatz. -/

noncomputable section
open Set
open scoped ContDiff BigOperators

namespace ClosedSurfaceR4.PeriodicExpansion
open CovarianceCorrector WeightedEstimates

variable {A E : Type} [NormedAddCommGroup A] [NormedSpace ℝ A]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E]

lemma phaseSum_smooth (U : ℕ → Family A E) (ℓ : A →L[ℝ] ℝ)
    (L : ℕ) (z : ℝ) : ContDiff ℝ ∞ (phaseSum U ℓ L z) :=
  ContDiff.sum fun i _ => contDiff_const.smul ((U i).fastValue_smooth ℓ z)

lemma phaseSum_fderiv (U : ℕ → Family A E) (ℓ : A →L[ℝ] ℝ)
    (L : ℕ) (z : ℝ) (p v : A) :
    fderiv ℝ (phaseSum U ℓ L z) p v =
      phaseSum (fun i => (U i).slow v) ℓ L z p +
        (ℓ v/z) • phaseSum (fun i => (U i).angle) ℓ L z p := by
  have hd (i : ℕ) := ((U i).fastValue_smooth ℓ z).differentiable (by simp) p
  change (fderiv ℝ (fun q : A => ∑ i ∈ Finset.range L,
    z^i • (U i).fastValue ℓ z q) p) v = _
  rw [fderiv_fun_sum (A := fun i (q : A) => z^i • (U i).fastValue ℓ z q)
    (u := Finset.range L) (fun i _ => (hd i).const_smul (z^i))]
  have hterm (i : ℕ) :
      fderiv ℝ (fun q : A => z^i • (U i).fastValue ℓ z q) p v =
        z^i • (((U i).slow v).fastValue ℓ z p+
          (ℓ v/z) • (U i).angle.fastValue ℓ z p) := by
    rw [fderiv_fun_const_smul (f := (U i).fastValue ℓ z) (hd i) (z^i),
      smul_apply,Family.fastValue_fderiv]
    simp only [Family.fastValue]
  simp only [sum_apply,hterm,smul_add,Finset.sum_add_distrib]
  congr 1
  rw [phaseSum,Finset.smul_sum]
  apply Finset.sum_congr rfl
  intro i hi
  change z^i • ((ℓ v/z) • (U i).angle.fastValue ℓ z p) =
    (ℓ v/z) • (z^i • (U i).angle.fastValue ℓ z p)
  exact smul_comm _ _ _

lemma finiteAnsatz_eq_phaseSum (F : A → E) (U : ℕ → Family A E)
    (ℓ : A →L[ℝ] ℝ) (L : ℕ) (z : ℝ) :
    finiteAnsatz F U ℓ L z = fun p => F p+z • phaseSum U ℓ L z p := by
  funext p
  simp only [finiteAnsatz,phaseSum,Finset.smul_sum,pow_succ,smul_smul]
  congr 1
  apply Finset.sum_congr rfl
  intro i hi
  rw [mul_comm]

lemma directionalMap_smooth {F : A → E} (hF : ContDiff ℝ ∞ F) (v : A) :
    ContDiff ℝ ∞ (directionalMap F v) :=
  (hF.fderiv_right (m := ∞) (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)).clm_apply contDiff_const

/-- The fast angular derivative cancels exactly one power of the scale. -/
lemma finiteAnsatz_directional {F : A → E} (hF : ContDiff ℝ ∞ F)
    (U : ℕ → Family A E) (ℓ : A →L[ℝ] ℝ) (L : ℕ)
    {z : ℝ} (hz : z ≠ 0) (v : A) :
    directionalMap (finiteAnsatz F U ℓ L z) v = fun p =>
      directionalMap F v p + z • phaseSum (fun i => (U i).slow v) ℓ L z p +
        ℓ v • phaseSum (fun i => (U i).angle) ℓ L z p := by
  funext p
  have hS := (phaseSum_smooth U ℓ L z).differentiable (by simp) p
  have hderiv : fderiv ℝ (fun q : A => F q+z • phaseSum U ℓ L z q) p =
      fderiv ℝ F p+z • fderiv ℝ (phaseSum U ℓ L z) p := by
    rw [fderiv_fun_add (f := F) (g := fun q : A => z • phaseSum U ℓ L z q)
      (hF.differentiable (by simp) p) (hS.const_smul z),
      fderiv_fun_const_smul (f := phaseSum U ℓ L z) hS z]
  rw [directionalMap,finiteAnsatz_eq_phaseSum,hderiv]
  simp only [add_apply,smul_apply,phaseSum_fderiv,smul_add,smul_smul]
  rw [show z*(ℓ v/z) = ℓ v by field_simp]
  simp only [directionalMap,add_assoc]

/-- Differentiation in a direction annihilated by the phase only differentiates
the slow coefficients. -/
lemma directional_phaseSum_transverse (U : ℕ → Family A E)
    (ℓ : A →L[ℝ] ℝ) (L : ℕ) (z : ℝ) {v : A} (hv : ℓ v = 0) :
    directionalMap (phaseSum U ℓ L z) v =
      phaseSum (fun i => (U i).slow v) ℓ L z := by
  funext p
  simp only [directionalMap,phaseSum_fderiv,hv,zero_div,zero_smul,add_zero]

private lemma directionalMap_add {F G : A → E}
    (hF : ContDiff ℝ ∞ F) (hG : ContDiff ℝ ∞ G) (v : A) :
    directionalMap (fun p => F p+G p) v =
      fun p => directionalMap F v p+directionalMap G v p := by
  funext p
  simp only [directionalMap,fderiv_fun_add
    (hF.differentiable (by simp) p) (hG.differentiable (by simp) p),add_apply]

private lemma directionalMap_smul {F : A → E}
    (hF : ContDiff ℝ ∞ F) (c : ℝ) (v : A) :
    directionalMap (fun p => c • F p) v =
      fun p => c • directionalMap F v p := by
  funext p
  simp only [directionalMap,fderiv_fun_const_smul
    (hF.differentiable (by simp) p),smul_apply]

private lemma directionalMap_three {F G H : A → E}
    (hF : ContDiff ℝ ∞ F) (hG : ContDiff ℝ ∞ G) (hH : ContDiff ℝ ∞ H)
    (c d : ℝ) (v : A) :
    directionalMap (fun p => F p+c • G p+d • H p) v =
      fun p => directionalMap F v p+c • directionalMap G v p+
        d • directionalMap H v p := by
  have hc : ContDiff ℝ ∞ (fun p : A => c • G p) := contDiff_const.smul hG
  have hd : ContDiff ℝ ∞ (fun p : A => d • H p) := contDiff_const.smul hH
  rw [directionalMap_add (F := fun p : A => F p+c • G p)
    (G := fun p : A => d • H p) (hF.add hc) hd,
    directionalMap_add (F := F) (G := fun p : A => c • G p) hF hc,
    directionalMap_smul hG c v,directionalMap_smul hH d v]

/-- Exact transverse and mixed second-derivative identities. -/
lemma finiteAnsatz_second_transverse {F : A → E} (hF : ContDiff ℝ ∞ F)
    (U : ℕ → Family A E) (ℓ : A →L[ℝ] ℝ) (L : ℕ)
    {z : ℝ} (hz : z ≠ 0) (v : A) {w : A} (hw : ℓ w = 0) :
    directionalMap (directionalMap (finiteAnsatz F U ℓ L z) v) w = fun p =>
      directionalMap (directionalMap F v) w p +
        z • phaseSum (fun i => ((U i).slow v).slow w) ℓ L z p +
        ℓ v • phaseSum (fun i => (U i).angle.slow w) ℓ L z p := by
  rw [finiteAnsatz_directional hF U ℓ L hz v,
    directionalMap_three (directionalMap_smooth hF v)
      (phaseSum_smooth (fun i => (U i).slow v) ℓ L z)
      (phaseSum_smooth (fun i => (U i).angle) ℓ L z) z (ℓ v) w,
    directional_phaseSum_transverse _ ℓ L z hw,
    directional_phaseSum_transverse _ ℓ L z hw]

lemma phaseSum_leading (U : ℕ → Family A E) (ℓ : A →L[ℝ] ℝ)
    (n : ℕ) (z : ℝ) (p : A) :
    phaseSum U ℓ (n+1) z p =
      (U 0).fastValue ℓ z p+z • phaseSum (fun i => U (i+1)) ℓ n z p := by
  rw [phaseSum,Finset.sum_range_succ']
  simp only [pow_zero,one_smul,phaseSum,Finset.smul_sum,pow_succ,smul_smul]
  rw [add_comm]
  congr 1
  apply Finset.sum_congr rfl
  intro i hi
  rw [mul_comm]

end ClosedSurfaceR4.PeriodicExpansion

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Primitive_LocalAnsatzProfiles
attribute [-instance] _root_.instVAddIntReal_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The leading jets of the supported local ansatz are the geometric profiles
of the initial periodic primitive. -/

noncomputable section
open Set Filter
open scoped ContDiff Topology

namespace ClosedSurfaceR4.LocalPeriodicExpansion
open CovarianceCorrector
open PeriodicExpansion (directionalMap)

variable {A E : Type} [NormedAddCommGroup A] [NormedSpace ℝ A]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  {O : TopologicalSpace.Opens A}

lemma globalCoefficients_finiteAnsatz (F : A → E) (U : ℕ → Family O E)
    (hU : ∀ i, ContDiff ℝ ∞ (fun y : A × ℝ => (U i).val y.1 (y.2 : Period)))
    (ℓ : A →L[ℝ] ℝ) (L : ℕ) (z : ℝ) :
    PeriodicExpansion.finiteAnsatz F (globalCoefficients U hU) ℓ L z =
      finiteAnsatz F U ℓ L z := rfl

end ClosedSurfaceR4.LocalPeriodicExpansion

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Primitive_PeriodicCoefficientProfiles
attribute [-instance] _root_.instMembershipProdContinuousLinearMapRealIdRelLoc _root_.instVAddIntReal_solutions
attribute [-simp] _root_.ContinuousLinearMap.comp_toSpanSingleton_apply _root_.Path.extend_div_self
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Explicit finite coefficient bounds for the varying-map version of the
periodic derivative estimates. -/
noncomputable section
open Set
open scoped ContDiff BigOperators
namespace ClosedSurfaceR4.PeriodicExpansion
open CovarianceCorrector
variable {A E : Type} [NormedAddCommGroup A] [NormedSpace ℝ A]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E]

lemma phaseSum_bound_of_coefficients (U : ℕ → Family A E)
    (ℓ : A →L[ℝ] ℝ) (L : ℕ) {z C : ℝ} {p : A}
    (hz : 0 ≤ z) (hz1 : z ≤ 1) (hC : 0 ≤ C)
    (hU : ∀ i < L, ‖(U i).fastValue ℓ z p‖ ≤ C) :
    ‖phaseSum U ℓ L z p‖ ≤ L*C := by
  apply (norm_sum_le _ _).trans
  calc
    ∑ i ∈ Finset.range L, ‖z^i • (U i).fastValue ℓ z p‖ ≤
        ∑ _i ∈ Finset.range L, C := by
      apply Finset.sum_le_sum
      intro i hi
      rw [norm_smul,Real.norm_eq_abs,abs_of_nonneg (pow_nonneg hz _)]
      exact (mul_le_mul_of_nonneg_left (hU i (Finset.mem_range.mp hi)) (pow_nonneg hz _)).trans
        (mul_le_of_le_one_left hC (pow_le_one₀ hz hz1))
    _ = L*C := by simp

lemma phaseSum_tail_bound_of_coefficients (U : ℕ → Family A E)
    (ℓ : A →L[ℝ] ℝ) (n : ℕ) {z C : ℝ} {p : A}
    (hz : 0 ≤ z) (hz1 : z ≤ 1) (hC : 0 ≤ C)
    (hU : ∀ i < n+1, ‖(U i).fastValue ℓ z p‖ ≤ C) :
    ‖phaseSum U ℓ (n+1) z p-(U 0).fastValue ℓ z p‖ ≤ (n*C)*z := by
  rw [phaseSum_leading,add_sub_cancel_left,norm_smul,Real.norm_eq_abs,abs_of_nonneg hz]
  have hh := phaseSum_bound_of_coefficients (fun i => U (i+1)) ℓ n hz hz1 hC
    (fun i hi => hU (i+1) (by omega))
  exact (mul_le_mul_of_nonneg_left hh hz).trans_eq (mul_comm _ _)

end ClosedSurfaceR4.PeriodicExpansion

namespace ClosedSurfaceR4.LocalPeriodicExpansion
open CovarianceCorrector
variable {A E : Type} [NormedAddCommGroup A] [NormedSpace ℝ A]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  {O : TopologicalSpace.Opens A}

lemma global_slow_eq_local_of_eqOn (W : PeriodicExpansion.Family A E) (U : Family O E)
    (hW : ∀ p ∈ O, ∀ t : Period, W.val p t = U.val p t)
    (v : A) {p : A} (hp : p ∈ O) (t : Period) :
    (W.slow v).val p t = (U.slow v).val p t := by
  refine Quotient.inductionOn' t ?_
  intro s
  rw [PeriodicExpansion.Family.slow_apply,Family.slow_apply U v hp]
  have he : (fun z : A × ℝ => W.val z.1 (z.2 : Period)) =ᶠ[nhds (p,s)]
      (fun z => U.val z.1 (z.2 : Period)) := by
    filter_upwards [(O.isOpen.prod isOpen_univ).mem_nhds ⟨hp,mem_univ s⟩] with z hz
    exact hW z.1 hz.1 (z.2 : Period)
  exact congrArg (fun L : (A × ℝ) →L[ℝ] E => L (v,0)) he.fderiv_eq

end ClosedSurfaceR4.LocalPeriodicExpansion

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Primitive_HigherLongitudinalProfiles
attribute [-instance] _root_.instVAddIntReal_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The two remaining leading second derivative profiles, with constants
depending only on the displayed finite coefficient bounds. -/
noncomputable section
open scoped ContDiff
namespace ClosedSurfaceR4.PeriodicExpansion
open CovarianceCorrector
variable {A E : Type} [NormedAddCommGroup A] [NormedSpace ℝ A]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E]

theorem mixed_profile_of_coefficients {F : A → E} (hF : ContDiff ℝ ∞ F)
    (U : ℕ → Family A E) (ℓ : A →L[ℝ] ℝ) (n : ℕ) {dx dy : A}
    (hx : ℓ dx = 1) (hy : ℓ dy = 0) {z C : ℝ} {p : A}
    (hz : 0 < z) (hz1 : z ≤ 1) (hC : 0 ≤ C)
    (hU : ∀ i < n+1, ‖(((U i).slow dx).slow dy).fastValue ℓ z p‖ ≤ C)
    (hA : ∀ i < n+1, ‖((U i).angle.slow dy).fastValue ℓ z p‖ ≤ C) :
    ‖directionalMap (directionalMap (finiteAnsatz F U ℓ (n+1) z) dx) dy p-
      (directionalMap (directionalMap F dx) dy p+((U 0).angle.slow dy).fastValue ℓ z p)‖ ≤
        (2*(n+1)*C)*z := by
  have he : directionalMap (directionalMap (finiteAnsatz F U ℓ (n+1) z) dx) dy p-
      (directionalMap (directionalMap F dx) dy p+((U 0).angle.slow dy).fastValue ℓ z p) =
      z • phaseSum (fun i => ((U i).slow dx).slow dy) ℓ (n+1) z p+
        (phaseSum (fun i => (U i).angle.slow dy) ℓ (n+1) z p-
          ((U 0).angle.slow dy).fastValue ℓ z p) := by
    rw [finiteAnsatz_second_transverse hF U ℓ (n+1) hz.ne' dx hy]
    simp only [hx,one_smul]
    abel
  rw [he]
  have hs := phaseSum_bound_of_coefficients (fun i => ((U i).slow dx).slow dy)
    ℓ (n+1) hz.le hz1 hC hU
  have ha := phaseSum_tail_bound_of_coefficients (fun i => (U i).angle.slow dy)
    ℓ n hz.le hz1 hC hA
  calc
    _ ≤ ‖z • phaseSum (fun i => ((U i).slow dx).slow dy) ℓ (n+1) z p‖+
        ‖phaseSum (fun i => (U i).angle.slow dy) ℓ (n+1) z p-
          ((U 0).angle.slow dy).fastValue ℓ z p‖ := norm_add_le _ _
    _ ≤ z*((n+1 : ℕ)*C)+(n*C)*z := by
      rw [norm_smul,Real.norm_eq_abs,abs_of_pos hz]
      exact add_le_add (mul_le_mul_of_nonneg_left hs hz.le) ha
    _ ≤ (2*(n+1)*C)*z := by
      push_cast
      nlinarith [mul_nonneg hC hz.le]

end ClosedSurfaceR4.PeriodicExpansion

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Primitive_SecondCoefficientProfiles
attribute [-instance] _root_.instMembershipProdContinuousLinearMapRealIdRelLoc _root_.instVAddIntReal_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Second coefficient derivatives agree with the local represented jets,
even when only their germs agree after the first derivative. -/
noncomputable section
open Set
open scoped ContDiff Matrix
namespace ClosedSurfaceR4.LocalPeriodicExpansion
open CovarianceCorrector JetPolynomial

lemma global_angle_eq_local_of_eqOn {A E : Type} [NormedAddCommGroup A] [NormedSpace ℝ A]
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] {O : TopologicalSpace.Opens A}
    (W : PeriodicExpansion.Family A E) (U : Family O E)
    (hW : ∀ p ∈ O, ∀ t : Period, W.val p t = U.val p t)
    {p : A} (hp : p ∈ O) (t : Period) : W.angle.val p t = U.angle.val p t := by
  refine Quotient.inductionOn' t ?_
  intro s
  rw [PeriodicExpansion.Family.angle_apply,Family.angle_apply U hp]
  have he : (fun z : A × ℝ => W.val z.1 (z.2 : Period)) =ᶠ[nhds (p,s)]
      (fun z => U.val z.1 (z.2 : Period)) := by
    filter_upwards [(O.isOpen.prod isOpen_univ).mem_nhds ⟨hp,mem_univ s⟩] with z hz
    exact hW z.1 hz.1 (z.2 : Period)
  exact congrArg (fun L : (A × ℝ) →L[ℝ] E => L (0,1)) he.fderiv_eq

lemma global_coefficientDerivative_eq_local {S : TopologicalSpace.Opens Base}
    (W : PeriodicExpansion.Family Base JetVelocityCoordinates.Euclidean)
    (U : Family S JetVelocityCoordinates.Euclidean)
    (hW : ∀ p ∈ S, ∀ t : Period, W.val p t = U.val p t)
    (k : Fin 3) {p : Base} (hp : p ∈ S) (t : Period) :
    (globalCoefficientDerivative W k).val p t =
      (VectorExpression.coefficientFamilyDerivative U k).val p t := by
  fin_cases k
  · exact global_slow_eq_local_of_eqOn W U hW _ hp t
  · exact global_slow_eq_local_of_eqOn W U hW _ hp t
  · exact global_angle_eq_local_of_eqOn W U hW hp t

lemma global_second_coefficientDerivative_eq_local {S : TopologicalSpace.Opens Base}
    (W : PeriodicExpansion.Family Base JetVelocityCoordinates.Euclidean)
    (U : Family S JetVelocityCoordinates.Euclidean) (hW : W.val = U.val)
    (k j : Fin 3) {p : Base} (hp : p ∈ S) (t : Period) :
    (globalCoefficientDerivative (globalCoefficientDerivative W k) j).val p t =
      (VectorExpression.coefficientFamilyDerivative
        (VectorExpression.coefficientFamilyDerivative U k) j).val p t := by
  apply global_coefficientDerivative_eq_local _ _ _ j hp t
  intro q hq r
  exact global_coefficientDerivative_eq_local W U (by intro q _ t; rw [hW]) k hq r

end ClosedSurfaceR4.LocalPeriodicExpansion

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Primitive_UniformMixedProfile
attribute [-instance] _root_.instMembershipProdContinuousLinearMapRealIdRelLoc _root_.instVAddIntReal_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The mixed derivative estimate is uniform for the actual varying slow
maps and the same finite represented coefficients. -/
noncomputable section
open Set
open scoped ContDiff
namespace ClosedSurfaceR4.SurfaceVelocityFamily.Loop
open JetPolynomial JetVelocityCoordinates LocalPeriodicExpansion CovarianceCorrector WeightedEstimates
variable {O : TopologicalSpace.Opens LowJet} (l : SurfaceVelocityFamily.Loop O)

theorem uniform_mixed_profile_oai {S : TopologicalSpace.Opens JetPolynomial.Base}
    {Q : Set LowJet} (hQ : IsCompact Q) (hQO : Q ⊆ O)
    (n : ℕ) (ℓ : JetPolynomial.Base →L[ℝ] ℝ)
    (hx : ℓ (coordinateVector 0) = 1) (hy : ℓ (coordinateVector 1) = 0) :
    ∃ loss : ℕ, ∀ B : ℝ, 1 ≤ B → ∃ D : ℝ, 0 ≤ D ∧
      ∀ (G : JetPolynomial.Base → JetPolynomial.Space) (_hG : ContDiff ℝ ∞ G),
      MapsTo (lowJet G) S Q → ∀ (s z : ℝ), 0 < z → z ≤ s → s ≤ 1 →
      WeightedBound S s ((2*n+2)+2) B (lowJet G) →
      ∀ U : ℕ → Family S Euclidean,
        (∀ i, ContDiff ℝ ∞ (fun y : JetPolynomial.Base × ℝ => (U i).val y.1 (y.2 : Period))) →
        (∀ i, VectorExpression.Represents G (l.coefficientExpressions n i) (U i)) →
      ∀ p ∈ S,
        let F := fun q => JetVelocityCoordinates.toEuclidean (G q)
        let f := finiteAnsatz F U ℓ (n+1) z
        ‖PeriodicExpansion.directionalMap (PeriodicExpansion.directionalMap f (coordinateVector 0))
            (coordinateVector 1) p-
          (PeriodicExpansion.directionalMap (PeriodicExpansion.directionalMap F (coordinateVector 0))
            (coordinateVector 1) p+((U 0).angle.slow (coordinateVector 1)).fastValue ℓ z p)‖ ≤
          D*z/s^loss := by
  obtain ⟨loss,hb⟩ := VectorExpression.compact_coefficient_two_jets (S := S) O.isOpen hQ hQO
    (l.coefficientExpressions n) (n+1) (2*n+2) (by omega)
    (fun i _ => l.coefficientExpressions_smooth n i)
    (fun i hi a => (MetricPolynomial.coefficients_order _ _ _ _ _ 0 1 n i a).trans (by omega)) ℓ
  refine ⟨loss,?_⟩
  intro B hB
  obtain ⟨D,hD,hd⟩ := hb B hB
  refine ⟨2*(n+1)*D,mul_nonneg (by positivity) hD,?_⟩
  intro G hG hGQ s z hz hzs hs1 hGb U hU hrep p hp
  let W := globalCoefficients U hU
  have hc := hd G s z hz hzs hs1 hG hGQ hGb U (fun i _ => hrep i)
  have hC : 0 ≤ D/s^loss := div_nonneg hD (pow_nonneg (hz.le.trans hzs) _)
  have hss (i : ℕ) (hi : i < n+1) :
      ‖(((W i).slow (coordinateVector 0)).slow (coordinateVector 1)).fastValue ℓ z p‖ ≤ D/s^loss := by
    change ‖(globalCoefficientDerivative (globalCoefficientDerivative (W i) 0) 1).val p
      ((ℓ p/z : ℝ) : Period)‖ ≤ _
    rw [global_second_coefficientDerivative_eq_local (W i) (U i) rfl 0 1 hp]
    exact (hc i hi 0 1 p hp).2
  have has (i : ℕ) (hi : i < n+1) :
      ‖((W i).angle.slow (coordinateVector 1)).fastValue ℓ z p‖ ≤ D/s^loss := by
    change ‖(globalCoefficientDerivative (globalCoefficientDerivative (W i) 2) 1).val p
      ((ℓ p/z : ℝ) : Period)‖ ≤ _
    rw [global_second_coefficientDerivative_eq_local (W i) (U i) rfl 2 1 hp]
    exact (hc i hi 2 1 p hp).2
  have hout := PeriodicExpansion.mixed_profile_of_coefficients
    (JetVelocityCoordinates.toEuclidean.contDiff.comp hG) W ℓ n hx hy hz (hzs.trans hs1) hC hss has
  have he : (2*((n : ℝ)+1))*(D/s^loss)*z = (2*((n : ℝ)+1))*D*z/s^loss := by ring
  rw [he] at hout
  have hlead : ((W 0).angle.slow (coordinateVector 1)).fastValue ℓ z p =
      ((U 0).angle.slow (coordinateVector 1)).fastValue ℓ z p :=
    global_second_coefficientDerivative_eq_local (W 0) (U 0) rfl 2 1 hp _
  rw [hlead] at hout
  simpa only [W,globalCoefficients_finiteAnsatz,Function.comp_def,
    Nat.cast_add,Nat.cast_one,Nat.cast_mul,Nat.cast_ofNat] using hout

end ClosedSurfaceR4.SurfaceVelocityFamily.Loop

end

end OAI
end

theorem solution : type_of% @OAI.ClosedSurfaceR4.SurfaceVelocityFamily.Loop.uniform_mixed_profile_oai := @OAI.ClosedSurfaceR4.SurfaceVelocityFamily.Loop.uniform_mixed_profile_oai
