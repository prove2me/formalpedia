-- Prove2me | solution 1 for OAI.ClosedSurfaceR4.JetPolynomial.exists_bounded_coefficients
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-12T12:49:48.782632+00:00
-- url     : https://prove2.me/submissions/cec39ca3-1f77-42de-9524-d69a7c7b54c3

import Mathlib
import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
import Definitions.Def_OAIQ249SI012
import Theorems.Thm_OAI_ClosedSurfaceR4_JetPolynomial_Expression_fullComponent_bounds
import Theorems.Thm_OAI_ClosedSurfaceR4_JetPolynomial_MetricPolynomial_coefficients_smooth
import Theorems.Thm_OAI_ClosedSurfaceR4_JetPolynomial_VectorExpression_compact_fast_bound
import Theorems.Thm_OAI_ClosedSurfaceR4_JetPolynomial_exists_polynomial_coefficients

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



lemma WeightedBound.mono_order {U : Set E} {s C : ℝ} {m r : ℕ} {f : E → F}
    (h : WeightedBound U s m C f) (hr : r ≤ m) : WeightedBound U s r C f :=
  fun j hj => h j (hj.trans hr)


lemma WeightedBound.const_smul {U : Set E} (hU : UniqueDiffOn ℝ U) {s C : ℝ}
    {m : ℕ} {f : E → F} (hf : ContDiffOn ℝ ∞ f U) (hb : WeightedBound U s m C f) (a : ℝ) :
    WeightedBound U s m (|a| * C) (fun x => a • f x) := by
  intro j hj x hx
  change s ^ j * ‖iteratedFDerivWithin ℝ j (a • f) U x‖ ≤ _
  rw [iteratedFDerivWithin_const_smul_apply
    ((hf.of_le (m := (j : ℕ∞ω)) (by exact_mod_cast (le_top : (j : ℕ∞) ≤ ⊤))).contDiffWithinAt hx)
    hU hx, norm_smul, Real.norm_eq_abs]
  calc
    _ = |a| * (s ^ j * ‖iteratedFDerivWithin ℝ j f U x‖) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left (hb j hj x hx) (abs_nonneg _)

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

lemma fastValue_smooth (U : Family O E) (ℓ : A →L[ℝ] ℝ) (z : ℝ) :
    ContDiffOn ℝ ∞ (U.fastValue ℓ z) O :=
  U.smooth.comp (contDiffOn_id.prodMk (ℓ.contDiff.div_const z).contDiffOn)
    (fun _ hp => ⟨hp, Set.mem_univ _⟩)

end ClosedSurfaceR4.LocalPeriodicExpansion.Family

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Geometry_FiniteFastBounds
attribute [-instance] _root_.instMembershipProdContinuousLinearMapRealIdRelLoc _root_.instVAddIntReal_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Uniform fast-scale estimates for finite collections of the actual
periodic correctors, and for their finite oscillatory sum. -/
noncomputable section
open scoped ContDiff BigOperators

namespace ClosedSurfaceR4.JetPolynomial.VectorExpression
open LocalPeriodicExpansion WeightedEstimates

/-- Finitely many coefficients admit one common prefactor and one common
scale loss, also in the Euclidean norm on the target. -/
theorem compact_finite_fast_bound {ι : Type*} [Fintype ι]
    {S : TopologicalSpace.Opens Base} {O K : Set LowJet}
    (hO : IsOpen O) (hK : IsCompact K) (hKO : K ⊆ O)
    (R : ι → VectorExpression) (hRs : ∀ a, (R a).SmoothCoeffs O)
    (N d : ℕ) (hN : ∀ a i, (R a i).order ≤ N) (hd : ∀ a i, (R a i).loss ≤ d)
    (ℓ : Base →L[ℝ] ℝ) (m : ℕ) (B : ℝ) (hB : 1 ≤ B) :
    ∃ D : ℝ, 0 ≤ D ∧ ∀ (G : Base → Space) (s z : ℝ),
      0 < z → z ≤ s → s ≤ 1 → ContDiff ℝ ∞ G →
      Set.MapsTo (lowJet G) S K → WeightedBound S s (m + N) B (lowJet G) →
      ∀ (U : ι → Family S R4), (∀ a, Represents G (R a) (U a)) → ∀ a,
        WeightedBound S z m (D / s ^ d) ((U a).fastValue ℓ z) := by
  classical
  have hex := fun a : ι × Fin 4 => compact_fast_bound (S := S) hO hK hKO (R a.1) (hRs a.1) a.2 ℓ m B hB
  choose C hC hc using hex
  let C₀ : ℝ := ∑ a : ι × Fin 4, C a
  let L : (Fin 4 → ℝ) →L[ℝ] R4 := (EuclideanSpace.equiv (Fin 4) ℝ).symm.toContinuousLinearMap
  refine ⟨‖L‖ * C₀, mul_nonneg (norm_nonneg _) (Finset.sum_nonneg fun a _ => hC a), ?_⟩
  intro G s z hz hzs hs1 hG hGK hb U hrep a
  have hs : 0 < s := hz.trans_le hzs
  have hcoord (i : Fin 4) :
      WeightedBound S z m (C₀ / s ^ d) (fun p => (U a).fastValue ℓ z p i) := by
    have hi := hc (a, i) G s z hz hzs hs1 hG hGK
      (hb.mono_order (Nat.add_le_add_left (hN a i) m)) (U a) (hrep a)
    apply hi.mono_const
    calc
      C (a, i) / s ^ (R a i).loss ≤ C (a, i) / s ^ d :=
        div_le_div_of_nonneg_left (hC _) (pow_pos hs _)
          (pow_le_pow_of_le_one hs.le hs1 (hd a i))
      _ ≤ C₀ / s ^ d := div_le_div_of_nonneg_right
        (Finset.single_le_sum (fun b _ => hC b) (Finset.mem_univ (a, i))) (pow_nonneg hs.le _)
  have hsmooth (i : Fin 4) : ContDiffOn ℝ ∞ (fun p => (U a).fastValue ℓ z p i) S :=
    (show R4 →L[ℝ] ℝ from EuclideanSpace.proj i).contDiff.comp_contDiffOn ((U a).fastValue_smooth ℓ z)
  have hp := WeightedBound.pi S.isOpen.uniqueDiffOn hz
    (div_nonneg (Finset.sum_nonneg fun b _ => hC b) (pow_nonneg hs.le _)) hsmooth hcoord
  have hp' := hp.linear S.isOpen.uniqueDiffOn hz.le (contDiffOn_pi.mpr hsmooth) L
  have heq : (L ∘ fun p i => (U a).fastValue ℓ z p i) = (U a).fastValue ℓ z := by
    funext p
    exact (EuclideanSpace.equiv (Fin 4) ℝ).symm_apply_apply _
  rw [heq] at hp'
  convert hp' using 1
  all_goals try with_reducible_and_instances rfl
  ring

/-- The finite ansatz differs from the slow map by `O_z(z s⁻ᵈ)`.
The exponent `d` is supplied by the finite jet expressions and is independent
of `m`; there is no assumption on an unconstructed correction. -/
theorem compact_finite_ansatz_bound {S : TopologicalSpace.Opens Base} {O K : Set LowJet}
    (hO : IsOpen O) (hK : IsCompact K) (hKO : K ⊆ O)
    (R : ℕ → VectorExpression) (L N d : ℕ)
    (hRs : ∀ i < L, (R i).SmoothCoeffs O)
    (hN : ∀ i < L, ∀ a, (R i a).order ≤ N)
    (hd : ∀ i < L, ∀ a, (R i a).loss ≤ d)
    (ℓ : Base →L[ℝ] ℝ) (m : ℕ) (B : ℝ) (hB : 1 ≤ B) :
    ∃ D : ℝ, 0 ≤ D ∧ ∀ (G : Base → Space) (s z : ℝ),
      0 < z → z ≤ s → s ≤ 1 → ContDiff ℝ ∞ G →
      Set.MapsTo (lowJet G) S K → WeightedBound S s (m + N) B (lowJet G) →
      ∀ (F : Base → R4) (U : ℕ → Family S R4),
        (∀ i < L, Represents G (R i) (U i)) →
        WeightedBound S z m (D * z / s ^ d)
          (fun p => finiteAnsatz F U ℓ L z p - F p) := by
  obtain ⟨C, hC, hc⟩ := compact_finite_fast_bound hO hK hKO
    (fun i : Fin L => R i) (fun i => hRs i i.isLt) N d
    (fun i => hN i i.isLt) (fun i => hd i i.isLt) ℓ m B hB
  refine ⟨L * C, mul_nonneg (Nat.cast_nonneg _) hC, ?_⟩
  intro G s z hz hzs hs1 hG hGK hb F U hrep
  have hs : 0 < s := hz.trans_le hzs
  have hz1 : z ≤ 1 := hzs.trans hs1
  have hbU : ∀ i < L, WeightedBound S z m (C / s ^ d) ((U i).fastValue ℓ z) := by
    intro i hi
    exact hc G s z hz hzs hs1 hG hGK hb (fun j : Fin L => U j)
      (fun j => hrep j j.isLt) ⟨i, hi⟩
  have hterm (i : ℕ) (hi : i ∈ Finset.range L) :
      WeightedBound S z m (z * (C / s ^ d))
        (fun p => z ^ (i + 1) • (U i).fastValue ℓ z p) := by
    have hh := (hbU i (Finset.mem_range.mp hi)).const_smul S.isOpen.uniqueDiffOn
      ((U i).fastValue_smooth ℓ z) (z ^ (i + 1))
    apply hh.mono_const
    rw [abs_of_nonneg (pow_nonneg hz.le _)]
    apply mul_le_mul_of_nonneg_right _ (div_nonneg hC (pow_nonneg hs.le _))
    simpa only [pow_one] using pow_le_pow_of_le_one hz.le hz1 (by omega : 1 ≤ i + 1)
  have hh := WeightedBound.finset_sum S.isOpen.uniqueDiffOn hz.le (Finset.range L)
    (fun _ => z * (C / s ^ d))
    (fun i p => z ^ (i + 1) • (U i).fastValue ℓ z p)
    (fun i _ => (contDiffOn_const (c := z ^ (i + 1))).smul ((U i).fastValue_smooth ℓ z)) hterm
  have heq : (fun p => finiteAnsatz F U ℓ L z p - F p) =
      (fun p => ∑ i ∈ Finset.range L, z ^ (i + 1) • (U i).fastValue ℓ z p) := by
    funext p
    simp only [finiteAnsatz, add_sub_cancel_left]
  rw [heq]
  convert hh using 1
  all_goals try with_reducible_and_instances rfl
  simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  ring

end ClosedSurfaceR4.JetPolynomial.VectorExpression

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Geometry_BoundedCoefficientRecursion
attribute [-instance] _root_.instMembershipProdContinuousLinearMapRealIdRelLoc _root_.instVAddIntReal_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The actual supported metric-cancelling recursion with uniform fast-scale
estimates. All losses are determined by the finite symbolic recursion before
the slow map or its scales are chosen. -/
noncomputable section
open scoped ContDiff

namespace ClosedSurfaceR4.JetPolynomial
open LocalPeriodicExpansion CovarianceCorrector WeightedEstimates

namespace VectorExpression

lemma loss_le_finiteLoss (R : ℕ → VectorExpression) {i L : ℕ} (hi : i < L) (a : Fin 4) :
    (R i a).loss ≤ finiteLoss R L :=
  (Finset.le_sup (f := fun a => (R i a).loss) (Finset.mem_univ a)).trans
    (Finset.le_sup (f := fun i => Finset.univ.sup (fun a => (R i a).loss)) (Finset.mem_range.mpr hi))

end VectorExpression

/-- The support and cancellation identities belong to the very same finite
family whose oscillatory ansatz satisfies the quantitative estimate. -/
theorem exists_bounded_coefficients_oai {S : TopologicalSpace.Opens Base} {O K : Set LowJet}
    (hO : IsOpen O) (hK : IsCompact K) (hKO : K ⊆ O)
    (dx dy : Fin 2) (n : ℕ) (ℓ : Base →L[ℝ] ℝ)
    {Y C X₀ : LowJet → R4} {V : LowJet → C(Period, R4)} {q : LowJet → ℝ}
    (hY : ContDiffOn ℝ ∞ Y O) (hC : ContDiffOn ℝ ∞ C O) (hX : ContDiffOn ℝ ∞ X₀ O)
    (hV : ContDiffOn ℝ ∞ (fun z : LowJet × ℝ => V z.1 (z.2 : Period)) (O ×ˢ Set.univ))
    (hdet : ∀ Q ∈ O, PeriodicCorrector.gramDet (Y Q) (C Q) ≠ 0)
    (hq : ContDiffOn ℝ ∞ q O) (hqp : ∀ Q ∈ O, 0 < q Q)
    (hcircle : ∀ Q ∈ O, ∀ t, inner ℝ (V Q t) (V Q t) = q Q) :
    ∃ d : ℕ, ∀ (m : ℕ) (B : ℝ), 1 ≤ B → ∃ D : ℝ, 0 ≤ D ∧
      ∀ (G : Base → Space) (g : Geometry (E := R4) S (coordinateVector dy)),
      ContDiff ℝ ∞ G → Set.MapsTo (lowJet G) S K →
      (∀ p ∈ S, g.Y p = Y (lowJet G p)) →
      (∀ p ∈ S, g.C p = C (lowJet G p)) →
      (∀ p ∈ S, g.X₀ p = X₀ (lowJet G p)) →
      (∀ p ∈ S, g.V.val p = V (lowJet G p)) →
      (∀ p ∈ S, g.q p = q (lowJet G p)) →
      ∃ U : ℕ → Family S R4,
        U 0 = g.initial ∧ (∀ i p, p ∈ S → average ((U i).val p) = 0) ∧
        (g.yyCoefficient U 1).fluct = 0 ∧
        (∀ Z : Set Base, IsOpen Z → Z ⊆ S → (∀ p ∈ Z, g.initial.val p = 0) →
          ∀ i p, p ∈ Z → (U i).val p = 0) ∧
        (∀ r, 1 ≤ r → r ≤ n →
          (g.xxCoefficient (coordinateVector dx) U r).fluct = 0 ∧
          (g.xyCoefficient (coordinateVector dx) U r).fluct = 0 ∧
          (g.yyCoefficient U (r + 1)).fluct = 0) ∧
        (∀ i, VectorExpression.Represents G
          (MetricPolynomial.coefficients Y C X₀ V q dx dy n i) (U i)) ∧
        ∀ (s z : ℝ), 0 < z → z ≤ s → s ≤ 1 →
          WeightedBound S s (m + (2 * n + 2)) B (lowJet G) → ∀ F : Base → R4,
          WeightedBound S z m (D * z / s ^ d)
            (fun p => finiteAnsatz F U ℓ (n + 1) z p - F p) := by
  let R := MetricPolynomial.coefficients Y C X₀ V q dx dy n
  let d := VectorExpression.finiteLoss R (n + 1)
  have hRs : ∀ i, (R i).SmoothCoeffs O :=
    MetricPolynomial.coefficients_smooth hO hY hC hX hV hdet hq hqp hcircle dx dy n
  refine ⟨d, ?_⟩
  intro m B hB
  obtain ⟨D, hD, hbound⟩ := VectorExpression.compact_finite_ansatz_bound (S := S)
    hO hK hKO R (n + 1) (2 * n + 2) d (fun i _ => hRs i)
    (fun i hi a => (MetricPolynomial.coefficients_order Y C X₀ V q dx dy n i a).trans (by omega))
    (fun i hi a => VectorExpression.loss_le_finiteLoss R hi a) ℓ m B hB
  refine ⟨D, hD, ?_⟩
  intro G g hG hGK hYg hCg hXg hVg hqg
  have hQ : Set.MapsTo (lowJet G) S O := fun _ hp => hKO (hGK hp)
  obtain ⟨U, hinit, hmean, hy, hsupport, hcancel, hrep⟩ :=
    exists_polynomial_coefficients hO dy g hY hC hX hV hdet hq hqp hcircle
      hG hQ hYg hCg hXg hVg hqg dx n
  refine ⟨U, hinit, hmean, hy, hsupport, hcancel, hrep, ?_⟩
  intro s z hz hzs hs1 hb F
  exact hbound G s z hz hzs hs1 hG hGK hb F U (fun i _ => hrep i)

end ClosedSurfaceR4.JetPolynomial

end

end OAI
end

theorem solution : type_of% @OAI.ClosedSurfaceR4.JetPolynomial.exists_bounded_coefficients_oai := @OAI.ClosedSurfaceR4.JetPolynomial.exists_bounded_coefficients_oai
