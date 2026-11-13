-- Prove2me | solution 1 for OAI.ClosedSurfaceR4.SurfaceVelocityFamily.Loop.uniform_transverse_profiles
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-12T12:51:52.037921+00:00
-- url     : https://prove2.me/submissions/4a704ae3-43a2-47ff-977a-829f698e8f94

import Mathlib
import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
import Mathlib.Geometry.Manifold.PartitionOfUnity
import Definitions.Def_OAIQ249SI012
import Theorems.Thm_OAI_ClosedSurfaceR4_JetPolynomial_Expression_fullComponent_bounds
import Theorems.Thm_OAI_ClosedSurfaceR4_JetPolynomial_MetricPolynomial_coefficients_smooth
import Theorems.Thm_OAI_ClosedSurfaceR4_JetPolynomial_VectorExpression_compact_fast_bound

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

end ClosedSurfaceR4.WeightedEstimates

end

end OAI
end

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
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Geometry_LowJetChainRule
attribute [-instance] _root_.instVAddIntReal_solutions
attribute [-simp] _root_.ContinuousLinearMap.comp_toSpanSingleton_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.circularPhaseBoundaryCurve_carrier _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.directionJetLinearization_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.eval_neg _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.eval_sub _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.loss_covariance _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.loss_liftOperator _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.loss_mapCoeff _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.order_covariance _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.order_liftOperator _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.order_mapCoeff _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_C _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_J _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_e _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_lowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_variationLowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowPosition_lowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.spatialAmplitude_lowJet _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_apply _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_one _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_zero _root_.OAI.ClosedSurfaceR4.SurfaceVelocityFamily.Loop.withSpatialAmplitude_amplitude _root_.Path.extend_div_self
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The chain rule for coefficients depending on position and the actual
second jet of a map from a surface chart into four-space. -/
noncomputable section
open scoped ContDiff BigOperators

namespace ClosedSurfaceR4.JetPolynomial
open WeightedEstimates

lemma jet_cons (G : Base → Space) (v : Fin 2) (w : List (Fin 2)) (a : Fin 4) (p : Base) :
    jet G (v :: w) a p = fderiv ℝ (jet G w a) p (coordinateVector v) := rfl

lemma lowJet_derivative {G : Base → Space} (hG : ContDiff ℝ ∞ G) (v : Fin 2) (p : Base) :
    fderiv ℝ (lowJet G) p (coordinateVector v) = lowDerivative G v p := by
  ext i
  have h := congrArg (fun L : Base →L[ℝ] ℝ => L (coordinateVector v))
    (fderiv_apply ((lowJet_smooth hG).differentiable (by simp) p) i)
  simpa only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.proj_apply,
    lowJet_coordinate_derivative] using h.symm

lemma lowBasis_expansion (J : LowJet) : J = ∑ i : LowIndex, J i • lowBasis i := by
  ext i
  simp [lowBasis, Pi.single_apply]

/-- Differentiating a low-jet coefficient introduces only the next coordinate
jet, linearly, with new smooth low-jet coefficients. -/
theorem coefficient_chain_rule {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {G : Base → Space} (hG : ContDiff ℝ ∞ G) {c : LowJet → E}
    (v : Fin 2) (p : Base) (hc : DifferentiableAt ℝ c (lowJet G p)) :
    fderiv ℝ (fun q => c (lowJet G q)) p (coordinateVector v) =
      ∑ i : LowIndex, (lowDerivative G v p i) • fderiv ℝ c (lowJet G p) (lowBasis i) := by
  have hQ := (lowJet_smooth hG).differentiable (by simp) p
  change fderiv ℝ (c ∘ lowJet G) p (coordinateVector v) = _
  rw [fderiv_comp p hc hQ, ContinuousLinearMap.comp_apply, lowJet_derivative hG]
  conv_lhs => rw [lowBasis_expansion (lowDerivative G v p), map_sum]
  simp only [map_smul]

end ClosedSurfaceR4.JetPolynomial

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

lemma eval_mapCoeff_mul (e : Expression) (G : Base → Space) (c : LowJet × ℝ → ℝ)
    (z : Base × ℝ) :
    (e.mapCoeff (fun d x => c x * d x)).eval G z = c (lowJet G z.1, z.2) * e.eval G z := by
  induction e with
  | coeff d => rfl
  | atom w a e ih => simp only [mapCoeff, eval, ih] <;> ring
  | add e f ihe ihf => simp only [mapCoeff, eval, ihe, ihf] <;> ring

lemma eval_mul (e f : Expression) (G : Base → Space) (z : Base × ℝ) :
    (e.mul f).eval G z = e.eval G z * f.eval G z := by
  induction e with
  | coeff c => exact eval_mapCoeff_mul f G c z
  | atom w a e ih => simp only [mul, eval, ih] <;> ring
  | add e g ihe ihg => simp only [mul, eval, ihe, ihg] <;> ring

lemma order_mul_le (e f : Expression) : (e.mul f).order ≤ max e.order f.order := by
  induction e with
  | coeff c => simp only [mul, order_mapCoeff, order]; exact le_max_right _ _
  | atom w a e ih => simp only [mul, order] at *; omega
  | add e g ihe ihg => simp only [mul, order] at *; omega

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
attribute [-simp] _root_.ContinuousLinearMap.comp_toSpanSingleton_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.circularPhaseBoundaryCurve_carrier _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.directionJetLinearization_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.eval_neg _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.eval_sub _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.loss_angle _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.loss_covariance _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.loss_fluct _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.loss_liftOperator _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.loss_mean _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.loss_neg _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.loss_primitive _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.loss_scale _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.loss_sub _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.order_angle _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.order_covariance _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.order_fluct _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.order_liftOperator _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.order_mean _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.order_neg _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.order_primitive _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.order_scale _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.order_sub _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_C _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_J _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_e _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_lowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_variationLowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowPosition_lowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.spatialAmplitude_lowJet _root_.OAI.ClosedSurfaceR4.PeriodicExpansion.Family.slow_apply _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_apply _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_one _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_zero _root_.OAI.ClosedSurfaceR4.SurfaceVelocityFamily.Loop.withSpatialAmplitude_amplitude _root_.Path.extend_div_self
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

lemma eval_sumList {ι : Type*} (l : List ι) (f : ι → Expression) (G : Base → Space)
    (z : Base × ℝ) : (sumList l f).eval G z = (l.map (fun i => (f i).eval G z)).sum := by
  induction l with
  | nil => rfl
  | cons i l ih => simp only [sumList, eval, List.map_cons, List.sum_cons, ih]

lemma order_sumList_le {ι : Type*} (l : List ι) (f : ι → Expression) (N : ℕ)
    (hN : 2 ≤ N) (hf : ∀ i ∈ l, (f i).order ≤ N) : (sumList l f).order ≤ N := by
  induction l with
  | nil => exact hN
  | cons i l ih =>
    exact max_le (hf i (List.mem_cons_self ..))
      (ih (fun j hj => hf j (List.mem_cons_of_mem _ hj)))

lemma smoothCoeffs_sumList {ι : Type*} {O : Set LowJet} (l : List ι) (f : ι → Expression)
    (hf : ∀ i ∈ l, (f i).SmoothCoeffs O) : (sumList l f).SmoothCoeffs O := by
  induction l with
  | nil => exact contDiffOn_const
  | cons i l ih => exact ⟨hf i (List.mem_cons_self ..),
      ih (fun j hj => hf j (List.mem_cons_of_mem _ hj))⟩

lemma eval_lowFactor (v : Fin 2) (i : LowIndex) (G : Base → Space) (z : Base × ℝ) :
    (lowFactor v i).eval G z = lowDerivative G v z.1 i := by
  cases i with
  | inl i => rfl
  | inr i => simp [lowFactor, eval, lowDerivative]

lemma order_lowFactor (v : Fin 2) (i : LowIndex) : (lowFactor v i).order ≤ 3 := by
  cases i with
  | inl i => simp [lowFactor, order]
  | inr i =>
    obtain ⟨w, a⟩ := i
    have h : (lowWord w).length ≤ 2 := by fin_cases w <;> simp [lowWord]
    simp only [lowFactor, order, List.length_cons]
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

lemma coefficient_chain_rule_joint {O : Set LowJet} (hO : IsOpen O)
    {G : Base → Space} (hG : ContDiff ℝ ∞ G) {c : LowJet × ℝ → ℝ}
    (hc : ContDiffOn ℝ ∞ c (O ×ˢ Set.univ)) (v : Fin 2) (p : Base)
    (hp : lowJet G p ∈ O) (t : ℝ) :
    fderiv ℝ (fun q => c (lowJet G q, t)) p (coordinateVector v) =
      ∑ i : LowIndex, lowDerivative G v p i * slowDerivative c (lowBasis i) (lowJet G p, t) := by
  have hs : DifferentiableAt ℝ (fun Q : LowJet => c (Q, t)) (lowJet G p) :=
    ((hc.contDiffAt ((hO.prod isOpen_univ).mem_nhds ⟨hp, Set.mem_univ t⟩)).comp _
      (contDiff_id.prodMk contDiff_const).contDiffAt).differentiableAt (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)
  simpa only [smul_eq_mul, LocalPeriodicCalculus.fderiv_slice hO hc hp] using
    coefficient_chain_rule hG v p hs

/-- The syntactic derivative evaluates to the genuine derivative on every
open region where the low-jet coefficients are smooth. -/
theorem eval_slow {O : Set LowJet} {S : Set Base} (hO : IsOpen O) (hS : IsOpen S)
    {G : Base → Space} (hG : ContDiff ℝ ∞ G) (hQ : Set.MapsTo (lowJet G) S O)
    (v : Fin 2) {e : Expression} (he : e.SmoothCoeffs O) {p : Base} (hp : p ∈ S) (t : ℝ) :
    (e.slow v).eval G (p, t) = fderiv ℝ (fun q => e.eval G (q, t)) p (coordinateVector v) := by
  induction e with
  | coeff c =>
    rw [slow, eval_sumList, ← List.sum_toFinset _ Finset.univ.nodup_toList,
      Finset.toList_toFinset]
    simp only [eval_mul, eval_lowFactor, eval]
    exact (coefficient_chain_rule_joint hO hG he v p (hQ hp) t).symm
  | atom w a e ih =>
    have hj := (jet_smooth hG w a).differentiable (by simp) p
    have he' : DifferentiableAt ℝ (fun q => e.eval G (q, t)) p :=
      (((eval_smooth hG hQ (e := e) he).contDiffAt
        ((hS.prod isOpen_univ).mem_nhds ⟨hp, Set.mem_univ t⟩)).comp p
        (contDiff_id.prodMk contDiff_const).contDiffAt).differentiableAt (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)
    simp only [slow, eval, ih he]
    rw [fderiv_fun_mul hj he']
    simp only [add_apply, smul_apply, smul_eq_mul,
      jet_cons]
    ring
  | add e f ihe ihf =>
    have hd (g : Expression) (hg : g.SmoothCoeffs O) :
        DifferentiableAt ℝ (fun q => g.eval G (q, t)) p :=
      (((eval_smooth hG hQ hg).contDiffAt
        ((hS.prod isOpen_univ).mem_nhds ⟨hp, Set.mem_univ t⟩)).comp p
        (contDiff_id.prodMk contDiff_const).contDiffAt).differentiableAt (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)
    simpa only [slow, eval, fderiv_fun_add (hd e he.1) (hd f he.2),
      add_apply] using congrArg₂ (· + ·) (ihe he.1) (ihf he.2)

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
attribute [-instance] _root_.instMembershipProdContinuousLinearMapRealIdRelLoc _root_.instMetricSpaceOneJet _root_.instVAddIntReal_solutions
attribute [-simp] _root_.ContinuousLinearMap.comp_toSpanSingleton_apply _root_.OAI.ClosedSurfaceR4.CollarVelocity.loopX_apply _root_.OAI.ClosedSurfaceR4.CollarVelocity.loopX_zero _root_.OAI.ClosedSurfaceR4.CollarVelocity.loopY_apply _root_.OAI.ClosedSurfaceR4.CollarVelocity.loopY_zero _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.circularPhaseBoundaryCurve_carrier _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.directionJetLinearization_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.loss_scale _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.order_scale _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_C _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_J _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_e _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_lowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_variationLowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowPosition_lowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.spatialAmplitude_lowJet _root_.OAI.ClosedSurfaceR4.LocalPeriodicExpansion.Family.global_apply _root_.OAI.ClosedSurfaceR4.LocalPeriodicExpansion.Geometry.xTangent_zero _root_.OAI.ClosedSurfaceR4.LocalPeriodicExpansion.Geometry.yTangent_zero _root_.OAI.ClosedSurfaceR4.PeriodicExpansion.Family.add_apply _root_.OAI.ClosedSurfaceR4.PeriodicExpansion.Family.angle_apply _root_.OAI.ClosedSurfaceR4.PeriodicExpansion.Family.constant_apply _root_.OAI.ClosedSurfaceR4.PeriodicExpansion.Family.fluct_apply _root_.OAI.ClosedSurfaceR4.PeriodicExpansion.Family.inner_apply _root_.OAI.ClosedSurfaceR4.PeriodicExpansion.Family.mean_apply _root_.OAI.ClosedSurfaceR4.PeriodicExpansion.Family.neg_apply _root_.OAI.ClosedSurfaceR4.PeriodicExpansion.Family.slow_apply _root_.OAI.ClosedSurfaceR4.PeriodicExpansion.Family.smul_apply _root_.OAI.ClosedSurfaceR4.PeriodicExpansion.Family.sub_apply _root_.OAI.ClosedSurfaceR4.PeriodicExpansion.Family.sum_apply _root_.OAI.ClosedSurfaceR4.PeriodicExpansion.Family.zero_apply _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_apply _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_one _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_zero _root_.OAI.ClosedSurfaceR4.SurfaceVelocityFamily.Loop.withSpatialAmplitude_amplitude _root_.Path.extend_div_self
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

lemma order_slow_le {R : VectorExpression} {N : ℕ} (hN : 2 ≤ N)
    (hR : ∀ i, (R i).order ≤ N) (v : Fin 2) : ∀ i, (R.slow v i).order ≤ N + 1 := by
  intro i
  have hi := hR i
  exact (Expression.order_slow_le v (R i)).trans (by omega)

lemma represents_slow {S : TopologicalSpace.Opens Base} {O : Set LowJet} (hO : IsOpen O)
    {G : Base → Space} (hG : ContDiff ℝ ∞ G) (hQ : Set.MapsTo (lowJet G) S O)
    {R : VectorExpression} {U : Family S R4} (hRs : R.SmoothCoeffs O)
    (hR : Represents G R U) (v : Fin 2) : Represents G (R.slow v) (U.slow (coordinateVector v)) := by
  intro i p hp t
  rw [slow, Expression.eval_slow hO S.isOpen hG hQ v (hRs i) hp]
  let L : R4 →L[ℝ] ℝ := EuclideanSpace.proj i
  have heq : (fun x => (R i).eval G (x, t)) =ᶠ[𝓝 p]
      (fun x => L (U.val x (t : CovarianceCorrector.Period))) := by
    filter_upwards [S.isOpen.mem_nhds hp] with x hx
    exact hR i x hx t
  rw [heq.fderiv_eq]
  have hU : DifferentiableAt ℝ (fun x => U.val x (t : CovarianceCorrector.Period)) p :=
    ((U.smooth.contDiffAt ((S.isOpen.prod isOpen_univ).mem_nhds ⟨hp, Set.mem_univ t⟩)).comp p
      (contDiff_id.prodMk contDiff_const).contDiffAt).differentiableAt (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)
  change fderiv ℝ (L ∘ fun x => U.val x (t : CovarianceCorrector.Period)) p
    (coordinateVector v) = _
  rw [(L.hasFDerivAt.comp p hU.hasFDerivAt).fderiv]
  rw [Family.slow_apply U (coordinateVector v) hp t,
    ← LocalPeriodicCalculus.fderiv_slice S.isOpen U.smooth hp]
  rfl

end VectorExpression
end ClosedSurfaceR4.JetPolynomial

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Correction_JetPolynomialScalar
attribute [-instance] _root_.instMembershipProdContinuousLinearMapRealIdRelLoc _root_.instVAddIntReal_solutions
attribute [-simp] _root_.ContinuousLinearMap.comp_toSpanSingleton_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.circularPhaseBoundaryCurve_carrier _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.directionJetLinearization_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_C _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_J _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_e _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_lowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_variationLowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowPosition_lowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.spatialAmplitude_lowJet _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_apply _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_one _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_zero _root_.OAI.ClosedSurfaceR4.SurfaceVelocityFamily.Loop.withSpatialAmplitude_amplitude _root_.Path.extend_div_self
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

@[simp] lemma eval_scale (a : ℝ) (e : Expression) (G : Base → Space) (z : Base × ℝ) :
    (e.scale a).eval G z = a * e.eval G z := eval_mapCoeff_mul e G (fun _ => a) z

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

end ClosedSurfaceR4.JetPolynomial.VectorExpression

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

end ClosedSurfaceR4.PeriodicExpansion

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Geometry_TransverseCoefficientBounds
attribute [-instance] _root_.instMembershipProdContinuousLinearMapRealIdRelLoc _root_.instVAddIntReal_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Uniform bounds for the first two transverse derivatives of represented
periodic coefficients. Their common loss is fixed before the slow map. -/
noncomputable section
open Set
open scoped ContDiff
namespace ClosedSurfaceR4.JetPolynomial.VectorExpression
open LocalPeriodicExpansion WeightedEstimates

lemma transverse_smooth {O : Set LowJet} (hO : IsOpen O) {R : VectorExpression}
    (hR : R.SmoothCoeffs O) (second : Bool) : (R.transverse second).SmoothCoeffs O := by
  have h1 : (R.slow 1).SmoothCoeffs O := fun a => Expression.smoothCoeffs_slow hO 1 (hR a)
  cases second
  · exact h1
  · exact fun a => Expression.smoothCoeffs_slow hO 1 (h1 a)

lemma transverse_order {R : VectorExpression} {N : ℕ} (hN : 2 ≤ N)
    (hR : ∀ a, (R a).order ≤ N) (second : Bool) (a : Fin 4) :
    (R.transverse second a).order ≤ N+2 := by
  have h1 := order_slow_le hN hR 1
  cases second
  · exact (h1 a).trans (by omega)
  · exact order_slow_le (by omega) h1 1 a

lemma represents_transverse {S : TopologicalSpace.Opens Base} {O : Set LowJet}
    (hO : IsOpen O) {G : Base → Space} (hG : ContDiff ℝ ∞ G) (hGO : MapsTo (lowJet G) S O)
    {R : VectorExpression} {U : Family S R4} (hRs : R.SmoothCoeffs O) (hR : Represents G R U)
    (second : Bool) : Represents G (R.transverse second) (transverseFamily U second) := by
  have h1 := represents_slow hO hG hGO hRs hR 1
  cases second
  · exact h1
  · exact represents_slow hO hG hGO
      (fun a => Expression.smoothCoeffs_slow hO 1 (hRs a)) h1 1

theorem compact_transverse_coefficients {S : TopologicalSpace.Opens Base} {O Q : Set LowJet}
    (hO : IsOpen O) (hQ : IsCompact Q) (hQO : Q ⊆ O)
    (R : ℕ → VectorExpression) (L N : ℕ) (hN : 2 ≤ N)
    (hRs : ∀ i < L, (R i).SmoothCoeffs O) (hRo : ∀ i < L, ∀ a, (R i a).order ≤ N)
    (ℓ : Base →L[ℝ] ℝ) :
    ∃ loss : ℕ, ∀ B : ℝ, 1 ≤ B → ∃ D : ℝ, 0 ≤ D ∧
      ∀ (G : Base → Space) (s z : ℝ), 0 < z → z ≤ s → s ≤ 1 →
      ContDiff ℝ ∞ G → MapsTo (lowJet G) S Q →
      WeightedBound S s (N+2) B (lowJet G) →
      ∀ U : ℕ → Family S R4, (∀ i < L, Represents G (R i) (U i)) →
      ∀ i < L, ∀ second : Bool, ∀ p ∈ S,
        ‖(transverseFamily (U i) second).fastValue ℓ z p‖ ≤ D/s^loss := by
  classical
  let R' : Bool × Fin L → VectorExpression := fun j => (R j.2).transverse j.1
  let loss := Finset.univ.sup (fun j : Bool × Fin L => Finset.univ.sup (fun a : Fin 4 => (R' j a).loss))
  have hl (j : Bool × Fin L) (a : Fin 4) : (R' j a).loss ≤ loss :=
    (Finset.le_sup (f := fun a : Fin 4 => (R' j a).loss) (Finset.mem_univ a)).trans
      (Finset.le_sup (f := fun j : Bool × Fin L => Finset.univ.sup (fun a : Fin 4 => (R' j a).loss))
        (Finset.mem_univ j))
  refine ⟨loss,?_⟩
  intro B hB
  obtain ⟨D,hD,hd⟩ := compact_finite_fast_bound (S := S) hO hQ hQO R'
    (fun j => transverse_smooth hO (hRs j.2 j.2.isLt) j.1) (N+2) loss
    (fun j a => transverse_order hN (hRo j.2 j.2.isLt) j.1 a) hl ℓ 0 B hB
  refine ⟨D,hD,?_⟩
  intro G s z hz hzs hs1 hG hGQ hb U hrep i hi second p hp
  have hGO : MapsTo (lowJet G) S O := fun _ hx => hQO (hGQ hx)
  have hh := hd G s z hz hzs hs1 hG hGQ (by simpa only [zero_add] using hb)
    (fun j : Bool × Fin L => transverseFamily (U j.2) j.1)
    (fun j => represents_transverse hO hG hGO (hRs j.2 j.2.isLt) (hrep j.2 j.2.isLt) j.1)
    (second,⟨i,hi⟩)
  exact hh.norm_le hp

end ClosedSurfaceR4.JetPolynomial.VectorExpression

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

/-- The two transverse derivatives only differentiate slow coefficients. -/
theorem transverse_profiles_of_coefficients {F : A → E} (hF : ContDiff ℝ ∞ F)
    (U : ℕ → Family A E) (ℓ : A →L[ℝ] ℝ) (L : ℕ) {dy : A} (hy : ℓ dy = 0)
    {z C : ℝ} {p : A} (hz : 0 < z) (hz1 : z ≤ 1) (hC : 0 ≤ C)
    (hU : ∀ i < L, ‖((U i).slow dy).fastValue ℓ z p‖ ≤ C)
    (hUU : ∀ i < L, ‖(((U i).slow dy).slow dy).fastValue ℓ z p‖ ≤ C) :
    ‖directionalMap (finiteAnsatz F U ℓ L z) dy p-directionalMap F dy p‖ ≤ (L*C)*z ∧
    ‖directionalMap (directionalMap (finiteAnsatz F U ℓ L z) dy) dy p-
      directionalMap (directionalMap F dy) dy p‖ ≤ (L*C)*z := by
  constructor
  · rw [finiteAnsatz_directional hF U ℓ L hz.ne' dy]
    simp only [hy,zero_smul,add_zero,add_sub_cancel_left,norm_smul,Real.norm_eq_abs,abs_of_pos hz]
    exact (mul_le_mul_of_nonneg_left (phaseSum_bound_of_coefficients _ ℓ L hz.le hz1 hC hU) hz.le).trans_eq
      (mul_comm _ _)
  · rw [finiteAnsatz_second_transverse hF U ℓ L hz.ne' dy hy]
    simp only [hy,zero_smul,add_zero,add_sub_cancel_left,norm_smul,Real.norm_eq_abs,abs_of_pos hz]
    exact (mul_le_mul_of_nonneg_left (phaseSum_bound_of_coefficients _ ℓ L hz.le hz1 hC hUU) hz.le).trans_eq
      (mul_comm _ _)

end ClosedSurfaceR4.PeriodicExpansion

namespace ClosedSurfaceR4.LocalPeriodicExpansion
open CovarianceCorrector
variable {A E : Type} [NormedAddCommGroup A] [NormedSpace ℝ A]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  {O : TopologicalSpace.Opens A}

lemma global_slow_eq_local (W : PeriodicExpansion.Family A E) (U : Family O E)
    (hW : W.val = U.val) (v : A) {p : A} (hp : p ∈ O) (t : Period) :
    (W.slow v).val p t = (U.slow v).val p t := by
  refine Quotient.inductionOn' t ?_
  intro s
  rw [PeriodicExpansion.Family.slow_apply,Family.slow_apply U v hp,hW]

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
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Primitive_UniformTransverseProfiles
attribute [-instance] _root_.instMembershipProdContinuousLinearMapRealIdRelLoc _root_.instVAddIntReal_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The actual primitive's transverse first and second derivatives approach
the slow baseline uniformly over all maps in the fixed compact jet domain. -/
noncomputable section
open Set
open scoped ContDiff
namespace ClosedSurfaceR4.SurfaceVelocityFamily.Loop
open JetPolynomial JetVelocityCoordinates LocalPeriodicExpansion CovarianceCorrector WeightedEstimates
variable {O : TopologicalSpace.Opens LowJet} (l : SurfaceVelocityFamily.Loop O)

theorem uniform_transverse_profiles_oai {S : TopologicalSpace.Opens JetPolynomial.Base}
    {Q : Set LowJet} (hQ : IsCompact Q) (hQO : Q ⊆ O)
    (n : ℕ) (ℓ : JetPolynomial.Base →L[ℝ] ℝ) (hy : ℓ (coordinateVector 1) = 0) :
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
        ‖PeriodicExpansion.directionalMap f (coordinateVector 1) p-
          PeriodicExpansion.directionalMap F (coordinateVector 1) p‖ ≤ D*z/s^loss ∧
        ‖PeriodicExpansion.directionalMap (PeriodicExpansion.directionalMap f (coordinateVector 1))
            (coordinateVector 1) p-
          PeriodicExpansion.directionalMap (PeriodicExpansion.directionalMap F (coordinateVector 1))
            (coordinateVector 1) p‖ ≤ D*z/s^loss := by
  obtain ⟨loss,hb⟩ := VectorExpression.compact_transverse_coefficients (S := S) O.isOpen hQ hQO
    (l.coefficientExpressions n) (n+1) (2*n+2) (by omega)
    (fun i _ => l.coefficientExpressions_smooth n i)
    (fun i hi a => (MetricPolynomial.coefficients_order _ _ _ _ _ 0 1 n i a).trans (by omega)) ℓ
  refine ⟨loss,?_⟩
  intro B hB
  obtain ⟨D,hD,hd⟩ := hb B hB
  refine ⟨(n+1)*D,mul_nonneg (by positivity) hD,?_⟩
  intro G hG hGQ s z hz hzs hs1 hGb U hU hrep p hp
  let W := globalCoefficients U hU
  have hw1 (i : ℕ) (q : JetPolynomial.Base) (hq : q ∈ S) (t : Period) :
      ((W i).slow (coordinateVector 1)).val q t =
        ((U i).slow (coordinateVector 1)).val q t :=
    global_slow_eq_local (W i) (U i) rfl (coordinateVector 1) hq t
  have hw2 (i : ℕ) (q : JetPolynomial.Base) (hq : q ∈ S) (t : Period) :
      (((W i).slow (coordinateVector 1)).slow (coordinateVector 1)).val q t =
        (((U i).slow (coordinateVector 1)).slow (coordinateVector 1)).val q t :=
    global_slow_eq_local_of_eqOn ((W i).slow (coordinateVector 1))
      ((U i).slow (coordinateVector 1)) (hw1 i) (coordinateVector 1) hq t
  have hc := hd G s z hz hzs hs1 hG hGQ hGb U (fun i _ => hrep i)
  have hC : 0 ≤ D/s^loss := div_nonneg hD (pow_nonneg (hz.le.trans hzs) _)
  have hfirst (i : ℕ) (hi : i < n+1) :
      ‖((W i).slow (coordinateVector 1)).fastValue ℓ z p‖ ≤ D/s^loss := by
    change ‖((W i).slow (coordinateVector 1)).val p ((ℓ p/z : ℝ) : Period)‖ ≤ _
    rw [hw1 i p hp]
    exact hc i hi false p hp
  have hsecond (i : ℕ) (hi : i < n+1) :
      ‖(((W i).slow (coordinateVector 1)).slow (coordinateVector 1)).fastValue ℓ z p‖ ≤ D/s^loss := by
    change ‖(((W i).slow (coordinateVector 1)).slow (coordinateVector 1)).val p
      ((ℓ p/z : ℝ) : Period)‖ ≤ _
    rw [hw2 i p hp]
    exact hc i hi true p hp
  have hout := PeriodicExpansion.transverse_profiles_of_coefficients
    (JetVelocityCoordinates.toEuclidean.contDiff.comp hG) W ℓ (n+1) hy hz (hzs.trans hs1) hC hfirst hsecond
  have he : ((n+1 : ℕ) : ℝ)*(D/s^loss)*z = ((n+1 : ℕ) : ℝ)*D*z/s^loss := by ring
  rw [he] at hout
  simpa only [W,globalCoefficients_finiteAnsatz,Function.comp_def,
    Nat.cast_add,Nat.cast_one,Nat.cast_mul,Nat.cast_ofNat] using hout

end ClosedSurfaceR4.SurfaceVelocityFamily.Loop

end

end OAI
end

theorem solution : type_of% @OAI.ClosedSurfaceR4.SurfaceVelocityFamily.Loop.uniform_transverse_profiles_oai := @OAI.ClosedSurfaceR4.SurfaceVelocityFamily.Loop.uniform_transverse_profiles_oai
