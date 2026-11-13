-- Prove2me | solution 1 for OAI.ClosedSurfaceR4.SurfaceVelocityFamily.Loop.meanMetric_eq_meanOperator
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-12T12:50:15.337338+00:00
-- url     : https://prove2.me/submissions/aeb265fb-651d-4aeb-b026-7061ed86dc64

import Mathlib
import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
import Mathlib.Geometry.Manifold.PartitionOfUnity
import Definitions.Def_OAIQ249SI012
import Theorems.Thm_OAI_ClosedSurfaceR4_JetPolynomial_MetricPolynomial_coefficients_smooth

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

lemma angleOn_hasDerivAt (F : P → C(Period, E)) (S : Set P) (hS : IsOpen S)
    (hF : ContDiffOn ℝ ∞ (fun z : P × ℝ => F z.1 (z.2 : Period)) (S ×ˢ Set.univ))
    {p : P} (hp : p ∈ S) (t : ℝ) :
    HasDerivAt (fun s : ℝ => F p (s : Period)) (angleOn F S hS hF p (t : Period)) t := by
  rw [angleOn, bundleOn_apply _ _ _ _ _ hp]
  exact angle_hasDerivAt hS hF hp t

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
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Correction_JetPolynomialIntegral
attribute [-instance] _root_.instMembershipProdContinuousLinearMapRealIdRelLoc _root_.instVAddIntReal_solutions
attribute [-simp] _root_.ContinuousLinearMap.comp_toSpanSingleton_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.circularPhaseBoundaryCurve_carrier _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.directionJetLinearization_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.eval_neg _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.eval_sub _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.loss_covariance _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.loss_fluct _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.loss_liftOperator _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.loss_neg _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.loss_scale _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.loss_sub _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.order_covariance _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.order_fluct _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.order_liftOperator _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.order_neg _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.order_scale _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.order_sub _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_C _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_J _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_e _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_lowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_variationLowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowPosition_lowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.spatialAmplitude_lowJet _root_.OAI.ClosedSurfaceR4.PeriodicExpansion.Family.angle_apply _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_apply _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_one _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_zero _root_.OAI.ClosedSurfaceR4.SurfaceVelocityFamily.Loop.withSpatialAmplitude_amplitude _root_.Path.extend_div_self
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

lemma eval_slice_smooth {O : Set LowJet} (hO : IsOpen O) {e : Expression}
    (he : e.SmoothCoeffs O) (G : Base → Space) {p : Base} (hp : lowJet G p ∈ O) :
    ContDiff ℝ ∞ (fun t => e.eval G (p, t)) := by
  induction e with
  | coeff c => exact LocalPeriodicCalculus.smooth_slice hO he hp
  | atom w a e ih =>
    change ContDiff ℝ ∞ (fun t => jet G w a p * e.eval G (p, t))
    exact contDiff_const.mul (ih he)
  | add e f ihe ihf => exact (ihe he.1).add (ihf he.2)

lemma smoothCoeffs_angle {O : Set LowJet} (hO : IsOpen O) {e : Expression}
    (he : e.SmoothCoeffs O) : e.angle.SmoothCoeffs O :=
  smoothCoeffs_map e _ (fun _ hc => LocalPeriodicCalculus.angle_smooth hO hc) he

lemma eval_angle {O : Set LowJet} (hO : IsOpen O) {e : Expression}
    (he : e.SmoothCoeffs O) (G : Base → Space) {p : Base} (hp : lowJet G p ∈ O) (t : ℝ) :
    e.angle.eval G (p, t) = deriv (fun s => e.eval G (p, s)) t := by
  induction e with
  | coeff c => exact (LocalPeriodicCalculus.angle_hasDerivAt hO he hp t).deriv.symm
  | atom w a e ih =>
    change jet G w a p * e.angle.eval G (p, t) =
      deriv (fun s => jet G w a p * e.eval G (p, s)) t
    rw [deriv_const_mul _ ((eval_slice_smooth hO (e := e) he G hp).differentiable (by simp) t),
      ih he]
  | add e f ihe ihf =>
    change e.angle.eval G (p, t) + f.angle.eval G (p, t) =
      deriv (fun s => e.eval G (p, s) + f.eval G (p, s)) t
    rw [deriv_fun_add ((eval_slice_smooth hO he.1 G hp).differentiable (by simp) t)
      ((eval_slice_smooth hO he.2 G hp).differentiable (by simp) t), ihe he.1, ihf he.2]

lemma eval_mean {O : Set LowJet} (hO : IsOpen O) {e : Expression}
    (he : e.SmoothCoeffs O) (G : Base → Space) {p : Base} (hp : lowJet G p ∈ O) (t : ℝ) :
    e.mean.eval G (p, t) = ∫ s in 0..1, e.eval G (p, s) := by
  induction e with
  | coeff c => rfl
  | atom w a e ih =>
    change jet G w a p * e.mean.eval G (p, t) = ∫ s in 0..1, jet G w a p * e.eval G (p, s)
    rw [intervalIntegral.integral_const_mul, ih he]
  | add e f ihe ihf =>
    change e.mean.eval G (p, t) + f.mean.eval G (p, t) =
      ∫ s in 0..1, (e.eval G (p, s) + f.eval G (p, s))
    rw [intervalIntegral.integral_add
      ((eval_slice_smooth hO he.1 G hp).continuous.intervalIntegrable 0 1)
      ((eval_slice_smooth hO he.2 G hp).continuous.intervalIntegrable 0 1), ihe he.1, ihf he.2]

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

lemma angle_hasDerivAt (F : Family O E) {p : A} (hp : p ∈ O) (t : ℝ) :
    HasDerivAt (fun s : ℝ => F.val p (s : Period)) (F.angle.val p (t : Period)) t := by
  rw [angle, ofLocal_apply _ _ hp]
  exact angleOn_hasDerivAt F.val O O.isOpen F.smooth hp t

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

lemma smoothCoeffs_dot {O : Set LowJet} {R T : VectorExpression}
    (hR : R.SmoothCoeffs O) (hT : T.SmoothCoeffs O) : (R.dot T).SmoothCoeffs O := by
  apply Expression.smoothCoeffs_sumList
  intro i _
  exact Expression.smoothCoeffs_mul (hR i) (hT i)

lemma represents_add {S : TopologicalSpace.Opens Base} {G : Base → Space}
    {R T : VectorExpression} {U W : Family S R4} (hR : Represents G R U)
    (hT : Represents G T W) : Represents G (R.add T) (U + W) := by
  intro i p hp t
  simp only [add, Expression.eval, hR i p hp t, hT i p hp t, Family.add_apply]
  rfl

lemma eval_dot {S : TopologicalSpace.Opens Base} {G : Base → Space}
    {R T : VectorExpression} {U W : Family S R4} (hR : Represents G R U)
    (hT : Represents G T W) {p : Base} (hp : p ∈ S) (t : ℝ) :
    (R.dot T).eval G (p, t) = inner ℝ (U.val p (t : CovarianceCorrector.Period))
      (W.val p (t : CovarianceCorrector.Period)) := by
  rw [dot, Expression.eval_sumList, ← List.sum_toFinset _ Finset.univ.nodup_toList,
    Finset.toList_toFinset]
  simp only [Expression.eval_mul, hR _ p hp t, hT _ p hp t]
  rw [EuclideanSpace.inner_eq_star_dotProduct]
  change (∑ i : Fin 4, U.val p (t : CovarianceCorrector.Period) i *
    W.val p (t : CovarianceCorrector.Period) i) =
    ∑ i : Fin 4, W.val p (t : CovarianceCorrector.Period) i * U.val p (t : CovarianceCorrector.Period) i
  exact Finset.sum_congr rfl (fun _ _ => mul_comm _ _)

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

lemma represents_angle {S : TopologicalSpace.Opens Base} {O : Set LowJet} (hO : IsOpen O)
    {G : Base → Space} (hQ : Set.MapsTo (lowJet G) S O)
    {R : VectorExpression} {U : Family S R4} (hRs : R.SmoothCoeffs O)
    (hR : Represents G R U) : Represents G R.angle U.angle := by
  intro i p hp t
  rw [angle, Expression.eval_angle hO (hRs i) G (hQ hp)]
  have heq : (fun s => (R i).eval G (p, s)) =
      (fun s : ℝ => U.val p (s : CovarianceCorrector.Period) i) := funext (hR i p hp)
  rw [heq]
  let L : R4 →L[ℝ] ℝ := EuclideanSpace.proj i
  exact (L.hasFDerivAt.comp_hasDerivAt t (U.angle_hasDerivAt hp t)).deriv

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

lemma represents_sumFinset {ι : Type*} {S : TopologicalSpace.Opens Base} {G : Base → Space}
    (a : Finset ι) {e : ι → Expression} {U : ι → Family S ℝ}
    (he : ∀ i ∈ a, Represents G (e i) (U i)) :
    Represents G (sumFinset a e) (∑ i ∈ a, U i) := by
  classical
  intro p hp t
  rw [sumFinset, eval_sumList, ← List.sum_toFinset _ a.nodup_toList, Finset.toList_toFinset,
    Family.sum_apply]
  exact Finset.sum_congr rfl (fun i hi => he i hi p hp t)

lemma smoothCoeffs_sumFinset {ι : Type*} {O : Set LowJet} (a : Finset ι) (e : ι → Expression)
    (he : ∀ i ∈ a, (e i).SmoothCoeffs O) : (sumFinset a e).SmoothCoeffs O := by
  apply smoothCoeffs_sumList
  intro i hi
  exact he i (Finset.mem_toList.mp hi)

lemma represents_dot {S : TopologicalSpace.Opens Base} {G : Base → Space}
    {R T : VectorExpression} {U W : Family S R4} (hR : VectorExpression.Represents G R U)
    (hT : VectorExpression.Represents G T W) : Represents G (R.dot T) (U.inner W) := by
  intro p hp t
  rw [VectorExpression.eval_dot hR hT hp, Family.inner_apply]

end ClosedSurfaceR4.JetPolynomial.Expression

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Correction_PolynomialMetricCoefficients
attribute [-instance] _root_.instVAddIntReal_solutions
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

lemma represents_xCoefficient {S : TopologicalSpace.Opens Base} {O : Set LowJet} (hO : IsOpen O)
    {G : Base → Space} (hG : ContDiff ℝ ∞ G) (hQ : Set.MapsTo (lowJet G) S O)
    {U : ℕ → VectorExpression} {W : ℕ → LocalPeriodicExpansion.Family S R4}
    (hUs : ∀ j, (U j).SmoothCoeffs O)
    (hU : ∀ j, VectorExpression.Represents G (U j) (W j)) (dx : Fin 2) (i : ℕ) :
    VectorExpression.Represents G (xCoefficient dx U i)
      (LocalPeriodicExpansion.xCoefficient (coordinateVector dx) W i) :=
  VectorExpression.represents_add
    (VectorExpression.represents_slow hO hG hQ (hUs _) (hU _) dx)
    (VectorExpression.represents_angle hO hQ (hUs _) (hU _))

lemma represents_yCoefficient {S : TopologicalSpace.Opens Base} {O : Set LowJet} (hO : IsOpen O)
    {G : Base → Space} (hG : ContDiff ℝ ∞ G) (hQ : Set.MapsTo (lowJet G) S O)
    {U : ℕ → VectorExpression} {W : ℕ → LocalPeriodicExpansion.Family S R4}
    (hUs : ∀ j, (U j).SmoothCoeffs O)
    (hU : ∀ j, VectorExpression.Represents G (U j) (W j)) (dy : Fin 2) (i : ℕ) :
    VectorExpression.Represents G (yCoefficient dy U i)
      (LocalPeriodicExpansion.yCoefficient (coordinateVector dy) W i) :=
  VectorExpression.represents_slow hO hG hQ (hUs _) (hU _) dy

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
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Correction_FiniteMetricPolynomial
attribute [-instance] _root_.instMembershipProdContinuousLinearMapRealIdRelLoc _root_.instVAddIntReal_solutions
attribute [-simp] _root_.ContinuousLinearMap.comp_toSpanSingleton_apply _root_.Path.extend_div_self
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Exact finite polynomial metric algebra for the periodic ansatz. -/

noncomputable section
open scoped BigOperators

namespace ClosedSurfaceR4.PeriodicExpansion

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- At each degree no larger than the vector degree, the usual convolution
contains every contributing term, with no truncation at either end. -/
lemma metricPolynomial_coeff {n r : ℕ} (hr : r ≤ n) (a b : ℕ → E) :
    (metricPolynomial n a b).coeff r =
      ∑ i ∈ Finset.range (r + 1), inner ℝ (a i) (b (r - i)) := by
  simp only [metricPolynomial, Polynomial.finsetSum_coeff]
  have hrow (i : ℕ) :
      (∑ j ∈ Finset.range (n + 1), (Polynomial.monomial (i + j) (inner ℝ (a i) (b j))).coeff r) =
        if i ≤ r then inner ℝ (a i) (b (r - i)) else 0 := by
    by_cases hi : i ≤ r
    · rw [ite_eq_left hi]
      have hc : (Polynomial.monomial (i + (r - i))
          (inner ℝ (a i) (b (r - i)))).coeff r = inner ℝ (a i) (b (r - i)) := by
        simp [Nat.add_sub_of_le hi]
      rw [← hc]
      apply Finset.sum_eq_single (r - i)
      · intro j hj hne
        rw [Polynomial.coeff_monomial]
        split_ifs with he
        · omega
        · rfl
      · intro hn
        exfalso
        apply hn
        exact Finset.mem_range.mpr (by omega)
    · rw [ite_eq_right hi]
      apply Finset.sum_eq_zero
      intro j hj
      rw [Polynomial.coeff_monomial]
      split_ifs with he
      · omega
      · rfl
  simp_rw [hrow]
  have hsub : Finset.range (r + 1) ⊆ Finset.range (n + 1) := Finset.range_mono (by omega)
  calc
    _ = ∑ i ∈ Finset.range (r + 1),
        if i ≤ r then inner ℝ (a i) (b (r - i)) else 0 := by
      symm
      apply Finset.sum_subset hsub
      intro i hin hir
      exact ite_eq_right (by simpa only [Finset.mem_range, Nat.lt_succ_iff] using hir)
    _ = _ := by
      apply Finset.sum_congr rfl
      intro i hi
      exact ite_eq_left (Nat.le_of_lt_succ (Finset.mem_range.mp hi))

lemma metricPolynomial_coeff_pos {n r : ℕ} (hr : r ≤ n) (hpos : 0 < r)
    (a b : ℕ → E) :
    (metricPolynomial n a b).coeff r = inner ℝ (a 0) (b r) + inner ℝ (a r) (b 0) +
      ∑ i ∈ Finset.Ico 1 r, inner ℝ (a i) (b (r - i)) := by
  rw [metricPolynomial_coeff hr, Finset.sum_range_succ,
    ← Finset.sum_range_add_sum_Ico (fun i => inner ℝ (a i) (b (r - i))) hpos]
  simp only [Finset.sum_range_one, Nat.sub_zero, Nat.sub_self]
  ring

end ClosedSurfaceR4.PeriodicExpansion

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Correction_LocalPeriodicPolynomialExpansion
attribute [-instance] _root_.instMembershipProdContinuousLinearMapRealIdRelLoc _root_.instVAddIntReal_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Metric polynomial coefficients of the finite periodic derivative ansatz. -/

noncomputable section
open scoped BigOperators

namespace ClosedSurfaceR4.LocalPeriodicExpansion

open CovarianceCorrector
open ClosedSurfaceR4.PeriodicExpansion (metricPolynomial metricPolynomial_coeff_pos
  metricPolynomial_coeff vectorPolynomialValue
  )


variable {A E : Type} [NormedAddCommGroup A] [NormedSpace ℝ A]
  [FiniteDimensional ℝ A] [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [CompleteSpace E] [FiniteDimensional ℝ E]
  {O : TopologicalSpace.Opens A}

namespace Geometry

variable {dy : A} (g : Geometry (E := E) O dy)

omit [FiniteDimensional ℝ A] [CompleteSpace E] [FiniteDimensional ℝ E] in
lemma xTangent_interior (dx : A) (U : ℕ → Family O E) {L i : ℕ}
    (hi : 0 < i) (hL : i < L) : g.xTangent dx U L i = xCoefficient dx U i := by
  simp only [xTangent, ne_of_gt hi, ne_of_lt hL, ite_false, if_false]

omit [FiniteDimensional ℝ A] [CompleteSpace E] [FiniteDimensional ℝ E] in
lemma yTangent_pos (U : ℕ → Family O E) {i : ℕ} (hi : 0 < i) :
    g.yTangent U i = yCoefficient dy U i := by
  simp only [yTangent, ne_of_gt hi, ite_false, if_false]

omit [FiniteDimensional ℝ A] [CompleteSpace E] [FiniteDimensional ℝ E] in
lemma xxPolynomial_coeff (dx : A) (U : ℕ → Family O E) {L r : ℕ}
    (hr : 0 < r) (hL : r < L) (p : A) (t : Period) :
    (g.xxPolynomial dx U L p t).coeff r = (g.xxCoefficient dx U r).val p t := by
  unfold xxPolynomial
  rw [metricPolynomial_coeff_pos (Nat.le_of_lt hL) hr,
    g.xTangent_zero, g.xTangent_interior dx U hr hL]
  have hs : (∑ i ∈ Finset.Ico 1 r,
      inner ℝ ((g.xTangent dx U L i).val p t) ((g.xTangent dx U L (r - i)).val p t)) =
      (xxQuadratic dx U r).val p t := by
    simp only [xxQuadratic, Family.sum_apply, Family.inner_apply]
    apply Finset.sum_congr rfl
    intro i hi
    obtain ⟨hi, hir⟩ := Finset.mem_Ico.mp hi
    rw [g.xTangent_interior dx U (by omega) (by omega),
      g.xTangent_interior dx U (by omega) (by omega)]
  rw [hs]
  simp only [xxCoefficient, Family.add_apply, Family.smul_apply, Family.inner_apply, smul_eq_mul]
  rw [real_inner_comm ((xCoefficient dx U r).val p t) (g.longitudinal.val p t)]
  ring

omit [FiniteDimensional ℝ A] [CompleteSpace E] [FiniteDimensional ℝ E] in
lemma xyPolynomial_coeff (dx : A) (U : ℕ → Family O E) {L r : ℕ}
    (hr : 0 < r) (hL : r < L) (p : A) (t : Period) :
    (g.xyPolynomial dx U L p t).coeff r = (g.xyCoefficient dx U r).val p t := by
  unfold xyPolynomial
  rw [metricPolynomial_coeff_pos (Nat.le_of_lt hL) hr,
    g.xTangent_zero, g.xTangent_interior dx U hr hL, g.yTangent_zero, g.yTangent_pos U hr]
  have hs : (∑ i ∈ Finset.Ico 1 r,
      inner ℝ ((g.xTangent dx U L i).val p t) ((g.yTangent U (r - i)).val p t)) =
      (xyQuadratic dx dy U r).val p t := by
    simp only [xyQuadratic, Family.sum_apply, Family.inner_apply]
    apply Finset.sum_congr rfl
    intro i hi
    obtain ⟨hi, hir⟩ := Finset.mem_Ico.mp hi
    rw [g.xTangent_interior dx U (by omega) (by omega), g.yTangent_pos U (by omega)]
  rw [hs]
  simp only [xyCoefficient, Family.add_apply, Family.inner_apply]
  rw [real_inner_comm ((xCoefficient dx U r).val p t) (g.transverse.val p t)]

omit [FiniteDimensional ℝ A] [CompleteSpace E] [FiniteDimensional ℝ E] in
lemma yyPolynomial_coeff (U : ℕ → Family O E) {L r : ℕ}
    (hr : 0 < r) (hL : r ≤ L) (p : A) (t : Period) :
    (g.yyPolynomial U L p t).coeff r = (g.yyCoefficient U r).val p t := by
  unfold yyPolynomial
  rw [metricPolynomial_coeff_pos hL hr, g.yTangent_zero, g.yTangent_pos U hr]
  have hs : (∑ i ∈ Finset.Ico 1 r,
      inner ℝ ((g.yTangent U i).val p t) ((g.yTangent U (r - i)).val p t)) =
      (yyQuadratic dy U r).val p t := by
    simp only [yyQuadratic, Family.sum_apply, Family.inner_apply]
    apply Finset.sum_congr rfl
    intro i hi
    obtain ⟨hi, hir⟩ := Finset.mem_Ico.mp hi
    rw [g.yTangent_pos U (by omega), g.yTangent_pos U (by omega)]
  rw [hs]
  simp only [yyCoefficient, Family.add_apply, Family.smul_apply, Family.inner_apply, smul_eq_mul]
  rw [real_inner_comm ((yCoefficient dy U r).val p t) (g.transverse.val p t)]
  ring

end Geometry
end ClosedSurfaceR4.LocalPeriodicExpansion

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Primitive_LocalPeriodicMetricRemainder
attribute [-instance] _root_.instVAddIntReal_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Smooth coefficient families and exact remainder of the finite metric expansion. -/

noncomputable section
open scoped BigOperators

namespace ClosedSurfaceR4.LocalPeriodicExpansion

open CovarianceCorrector
open ClosedSurfaceR4.PeriodicExpansion (metricPolynomial metricPolynomial_coeff_pos
  metricPolynomial_coeff vectorPolynomialValue
  )


variable {A E : Type} [NormedAddCommGroup A] [NormedSpace ℝ A]
  [FiniteDimensional ℝ A] [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [CompleteSpace E] [FiniteDimensional ℝ E]
  {O : TopologicalSpace.Opens A}

omit [FiniteDimensional ℝ A] [CompleteSpace E] [FiniteDimensional ℝ E] in
lemma metricCoefficientFamily_apply (n r : ℕ) (a b : ℕ → Family O E) (p : A) (t : Period) :
    (metricCoefficientFamily n r a b).val p t =
      (metricPolynomial n (fun i => (a i).val p t) (fun i => (b i).val p t)).coeff r := by
  simp only [metricCoefficientFamily, Family.sum_apply, metricPolynomial, Polynomial.finsetSum_coeff]
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro j hj
  split_ifs with h
  · simp only [h, Family.inner_apply, Polynomial.coeff_monomial_same]
  · simp only [Polynomial.coeff_monomial, h, ite_false, if_false, Family.zero_apply]

end ClosedSurfaceR4.LocalPeriodicExpansion

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

lemma represents_finiteMetric {S : TopologicalSpace.Opens Base} {G : Base → Space}
    {X Y : ℕ → VectorExpression} {A B : ℕ → Family S R4}
    (hX : ∀ i, VectorExpression.Represents G (X i) (A i))
    (hY : ∀ i, VectorExpression.Represents G (Y i) (B i)) (L r : ℕ) :
    Expression.Represents G (finiteMetric L r X Y) (metricCoefficientFamily L r A B) := by
  apply Expression.represents_sumFinset
  intro i _
  apply Expression.represents_sumFinset
  intro j _
  split_ifs
  · exact Expression.represents_dot (hX i) (hY j)
  · intro p _ t
    rfl

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

lemma represents_xTangent {S : TopologicalSpace.Opens Base} {O : Set LowJet}
    (hO : IsOpen O) {G : Base → Space} (hG : ContDiff ℝ ∞ G)
    (hQ : Set.MapsTo (lowJet G) S O) {dy : Base} (g : Geometry (E := R4) S dy)
    {X : VectorExpression} {U : ℕ → VectorExpression} {W : ℕ → Family S R4}
    (hX : VectorExpression.Represents G X g.longitudinal)
    (hUs : ∀ i, (U i).SmoothCoeffs O) (hU : ∀ i, VectorExpression.Represents G (U i) (W i))
    (dx : Fin 2) (L i : ℕ) :
    VectorExpression.Represents G (xTangent X dx U L i) (g.xTangent (coordinateVector dx) W L i) := by
  unfold xTangent Geometry.xTangent
  split_ifs
  · exact hX
  · exact VectorExpression.represents_slow hO hG hQ (hUs _) (hU _) dx
  · exact represents_xCoefficient hO hG hQ hUs hU dx i

lemma represents_yTangent {S : TopologicalSpace.Opens Base} {O : Set LowJet}
    (hO : IsOpen O) {G : Base → Space} (hG : ContDiff ℝ ∞ G)
    (hQ : Set.MapsTo (lowJet G) S O) (dy : Fin 2) (g : Geometry (E := R4) S (coordinateVector dy))
    {Y : VectorExpression} {U : ℕ → VectorExpression} {W : ℕ → Family S R4}
    (hY : VectorExpression.Represents G Y g.transverse)
    (hUs : ∀ i, (U i).SmoothCoeffs O) (hU : ∀ i, VectorExpression.Represents G (U i) (W i)) (i : ℕ) :
    VectorExpression.Represents G (yTangent Y dy U i) (g.yTangent W i) := by
  unfold yTangent Geometry.yTangent
  split_ifs
  · exact hY
  · exact represents_yCoefficient hO hG hQ hUs hU dy i

end ClosedSurfaceR4.JetPolynomial.MetricPolynomial

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

lemma represents_tangentExpression {S : TopologicalSpace.Opens Base} {O : Set LowJet}
    (hO : IsOpen O) {G : Base → Space} (hG : ContDiff ℝ ∞ G)
    (hQ : Set.MapsTo (lowJet G) S O) (dx dy : Fin 2)
    (g : Geometry (E := R4) S (coordinateVector dy))
    {X Y : VectorExpression} {R : ℕ → VectorExpression} {U : ℕ → Family S R4}
    (hX : VectorExpression.Represents G X g.longitudinal)
    (hY : VectorExpression.Represents G Y g.transverse)
    (hRs : ∀ i, (R i).SmoothCoeffs O) (hR : ∀ i, VectorExpression.Represents G (R i) (U i))
    (L : ℕ) (b : Bool) (i : ℕ) :
    VectorExpression.Represents G (tangentExpression X Y R dx dy L b i)
      (tangentFamily g U (coordinateVector dx) L b i) := by
  cases b
  · exact represents_yTangent hO hG hQ dy g hY hRs hR i
  · exact represents_xTangent hO hG hQ g hX hRs hR dx L i

end ClosedSurfaceR4.JetPolynomial.MetricPolynomial

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Primitive_SurfaceVelocityIdentities
attribute [-instance] _root_.instMembershipProdContinuousLinearMapRealIdRelLoc _root_.instMetricSpaceOneJet _root_.instVAddIntReal_solutions
attribute [-simp] _root_.ContinuousLinearMap.comp_toSpanSingleton_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.circularPhaseBoundaryCurve_carrier _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.directionJetLinearization_apply _root_.OAI.ClosedSurfaceR4.GeometryPreservation.boundaryProfileMap_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.eval_neg _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.eval_scale _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.eval_sub _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.loss_covariance _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.loss_liftOperator _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.loss_mapCoeff _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.order_covariance _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.order_liftOperator _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.order_mapCoeff _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_C _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_J _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_e _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_lowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_variationLowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowPosition_lowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.spatialAmplitude_lowJet _root_.OAI.ClosedSurfaceR4.RealModes.secondTensorFromJet_realTwoJet _root_.OAI.ClosedSurfaceR4.SurfaceVelocityFamily.Loop.withSpatialAmplitude_amplitude _root_.Path.extend_div_self
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

lemma leading_xx {J : LowJet} (hJ : J ∈ O) :
    inner ℝ (ι (tangent J)) (ι (tangent J)) + l.q J =
      inner ℝ (ι (slot 1 J)) (ι (slot 1 J)) + l.amplitude J ^ 2 := by
  have hp := realNormalPart_perp (slot 2 J) (slot 6 J) (slot 1 J) (l.gram_ne J hJ)
  have ht : tangent J ⬝ᵥ normal J = 0 := tangential_part_perp _ _ _ _ hp.1 hp.2
  have hx : slot 1 J = tangent J + normal J := by dsimp [tangent]; abel
  simp only [inner_toEuclidean, q]
  conv_rhs => rw [hx]
  simp only [add_dotProduct, dotProduct_add, ht, dotProduct_comm (normal J) (tangent J)]
  ring

include l in
lemma leading_xy {J : LowJet} (hJ : J ∈ O) :
    inner ℝ (ι (tangent J)) (ι (slot 2 J)) =
      inner ℝ (ι (slot 1 J)) (ι (slot 2 J)) := by
  have hp := realNormalPart_perp (slot 2 J) (slot 6 J) (slot 1 J) (l.gram_ne J hJ)
  simp only [inner_toEuclidean, tangent, sub_dotProduct]
  rw [dotProduct_comm (normal J) (slot 2 J), show slot 2 J ⬝ᵥ normal J = 0 from hp.1, sub_zero]

variable {S : TopologicalSpace.Opens JetPolynomial.Base}
    {G : JetPolynomial.Base → JetPolynomial.Space} (hG : ContDiff ℝ ∞ G)
    (hGO : MapsTo (lowJet G) S O)

lemma geometry_velocity {p : JetPolynomial.Base} (hp : p ∈ S) :
    (l.geometry G hG hGO).V.val p = l.euclideanVelocity (lowJet G p) := by
  apply ContinuousMap.ext
  intro t
  change (Family.ofLocal (fun q => l.euclideanVelocity (lowJet G q)) _).val p t = _
  exact Family.ofLocal_apply _ _ hp t

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

lemma meanMetric_eq {S : TopologicalSpace.Opens JetPolynomial.Base}
    {G : JetPolynomial.Base → JetPolynomial.Space} (hG : ContDiff ℝ ∞ G)
    (hGO : MapsTo (lowJet G) S O) (U : ℕ → Family S Euclidean)
    (n : ℕ) (b c : Bool) (z : ℝ) {p : JetPolynomial.Base} (hp : p ∈ S) :
    let g := l.geometry G hG hGO
    MetricPolynomial.meanMetric g (coordinateVector 0) U n b c z p =
      inner ℝ
        (fderiv ℝ (fun q => ι (G q)) p
          (MetricPolynomial.metricDirection (coordinateVector 0) (coordinateVector 1) b))
        (fderiv ℝ (fun q => ι (G q)) p
          (MetricPolynomial.metricDirection (coordinateVector 0) (coordinateVector 1) c)) +
      (if b && c then l.amplitude (lowJet G p) ^ 2 else 0) + meanCorrection g U n b c z p := by
  dsimp only
  cases b <;> cases c <;>
    simp only [MetricPolynomial.meanMetric, meanCorrection, MetricPolynomial.metricDirection,
      Bool.and, Bool.or, Bool.false_eq_true, ↓reduceIte,
      euclidean_first_derivative hG, Matrix.cons_val_zero, Matrix.cons_val_one]
  · simp only [add_zero]; rfl
  · change inner ℝ (ι (tangent (lowJet G p))) (ι (slot 2 (lowJet G p))) + _ = _
    rw [l.leading_xy (hGO hp), real_inner_comm (ι (slot 1 (lowJet G p))) (ι (slot 2 (lowJet G p)))]
    simp only [add_zero]
  · change inner ℝ (ι (tangent (lowJet G p))) (ι (slot 2 (lowJet G p))) + _ = _
    rw [l.leading_xy (hGO hp)]
    simp only [add_zero]
  · change (inner ℝ (ι (tangent (lowJet G p))) (ι (tangent (lowJet G p))) +
      l.q (lowJet G p)) + _ = _
    rw [l.leading_xx (hGO hp)]

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

/-- Each coefficient used by the slow correction is the mean of the same
coefficient in the actual periodic pullback metric. -/
lemma meanPolynomial_eval {S : TopologicalSpace.Opens JetPolynomial.Base}
    {G : JetPolynomial.Base → JetPolynomial.Space} (hG : ContDiff ℝ ∞ G)
    (hGO : MapsTo (lowJet G) S O) (n : ℕ) (b c : Bool) (r : Fin n)
    (U : ℕ → Family S Euclidean)
    (hU : ∀ i, VectorExpression.Represents G (l.coefficientExpressions n i) (U i))
    {p : JetPolynomial.Base} (hp : p ∈ S) (t : ℝ) :
    (l.meanPolynomial n b c r).eval G (p,t) =
      meanCoefficientValue (l.geometry G hG hGO) U b c (r.val+1) p := by
  let g := l.geometry G hG hGO
  have hX : VectorExpression.Represents G
      (MetricPolynomial.longitudinal xData l.euclideanVelocity) g.longitudinal :=
    MetricPolynomial.represents_longitudinal g xData l.euclideanVelocity (fun _ _ => rfl)
      (fun _ hp => l.geometry_velocity hG hGO hp)
  have hY : VectorExpression.Represents G (MetricPolynomial.transverse yData) g.transverse :=
    MetricPolynomial.represents_transverse g yData (fun _ _ => rfl)
  have hT (b : Bool) (i : ℕ) := MetricPolynomial.represents_tangentExpression
    O.isOpen hG hGO 0 1 g hX hY (l.coefficientExpressions_smooth n) hU (n+1) b i
  have hrep := MetricPolynomial.represents_finiteMetric (hT (b || c)) (hT (b && c))
    (n+1) (r.val+1)
  have hs := MetricPolynomial.smooth_finiteMetric
    (fun i => MetricPolynomial.smooth_tangentExpression O.isOpen
      (MetricPolynomial.smooth_longitudinal (xData_smooth l) l.euclideanVelocity_smooth)
      (MetricPolynomial.smooth_transverse yData_smooth) (l.coefficientExpressions_smooth n)
      0 1 (n+1) (b || c) i)
    (fun i => MetricPolynomial.smooth_tangentExpression O.isOpen
      (MetricPolynomial.smooth_longitudinal (xData_smooth l) l.euclideanVelocity_smooth)
      (MetricPolynomial.smooth_transverse yData_smooth) (l.coefficientExpressions_smooth n)
      0 1 (n+1) (b && c) i) (n+1) (r.val+1)
  unfold meanPolynomial meanTangentExpression
  rw [Expression.eval_mean O.isOpen hs G (hGO hp)]
  have hr : 0 < r.val+1 := by omega
  have hrn : r.val+1 < n+1 := by omega
  cases b <;> cases c
  all_goals
    simp only [Bool.and,Bool.or,meanCoefficientValue,Bool.false_eq_true,↓reduceIte]
    simp only [Bool.and,Bool.or] at hrep
    simp_rw [hrep p hp,metricCoefficientFamily_apply]
  · change (∫ s in (0 : ℝ)..1, (g.yyPolynomial U (n+1) p (s : Period)).coeff (r.val+1)) =
      average ((g.yyCoefficient U (r.val+1)).val p)
    simp_rw [g.yyPolynomial_coeff U hr hrn.le]
    exact PeriodicPrimitive.integral_lift_eq_haar _
  · change (∫ s in (0 : ℝ)..1, (g.xyPolynomial (coordinateVector 0) U (n+1) p
      (s : Period)).coeff (r.val+1)) = average ((g.xyCoefficient (coordinateVector 0) U
        (r.val+1)).val p)
    simp_rw [g.xyPolynomial_coeff (coordinateVector 0) U hr hrn]
    exact PeriodicPrimitive.integral_lift_eq_haar _
  · change (∫ s in (0 : ℝ)..1, (g.xyPolynomial (coordinateVector 0) U (n+1) p
      (s : Period)).coeff (r.val+1)) = average ((g.xyCoefficient (coordinateVector 0) U
        (r.val+1)).val p)
    simp_rw [g.xyPolynomial_coeff (coordinateVector 0) U hr hrn]
    exact PeriodicPrimitive.integral_lift_eq_haar _
  · change (∫ s in (0 : ℝ)..1, (g.xxPolynomial (coordinateVector 0) U (n+1) p
      (s : Period)).coeff (r.val+1)) = average ((g.xxCoefficient (coordinateVector 0) U
        (r.val+1)).val p)
    simp_rw [g.xxPolynomial_coeff (coordinateVector 0) U hr hrn]
    exact PeriodicPrimitive.integral_lift_eq_haar _

/-- The full mean correction is precisely the polynomial perturbation
evaluated by the finite-parametrix machinery. -/
lemma meanPolynomial_eval_sum {S : TopologicalSpace.Opens JetPolynomial.Base}
    {G : JetPolynomial.Base → JetPolynomial.Space} (hG : ContDiff ℝ ∞ G)
    (hGO : MapsTo (lowJet G) S O) (n : ℕ) (b c : Bool)
    (U : ℕ → Family S Euclidean)
    (hU : ∀ i, VectorExpression.Represents G (l.coefficientExpressions n i) (U i))
    (z : ℝ) {p : JetPolynomial.Base} (hp : p ∈ S) (t : ℝ) :
    Perturbation.eval (l.meanPolynomial n b c) z G (p,t) =
      meanCorrection (l.geometry G hG hGO) U n b c z p := by
  unfold Perturbation.eval
  simp_rw [l.meanPolynomial_eval hG hGO n b c _ U hU hp t]
  change (∑ r : Fin n, (fun j : ℕ => z^(j+1)*
    meanCoefficientValue (l.geometry G hG hGO) U b c (j+1) p) r.val) = _
  rw [Fin.sum_univ_eq_sum_range (fun j : ℕ => z^(j+1)*
    meanCoefficientValue (l.geometry G hG hGO) U b c (j+1) p)]
  have he := Finset.sum_Ico_add'
    (fun r => z^r*meanCoefficientValue (l.geometry G hG hGO) U b c r p) 0 n 1
  simp only [zero_add,Nat.Ico_zero_eq_range] at he
  rw [he]
  cases b <;> cases c <;>
    simp only [meanCoefficientValue,meanCorrection,Bool.and,Bool.or,Bool.false_eq_true,↓reduceIte]
  all_goals exact Finset.sum_congr rfl (fun _ _ => mul_comm _ _)

/-- The mean pullback metric is the original metric plus the primitive
rank-one term and this explicitly constructed polynomial operator. -/
theorem meanMetric_eq_polynomial {S : TopologicalSpace.Opens JetPolynomial.Base}
    {G : JetPolynomial.Base → JetPolynomial.Space} (hG : ContDiff ℝ ∞ G)
    (hGO : MapsTo (lowJet G) S O) (n : ℕ) (b c : Bool)
    (U : ℕ → Family S Euclidean)
    (hU : ∀ i, VectorExpression.Represents G (l.coefficientExpressions n i) (U i))
    (z : ℝ) {p : JetPolynomial.Base} (hp : p ∈ S) :
    MetricPolynomial.meanMetric (l.geometry G hG hGO) (coordinateVector 0) U n b c z p =
      inner ℝ
        (fderiv ℝ (fun q => JetVelocityCoordinates.toEuclidean (G q)) p
          (MetricPolynomial.metricDirection (coordinateVector 0) (coordinateVector 1) b))
        (fderiv ℝ (fun q => JetVelocityCoordinates.toEuclidean (G q)) p
          (MetricPolynomial.metricDirection (coordinateVector 0) (coordinateVector 1) c)) +
      (if b && c then l.amplitude (lowJet G p)^2 else 0) +
        Perturbation.eval (l.meanPolynomial n b c) z G (p,0) := by
  rw [l.meanPolynomial_eval_sum hG hGO n b c U hU z hp 0]
  exact l.meanMetric_eq hG hGO U n b c z hp

end Loop
end ClosedSurfaceR4.SurfaceVelocityFamily

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Primitive_SpatialLoopAmplitude
attribute [-instance] _root_.instMembershipProdContinuousLinearMapRealIdRelLoc _root_.instVAddIntReal_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A prescribed spatial amplitude is independent of the varying immersion,
even though the coefficient calculus stores it as a function of the full jet. -/

noncomputable section
open Set
open scoped ContDiff

namespace ClosedSurfaceR4.SurfaceVelocityFamily.Loop
open RealModes JetPolynomial JetVelocityCoordinates LocalPeriodicExpansion CovarianceCorrector

variable {O : TopologicalSpace.Opens LowJet} (l : SurfaceVelocityFamily.Loop O)

lemma amplitude_at_lowJet {a : Base → ℝ} (ha : l.HasSpatialAmplitude a)
    (G : JetPolynomial.Base → JetPolynomial.Space) {p : JetPolynomial.Base}
    (hp : lowJet G p ∈ O) :
    l.amplitude (lowJet G p) = a p := by
  simpa only [lowJetPosition_lowJet] using ha (lowJet G p) hp

/-- The existing mean-polynomial theorem with its primitive rank-one term
written as the prescribed spatial amplitude, uniformly for all nearby maps. -/
theorem meanMetric_eq_spatial_polynomial {a : Base → ℝ} (ha : l.HasSpatialAmplitude a)
    {S : TopologicalSpace.Opens JetPolynomial.Base}
    {G : JetPolynomial.Base → JetPolynomial.Space} (hG : ContDiff ℝ ∞ G)
    (hGO : MapsTo (lowJet G) S O) (n : ℕ) (b c : Bool)
    (U : ℕ → Family S Euclidean)
    (hU : ∀ i, VectorExpression.Represents G (l.coefficientExpressions n i) (U i))
    (z : ℝ) {p : JetPolynomial.Base} (hp : p ∈ S) :
    MetricPolynomial.meanMetric (l.geometry G hG hGO) (coordinateVector 0) U n b c z p =
      inner ℝ
        (fderiv ℝ (fun q => JetVelocityCoordinates.toEuclidean (G q)) p
          (MetricPolynomial.metricDirection (coordinateVector 0) (coordinateVector 1) b))
        (fderiv ℝ (fun q => JetVelocityCoordinates.toEuclidean (G q)) p
          (MetricPolynomial.metricDirection (coordinateVector 0) (coordinateVector 1) c)) +
      (if b && c then a p^2 else 0) +
        Perturbation.eval (l.meanPolynomial n b c) z G (p,0) := by
  rw [l.meanMetric_eq_polynomial hG hGO n b c U hU z hp,
    l.amplitude_at_lowJet ha G (hGO hp)]

end ClosedSurfaceR4.SurfaceVelocityFamily.Loop

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Primitive_SurfacePrimitiveError
attribute [-instance] _root_.instMembershipProdContinuousLinearMapRealIdRelLoc _root_.instVAddIntReal_solutions
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

lemma meanMetric_eq_meanOperator_oai {a : Base → ℝ} (ha : l.HasSpatialAmplitude a)
    {S : TopologicalSpace.Opens Base} {G : JetPolynomial.Base → JetPolynomial.Space} (hG : ContDiff ℝ ∞ G)
    (hGO : MapsTo (lowJet G) S O) (n : ℕ) (b c : Bool) (z : ℝ)
    (U : ℕ → Family S Euclidean)
    (hU : ∀ i, VectorExpression.Represents G (l.coefficientExpressions n i) (U i))
    {p : Base} (hp : p ∈ S) :
    MetricPolynomial.meanMetric (l.geometry G hG hGO) (coordinateVector 0) U n b c z p =
      l.meanOperator n b c z G p+(if b && c then a p^2 else 0) := by
  rw [l.meanMetric_eq_spatial_polynomial ha hG hGO n b c U hU z hp]
  unfold meanOperator
  ring

end ClosedSurfaceR4.SurfaceVelocityFamily.Loop

end

end OAI
end

theorem solution : type_of% @OAI.ClosedSurfaceR4.SurfaceVelocityFamily.Loop.meanMetric_eq_meanOperator_oai := @OAI.ClosedSurfaceR4.SurfaceVelocityFamily.Loop.meanMetric_eq_meanOperator_oai
