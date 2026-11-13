-- Prove2me | solution 1 for OAI.ClosedSurfaceR4.SurfaceVelocityFamily.Loop.meanTensorPolynomial_global_extension
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-12T12:50:16.450901+00:00
-- url     : https://prove2.me/submissions/069da98f-a871-44d0-b2b0-a9538b6add6b

import Mathlib
import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
import Mathlib.Analysis.Calculus.BumpFunction.Normed
import Mathlib.Analysis.Calculus.ContDiff.Convolution
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Geometry.Manifold.PartitionOfUnity
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.LinearAlgebra.Vandermonde
import Mathlib.MeasureTheory.Measure.Haar.NormedSpace
import Definitions.Def_OAIQ249SI012
import Theorems.Thm_OAI_ClosedSurfaceR4_JetPolynomial_MetricPolynomial_coefficients_smooth

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

lemma smoothCoeffs_sumList {ι : Type*} {O : Set LowJet} (l : List ι) (f : ι → Expression)
    (hf : ∀ i ∈ l, (f i).SmoothCoeffs O) : (sumList l f).SmoothCoeffs O := by
  induction l with
  | nil => exact contDiffOn_const
  | cons i l ih => exact ⟨hf i (List.mem_cons_self ..),
      ih (fun j hj => hf j (List.mem_cons_of_mem _ hj))⟩

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

lemma smoothCoeffs_sumFinset {ι : Type*} {O : Set LowJet} (a : Finset ι) (e : ι → Expression)
    (he : ∀ i ∈ a, (e i).SmoothCoeffs O) : (sumFinset a e).SmoothCoeffs O := by
  apply smoothCoeffs_sumList
  intro i hi
  exact he i (Finset.mem_toList.mp hi)

end ClosedSurfaceR4.JetPolynomial.Expression

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
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Correction_PolynomialCoefficientExtension
attribute [-instance] _root_.instMembershipProdContinuousLinearMapRealIdRelLoc _root_.instVAddIntReal_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Coefficients can be extended smoothly off the permitted compact low-jet
set without changing the operator there or changing its jet order/loss. -/
noncomputable section
open scoped ContDiff

namespace ClosedSurfaceR4.JetPolynomial.Expression

lemma cutoffCoeffs_smooth {e : Expression} {O : Set LowJet} (hO : IsOpen O)
    (he : e.SmoothCoeffs O) {χ : LowJet → ℝ} (hχ : ContDiff ℝ ∞ χ)
    (hs : tsupport χ ⊆ O) : (e.cutoffCoeffs χ).SmoothCoeffs Set.univ := by
  induction e with
  | coeff c =>
    have hc := SmoothParameterIntegral.contDiff_supported_smul hO he hχ hs
    change ContDiffOn ℝ ∞ (fun z : LowJet × ℝ => χ z.1 * c z) (Set.univ ×ˢ Set.univ)
    exact hc.contDiffOn
  | atom w a e ih => exact ih he
  | add e f ihe ihf => exact ⟨ihe he.1, ihf he.2⟩

lemma cutoffCoeffs_eval (e : Expression) (χ : LowJet → ℝ) (G : Base → Space) (z : Base × ℝ) :
    (e.cutoffCoeffs χ).eval G z = χ (lowJet G z.1) * e.eval G z :=
  e.eval_mapCoeff_mul G (fun x => χ x.1) z

/-- Only the compact set of low jets used by the application is retained. -/
theorem exists_global_extension {e : Expression} {O Q : Set LowJet}
    (hO : IsOpen O) (he : e.SmoothCoeffs O) (hQ : IsCompact Q) (hQO : Q ⊆ O) :
    ∃ e' : Expression, e'.SmoothCoeffs Set.univ ∧ e'.order = e.order ∧ e'.loss = e.loss ∧
      ∀ (G : Base → Space) (z : Base × ℝ), lowJet G z.1 ∈ Q → e'.eval G z = e.eval G z := by
  obtain ⟨χ, hχ, _, _, hs, hχone⟩ := CollarVelocity.compact_cutoff hQ hO hQO
  refine ⟨e.cutoffCoeffs χ, cutoffCoeffs_smooth hO he hχ hs, ?_, ?_, ?_⟩
  · exact e.order_mapCoeff _
  · exact e.loss_mapCoeff _
  · intro G z hz
    rw [cutoffCoeffs_eval, hχone _ hz, one_mul]

end ClosedSurfaceR4.JetPolynomial.Expression

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
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Correction_SurfaceMeanTensor
attribute [-instance] _root_.instMetricSpaceOneJet _root_.instVAddIntReal_solutions
attribute [-simp] _root_.ContinuousLinearMap.comp_toSpanSingleton_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.circularPhaseBoundaryCurve_carrier _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.exactCellCutoff_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.supportedPlaneWeight_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.directionJetLinearization_apply _root_.OAI.ClosedSurfaceR4.GeometryPreservation.boundaryProfileMap_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_C _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_J _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_e _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.modeSupport_jetSupport _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.onModeSupport_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowPosition_lowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.realTensorChartPull_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.tensorChartPull_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.tensorChartPush_apply _root_.OAI.ClosedSurfaceR4.PhaseGeometry.linearPhaseChart_apply _root_.OAI.ClosedSurfaceR4.PhaseGeometry.linearPhaseChart_source _root_.OAI.ClosedSurfaceR4.PhaseGeometry.linearPhaseChart_symm_apply _root_.OAI.ClosedSurfaceR4.PhaseGeometry.linearPhaseChart_target _root_.OAI.ClosedSurfaceR4.PhaseGeometry.phaseEquiv_apply _root_.OAI.ClosedSurfaceR4.PhaseGeometry.phaseEquiv_symm_apply _root_.OAI.ClosedSurfaceR4.PhasePartitions.CompactPhasePartition.coe_pieceSupport _root_.OAI.ClosedSurfaceR4.PhasePartitions.CompactPhasePartition.coe_supportCompact _root_.OAI.ClosedSurfaceR4.PhasePartitions.CompactPhasePartition.splitSupported_apply _root_.OAI.ClosedSurfaceR4.PhasePartitions.CompactPhasePartition.supportedWeight_apply _root_.OAI.ClosedSurfaceR4.RealModes.secondTensorFromJet_realTwoJet _root_.Path.extend_div_self
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The primitive's three mean metric coefficients are exactly the tensor
operator used by the finite parametrix, in its product coordinates. -/
noncomputable section
open scoped ContDiff Matrix
namespace ClosedSurfaceR4.SurfaceVelocityFamily.Loop
open RealModes JetPolynomial JetVelocityCoordinates LocalPeriodicExpansion
open CovarianceCorrector

variable {O : TopologicalSpace.Opens LowJet} (l : SurfaceVelocityFamily.Loop O)

lemma meanTensorPolynomial_smooth (n : ℕ) (k : Fin 3) (r : Fin n) :
    (l.meanTensorPolynomial n k r).SmoothCoeffs O := by
  fin_cases k <;> exact l.meanPolynomial_smooth n _ _ r

private lemma realMetric_coordinate {G : JetPolynomial.Base → JetPolynomial.Space}
    (hG : ContDiff ℝ ∞ G) (p : SmallModes.Base) (b c : Bool) :
    RealModes.realMetric (G ∘ planeCoordinateIsometry.symm)
        (if b then SmallModes.dx else SmallModes.dy)
        (if c then SmallModes.dx else SmallModes.dy) p =
      inner ℝ
        (fderiv ℝ (fun q => JetVelocityCoordinates.toEuclidean (G q))
          (planeCoordinateIsometry.symm p)
          (MetricPolynomial.metricDirection (coordinateVector 0) (coordinateVector 1) b))
        (fderiv ℝ (fun q => JetVelocityCoordinates.toEuclidean (G q))
          (planeCoordinateIsometry.symm p)
          (MetricPolynomial.metricDirection (coordinateVector 0) (coordinateVector 1) c)) := by
  have hcomp (v : SmallModes.Base) :
      fderiv ℝ (G ∘ planeCoordinateIsometry.symm) p v =
        fderiv ℝ G (planeCoordinateIsometry.symm p) (planeCoordinateIsometry.symm v) := by
    rw [fderiv_comp p (hG.differentiable (by simp) _) planeCoordinateIsometry.symm.differentiableAt]
    change (fderiv ℝ G (planeCoordinateIsometry.symm p))
      ((fderiv ℝ planeCoordinateIsometry.symm.toContinuousLinearEquiv.toContinuousLinearMap p) v) = _
    rw [planeCoordinateIsometry.symm.toContinuousLinearEquiv.toContinuousLinearMap.fderiv]
    rfl
  have heuc (v : JetPolynomial.Base) :
      fderiv ℝ (fun q => JetVelocityCoordinates.toEuclidean (G q))
        (planeCoordinateIsometry.symm p) v =
      JetVelocityCoordinates.toEuclidean (fderiv ℝ G (planeCoordinateIsometry.symm p) v) := by
    change (fderiv ℝ ((JetVelocityCoordinates.toEuclidean : JetPolynomial.Space → Euclidean) ∘ G)
      (planeCoordinateIsometry.symm p)) v = _
    rw [fderiv_comp (planeCoordinateIsometry.symm p)
      JetVelocityCoordinates.toEuclidean.differentiableAt (hG.differentiable (by simp) _)]
    change (fderiv ℝ JetVelocityCoordinates.toEuclidean.toContinuousLinearMap
      (G (planeCoordinateIsometry.symm p))) ((fderiv ℝ G (planeCoordinateIsometry.symm p)) v) = _
    rw [JetVelocityCoordinates.toEuclidean.toContinuousLinearMap.fderiv]
    rfl
  have hdir (d : Bool) :
      planeCoordinateIsometry.symm (if d then SmallModes.dx else SmallModes.dy) =
        MetricPolynomial.metricDirection (coordinateVector 0) (coordinateVector 1) d := by
    cases d <;> ext i <;> fin_cases i <;> rfl
  change (fderiv ℝ (G ∘ planeCoordinateIsometry.symm) p
    (if b then SmallModes.dx else SmallModes.dy)) ⬝ᵥ
    (fderiv ℝ (G ∘ planeCoordinateIsometry.symm) p
      (if c then SmallModes.dx else SmallModes.dy)) = _
  rw [hcomp,hcomp,heuc,heuc,inner_toEuclidean,hdir,hdir]

/-- No identification of metric operators is assumed: the coordinate
conversion and all three polynomial coefficients are proved equal. -/
theorem coordinateMetricMap_eq_meanTensorOperator
    {G : JetPolynomial.Base → JetPolynomial.Space} (hG : ContDiff ℝ ∞ G)
    (n : ℕ) (z : ℝ) :
    Perturbation.coordinateMetricMap (l.meanTensorPolynomial n) z G =
      l.meanTensorOperator n z G := by
  funext p k
  fin_cases k
  all_goals
    dsimp only [Perturbation.coordinateMetricMap,RealModes.realMetricTensor,
      Perturbation.coordinatePolynomialValue,meanTensorOperator,meanTensorPolynomial,
      meanOperator,Perturbation.eval,Pi.add_apply,Matrix.cons_val_zero,Matrix.cons_val_one,
      Matrix.cons_val_two]
  · change RealModes.realMetric (G ∘ planeCoordinateIsometry.symm)
      SmallModes.dx SmallModes.dx p + _ = _
    have hh := realMetric_coordinate hG p true true
    simp only [↓reduceIte] at hh
    rw [hh]
    rfl
  · change RealModes.realMetric (G ∘ planeCoordinateIsometry.symm)
      SmallModes.dx SmallModes.dy p + _ = _
    have hh := realMetric_coordinate hG p true false
    simp only [Bool.false_eq_true, ↓reduceIte] at hh
    rw [hh]
    rfl
  · change RealModes.realMetric (G ∘ planeCoordinateIsometry.symm)
      SmallModes.dy SmallModes.dy p + _ = _
    have hh := realMetric_coordinate hG p false false
    simp only [Bool.false_eq_true, ↓reduceIte] at hh
    rw [hh]
    rfl

end ClosedSurfaceR4.SurfaceVelocityFamily.Loop

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Correction_AtlasPrimitivePolynomial
attribute [-instance] _root_.instMembershipProdContinuousLinearMapRealIdRelLoc _root_.instVAddIntReal_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Embed the three mean-polynomial coefficients of one primitive in the
actual global atlas operator, with zero contribution from every other chart. -/
noncomputable section
open Set Manifold Bundle
open scoped ContDiff Manifold Topology BigOperators
namespace ClosedSurfaceR4.SurfaceVelocityFamily.Loop
open JetPolynomial JetPolynomial.Perturbation
variable {O : TopologicalSpace.Opens LowJet} (l : SurfaceVelocityFamily.Loop O)

lemma meanTensorPolynomial_global_extension_oai {Q : Set LowJet} (hQ : IsCompact Q)
    (hQO : Q ⊆ O) (n : ℕ) :
    ∃ P : Fin 3 → Fin n → Expression,
      (∀ k r, (P k r).SmoothCoeffs univ) ∧
      (∀ k r, (P k r).order = (l.meanTensorPolynomial n k r).order) ∧
      (∀ k r, (P k r).loss = (l.meanTensorPolynomial n k r).loss) ∧
      ∀ (G : JetPolynomial.Base → JetPolynomial.Space), ContDiff ℝ ∞ G →
        ∀ (z : ℝ) (p : JetPolynomial.Base), lowJet G p ∈ Q →
        coordinateMetricMap P z G (planeCoordinateIsometry p) =
          l.meanTensorOperator n z G (planeCoordinateIsometry p) := by
  classical
  choose P hs ho hl he using fun k r => Expression.exists_global_extension O.isOpen
    (l.meanTensorPolynomial_smooth n k r) hQ hQO
  refine ⟨P,hs,ho,hl,?_⟩
  intro G hG z p hp
  rw [← l.coordinateMetricMap_eq_meanTensorOperator hG]
  have hpoly : coordinatePolynomialValue P z G 0 (planeCoordinateIsometry p) =
      coordinatePolynomialValue (l.meanTensorPolynomial n) z G 0 (planeCoordinateIsometry p) := by
    funext k
    unfold coordinatePolynomialValue
    apply Finset.sum_congr rfl
    intro r _
    rw [he k r G (planeCoordinateIsometry.symm (planeCoordinateIsometry p),0)
      (by simpa only [planeCoordinateIsometry.symm_apply_apply] using hp)]
  change RealModes.realMetricTensor (G ∘ planeCoordinateIsometry.symm) (planeCoordinateIsometry p)+
    coordinatePolynomialValue P z G 0 (planeCoordinateIsometry p) = _
  rw [hpoly]
  rfl

end ClosedSurfaceR4.SurfaceVelocityFamily.Loop

end

end OAI
end

theorem solution : type_of% @OAI.ClosedSurfaceR4.SurfaceVelocityFamily.Loop.meanTensorPolynomial_global_extension_oai := @OAI.ClosedSurfaceR4.SurfaceVelocityFamily.Loop.meanTensorPolynomial_global_extension_oai
