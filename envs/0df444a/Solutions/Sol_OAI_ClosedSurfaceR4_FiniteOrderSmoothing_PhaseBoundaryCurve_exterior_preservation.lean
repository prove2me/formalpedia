-- Prove2me | solution 1 for OAI.ClosedSurfaceR4.FiniteOrderSmoothing.PhaseBoundaryCurve.exterior_preservation
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-12T12:03:26.090523+00:00
-- url     : https://prove2.me/submissions/f3b37197-38c9-4b03-9190-60a024d52469

import Mathlib
import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
import Mathlib.Analysis.Calculus.BumpFunction.Normed
import Mathlib.Analysis.Calculus.ContDiff.Convolution
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.ContDiff
import Mathlib.Analysis.Calculus.IteratedDeriv.WithinZpow
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Angle
import Mathlib.Analysis.SpecificLimits.ArithmeticGeometric
import Mathlib.Geometry.Manifold.PartitionOfUnity
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.LinearAlgebra.Vandermonde
import Mathlib.MeasureTheory.Measure.Haar.NormedSpace
import Mathlib.Tactic
import Mathlib.Topology.MetricSpace.Thickening
import Mathlib.Topology.UniformSpace.HeineCantor
import Definitions.Def_SurfaceImmersion
import Definitions.Def_OAIQ249SI006
import Definitions.Def_OAIQ249SI007
import Theorems.Thm_OAI_ClosedSurfaceR4_FiniteOrderSmoothing_SmoothingAtlas_compact_surface_phase_exterior_preservation

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Geometry_CurveSecondFields
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Smooth global representatives of second-form fields along a compact curve.
A cutoff in its own phase chart extends the field without choosing a normal frame. -/
noncomputable section
open Set Filter Manifold
open scoped ContDiff Topology
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open RealModes SmallModes NormalFrame SurfaceJetCoordinates
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M] [CompactSpace M]
namespace SmoothingAtlas
variable (A : SmoothingAtlas M)

omit [CompactSpace M] in
lemma phaseCurveSecondField_eq (i : A.centers)
    (e : OpenPartialHomeomorph JetPolynomial.Base JetPolynomial.Base)
    (β : SmallModes.Base → ℝ) (F : M → Space) (v w : SmallModes.Base → SmallModes.Base)
    {p : M} (hp : p ∈ (chart (i : M)).source) (ho : A.outer i p = 1)
    (hβ : β (baseEquiv (e (chart (i : M) p))) = 1) :
    spaceCoordinates (A.phaseCurveSecondField i e β F v w p) =
      realSecondForm (A.phaseRealChartMap i e.symm F)
        (v (baseEquiv (e (chart (i : M) p)))) (w (baseEquiv (e (chart (i : M) p))))
        (baseEquiv (e (chart (i : M) p))) := by
  simp only [phaseCurveSecondField,restore,indicator_of_mem hp,ho,hβ,one_smul,
    spaceCoordinates.apply_symm_apply]

end SmoothingAtlas
end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Atlas_PhaseBoundaryCurve
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Fixed compact boundary curves and their actual second-form fields.
The cutoff is chosen from the curve geometry, independently of any immersion. -/
noncomputable section
open Set Filter Manifold
open scoped ContDiff Topology
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open JetPolynomial SurfaceJetCoordinates RealModes SmallModes VelocityFrame NormalFrame
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M] [CompactSpace M]

namespace PhaseBoundaryCurve
variable {B : SmoothingAtlas M} (c : PhaseBoundaryCurve B)

lemma cutoff_properties : ContDiff ℝ ∞ c.cutoff ∧ HasCompactSupport c.cutoff ∧
    (∀ x ∈ c.coordinate '' c.carrier, c.cutoff x = 1) ∧
    ∀ x ∈ tsupport c.cutoff, baseEquiv.symm x ∈ c.phase.target ∧
      B.chartWeight c.index (c.phase.symm (baseEquiv.symm x)) ≠ 0 :=
  Classical.choose_spec c.cutoff_exists

lemma second_eq (F : M → Space) {p : M} (hp : p ∈ c.carrier) :
    c.second F p = realSecondForm (B.phaseRealChartMap c.index c.phase.symm F)
      dy dy (c.coordinate p) := by
  apply B.phaseCurveSecondField_eq c.index c.phase c.cutoff F (fun _ => dy) (fun _ => dy)
    (c.source hp).1
  · exact B.outer_one c.index p (subset_tsupport _ (c.active p hp))
  · exact c.cutoff_properties.2.2.1 _ ⟨p,hp,rfl⟩

theorem exterior_preservation_oai (A : SmoothingAtlas M)
    {g : SmoothMetric M} {F : M → Space} (hF : IsSmoothIsometricImmersion M g F)
    (n : PreferredNormal F)
    (houter : ∀ i p, p ∈ tsupport (A.weight i) → A.outer i =ᶠ[𝓝 p] (fun _ => 1))
    (hB : ∀ p ∈ c.carrier, c.second F p ≠ 0)
    (havoid : ∀ p ∈ c.carrier, spaceCoordinates (n.vector p) ≠ -normalize (c.second F p)) :
    ∃ ρ : ℝ, 0 < ρ ∧ ∀ G V W : M → Space,
      ContMDiff planeModel spaceModel ∞ G → ContMDiff planeModel spaceModel ∞ V →
      ContMDiff planeModel spaceModel ∞ W → ∀ b d : ℝ, 0 ≤ b → 0 ≤ d → b+d < ρ →
      A.WeightedBound 1 2 b (G-F) → A.WeightedBound 1 2 d (W-V) →
      ∀ O : Set M, (∀ y ∈ O, V =ᶠ[𝓝 y] G) → ∀ p ∈ c.carrier ∩ closure O,
      A.projectedNormalField W n.vector p ≠ 0 ∧ c.second W p ≠ 0 ∧
      spaceCoordinates (A.unitProjectedNormalField W n.vector p) ≠ -normalize (c.second W p) := by
  obtain ⟨ρ,hρ,hpres⟩ := A.compact_surface_phase_exterior_preservation B hF n houter
    c.index c.phase c.smooth c.inverse_smooth c.compact c.source c.active
    (fun p hp => by simpa only [c.second_eq F hp,coordinate] using hB p hp)
    (fun p hp => by simpa only [c.second_eq F hp,coordinate] using havoid p hp)
  refine ⟨ρ,hρ,?_⟩
  intro G V W hG hV hW b d hb hd hbd hGF hWV O hext p hp
  simpa only [c.second_eq W hp.1,coordinate] using hpres G V W hG hV hW b d hb hd hbd hGF hWV O hext p hp

end PhaseBoundaryCurve
end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

theorem solution.{u_1} : type_of% @OAI.ClosedSurfaceR4.FiniteOrderSmoothing.PhaseBoundaryCurve.exterior_preservation_oai.{u_1} := @OAI.ClosedSurfaceR4.FiniteOrderSmoothing.PhaseBoundaryCurve.exterior_preservation_oai.{u_1}
