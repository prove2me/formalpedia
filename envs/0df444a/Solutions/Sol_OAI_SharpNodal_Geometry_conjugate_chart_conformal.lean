-- Prove2me | solution 1 for OAI.SharpNodal.Geometry.conjugate_chart_conformal
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-26T06:13:57.522131+00:00
-- url     : https://prove2.me/submissions/be935a89-ffe7-45ad-a54f-07af4d264d8c

import Mathlib
import Definitions.Def_NodalLength
import Definitions.Def_OAIQ4Nl000

section
-- module Solutions.OAIQ4_Nl.NodalLength_MetricFamilies
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped ContDiff Bundle ENNReal
open Bundle Manifold MeasureTheory
open scoped ContDiff ENNReal Topology
open MeasureTheory Filter Set
open scoped Topology ENNReal
open MeasureTheory Filter Set
open scoped Topology ENNReal ContDiff
open MeasureTheory Filter Set
open scoped Topology ENNReal ContDiff
open MeasureTheory Filter Set
open scoped Topology ENNReal ContDiff
open MeasureTheory Filter Set
open scoped Topology ContDiff
open Filter Set
open scoped Topology ContDiff
open Filter Set
open scoped Topology ENNReal
open Filter Set MeasureTheory TopologicalSpace
open scoped Topology ContDiff
open Filter Set
open scoped Topology ENNReal
open Filter Set MeasureTheory TopologicalSpace
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory TopologicalSpace
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory Laplacian
open scoped Topology ENNReal ContDiff ComplexConjugate
open Filter Set MeasureTheory Laplacian
open scoped Topology ENNReal ContDiff ComplexConjugate
open Filter Set MeasureTheory Laplacian
open scoped Topology ENNReal NNReal
open Filter Set MeasureTheory
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory
open scoped Topology ENNReal
open Set MeasureTheory Filter
open scoped Topology ENNReal
open Filter Set MeasureTheory
open scoped Topology ENNReal
open Filter Set MeasureTheory
open scoped Topology ENNReal
open Filter Set MeasureTheory
open scoped Topology ContDiff
open Filter Set MeasureTheory
open scoped Topology ContDiff Laplacian
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ContDiff
open Filter Set MeasureTheory
open scoped Topology ENNReal
open Filter Set MeasureTheory
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory
open scoped Topology ENNReal ContDiff CompactlySupported
open Set MeasureTheory
open scoped Topology ENNReal ContDiff CompactlySupported
open Set MeasureTheory
open scoped Topology ENNReal ContDiff CompactlySupported
open Set MeasureTheory
open scoped Topology ContDiff
open Filter Set MeasureTheory
open scoped Topology ContDiff
open Filter Set MeasureTheory
open scoped Topology ContDiff
open Filter Set MeasureTheory
open scoped Topology ContDiff
open Filter Set MeasureTheory
open scoped Topology ContDiff
open Filter Set MeasureTheory
open scoped Topology ContDiff
open Filter Set MeasureTheory
open scoped Topology ContDiff Laplacian
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ContDiff Convolution
open Filter Set MeasureTheory
open scoped Topology ContDiff Convolution
open Filter Set MeasureTheory
open scoped Topology ContDiff Convolution
open Filter Set MeasureTheory
open scoped Topology ContDiff Convolution
open Filter Set MeasureTheory
open scoped Topology ContDiff Convolution
open Filter Set MeasureTheory
open scoped Topology ContDiff Convolution ENNReal
open Filter Set MeasureTheory
open scoped Topology ContDiff ENNReal
open Filter Set MeasureTheory
open scoped Topology ContDiff ENNReal
open Filter Set MeasureTheory
open scoped Topology ContDiff ENNReal
open Filter Set MeasureTheory
open scoped Topology ContDiff
open Filter Set MeasureTheory
open scoped Topology ContDiff
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ContDiff
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ContDiff
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ContDiff
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ContDiff
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ContDiff ENNReal
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ContDiff ENNReal
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ContDiff
open Filter Set MeasureTheory Function
open scoped Topology
open Filter Set MeasureTheory
open scoped Topology ENNReal
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ENNReal
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ENNReal
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ENNReal
open Filter Set MeasureTheory
open scoped Topology ENNReal
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ENNReal
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory InnerProductSpace
open scoped BigOperators
open Filter Set MeasureTheory
open scoped BigOperators
open scoped Topology ContDiff
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ContDiff
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ContDiff
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ContDiff
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ContDiff Convolution
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ContDiff
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ContDiff
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology
open Filter Set MeasureTheory
open scoped Topology ContDiff
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ENNReal ContDiff BigOperators
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ENNReal ContDiff BigOperators
open Filter Set MeasureTheory InnerProductSpace
open scoped BigOperators
open MeasureTheory
open scoped BigOperators
open Set MeasureTheory
open scoped BigOperators
open scoped Classical
open scoped BigOperators Topology ENNReal
open Set MeasureTheory
open scoped BigOperators
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory InnerProductSpace
open scoped BigOperators Classical Topology
open Filter Set MeasureTheory
open scoped BigOperators Classical Topology
open Filter Set MeasureTheory
open scoped BigOperators
open Set
open scoped BigOperators Topology
open Set MeasureTheory
open scoped BigOperators
open Set
open scoped BigOperators symmDiff
open Set
open scoped BigOperators
open Set
open scoped BigOperators symmDiff
open Set
open scoped BigOperators Classical
open Set
open scoped BigOperators
open Set
open scoped BigOperators Classical
open Set
open scoped BigOperators Classical
open Set
open scoped Topology ContDiff Convolution
open Filter Set MeasureTheory
open scoped Topology ContDiff Convolution
open Filter Set MeasureTheory
open scoped Topology ContDiff BigOperators
open Filter Set MeasureTheory
open scoped Topology ContDiff BigOperators
open Filter Set MeasureTheory
open scoped Topology ContDiff BigOperators
open Filter Set MeasureTheory
open scoped Topology ContDiff
open Filter Set MeasureTheory
open scoped Topology ContDiff
open Filter Set MeasureTheory
open scoped Topology ContDiff
open Filter Set MeasureTheory
open scoped Topology ContDiff
open Filter Set MeasureTheory ComplexConjugate
open scoped Topology ContDiff
open Filter Set MeasureTheory ComplexConjugate
open scoped Topology NNReal BoundedContinuousFunction
open Filter Set Metric
open scoped Topology ContDiff
open Filter Set MeasureTheory
open scoped Topology ContDiff BigOperators
open Filter Set MeasureTheory
open scoped Topology ContDiff BigOperators
open Filter Set MeasureTheory
open scoped Topology ComplexConjugate BigOperators
open Filter Set Metric Complex MeromorphicOn
open scoped Topology ComplexConjugate BigOperators
open Filter Set Metric Complex MeromorphicOn
open scoped Topology ComplexConjugate BigOperators
open Filter Set Metric Complex
open scoped Topology ContDiff ENNReal
open Set MeasureTheory Metric
open scoped Topology
open Set Metric
open scoped Topology ComplexConjugate BigOperators
open Filter Set Metric Complex MeromorphicOn
open scoped Topology
open Set Metric Complex
open scoped Topology
open Set Metric
open scoped Topology ContDiff ENNReal
open Set MeasureTheory Metric
open scoped Topology
open Set Metric Complex MeasureTheory
open scoped ENNReal Topology
open Set Metric MeasureTheory TopologicalSpace Function
open scoped Topology ENNReal
open Set Metric MeasureTheory Filter
open scoped Topology ENNReal
open Set Metric MeasureTheory Filter
open scoped Topology ENNReal
open Set Metric MeasureTheory
open scoped Topology ComplexConjugate BigOperators ENNReal
open Filter Set Metric Complex MeasureTheory MeromorphicOn
open scoped Topology ContDiff Convolution ENNReal
open Filter Set MeasureTheory Metric
open scoped Topology ContDiff NNReal ENNReal
open Filter Set Metric MeasureTheory
open scoped Topology ContDiff NNReal ENNReal
open Filter Set Metric MeasureTheory
open scoped Topology ContDiff ENNReal
open Filter Set MeasureTheory Metric
open scoped Topology ContDiff ENNReal
open Filter Set Metric MeasureTheory
open scoped Topology ContDiff ENNReal
open Filter Set Metric MeasureTheory
open scoped Topology ContDiff Convolution
open Filter Set Metric MeasureTheory
open scoped Topology ContDiff Convolution
open Filter Set Metric MeasureTheory

namespace SharpNodal.Profiles
open Carleman
namespace Elliptic

lemma coordMap_zero (u v : Plane → ℝ) (x : Plane) : coordMap u v x 0=u x := by simp [coordMap]
lemma coordMap_one (u v : Plane → ℝ) (x : Plane) : coordMap u v x 1=v x := by simp [coordMap]

lemma hasFDerivAt_coordMap {u v : Plane → ℝ} {x : Plane}
    (hu : DifferentiableAt ℝ u x) (hv : DifferentiableAt ℝ v x) :
    HasFDerivAt (coordMap u v)
      ((fderiv ℝ u x).smulRight (EuclideanSpace.single 0 1)+(fderiv ℝ v x).smulRight (EuclideanSpace.single 1 1)) x :=
  (hu.hasFDerivAt.smul_const _).add (hv.hasFDerivAt.smul_const _)

end Elliptic
end SharpNodal.Profiles

end

end OAI
end

section
-- module Solutions.OAIQ4_Nl.NodalLength_MetricFlux
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped ContDiff Bundle ENNReal
open Bundle Manifold MeasureTheory
open scoped ContDiff ENNReal Topology
open MeasureTheory Filter Set
open scoped Topology ENNReal
open MeasureTheory Filter Set
open scoped Topology ENNReal ContDiff
open MeasureTheory Filter Set
open scoped Topology ENNReal ContDiff
open MeasureTheory Filter Set
open scoped Topology ENNReal ContDiff
open MeasureTheory Filter Set
open scoped Topology ContDiff
open Filter Set
open scoped Topology ContDiff
open Filter Set
open scoped Topology ENNReal
open Filter Set MeasureTheory TopologicalSpace
open scoped Topology ContDiff
open Filter Set
open scoped Topology ENNReal
open Filter Set MeasureTheory TopologicalSpace
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory TopologicalSpace
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory Laplacian
open scoped Topology ENNReal ContDiff ComplexConjugate
open Filter Set MeasureTheory Laplacian
open scoped Topology ENNReal ContDiff ComplexConjugate
open Filter Set MeasureTheory Laplacian
open scoped Topology ENNReal NNReal
open Filter Set MeasureTheory
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory
open scoped Topology ENNReal
open Set MeasureTheory Filter
open scoped Topology ENNReal
open Filter Set MeasureTheory
open scoped Topology ENNReal
open Filter Set MeasureTheory
open scoped Topology ENNReal
open Filter Set MeasureTheory
open scoped Topology ContDiff
open Filter Set MeasureTheory
open scoped Topology ContDiff Laplacian
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ContDiff
open Filter Set MeasureTheory
open scoped Topology ENNReal
open Filter Set MeasureTheory
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory
open scoped Topology ENNReal ContDiff CompactlySupported
open Set MeasureTheory
open scoped Topology ENNReal ContDiff CompactlySupported
open Set MeasureTheory
open scoped Topology ENNReal ContDiff CompactlySupported
open Set MeasureTheory
open scoped Topology ContDiff
open Filter Set MeasureTheory
open scoped Topology ContDiff
open Filter Set MeasureTheory
open scoped Topology ContDiff
open Filter Set MeasureTheory
open scoped Topology ContDiff
open Filter Set MeasureTheory
open scoped Topology ContDiff
open Filter Set MeasureTheory
open scoped Topology ContDiff
open Filter Set MeasureTheory
open scoped Topology ContDiff Laplacian
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ContDiff Convolution
open Filter Set MeasureTheory
open scoped Topology ContDiff Convolution
open Filter Set MeasureTheory
open scoped Topology ContDiff Convolution
open Filter Set MeasureTheory
open scoped Topology ContDiff Convolution
open Filter Set MeasureTheory
open scoped Topology ContDiff Convolution
open Filter Set MeasureTheory
open scoped Topology ContDiff Convolution ENNReal
open Filter Set MeasureTheory
open scoped Topology ContDiff ENNReal
open Filter Set MeasureTheory
open scoped Topology ContDiff ENNReal
open Filter Set MeasureTheory
open scoped Topology ContDiff ENNReal
open Filter Set MeasureTheory
open scoped Topology ContDiff
open Filter Set MeasureTheory
open scoped Topology ContDiff
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ContDiff
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ContDiff
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ContDiff
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ContDiff
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ContDiff ENNReal
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ContDiff ENNReal
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ContDiff
open Filter Set MeasureTheory Function
open scoped Topology
open Filter Set MeasureTheory
open scoped Topology ENNReal
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ENNReal
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ENNReal
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ENNReal
open Filter Set MeasureTheory
open scoped Topology ENNReal
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ENNReal
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory InnerProductSpace
open scoped BigOperators
open Filter Set MeasureTheory
open scoped BigOperators
open scoped Topology ContDiff
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ContDiff
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ContDiff
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ContDiff
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ContDiff Convolution
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ContDiff
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ContDiff
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology
open Filter Set MeasureTheory
open scoped Topology ContDiff
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ENNReal ContDiff BigOperators
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ENNReal ContDiff BigOperators
open Filter Set MeasureTheory InnerProductSpace
open scoped BigOperators
open MeasureTheory
open scoped BigOperators
open Set MeasureTheory
open scoped BigOperators
open scoped Classical
open scoped BigOperators Topology ENNReal
open Set MeasureTheory
open scoped BigOperators
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory InnerProductSpace
open scoped BigOperators Classical Topology
open Filter Set MeasureTheory
open scoped BigOperators Classical Topology
open Filter Set MeasureTheory
open scoped BigOperators
open Set
open scoped BigOperators Topology
open Set MeasureTheory
open scoped BigOperators
open Set
open scoped BigOperators symmDiff
open Set
open scoped BigOperators
open Set
open scoped BigOperators symmDiff
open Set
open scoped BigOperators Classical
open Set
open scoped BigOperators
open Set
open scoped BigOperators Classical
open Set
open scoped BigOperators Classical
open Set
open scoped Topology ContDiff Convolution
open Filter Set MeasureTheory
open scoped Topology ContDiff Convolution
open Filter Set MeasureTheory
open scoped Topology ContDiff BigOperators
open Filter Set MeasureTheory
open scoped Topology ContDiff BigOperators
open Filter Set MeasureTheory
open scoped Topology ContDiff BigOperators
open Filter Set MeasureTheory
open scoped Topology ContDiff
open Filter Set MeasureTheory
open scoped Topology ContDiff
open Filter Set MeasureTheory
open scoped Topology ContDiff
open Filter Set MeasureTheory
open scoped Topology ContDiff
open Filter Set MeasureTheory ComplexConjugate
open scoped Topology ContDiff
open Filter Set MeasureTheory ComplexConjugate
open scoped Topology NNReal BoundedContinuousFunction
open Filter Set Metric
open scoped Topology ContDiff
open Filter Set MeasureTheory
open scoped Topology ContDiff BigOperators
open Filter Set MeasureTheory
open scoped Topology ContDiff BigOperators
open Filter Set MeasureTheory
open scoped Topology ComplexConjugate BigOperators
open Filter Set Metric Complex MeromorphicOn
open scoped Topology ComplexConjugate BigOperators
open Filter Set Metric Complex MeromorphicOn
open scoped Topology ComplexConjugate BigOperators
open Filter Set Metric Complex
open scoped Topology ContDiff ENNReal
open Set MeasureTheory Metric
open scoped Topology
open Set Metric
open scoped Topology ComplexConjugate BigOperators
open Filter Set Metric Complex MeromorphicOn
open scoped Topology
open Set Metric Complex
open scoped Topology
open Set Metric
open scoped Topology ContDiff ENNReal
open Set MeasureTheory Metric
open scoped Topology
open Set Metric Complex MeasureTheory
open scoped ENNReal Topology
open Set Metric MeasureTheory TopologicalSpace Function
open scoped Topology ENNReal
open Set Metric MeasureTheory Filter
open scoped Topology ENNReal
open Set Metric MeasureTheory Filter
open scoped Topology ENNReal
open Set Metric MeasureTheory
open scoped Topology ComplexConjugate BigOperators ENNReal
open Filter Set Metric Complex MeasureTheory MeromorphicOn
open scoped Topology ContDiff Convolution ENNReal
open Filter Set MeasureTheory Metric
open scoped Topology ContDiff NNReal ENNReal
open Filter Set Metric MeasureTheory
open scoped Topology ContDiff NNReal ENNReal
open Filter Set Metric MeasureTheory
open scoped Topology ContDiff ENNReal
open Filter Set MeasureTheory Metric
open scoped Topology ContDiff ENNReal
open Filter Set Metric MeasureTheory
open scoped Topology ContDiff ENNReal
open Filter Set Metric MeasureTheory
open scoped Topology ContDiff Convolution
open Filter Set Metric MeasureTheory
open scoped Topology ContDiff Convolution
open Filter Set Metric MeasureTheory
open scoped Topology ContDiff
open Filter Set Metric

namespace SharpNodal.Geometry
open Carleman Profiles.Elliptic

lemma partial_congr_nhds {f g : Plane → ℝ} {x : Plane} (h : f=ᶠ[𝓝 x]g) (i : Fin 2) :
    coordPartial f i x=coordPartial g i x := by unfold coordPartial; rw [h.fderiv_eq]

lemma differentiableAt_coordMap {f g : Plane → ℝ} {x : Plane}
    (hf : DifferentiableAt ℝ f x) (hg : DifferentiableAt ℝ g x) :
    DifferentiableAt ℝ (coordMap f g) x := (hasFDerivAt_coordMap hf hg).differentiableAt
lemma partial_comp_coordMap {f g U : Plane → ℝ} {x : Plane}
    (hf : DifferentiableAt ℝ f x) (hg : DifferentiableAt ℝ g x)
    (hU : DifferentiableAt ℝ U (coordMap f g x)) (i : Fin 2) :
    coordPartial (fun y=>U (coordMap f g y)) i x=
      coordPartial U 0 (coordMap f g x)*coordPartial f i x+
      coordPartial U 1 (coordMap f g x)*coordPartial g i x := by
  unfold coordPartial
  rw [fderiv_fun_comp x hU (differentiableAt_coordMap hf hg),(hasFDerivAt_coordMap hf hg).fderiv]
  simp only [ContinuousLinearMap.comp_apply,add_apply,ContinuousLinearMap.smulRight_apply,
    map_add,map_smul,smul_eq_mul]
  ring

end SharpNodal.Geometry
end

end OAI
end

section
-- module Solutions.OAIQ4_Nl.NodalLength_NormalizedCharts
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped ContDiff Bundle ENNReal
open Bundle Manifold MeasureTheory
open scoped ContDiff ENNReal Topology
open MeasureTheory Filter Set
open scoped Topology ENNReal
open MeasureTheory Filter Set
open scoped Topology ENNReal ContDiff
open MeasureTheory Filter Set
open scoped Topology ENNReal ContDiff
open MeasureTheory Filter Set
open scoped Topology ENNReal ContDiff
open MeasureTheory Filter Set
open scoped Topology ContDiff
open Filter Set
open scoped Topology ContDiff
open Filter Set
open scoped Topology ENNReal
open Filter Set MeasureTheory TopologicalSpace
open scoped Topology ContDiff
open Filter Set
open scoped Topology ENNReal
open Filter Set MeasureTheory TopologicalSpace
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory TopologicalSpace
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory Laplacian
open scoped Topology ENNReal ContDiff ComplexConjugate
open Filter Set MeasureTheory Laplacian
open scoped Topology ENNReal ContDiff ComplexConjugate
open Filter Set MeasureTheory Laplacian
open scoped Topology ENNReal NNReal
open Filter Set MeasureTheory
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory
open scoped Topology ENNReal
open Set MeasureTheory Filter
open scoped Topology ENNReal
open Filter Set MeasureTheory
open scoped Topology ENNReal
open Filter Set MeasureTheory
open scoped Topology ENNReal
open Filter Set MeasureTheory
open scoped Topology ContDiff
open Filter Set MeasureTheory
open scoped Topology ContDiff Laplacian
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ContDiff
open Filter Set MeasureTheory
open scoped Topology ENNReal
open Filter Set MeasureTheory
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory
open scoped Topology ENNReal ContDiff CompactlySupported
open Set MeasureTheory
open scoped Topology ENNReal ContDiff CompactlySupported
open Set MeasureTheory
open scoped Topology ENNReal ContDiff CompactlySupported
open Set MeasureTheory
open scoped Topology ContDiff
open Filter Set MeasureTheory
open scoped Topology ContDiff
open Filter Set MeasureTheory
open scoped Topology ContDiff
open Filter Set MeasureTheory
open scoped Topology ContDiff
open Filter Set MeasureTheory
open scoped Topology ContDiff
open Filter Set MeasureTheory
open scoped Topology ContDiff
open Filter Set MeasureTheory
open scoped Topology ContDiff Laplacian
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ContDiff Convolution
open Filter Set MeasureTheory
open scoped Topology ContDiff Convolution
open Filter Set MeasureTheory
open scoped Topology ContDiff Convolution
open Filter Set MeasureTheory
open scoped Topology ContDiff Convolution
open Filter Set MeasureTheory
open scoped Topology ContDiff Convolution
open Filter Set MeasureTheory
open scoped Topology ContDiff Convolution ENNReal
open Filter Set MeasureTheory
open scoped Topology ContDiff ENNReal
open Filter Set MeasureTheory
open scoped Topology ContDiff ENNReal
open Filter Set MeasureTheory
open scoped Topology ContDiff ENNReal
open Filter Set MeasureTheory
open scoped Topology ContDiff
open Filter Set MeasureTheory
open scoped Topology ContDiff
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ContDiff
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ContDiff
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ContDiff
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ContDiff
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ContDiff ENNReal
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ContDiff ENNReal
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ContDiff
open Filter Set MeasureTheory Function
open scoped Topology
open Filter Set MeasureTheory
open scoped Topology ENNReal
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ENNReal
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ENNReal
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ENNReal
open Filter Set MeasureTheory
open scoped Topology ENNReal
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ENNReal
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory InnerProductSpace
open scoped BigOperators
open Filter Set MeasureTheory
open scoped BigOperators
open scoped Topology ContDiff
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ContDiff
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ContDiff
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ContDiff
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ContDiff Convolution
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ContDiff
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ContDiff
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology
open Filter Set MeasureTheory
open scoped Topology ContDiff
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ENNReal ContDiff BigOperators
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ENNReal ContDiff BigOperators
open Filter Set MeasureTheory InnerProductSpace
open scoped BigOperators
open MeasureTheory
open scoped BigOperators
open Set MeasureTheory
open scoped BigOperators
open scoped Classical
open scoped BigOperators Topology ENNReal
open Set MeasureTheory
open scoped BigOperators
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory InnerProductSpace
open scoped BigOperators Classical Topology
open Filter Set MeasureTheory
open scoped BigOperators Classical Topology
open Filter Set MeasureTheory
open scoped BigOperators
open Set
open scoped BigOperators Topology
open Set MeasureTheory
open scoped BigOperators
open Set
open scoped BigOperators symmDiff
open Set
open scoped BigOperators
open Set
open scoped BigOperators symmDiff
open Set
open scoped BigOperators Classical
open Set
open scoped BigOperators
open Set
open scoped BigOperators Classical
open Set
open scoped BigOperators Classical
open Set
open scoped Topology ContDiff Convolution
open Filter Set MeasureTheory
open scoped Topology ContDiff Convolution
open Filter Set MeasureTheory
open scoped Topology ContDiff BigOperators
open Filter Set MeasureTheory
open scoped Topology ContDiff BigOperators
open Filter Set MeasureTheory
open scoped Topology ContDiff BigOperators
open Filter Set MeasureTheory
open scoped Topology ContDiff
open Filter Set MeasureTheory
open scoped Topology ContDiff
open Filter Set MeasureTheory
open scoped Topology ContDiff
open Filter Set MeasureTheory
open scoped Topology ContDiff
open Filter Set MeasureTheory ComplexConjugate
open scoped Topology ContDiff
open Filter Set MeasureTheory ComplexConjugate
open scoped Topology NNReal BoundedContinuousFunction
open Filter Set Metric
open scoped Topology ContDiff
open Filter Set MeasureTheory
open scoped Topology ContDiff BigOperators
open Filter Set MeasureTheory
open scoped Topology ContDiff BigOperators
open Filter Set MeasureTheory
open scoped Topology ComplexConjugate BigOperators
open Filter Set Metric Complex MeromorphicOn
open scoped Topology ComplexConjugate BigOperators
open Filter Set Metric Complex MeromorphicOn
open scoped Topology ComplexConjugate BigOperators
open Filter Set Metric Complex
open scoped Topology ContDiff ENNReal
open Set MeasureTheory Metric
open scoped Topology
open Set Metric
open scoped Topology ComplexConjugate BigOperators
open Filter Set Metric Complex MeromorphicOn
open scoped Topology
open Set Metric Complex
open scoped Topology
open Set Metric
open scoped Topology ContDiff ENNReal
open Set MeasureTheory Metric
open scoped Topology
open Set Metric Complex MeasureTheory
open scoped ENNReal Topology
open Set Metric MeasureTheory TopologicalSpace Function
open scoped Topology ENNReal
open Set Metric MeasureTheory Filter
open scoped Topology ENNReal
open Set Metric MeasureTheory Filter
open scoped Topology ENNReal
open Set Metric MeasureTheory
open scoped Topology ComplexConjugate BigOperators ENNReal
open Filter Set Metric Complex MeasureTheory MeromorphicOn
open scoped Topology ContDiff Convolution ENNReal
open Filter Set MeasureTheory Metric
open scoped Topology ContDiff NNReal ENNReal
open Filter Set Metric MeasureTheory
open scoped Topology ContDiff NNReal ENNReal
open Filter Set Metric MeasureTheory
open scoped Topology ContDiff ENNReal
open Filter Set MeasureTheory Metric
open scoped Topology ContDiff ENNReal
open Filter Set Metric MeasureTheory
open scoped Topology ContDiff ENNReal
open Filter Set Metric MeasureTheory
open scoped Topology ContDiff Convolution
open Filter Set Metric MeasureTheory
open scoped Topology ContDiff Convolution
open Filter Set Metric MeasureTheory
open scoped Topology ContDiff
open Filter Set Metric
open scoped Matrix
open scoped Topology ContDiff
open Filter Set Metric
open scoped Topology ContDiff Bundle
open Filter Set Metric Bundle Manifold

namespace SharpNodal.Geometry
variable {M : Type*} [MetricSpace M] [ChartedSpace Plane M]
  [IsManifold 𝓘(ℝ, Plane) ∞ M]
  [RiemannianBundle (fun x : M=>TangentSpace 𝓘(ℝ,Plane) x)]
  [IsContMDiffRiemannianBundle 𝓘(ℝ,Plane) ∞ Plane (fun x:M=>TangentSpace 𝓘(ℝ,Plane) x)]

lemma gram_two_positive {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F]
    (D : Plane →L[ℝ] F) (hi : Function.Injective D) :
    0 < inner ℝ (D (EuclideanSpace.single 0 1)) (D (EuclideanSpace.single 0 1)) ∧
    0 < inner ℝ (D (EuclideanSpace.single 0 1)) (D (EuclideanSpace.single 0 1))*
      inner ℝ (D (EuclideanSpace.single 1 1)) (D (EuclideanSpace.single 1 1))-
      (inner ℝ (D (EuclideanSpace.single 0 1)) (D (EuclideanSpace.single 1 1)))^2 := by
  let v:=D (EuclideanSpace.single 0 1)
  let w:=D (EuclideanSpace.single 1 1)
  let a:=inner ℝ v v
  let b:=inner ℝ v w
  let c:=inner ℝ w w
  have hv : v≠0 := by
    intro hz
    have hh:=hi (hz.trans D.map_zero.symm)
    have := congrArg (fun z:Plane=>z 0) hh
    norm_num at this
  have ha : 0<a:=real_inner_self_pos.mpr hv
  have hw : a • w-b • v≠0 := by
    intro hz
    have he : D (a • EuclideanSpace.single 1 1-b • EuclideanSpace.single 0 1)=D 0 := by
      simpa only [map_sub,map_smul,map_zero] using hz
    have hh:=congrArg (fun z:Plane=>z 1) (hi he)
    norm_num at hh
    exact ha.ne' hh
  have hp:=real_inner_self_pos.mpr hw
  have hab : inner ℝ w v=b:=real_inner_comm _ _
  have he : inner ℝ (a • w-b • v) (a • w-b • v)=a*(a*c-b^2) := by
    simp only [inner_sub_left,inner_sub_right,inner_smul_left,inner_smul_right,
      RCLike.conj_to_real,hab]
    dsimp [a,b,c]; ring
  rw [he] at hp
  exact ⟨ha,(mul_pos_iff.mp hp).resolve_right (fun h=>not_lt_of_ge ha.le h.1) |>.2⟩

omit [IsManifold 𝓘(ℝ,Plane) ∞ M]
  [RiemannianBundle (fun x : M=>TangentSpace 𝓘(ℝ,Plane) x)]
  [IsContMDiffRiemannianBundle 𝓘(ℝ,Plane) ∞ Plane (fun x:M=>TangentSpace 𝓘(ℝ,Plane) x)] in
lemma ChartSmooth.mdiff {e : OpenPartialHomeomorph M Plane} (he : ChartSmooth e) :
    e.MDifferentiable 𝓘(ℝ,Plane) 𝓘(ℝ,Plane) :=
  ⟨he.1.mdifferentiableOn (by simp),he.2.mdifferentiableOn (by simp)⟩

omit [IsManifold 𝓘(ℝ,Plane) ∞ M]
  [IsContMDiffRiemannianBundle 𝓘(ℝ,Plane) ∞ Plane (fun x:M=>TangentSpace 𝓘(ℝ,Plane) x)] in
lemma ChartSmooth.metric_positive {e : OpenPartialHomeomorph M Plane} (he : ChartSmooth e)
    {y : Plane} (hy : y∈e.target) : 0<pullMetric (e.symm : Plane → M) y 0 0 ∧
      0<(pullMetric (e.symm : Plane → M) y).det := by
  have hh:=gram_two_positive (mfderiv 𝓘(ℝ,Plane) 𝓘(ℝ,Plane) e.symm y)
    (he.mdiff.symm.mfderiv_injective hy)
  refine ⟨hh.1,?_⟩
  have hp : 0<pullMetric (e.symm : Plane → M) y 0 0*pullMetric (e.symm : Plane → M) y 1 1-
      (pullMetric (e.symm : Plane → M) y 0 1)^2:=hh.2
  have hc : pullMetric (e.symm : Plane → M) y 1 0=pullMetric (e.symm : Plane → M) y 0 1 :=
    real_inner_comm _ _
  rw [Matrix.det_fin_two,hc]
  nlinarith [hp]

end SharpNodal.Geometry

noncomputable section
open scoped Topology ContDiff Bundle
open Filter Set Metric Bundle Manifold
namespace SharpNodal.Geometry
open Carleman Profiles.Elliptic

variable {M : Type*} [MetricSpace M] [ChartedSpace Plane M]
  [IsManifold 𝓘(ℝ, Plane) ∞ M]
  [RiemannianBundle (fun x : M=>TangentSpace 𝓘(ℝ,Plane) x)]
  [IsContMDiffRiemannianBundle 𝓘(ℝ,Plane) ∞ Plane (fun x:M=>TangentSpace 𝓘(ℝ,Plane) x)]

omit [IsManifold 𝓘(ℝ,Plane) ∞ M]
  [IsContMDiffRiemannianBundle 𝓘(ℝ,Plane) ∞ Plane (fun x:M=>TangentSpace 𝓘(ℝ,Plane) x)] in
lemma pullMetric_symm (F : Plane → M) (y : Plane) (i j : Fin 2) :
    pullMetric F y i j=pullMetric F y j i := real_inner_comm _ _

omit [IsManifold 𝓘(ℝ,Plane) ∞ M]
  [IsContMDiffRiemannianBundle 𝓘(ℝ,Plane) ∞ Plane (fun x:M=>TangentSpace 𝓘(ℝ,Plane) x)] in
lemma pullMetric_transform {F : Plane → M} {f g : Plane → ℝ} {x : Plane}
    (hF : MDifferentiableAt 𝓘(ℝ,Plane) 𝓘(ℝ,Plane) F (coordMap f g x))
    (hf : DifferentiableAt ℝ f x) (hg : DifferentiableAt ℝ g x) (i j : Fin 2) :
    pullMetric (fun y=>F (coordMap f g y)) x i j=
      pullMetric F (coordMap f g x) 0 0*coordPartial f i x*coordPartial f j x+
      pullMetric F (coordMap f g x) 0 1*(coordPartial f i x*coordPartial g j x+
        coordPartial f j x*coordPartial g i x)+
      pullMetric F (coordMap f g x) 1 1*coordPartial g i x*coordPartial g j x := by
  have hp : MDifferentiableAt 𝓘(ℝ,Plane) 𝓘(ℝ,Plane) (coordMap f g) x:=
    (differentiableAt_coordMap hf hg).mdifferentiableAt
  have hd:=mfderiv_comp x hF hp
  rw [mfderiv_eq_fderiv,(hasFDerivAt_coordMap hf hg).fderiv] at hd
  have he (k : Fin 2) : mfderiv 𝓘(ℝ,Plane) 𝓘(ℝ,Plane) (fun y=>F (coordMap f g y)) x (EuclideanSpace.single k 1)=
      coordPartial f k x • mfderiv 𝓘(ℝ,Plane) 𝓘(ℝ,Plane) F (coordMap f g x) (EuclideanSpace.single 0 1)+
      coordPartial g k x • mfderiv 𝓘(ℝ,Plane) 𝓘(ℝ,Plane) F (coordMap f g x) (EuclideanSpace.single 1 1) := by
    erw [hd]
    change mfderiv 𝓘(ℝ,Plane) 𝓘(ℝ,Plane) F (coordMap f g x) (_ + _) = _
    erw [map_add, map_smul, map_smul]
    rfl
  unfold pullMetric
  erw [he i,he j]
  simp only [inner_add_left,inner_add_right,inner_smul_left,inner_smul_right,RCLike.conj_to_real]
  have hs:=real_inner_comm
    (mfderiv 𝓘(ℝ,Plane) 𝓘(ℝ,Plane) F (coordMap f g x) (EuclideanSpace.single 1 1))
    (mfderiv 𝓘(ℝ,Plane) 𝓘(ℝ,Plane) F (coordMap f g x) (EuclideanSpace.single 0 1))
  rw [hs]; ring

omit [IsManifold 𝓘(ℝ,Plane) ∞ M]
  [IsContMDiffRiemannianBundle 𝓘(ℝ,Plane) ∞ Plane (fun x:M=>TangentSpace 𝓘(ℝ,Plane) x)] in
lemma pullMetric_transform_three {F : Plane → M} {f g : Plane → ℝ} {x : Plane}
    (hF : MDifferentiableAt 𝓘(ℝ,Plane) 𝓘(ℝ,Plane) F (coordMap f g x))
    (hf : DifferentiableAt ℝ f x) (hg : DifferentiableAt ℝ g x) :
    let a:=fun y=>pullMetric F y 0 0
    let b:=fun y=>pullMetric F y 0 1
    let c:=fun y=>pullMetric F y 1 1
    pullMetric (fun y=>F (coordMap f g y)) x 0 0=transformA a b c f g x ∧
    pullMetric (fun y=>F (coordMap f g y)) x 0 1=transformB a b c f g x ∧
    pullMetric (fun y=>F (coordMap f g y)) x 1 1=transformC a b c f g x := by
  dsimp
  rw [pullMetric_transform hF hf hg 0 0,pullMetric_transform hF hf hg 0 1,
    pullMetric_transform hF hf hg 1 1]
  unfold transformA transformB transformC
  exact ⟨by ring,by ring,by ring⟩

end SharpNodal.Geometry

end
end

end OAI
end

section
-- module Solutions.OAIQ4_Nl.NodalLength_Conductivity
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped ContDiff Bundle ENNReal
open Bundle Manifold MeasureTheory
open scoped ContDiff ENNReal Topology
open MeasureTheory Filter Set
open scoped Topology ENNReal
open MeasureTheory Filter Set
open scoped Topology ENNReal ContDiff
open MeasureTheory Filter Set
open scoped Topology ENNReal ContDiff
open MeasureTheory Filter Set
open scoped Topology ENNReal ContDiff
open MeasureTheory Filter Set
open scoped Topology ContDiff
open Filter Set
open scoped Topology ContDiff
open Filter Set
open scoped Topology ENNReal
open Filter Set MeasureTheory TopologicalSpace
open scoped Topology ContDiff
open Filter Set
open scoped Topology ENNReal
open Filter Set MeasureTheory TopologicalSpace
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory TopologicalSpace
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory Laplacian
open scoped Topology ENNReal ContDiff ComplexConjugate
open Filter Set MeasureTheory Laplacian
open scoped Topology ENNReal ContDiff ComplexConjugate
open Filter Set MeasureTheory Laplacian
open scoped Topology ENNReal NNReal
open Filter Set MeasureTheory
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory
open scoped Topology ENNReal
open Set MeasureTheory Filter
open scoped Topology ENNReal
open Filter Set MeasureTheory
open scoped Topology ENNReal
open Filter Set MeasureTheory
open scoped Topology ENNReal
open Filter Set MeasureTheory
open scoped Topology ContDiff
open Filter Set MeasureTheory
open scoped Topology ContDiff Laplacian
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ContDiff
open Filter Set MeasureTheory
open scoped Topology ENNReal
open Filter Set MeasureTheory
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory
open scoped Topology ENNReal ContDiff CompactlySupported
open Set MeasureTheory
open scoped Topology ENNReal ContDiff CompactlySupported
open Set MeasureTheory
open scoped Topology ENNReal ContDiff CompactlySupported
open Set MeasureTheory
open scoped Topology ContDiff
open Filter Set MeasureTheory
open scoped Topology ContDiff
open Filter Set MeasureTheory
open scoped Topology ContDiff
open Filter Set MeasureTheory
open scoped Topology ContDiff
open Filter Set MeasureTheory
open scoped Topology ContDiff
open Filter Set MeasureTheory
open scoped Topology ContDiff
open Filter Set MeasureTheory
open scoped Topology ContDiff Laplacian
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ContDiff Convolution
open Filter Set MeasureTheory
open scoped Topology ContDiff Convolution
open Filter Set MeasureTheory
open scoped Topology ContDiff Convolution
open Filter Set MeasureTheory
open scoped Topology ContDiff Convolution
open Filter Set MeasureTheory
open scoped Topology ContDiff Convolution
open Filter Set MeasureTheory
open scoped Topology ContDiff Convolution ENNReal
open Filter Set MeasureTheory
open scoped Topology ContDiff ENNReal
open Filter Set MeasureTheory
open scoped Topology ContDiff ENNReal
open Filter Set MeasureTheory
open scoped Topology ContDiff ENNReal
open Filter Set MeasureTheory
open scoped Topology ContDiff
open Filter Set MeasureTheory
open scoped Topology ContDiff
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ContDiff
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ContDiff
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ContDiff
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ContDiff
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ContDiff ENNReal
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ContDiff ENNReal
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ContDiff
open Filter Set MeasureTheory Function
open scoped Topology
open Filter Set MeasureTheory
open scoped Topology ENNReal
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ENNReal
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ENNReal
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ENNReal
open Filter Set MeasureTheory
open scoped Topology ENNReal
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ENNReal
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory InnerProductSpace
open scoped BigOperators
open Filter Set MeasureTheory
open scoped BigOperators
open scoped Topology ContDiff
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ContDiff
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ContDiff
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ContDiff
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ContDiff Convolution
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ContDiff
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ContDiff
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology
open Filter Set MeasureTheory
open scoped Topology ContDiff
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ENNReal ContDiff BigOperators
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ENNReal ContDiff BigOperators
open Filter Set MeasureTheory InnerProductSpace
open scoped BigOperators
open MeasureTheory
open scoped BigOperators
open Set MeasureTheory
open scoped BigOperators
open scoped Classical
open scoped BigOperators Topology ENNReal
open Set MeasureTheory
open scoped BigOperators
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory InnerProductSpace
open scoped BigOperators Classical Topology
open Filter Set MeasureTheory
open scoped BigOperators Classical Topology
open Filter Set MeasureTheory
open scoped BigOperators
open Set
open scoped BigOperators Topology
open Set MeasureTheory
open scoped BigOperators
open Set
open scoped BigOperators symmDiff
open Set
open scoped BigOperators
open Set
open scoped BigOperators symmDiff
open Set
open scoped BigOperators Classical
open Set
open scoped BigOperators
open Set
open scoped BigOperators Classical
open Set
open scoped BigOperators Classical
open Set
open scoped Topology ContDiff Convolution
open Filter Set MeasureTheory
open scoped Topology ContDiff Convolution
open Filter Set MeasureTheory
open scoped Topology ContDiff BigOperators
open Filter Set MeasureTheory
open scoped Topology ContDiff BigOperators
open Filter Set MeasureTheory
open scoped Topology ContDiff BigOperators
open Filter Set MeasureTheory
open scoped Topology ContDiff
open Filter Set MeasureTheory
open scoped Topology ContDiff
open Filter Set MeasureTheory
open scoped Topology ContDiff
open Filter Set MeasureTheory
open scoped Topology ContDiff
open Filter Set MeasureTheory ComplexConjugate
open scoped Topology ContDiff
open Filter Set MeasureTheory ComplexConjugate
open scoped Topology NNReal BoundedContinuousFunction
open Filter Set Metric
open scoped Topology ContDiff
open Filter Set MeasureTheory
open scoped Topology ContDiff BigOperators
open Filter Set MeasureTheory
open scoped Topology ContDiff BigOperators
open Filter Set MeasureTheory
open scoped Topology ComplexConjugate BigOperators
open Filter Set Metric Complex MeromorphicOn
open scoped Topology ComplexConjugate BigOperators
open Filter Set Metric Complex MeromorphicOn
open scoped Topology ComplexConjugate BigOperators
open Filter Set Metric Complex
open scoped Topology ContDiff ENNReal
open Set MeasureTheory Metric
open scoped Topology
open Set Metric
open scoped Topology ComplexConjugate BigOperators
open Filter Set Metric Complex MeromorphicOn
open scoped Topology
open Set Metric Complex
open scoped Topology
open Set Metric
open scoped Topology ContDiff ENNReal
open Set MeasureTheory Metric
open scoped Topology
open Set Metric Complex MeasureTheory
open scoped ENNReal Topology
open Set Metric MeasureTheory TopologicalSpace Function
open scoped Topology ENNReal
open Set Metric MeasureTheory Filter
open scoped Topology ENNReal
open Set Metric MeasureTheory Filter
open scoped Topology ENNReal
open Set Metric MeasureTheory
open scoped Topology ComplexConjugate BigOperators ENNReal
open Filter Set Metric Complex MeasureTheory MeromorphicOn
open scoped Topology ContDiff Convolution ENNReal
open Filter Set MeasureTheory Metric
open scoped Topology ContDiff NNReal ENNReal
open Filter Set Metric MeasureTheory
open scoped Topology ContDiff NNReal ENNReal
open Filter Set Metric MeasureTheory
open scoped Topology ContDiff ENNReal
open Filter Set MeasureTheory Metric
open scoped Topology ContDiff ENNReal
open Filter Set Metric MeasureTheory
open scoped Topology ContDiff ENNReal
open Filter Set Metric MeasureTheory
open scoped Topology ContDiff Convolution
open Filter Set Metric MeasureTheory
open scoped Topology ContDiff Convolution
open Filter Set Metric MeasureTheory
open scoped Topology ContDiff
open Filter Set Metric
open scoped Matrix
open scoped Topology ContDiff
open Filter Set Metric
open scoped Topology ContDiff Bundle
open Filter Set Metric Bundle Manifold
open scoped Topology ContDiff Bundle
open Filter Set Metric Bundle Manifold
open scoped Topology ContDiff
open Filter Set Metric
open scoped Topology ContDiff Bundle
open Filter Set Metric Bundle Manifold

namespace SharpNodal.Geometry
open Carleman Profiles.Elliptic

lemma coordMap_components (F : Plane → Plane) :
    coordMap (fun x=>F x 0) (fun x=>F x 1)=F := by
  funext x
  ext i
  fin_cases i <;> simp [coordMap]

lemma smoothAt_component {F : Plane → Plane} {x : Plane} (hF : ContDiffAt ℝ ∞ F x) (i : Fin 2) :
    ContDiffAt ℝ ∞ (fun y=>F y i) x :=
  (EuclideanSpace.proj i : Plane →L[ℝ] ℝ).contDiff.contDiffAt.comp x hF

lemma coordPartial_component (i j : Fin 2) (x : Plane) :
    coordPartial (fun y:Plane=>y i) j x=if i=j then 1 else 0 := by
  unfold coordPartial
  change (fderiv ℝ (EuclideanSpace.proj i : Plane →L[ℝ] ℝ) x) (EuclideanSpace.single j 1)=_
  rw [(EuclideanSpace.proj i : Plane →L[ℝ] ℝ).fderiv]
  simp [EuclideanSpace.proj]

lemma inverse_coordinate_equations {e : OpenPartialHomeomorph Plane Plane} {u v : Plane → ℝ}
    (he : (e : Plane → Plane)=coordMap u v)
    (hu : ContDiffOn ℝ ∞ u e.source) (hv : ContDiffOn ℝ ∞ v e.source)
    (hi : ContDiffOn ℝ ∞ (e.symm : Plane → Plane) e.target) {y : Plane} (hy : y∈e.target) (i : Fin 2) :
    coordPartial u 0 (e.symm y)*coordPartial (fun z=>e.symm z 0) i y+
      coordPartial u 1 (e.symm y)*coordPartial (fun z=>e.symm z 1) i y=(if (0:Fin 2)=i then 1 else 0) ∧
    coordPartial v 0 (e.symm y)*coordPartial (fun z=>e.symm z 0) i y+
      coordPartial v 1 (e.symm y)*coordPartial (fun z=>e.symm z 1) i y=(if (1:Fin 2)=i then 1 else 0) := by
  have h0:=(smoothAt_component (hi.contDiffAt (e.open_target.mem_nhds hy)) 0).differentiableAt (by simp)
  have h1:=(smoothAt_component (hi.contDiffAt (e.open_target.mem_nhds hy)) 1).differentiableAt (by simp)
  have hud:=(hu.contDiffAt (e.open_source.mem_nhds (e.map_target hy))).differentiableAt (by simp)
  have hvd:=(hv.contDiffAt (e.open_source.mem_nhds (e.map_target hy))).differentiableAt (by simp)
  have hucomp : (fun z=>u (e.symm z))=ᶠ[𝓝 y]fun z=>z 0 := by
    filter_upwards [e.open_target.mem_nhds hy] with z hz
    have hh:=congrArg (fun x:Plane=>x 0) (e.right_inv hz)
    simpa only [he,coordMap_zero] using hh
  have hvcomp : (fun z=>v (e.symm z))=ᶠ[𝓝 y]fun z=>z 1 := by
    filter_upwards [e.open_target.mem_nhds hy] with z hz
    have hh:=congrArg (fun x:Plane=>x 1) (e.right_inv hz)
    simpa only [he,coordMap_one] using hh
  have hd (f : Plane → ℝ) (hf : DifferentiableAt ℝ f (e.symm y)) :=
    partial_comp_coordMap h0 h1 (show DifferentiableAt ℝ f (coordMap (fun z=>e.symm z 0) (fun z=>e.symm z 1) y) from by rwa [coordMap_components]) i
  have hdu:=hd u hud
  have hdv:=hd v hvd
  rw [coordMap_components] at hdu hdv
  constructor
  · rw [← hdu,partial_congr_nhds hucomp,coordPartial_component]
  · rw [← hdv,partial_congr_nhds hvcomp,coordPartial_component]

end SharpNodal.Geometry
noncomputable section
namespace SharpNodal.Geometry

lemma inverse_jacobian_entries {r s v w α β γ δ : ℝ}
    (hd : r*w-s*v≠0) (h00 : r*α+s*γ=1) (h01 : r*β+s*δ=0)
    (h10 : v*α+w*γ=0) (h11 : v*β+w*δ=1) :
    α=w/(r*w-s*v) ∧ β= -s/(r*w-s*v) ∧ γ= -v/(r*w-s*v) ∧ δ=r/(r*w-s*v) := by
  constructor
  · apply (eq_div_iff hd).mpr
    linear_combination w*h00-s*h10
  constructor
  · apply (eq_div_iff hd).mpr
    linear_combination w*h01-s*h11
  constructor
  · apply (eq_div_iff hd).mpr
    linear_combination r*h10-v*h00
  · apply (eq_div_iff hd).mpr
    linear_combination r*h11-v*h01

lemma conjugate_inverse_metric_numerators {a b c ρ r s : ℝ} (hρ : ρ≠0)
    (hdet : ρ^2=a*c-b^2) :
    let v:=(b*r-a*s)/ρ
    let w:=(c*r-b*s)/ρ
    let d:=r*w-s*v
    a*w^2-2*b*w*v+c*v^2=ρ*d ∧
    -a*w*s+b*(w*r+s*v)-c*v*r=0 ∧ a*s^2-2*b*s*r+c*r^2=ρ*d := by
  dsimp
  constructor
  · field_simp [hρ]
    linear_combination -(c*r^2-2*b*r*s+a*s^2)*hdet
  constructor
  · field_simp [hρ]
    ring
  · field_simp [hρ]
    ring

lemma conformal_inverse_metric {a b c ρ r s v w α β γ δ : ℝ}
    (hρ : ρ≠0) (hdet : ρ^2=a*c-b^2)
    (hv : v=(b*r-a*s)/ρ) (hw : w=(c*r-b*s)/ρ)
    (hd : r*w-s*v≠0) (h00 : r*α+s*γ=1) (h01 : r*β+s*δ=0)
    (h10 : v*α+w*γ=0) (h11 : v*β+w*δ=1) :
    a*α^2+2*b*α*γ+c*γ^2=ρ/(r*w-s*v) ∧
    a*α*β+b*(α*δ+β*γ)+c*γ*δ=0 ∧
    a*β^2+2*b*β*δ+c*δ^2=ρ/(r*w-s*v) := by
  obtain ⟨rfl,rfl,rfl,rfl⟩:=inverse_jacobian_entries hd h00 h01 h10 h11
  have hn:=conjugate_inverse_metric_numerators (r:=r) (s:=s) hρ hdet
  rw [← hv,← hw] at hn
  constructor
  · calc
      _ = (a*w^2-2*b*w*v+c*v^2)/(r*w-s*v)^2 := by simp only [div_eq_mul_inv,← inv_pow]; ring
      _ = ρ/(r*w-s*v) := by rw [hn.1]; field_simp
  constructor
  · calc
      _ = (-a*w*s+b*(w*r+s*v)-c*v*r)/(r*w-s*v)^2 := by simp only [div_eq_mul_inv,← inv_pow]; ring
      _ = 0 := by rw [hn.2.1]; simp
  · calc
      _ = (a*s^2-2*b*s*r+c*r^2)/(r*w-s*v)^2 := by simp only [div_eq_mul_inv,← inv_pow]; ring
      _ = ρ/(r*w-s*v) := by rw [hn.2.2]; field_simp

end SharpNodal.Geometry

noncomputable section
open scoped Topology ContDiff Bundle
open Filter Set Metric Bundle Manifold
namespace SharpNodal.Geometry
open Carleman Profiles.Elliptic

variable {M : Type*} [MetricSpace M] [ChartedSpace Plane M]
  [IsManifold 𝓘(ℝ,Plane) ∞ M]
  [RiemannianBundle (fun x:M=>TangentSpace 𝓘(ℝ,Plane) x)]
  [IsContMDiffRiemannianBundle 𝓘(ℝ,Plane) ∞ Plane (fun x:M=>TangentSpace 𝓘(ℝ,Plane) x)]

omit [IsManifold 𝓘(ℝ,Plane) ∞ M] [IsContMDiffRiemannianBundle 𝓘(ℝ,Plane) ∞ Plane (fun x:M=>TangentSpace 𝓘(ℝ,Plane) x)] in
lemma conjugate_chart_conformal_oai {E : OpenPartialHomeomorph M Plane}
    {e : OpenPartialHomeomorph Plane Plane} {u v : Plane → ℝ}
    (hE : ChartSmooth E) (he : (e : Plane → Plane)=coordMap u v)
    (hu : ContDiffOn ℝ ∞ u e.source) (hv : ContDiffOn ℝ ∞ v e.source)
    (hi : ContDiffOn ℝ ∞ (e.symm : Plane → Plane) e.target)
    (hc : ∀x∈e.source,
      coordPartial v 0 x=(pullMetric (E.symm : Plane → M) x 0 1*coordPartial u 0 x-
        pullMetric (E.symm : Plane → M) x 0 0*coordPartial u 1 x)/
          Real.sqrt (pullMetric (E.symm : Plane → M) x).det ∧
      coordPartial v 1 x=(pullMetric (E.symm : Plane → M) x 1 1*coordPartial u 0 x-
        pullMetric (E.symm : Plane → M) x 0 1*coordPartial u 1 x)/
          Real.sqrt (pullMetric (E.symm : Plane → M) x).det)
    (hD : ∀x∈e.source,0 < coordDet u v x) {y : Plane} (hy : y∈(E.trans e).target) :
    ∃p : ℝ,0<p ∧ pullMetric ((E.trans e).symm : Plane → M) y=p • (1 : Matrix (Fin 2) (Fin 2) ℝ) := by
  have hy0 : y∈e.target:=hy.1
  have hx : e.symm y∈e.source:=e.map_target hy0
  have hxE : e.symm y∈E.target:=hy.2
  let a:=fun x=>pullMetric (E.symm : Plane → M) x 0 0
  let b:=fun x=>pullMetric (E.symm : Plane → M) x 0 1
  let c:=fun x=>pullMetric (E.symm : Plane → M) x 1 1
  let ρ:=Real.sqrt (pullMetric (E.symm : Plane → M) (e.symm y)).det
  have hρ : 0<ρ:=Real.sqrt_pos.mpr (hE.metric_positive hxE).2
  have hρ2 : ρ^2=a (e.symm y)*c (e.symm y)-(b (e.symm y))^2 := by
    rw [Real.sq_sqrt (hE.metric_positive hxE).2.le,Matrix.det_fin_two,pullMetric_symm _ _ 1 0]
    dsimp [a,b,c]; ring
  have hf0:=(smoothAt_component (hi.contDiffAt (e.open_target.mem_nhds hy0)) 0).differentiableAt (by simp)
  have hf1:=(smoothAt_component (hi.contDiffAt (e.open_target.mem_nhds hy0)) 1).differentiableAt (by simp)
  have hF:=hE.mdiff.mdifferentiableAt_symm hxE
  have hp:=pullMetric_transform_three
    (f:=fun z=>e.symm z 0) (g:=fun z=>e.symm z 1)
    (show MDifferentiableAt 𝓘(ℝ,Plane) 𝓘(ℝ,Plane) (E.symm : Plane → M)
      (coordMap (fun z=>e.symm z 0) (fun z=>e.symm z 1) y) from by rwa [coordMap_components]) hf0 hf1
  rw [coordMap_components] at hp
  simp only [transformA,transformB,transformC,coordMap_components] at hp
  have hi0:=inverse_coordinate_equations he hu hv hi hy0 0
  have hi1:=inverse_coordinate_equations he hu hv hi hy0 1
  norm_num at hi0 hi1
  have hconf:=conformal_inverse_metric hρ.ne' hρ2 (hc _ hx).1 (hc _ hx).2
    (hD _ hx).ne' hi0.1 hi1.1 hi0.2 hi1.2
  let p:=ρ/coordDet u v (e.symm y)
  have hp0 : 0<p:=div_pos hρ (hD _ hx)
  refine ⟨p,hp0,?_⟩
  have eq00 : pullMetric ((E.trans e).symm : Plane → M) y 0 0=p := by
    exact hp.1.trans hconf.1
  have eq01 : pullMetric ((E.trans e).symm : Plane → M) y 0 1=0 := by
    exact hp.2.1.trans hconf.2.1
  have eq11 : pullMetric ((E.trans e).symm : Plane → M) y 1 1=p := by
    exact hp.2.2.trans hconf.2.2
  ext i j
  fin_cases i <;> fin_cases j
  · simpa using eq00
  · simpa using eq01
  · simpa using (pullMetric_symm ((E.trans e).symm : Plane → M) y 1 0).trans eq01
  · simpa using eq11

end SharpNodal.Geometry

end
end
end

end OAI
end

theorem solution.{u_1} : type_of% @OAI.SharpNodal.Geometry.conjugate_chart_conformal_oai.{u_1} := @OAI.SharpNodal.Geometry.conjugate_chart_conformal_oai.{u_1}
