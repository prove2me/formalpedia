-- Prove2me | solution 1 for OAI.SharpNodal.Geometry.laplaceBeltrami_in_chart
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-26T06:15:05.73157+00:00
-- url     : https://prove2.me/submissions/69f8e851-6055-402c-9a96-54dca4c6b94a

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

lemma partial_sub_at {f g : Plane → ℝ} {x : Plane}
    (hf : DifferentiableAt ℝ f x) (hg : DifferentiableAt ℝ g x) (i : Fin 2) :
    coordPartial (fun y=>f y-g y) i x=coordPartial f i x-coordPartial g i x := by
  unfold coordPartial
  rw [fderiv_fun_sub hf hg]; rfl
lemma partial_mul_at {f g : Plane → ℝ} {x : Plane}
    (hf : DifferentiableAt ℝ f x) (hg : DifferentiableAt ℝ g x) (i : Fin 2) :
    coordPartial (fun y=>f y*g y) i x=coordPartial f i x*g x+f x*coordPartial g i x := by
  unfold coordPartial
  rw [fderiv_fun_mul hf hg]; simp; ring
lemma smoothAt_partial {f : Plane → ℝ} {x : Plane} (hf : ContDiffAt ℝ ∞ f x) (i : Fin 2) :
    ContDiffAt ℝ ∞ (coordPartial f i) x :=
  (hf.fderiv_right (by simp)).clm_apply contDiffAt_const
lemma partial_partial_at {f : Plane → ℝ} {x : Plane} (hf : ContDiffAt ℝ ∞ f x) (i j : Fin 2) :
    coordPartial (coordPartial f i) j x=coordPartial (coordPartial f j) i x := by
  have hdf := (hf.fderiv_right (m:=∞) (by simp)).differentiableAt (by simp)
  have hh (a b : Fin 2) : coordPartial (coordPartial f a) b x=
      fderiv ℝ (fderiv ℝ f) x (EuclideanSpace.single b 1) (EuclideanSpace.single a 1) := by
    unfold coordPartial
    rw [fderiv_clm_apply hdf (differentiableAt_const _)]; simp
  rw [hh i j,hh j i]
  exact (hf.isSymmSndFDerivAt (by
    simp only [minSmoothness_of_isRCLikeNormedField]
    exact WithTop.coe_le_coe.mpr (le_top : (2 : ℕ∞) ≤ ⊤))).eq _ _
lemma partial_congr_nhds {f g : Plane → ℝ} {x : Plane} (h : f=ᶠ[𝓝 x]g) (i : Fin 2) :
    coordPartial f i x=coordPartial g i x := by unfold coordPartial; rw [h.fderiv_eq]

lemma differentiableAt_coordMap {f g : Plane → ℝ} {x : Plane}
    (hf : DifferentiableAt ℝ f x) (hg : DifferentiableAt ℝ g x) :
    DifferentiableAt ℝ (coordMap f g) x := (hasFDerivAt_coordMap hf hg).differentiableAt
lemma contDiffAt_coordMap {f g : Plane → ℝ} {x : Plane}
    (hf : ContDiffAt ℝ ∞ f x) (hg : ContDiffAt ℝ ∞ g x) :
    ContDiffAt ℝ ∞ (coordMap f g) x := (hf.smul contDiffAt_const).add (hg.smul contDiffAt_const)
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

lemma piola_identity {f g p q : Plane → ℝ} {x : Plane}
    (hf : ContDiffAt ℝ ∞ f x) (hg : ContDiffAt ℝ ∞ g x)
    (hp : DifferentiableAt ℝ p (coordMap f g x))
    (hq : DifferentiableAt ℝ q (coordMap f g x)) :
    coordPartial (fun y=>coordPartial g 1 y*p (coordMap f g y)-coordPartial f 1 y*q (coordMap f g y)) 0 x+
    coordPartial (fun y=>coordPartial f 0 y*q (coordMap f g y)-coordPartial g 0 y*p (coordMap f g y)) 1 x=
    (coordPartial f 0 x*coordPartial g 1 x-coordPartial f 1 x*coordPartial g 0 x)*
      (coordPartial p 0 (coordMap f g x)+coordPartial q 1 (coordMap f g x)) := by
  have hfd:=hf.differentiableAt (by simp)
  have hgd:=hg.differentiableAt (by simp)
  have hF:=differentiableAt_coordMap hfd hgd
  have hpd : DifferentiableAt ℝ (fun y=>p (coordMap f g y)) x :=hp.comp x hF
  have hqd : DifferentiableAt ℝ (fun y=>q (coordMap f g y)) x :=hq.comp x hF
  have hfp i:=(smoothAt_partial hf i).differentiableAt (by simp)
  have hgp i:=(smoothAt_partial hg i).differentiableAt (by simp)
  rw [partial_sub_at ((hgp 1).fun_mul hpd) ((hfp 1).fun_mul hqd),
      partial_sub_at ((hfp 0).fun_mul hqd) ((hgp 0).fun_mul hpd),
      partial_mul_at (hgp 1) hpd,partial_mul_at (hfp 1) hqd,
      partial_mul_at (hfp 0) hqd,partial_mul_at (hgp 0) hpd]
  change _+_=(coordPartial f 0 x*coordPartial g 1 x-coordPartial f 1 x*coordPartial g 0 x)*_
  rw [partial_comp_coordMap hfd hgd hp,partial_comp_coordMap hfd hgd hq,
    partial_comp_coordMap hfd hgd hq,partial_comp_coordMap hfd hgd hp,
    partial_partial_at hf 1 0,partial_partial_at hg 1 0]
  ring

end SharpNodal.Geometry
noncomputable section
open scoped Matrix
namespace SharpNodal.Geometry

lemma density_flux_two (G : Matrix (Fin 2) (Fin 2) ℝ) (hG : G 1 0=G 0 1)
    (hdet : 0<G.det) (r s : ℝ) :
    let ρ:=Real.sqrt G.det
    ρ*((G⁻¹) 0 0*r+(G⁻¹) 0 1*s)=(G 1 1*r-G 0 1*s)/ρ ∧
    ρ*((G⁻¹) 1 0*r+(G⁻¹) 1 1*s)=(G 0 0*s-G 0 1*r)/ρ := by
  dsimp
  have hρ:=Real.sqrt_pos.mpr hdet
  have hρ2:=Real.sq_sqrt hdet.le
  rw [Matrix.inv_def,Ring.inverse_eq_inv,Matrix.adjugate_fin_two]
  simp only [Matrix.smul_apply,Matrix.of_apply,Matrix.cons_val_zero,Matrix.cons_val_one,
    Matrix.cons_val_fin_one,smul_eq_mul,hG]
  constructor <;> field_simp [hdet.ne',hρ.ne'] <;> rw [hρ2] <;> ring

lemma transform_metric_det (a b c α β γ δ : ℝ) :
    (a*α^2+2*b*α*γ+c*γ^2)*(a*β^2+2*b*β*δ+c*δ^2)-
      (a*α*β+b*(α*δ+β*γ)+c*γ*δ)^2=(α*δ-β*γ)^2*(a*c-b^2) := by ring

lemma transform_metric_density {a b c α β γ δ : ℝ} (_h : 0≤a*c-b^2) :
    Real.sqrt ((a*α^2+2*b*α*γ+c*γ^2)*(a*β^2+2*b*β*δ+c*δ^2)-
      (a*α*β+b*(α*δ+β*γ)+c*γ*δ)^2)=|α*δ-β*γ| *Real.sqrt (a*c-b^2) := by
  rw [transform_metric_det,Real.sqrt_mul (sq_nonneg _),Real.sqrt_sq_eq_abs]

lemma transform_metric_cofactor (a b c α β γ δ r s : ℝ) :
    let a':=a*α^2+2*b*α*γ+c*γ^2
    let b':=a*α*β+b*(α*δ+β*γ)+c*γ*δ
    let c':=a*β^2+2*b*β*δ+c*δ^2
    c'*(r*α+s*γ)-b'*(r*β+s*δ)=(α*δ-β*γ)*(δ*(c*r-b*s)-β*(a*s-b*r)) ∧
    a'*(r*β+s*δ)-b'*(r*α+s*γ)=(α*δ-β*γ)*(α*(a*s-b*r)-γ*(c*r-b*s)) := by
  dsimp; constructor <;> ring

lemma transform_metric_flux {ρ d σ : ℝ} (hρ : ρ≠0) (hd : d≠0) (hσ : σ=1 ∨ σ= -1)
    (habs : |d|=σ*d) (P Q N₀ N₁ α β γ δ : ℝ)
    (hN₀ : N₀=d*(δ*P-β*Q)) (hN₁ : N₁=d*(α*Q-γ*P)) :
    N₀/(|d| *ρ)=σ*(δ*(P/ρ)-β*(Q/ρ)) ∧
    N₁/(|d| *ρ)=σ*(α*(Q/ρ)-γ*(P/ρ)) := by
  rw [hN₀,hN₁,habs]
  rcases hσ with rfl|rfl <;> constructor <;> field_simp [hρ,hd]

end SharpNodal.Geometry

noncomputable section
open scoped Topology ContDiff
open Filter Set Metric
namespace SharpNodal.Geometry
open Carleman Profiles.Elliptic

lemma smoothAt_scalarDensity {a b c : Plane → ℝ} {x : Plane}
    (ha : ContDiffAt ℝ ∞ a x) (hb : ContDiffAt ℝ ∞ b x) (hc : ContDiffAt ℝ ∞ c x)
    (h : 0<a x*c x-(b x)^2) : ContDiffAt ℝ ∞ (scalarDensity a b c) x :=
  ((ha.mul hc).sub (hb.pow 2)).sqrt h.ne'
lemma smoothAt_scalarFlux {a b c U : Plane → ℝ} {x : Plane}
    (ha : ContDiffAt ℝ ∞ a x) (hb : ContDiffAt ℝ ∞ b x) (hc : ContDiffAt ℝ ∞ c x)
    (hU : ContDiffAt ℝ ∞ U x) (h : 0<a x*c x-(b x)^2) :
    ContDiffAt ℝ ∞ (scalarFlux0 a b c U) x ∧ ContDiffAt ℝ ∞ (scalarFlux1 a b c U) x := by
  have hρ:=smoothAt_scalarDensity ha hb hc h
  have hn : scalarDensity a b c x≠0:=(Real.sqrt_pos.mpr h).ne'
  exact ⟨((hc.mul (smoothAt_partial hU 0)).sub (hb.mul (smoothAt_partial hU 1))).div hρ hn,
    ((ha.mul (smoothAt_partial hU 1)).sub (hb.mul (smoothAt_partial hU 0))).div hρ hn⟩

lemma transform_scalarDensity {a b c f g : Plane → ℝ} {x : Plane}
    (h : 0≤a (coordMap f g x)*c (coordMap f g x)-(b (coordMap f g x))^2) :
    scalarDensity (transformA a b c f g) (transformB a b c f g) (transformC a b c f g) x=
      |coordDet f g x| *scalarDensity a b c (coordMap f g x) :=
  transform_metric_density h

lemma transform_scalarFlux {a b c f g U : Plane → ℝ} {x : Plane} {σ : ℝ}
    (hf : DifferentiableAt ℝ f x) (hg : DifferentiableAt ℝ g x)
    (hU : DifferentiableAt ℝ U (coordMap f g x))
    (hp : 0<a (coordMap f g x)*c (coordMap f g x)-(b (coordMap f g x))^2)
    (hd : coordDet f g x≠0) (hσ : σ=1 ∨ σ= -1) (habs : |coordDet f g x|=σ*coordDet f g x) :
    scalarFlux0 (transformA a b c f g) (transformB a b c f g) (transformC a b c f g)
        (fun y=>U (coordMap f g y)) x=
      σ*(coordPartial g 1 x*scalarFlux0 a b c U (coordMap f g x)-
        coordPartial f 1 x*scalarFlux1 a b c U (coordMap f g x)) ∧
    scalarFlux1 (transformA a b c f g) (transformB a b c f g) (transformC a b c f g)
        (fun y=>U (coordMap f g y)) x=
      σ*(coordPartial f 0 x*scalarFlux1 a b c U (coordMap f g x)-
        coordPartial g 0 x*scalarFlux0 a b c U (coordMap f g x)) := by
  unfold scalarFlux0 scalarFlux1
  rw [transform_scalarDensity hp.le,partial_comp_coordMap hf hg hU 0,
    partial_comp_coordMap hf hg hU 1]
  apply transform_metric_flux (Real.sqrt_pos.mpr hp).ne' hd hσ habs
  · exact (transform_metric_cofactor _ _ _ _ _ _ _ _ _).1
  · exact (transform_metric_cofactor _ _ _ _ _ _ _ _ _).2

lemma continuousAt_abs_sign {d : Plane → ℝ} {x : Plane} (hc : ContinuousAt d x) (hd : d x≠0) :
    ∃σ : ℝ, (σ=1 ∨ σ= -1) ∧ ∀ᶠy in 𝓝 x, d y≠0 ∧ |d y|=σ*d y := by
  rcases hd.lt_or_gt with hn|hp
  · refine ⟨-1,Or.inr rfl,?_⟩
    filter_upwards [hc.eventually (gt_mem_nhds hn)] with y hy
    exact ⟨hy.ne,by rw [abs_of_neg hy]; ring⟩
  · refine ⟨1,Or.inl rfl,?_⟩
    filter_upwards [hc.eventually (lt_mem_nhds hp)] with y hy
    exact ⟨hy.ne',by rw [abs_of_pos hy,one_mul]⟩

lemma scalarLaplace_covariant {a b c U f g : Plane → ℝ} {x : Plane}
    (ha : ContDiffAt ℝ ∞ a (coordMap f g x)) (hb : ContDiffAt ℝ ∞ b (coordMap f g x))
    (hc : ContDiffAt ℝ ∞ c (coordMap f g x)) (hU : ContDiffAt ℝ ∞ U (coordMap f g x))
    (hf : ContDiffAt ℝ ∞ f x) (hg : ContDiffAt ℝ ∞ g x)
    (hp : 0<a (coordMap f g x)*c (coordMap f g x)-(b (coordMap f g x))^2)
    (hd : coordDet f g x≠0) :
    scalarLaplace (transformA a b c f g) (transformB a b c f g) (transformC a b c f g)
      (fun y=>U (coordMap f g y)) x=scalarLaplace a b c U (coordMap f g x) := by
  have hF:=contDiffAt_coordMap hf hg
  have hdC : ContinuousAt (coordDet f g) x:=
    (((smoothAt_partial hf 0).mul (smoothAt_partial hg 1)).sub
      ((smoothAt_partial hf 1).mul (smoothAt_partial hg 0))).continuousAt
  obtain ⟨σ,hσ,hs⟩:=continuousAt_abs_sign hdC hd
  have hpos : ∀ᶠy in 𝓝 x, 0<a (coordMap f g y)*c (coordMap f g y)-(b (coordMap f g y))^2 :=
    ((((ha.mul hc).sub (hb.pow 2)).comp x hF).continuousAt).eventually (lt_mem_nhds hp)
  have hfn:=(hf.of_le (show (1 : WithTop ℕ∞)≤(∞ : WithTop ℕ∞) by simp)).eventually (by simp)
  have hgn:=(hg.of_le (show (1 : WithTop ℕ∞)≤(∞ : WithTop ℕ∞) by simp)).eventually (by simp)
  have hun:=(hU.of_le (show (1 : WithTop ℕ∞)≤(∞ : WithTop ℕ∞) by simp)).eventually (by simp)
  have huF : ∀ᶠ y in 𝓝 x, ContDiffAt ℝ 1 U (coordMap f g y):=hF.continuousAt hun
  have he : ∀ᶠy in 𝓝 x,
      scalarFlux0 (transformA a b c f g) (transformB a b c f g) (transformC a b c f g)
        (fun z=>U (coordMap f g z)) y=
      σ*(coordPartial g 1 y*scalarFlux0 a b c U (coordMap f g y)-
        coordPartial f 1 y*scalarFlux1 a b c U (coordMap f g y)) ∧
      scalarFlux1 (transformA a b c f g) (transformB a b c f g) (transformC a b c f g)
        (fun z=>U (coordMap f g z)) y=
      σ*(coordPartial f 0 y*scalarFlux1 a b c U (coordMap f g y)-
        coordPartial g 0 y*scalarFlux0 a b c U (coordMap f g y)) := by
    filter_upwards [hfn,hgn,huF,hpos,hs] with y hyf hyg hyU hyp hys
    exact transform_scalarFlux (hyf.differentiableAt (by simp)) (hyg.differentiableAt (by simp))
      (hyU.differentiableAt (by simp)) hyp hys.1 hσ hys.2
  have hfl:=smoothAt_scalarFlux ha hb hc hU hp
  have hpD:=hfl.1.differentiableAt (by simp)
  have hqD:=hfl.2.differentiableAt (by simp)
  have hFdiff:=hF.differentiableAt (by simp)
  have hterm0 : DifferentiableAt ℝ (fun y=>coordPartial g 1 y*scalarFlux0 a b c U (coordMap f g y)-
      coordPartial f 1 y*scalarFlux1 a b c U (coordMap f g y)) x:=
    (((smoothAt_partial hg 1).differentiableAt (by simp)).mul (hpD.comp x hFdiff)).sub
    (((smoothAt_partial hf 1).differentiableAt (by simp)).mul (hqD.comp x hFdiff))
  have hterm1 : DifferentiableAt ℝ (fun y=>coordPartial f 0 y*scalarFlux1 a b c U (coordMap f g y)-
      coordPartial g 0 y*scalarFlux0 a b c U (coordMap f g y)) x:=
    (((smoothAt_partial hf 0).differentiableAt (by simp)).mul (hqD.comp x hFdiff)).sub
    (((smoothAt_partial hg 0).differentiableAt (by simp)).mul (hpD.comp x hFdiff))
  unfold scalarLaplace
  rw [partial_congr_nhds (he.mono fun _ hy=>hy.1) 0,
    partial_congr_nhds (he.mono fun _ hy=>hy.2) 1,
    partial_mul_at (differentiableAt_const σ) hterm0,
    partial_mul_at (differentiableAt_const σ) hterm1]
  have hz (i : Fin 2) : coordPartial (fun _ : Plane=>σ) i x=0:=by simp [coordPartial]
  rw [hz,hz,zero_mul,zero_mul,zero_add,zero_add,← mul_add,
    piola_identity hf hg hpD hqD,transform_scalarDensity hp.le]
  have hxsign:=Filter.Eventually.self_of_nhds hs
  rw [hxsign.2]
  have hsn : σ≠0:=by rcases hσ with rfl|rfl <;> norm_num
  change σ*(coordDet f g x*_)/(σ*coordDet f g x*scalarDensity a b c (coordMap f g x))=_
  field_simp [hsn,hd,(Real.sqrt_pos.mpr hp).ne']

end SharpNodal.Geometry

end
end
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

lemma smoothOn_pullback_metric {f : Plane → M} {s : Set Plane} (hs : IsOpen s)
    (hf : ContMDiffOn 𝓘(ℝ,Plane) 𝓘(ℝ,Plane) ∞ f s) (v w : Plane) :
    ContDiffOn ℝ ∞ (fun y=>inner ℝ
      (mfderiv 𝓘(ℝ,Plane) 𝓘(ℝ,Plane) f y v)
      (mfderiv 𝓘(ℝ,Plane) 𝓘(ℝ,Plane) f y w)) s := by
  have hc (a : Plane) : ContMDiff 𝓘(ℝ,Plane) (𝓘(ℝ,Plane)).tangent ∞
      (fun y:Plane=>(⟨y,a⟩ : TangentBundle 𝓘(ℝ,Plane) Plane)) := by
    intro y
    exact contMDiffAt_vectorSpace_iff_contDiffAt.mpr contDiffAt_const
  have ht:=hf.contMDiffOn_tangentMapWithin (m:=∞) (by simp) hs.uniqueMDiffOn
  have hv (a : Plane) : ContMDiffOn 𝓘(ℝ,Plane) (𝓘(ℝ,Plane)).tangent ∞
      (fun y=> (⟨f y,mfderiv 𝓘(ℝ,Plane) 𝓘(ℝ,Plane) f y a⟩ : TangentBundle 𝓘(ℝ,Plane) M)) s := by
    have hh:=ht.comp (hc a).contMDiffOn (show MapsTo (fun y:Plane=>(⟨y,a⟩ : TangentBundle 𝓘(ℝ,Plane) Plane)) s (Bundle.TotalSpace.proj ⁻¹' s) from fun _ hy=>hy)
    apply hh.congr
    intro y hy
    simp only [Function.comp_apply,tangentMapWithin,
      mfderivWithin_of_mem_nhds (I:=𝓘(ℝ,Plane)) (I':=𝓘(ℝ,Plane)) (f:=f) (hs.mem_nhds hy)]
  exact ((hv v).inner_bundle (hv w)).contDiffOn

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
  [IsContMDiffRiemannianBundle 𝓘(ℝ,Plane) ∞ Plane (fun x:M=>TangentSpace 𝓘(ℝ,Plane) x)] in
lemma coordinateMetric_symm (x : M) (y : Plane) (i j : Fin 2) :
    coordinateMetric x y i j=coordinateMetric x y j i := real_inner_comm _ _

omit [IsContMDiffRiemannianBundle 𝓘(ℝ,Plane) ∞ Plane (fun x:M=>TangentSpace 𝓘(ℝ,Plane) x)] in
lemma coordinateMetric_positive (x : M) {y : Plane} (hy : y∈(chartAt Plane x).target) :
    0 < coordinateMetric x y 0 0 ∧ 0<(coordinateMetric x y).det := by
  have hh:=gram_two_positive (mfderiv 𝓘(ℝ,Plane) 𝓘(ℝ,Plane) (chartAt Plane x).symm y)
    ((mdifferentiable_chart (I:=𝓘(ℝ,Plane)) x).symm.mfderiv_injective hy)
  refine ⟨hh.1,?_⟩
  rw [Matrix.det_fin_two,coordinateMetric_symm x y 1 0]
  convert hh.2 using 1
  all_goals try with_reducible_and_instances rfl
  simp only [coordinateMetric,pow_two]
  rfl

omit [RiemannianBundle (fun x : M=>TangentSpace 𝓘(ℝ,Plane) x)]
  [IsContMDiffRiemannianBundle 𝓘(ℝ,Plane) ∞ Plane (fun x:M=>TangentSpace 𝓘(ℝ,Plane) x)] in
lemma chartSmooth_chartAt (x : M) : ChartSmooth (chartAt Plane x) :=
  ⟨contMDiffOn_chart,contMDiffOn_chart_symm⟩

omit [IsManifold 𝓘(ℝ,Plane) ∞ M]
  [RiemannianBundle (fun x : M=>TangentSpace 𝓘(ℝ,Plane) x)]
  [IsContMDiffRiemannianBundle 𝓘(ℝ,Plane) ∞ Plane (fun x:M=>TangentSpace 𝓘(ℝ,Plane) x)] in
lemma ChartSmooth.mdiff {e : OpenPartialHomeomorph M Plane} (he : ChartSmooth e) :
    e.MDifferentiable 𝓘(ℝ,Plane) 𝓘(ℝ,Plane) :=
  ⟨he.1.mdifferentiableOn (by simp),he.2.mdifferentiableOn (by simp)⟩

lemma ChartSmooth.metric_smooth {e : OpenPartialHomeomorph M Plane} (he : ChartSmooth e)
    (i j : Fin 2) : ContDiffOn ℝ ∞ (fun y=>pullMetric (e.symm : Plane → M) y i j) e.target :=
  smoothOn_pullback_metric e.open_target he.2 _ _

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

lemma partial_eventuallyEq {f g : Plane → ℝ} {x : Plane} (h : f=ᶠ[𝓝 x]g) (i : Fin 2) :
    coordPartial f i=ᶠ[𝓝 x]coordPartial g i := by
  filter_upwards [h.fderiv (𝕜:=ℝ)] with y hy
  exact congrArg (fun L:Plane →L[ℝ] ℝ=>L (EuclideanSpace.single i 1)) hy

lemma scalarLaplace_congr {a b c U a' b' c' U' : Plane → ℝ} {x : Plane}
    (ha : a=ᶠ[𝓝 x]a') (hb : b=ᶠ[𝓝 x]b') (hc : c=ᶠ[𝓝 x]c') (hU : U=ᶠ[𝓝 x]U') :
    scalarLaplace a b c U x=scalarLaplace a' b' c' U' x := by
  have hρ : scalarDensity a b c=ᶠ[𝓝 x]scalarDensity a' b' c' := by
    filter_upwards [ha,hb,hc] with y hy0 hy1 hy2; simp only [scalarDensity,hy0,hy1,hy2]
  have hf0 : scalarFlux0 a b c U=ᶠ[𝓝 x]scalarFlux0 a' b' c' U' := by
    filter_upwards [hb,hc,hρ,partial_eventuallyEq hU 0,partial_eventuallyEq hU 1] with y hy0 hy1 hy2 hy3 hy4
    simp only [scalarFlux0,hy0,hy1,hy2,hy3,hy4]
  have hf1 : scalarFlux1 a b c U=ᶠ[𝓝 x]scalarFlux1 a' b' c' U' := by
    filter_upwards [ha,hb,hρ,partial_eventuallyEq hU 0,partial_eventuallyEq hU 1] with y hy0 hy1 hy2 hy3 hy4
    simp only [scalarFlux1,hy0,hy1,hy2,hy3,hy4]
  simp only [scalarLaplace,partial_congr_nhds hf0,partial_congr_nhds hf1,hρ.self_of_nhds]

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
lemma pullMetric_congr {F G : Plane → M} {x : Plane} (h : F=ᶠ[𝓝 x]G) :
    pullMetric F x=pullMetric G x := by
  have he:=h.self_of_nhds
  have hd:=h.mfderiv_eq (I:=𝓘(ℝ,Plane)) (I':=𝓘(ℝ,Plane))
  ext i j
  unfold pullMetric
  rw [he] at hd ⊢
  rw [hd]

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

lemma smoothOn_component {F : Plane → Plane} {s : Set Plane} (hF : ContDiffOn ℝ ∞ F s) (i : Fin 2) :
    ContDiffOn ℝ ∞ (fun y=>F y i) s :=
  (EuclideanSpace.proj i : Plane →L[ℝ] ℝ).contDiff.comp_contDiffOn hF

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

lemma coordDet_chart_ne_zero {e : OpenPartialHomeomorph Plane Plane}
    (he : ChartSmooth e) {x : Plane} (hx : x∈e.source) :
    coordDet (fun z=>e z 0) (fun z=>e z 1) x≠0 := by
  have hu:=smoothOn_component he.1.contDiffOn 0
  have hv:=smoothOn_component he.1.contDiffOn 1
  have h0:=inverse_coordinate_equations (coordMap_components (e : Plane → Plane)).symm hu hv he.2.contDiffOn (e.map_source hx) 0
  have h1:=inverse_coordinate_equations (coordMap_components (e : Plane → Plane)).symm hu hv he.2.contDiffOn (e.map_source hx) 1
  rw [e.left_inv hx] at h0 h1
  norm_num at h0 h1
  let r:=coordPartial (fun z=>e z 0) 0 x
  let s:=coordPartial (fun z=>e z 0) 1 x
  let v:=coordPartial (fun z=>e z 1) 0 x
  let w:=coordPartial (fun z=>e z 1) 1 x
  let α:=coordPartial (fun z=>e.symm z 0) 0 (e x)
  let β:=coordPartial (fun z=>e.symm z 0) 1 (e x)
  let γ:=coordPartial (fun z=>e.symm z 1) 0 (e x)
  let δ:=coordPartial (fun z=>e.symm z 1) 1 (e x)
  have H : (r*w-s*v)*(α*δ-β*γ)=1 := by
    calc
      _ = (r*α+s*γ)*(v*β+w*δ)-(r*β+s*δ)*(v*α+w*γ) := by ring
      _ = 1 := by rw [h0.1,h1.1,h0.2,h1.2]; norm_num
  intro hz
  change r*w-s*v=0 at hz
  rw [hz,zero_mul] at H
  norm_num at H

end SharpNodal.Geometry
end

end OAI
end

section
-- module Solutions.OAIQ4_Nl.NodalLength_Isothermal
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
open scoped Topology ContDiff Bundle
open Filter Set Metric Bundle Manifold
open scoped Topology ContDiff Bundle
open Filter Set Metric Bundle Manifold
open scoped Topology ContDiff Bundle
open Filter Set Metric Bundle Manifold

noncomputable section
open scoped Topology ContDiff Bundle
open Filter Set Metric Bundle Manifold
namespace SharpNodal.Geometry
open Carleman Profiles.Elliptic
variable {M : Type*} [MetricSpace M] [ChartedSpace Plane M]
  [IsManifold 𝓘(ℝ,Plane) ∞ M]
  [RiemannianBundle (fun x:M=>TangentSpace 𝓘(ℝ,Plane) x)]
  [IsContMDiffRiemannianBundle 𝓘(ℝ,Plane) ∞ Plane (fun x:M=>TangentSpace 𝓘(ℝ,Plane) x)]

omit [IsContMDiffRiemannianBundle 𝓘(ℝ,Plane) ∞ Plane (fun x:M=>TangentSpace 𝓘(ℝ,Plane) x)] in
lemma laplaceBeltrami_eq_chartScalar (u : M → ℝ) (x : M) :
    laplaceBeltrami u x=chartScalarLaplace (chartAt Plane x) u (chartAt Plane x x) := by
  let c:=chartAt Plane x
  let a:=fun y=>coordinateMetric x y 0 0
  let b:=fun y=>coordinateMetric x y 0 1
  let d:=fun y=>coordinateMetric x y 1 1
  have hρ : coordinateDensity x=scalarDensity a b d := by
    funext y
    unfold coordinateDensity scalarDensity
    congr 1
    rw [Matrix.det_fin_two,coordinateMetric_symm x y 1 0]
    dsimp [a,b,d]; ring
  have h0 : (fun y=>coordinateDensity x y*∑j:Fin 2,(coordinateMetric x y)⁻¹ 0 j*coordPartial (u ∘ c.symm) j y)=ᶠ[𝓝 (c x)]scalarFlux0 a b d (u ∘ c.symm) := by
    filter_upwards [c.open_target.mem_nhds (c.map_source (mem_chart_source Plane x))] with y hy
    have hh:=(density_flux_two (coordinateMetric x y) (coordinateMetric_symm x y 1 0) (coordinateMetric_positive x hy).2
      (coordPartial (u ∘ c.symm) 0 y) (coordPartial (u ∘ c.symm) 1 y)).1
    simpa only [Fin.sum_univ_two,scalarFlux0,← hρ,coordinateDensity] using hh
  have h1 : (fun y=>coordinateDensity x y*∑j:Fin 2,(coordinateMetric x y)⁻¹ 1 j*coordPartial (u ∘ c.symm) j y)=ᶠ[𝓝 (c x)]scalarFlux1 a b d (u ∘ c.symm) := by
    filter_upwards [c.open_target.mem_nhds (c.map_source (mem_chart_source Plane x))] with y hy
    have hh:=(density_flux_two (coordinateMetric x y) (coordinateMetric_symm x y 1 0) (coordinateMetric_positive x hy).2
      (coordPartial (u ∘ c.symm) 0 y) (coordPartial (u ∘ c.symm) 1 y)).2
    simpa only [Fin.sum_univ_two,scalarFlux1,← hρ,coordinateDensity] using hh
  unfold laplaceBeltrami
  rw [Fin.sum_univ_two,partial_congr_nhds h0,partial_congr_nhds h1,hρ]
  have hpull : (fun z=>pullMetric ((chartAt Plane x).symm : Plane → M) z)=coordinateMetric x:=rfl
  unfold chartScalarLaplace
  simp only [hpull,scalarLaplace]
  change (scalarDensity a b d (c x))⁻¹*(coordPartial (scalarFlux0 a b d (u ∘ c.symm)) 0 (c x)+coordPartial (scalarFlux1 a b d (u ∘ c.symm)) 1 (c x))=
    (coordPartial (scalarFlux0 a b d (u ∘ c.symm)) 0 (c x)+coordPartial (scalarFlux1 a b d (u ∘ c.symm)) 1 (c x))/scalarDensity a b d (c x)
  ring

lemma chartScalarLaplace_covariant {e c : OpenPartialHomeomorph M Plane}
    (he : ChartSmooth e) (hc : ChartSmooth c) {x : M} (hxe : x∈e.source) (hxc : x∈c.source)
    {U : M → ℝ} (hU : ContMDiff 𝓘(ℝ,Plane) 𝓘(ℝ) ∞ U) :
    chartScalarLaplace e U (e x)=chartScalarLaplace c U (c x) := by
  let t:=e.symm.trans c
  have ht : ChartSmooth t := by
    constructor
    · exact hc.1.comp (he.2.mono inter_subset_left) (fun _ h=>h.2)
    · exact he.1.comp (hc.2.mono inter_subset_left) (fun _ h=>h.2)
  have hxt : e x∈t.source:=⟨e.map_source hxe,by change e.symm (e x)∈c.source; rwa [e.left_inv hxe]⟩
  let f:=fun z=>t z 0
  let g:=fun z=>t z 1
  have hfg : coordMap f g=(t : Plane → Plane):=coordMap_components t
  have htval : t (e x)=c x:=by change c (e.symm (e x))=c x; rw [e.left_inv hxe]
  let a:=fun z=>pullMetric (c.symm : Plane → M) z 0 0
  let b:=fun z=>pullMetric (c.symm : Plane → M) z 0 1
  let d:=fun z=>pullMetric (c.symm : Plane → M) z 1 1
  have hcxs : coordMap f g (e x)∈c.target:=by rw [hfg,htval]; exact c.map_source hxc
  have hsf:=(smoothAt_component (ht.1.contDiffOn.contDiffAt (t.open_source.mem_nhds hxt)) 0)
  have hsg:=(smoothAt_component (ht.1.contDiffOn.contDiffAt (t.open_source.mem_nhds hxt)) 1)
  have hUa : ContDiffAt ℝ ∞ (U ∘ c.symm) (coordMap f g (e x)) :=
    (hU.comp_contMDiffOn hc.2).contDiffOn.contDiffAt (c.open_target.mem_nhds hcxs)
  have ha:=(hc.metric_smooth 0 0).contDiffAt (c.open_target.mem_nhds hcxs)
  have hb:=(hc.metric_smooth 0 1).contDiffAt (c.open_target.mem_nhds hcxs)
  have hd:=(hc.metric_smooth 1 1).contDiffAt (c.open_target.mem_nhds hcxs)
  have hpos : 0<a (coordMap f g (e x))*d (coordMap f g (e x))-(b (coordMap f g (e x)))^2 := by
    have hh:=(hc.metric_positive hcxs).2
    rw [Matrix.det_fin_two,pullMetric_symm _ _ 1 0] at hh
    simpa only [pow_two] using hh
  have hcov:=scalarLaplace_covariant ha hb hd hUa hsf hsg hpos (coordDet_chart_ne_zero ht hxt)
  have hEq : (e.symm : Plane → M)=ᶠ[𝓝 (e x)]fun z=>c.symm (coordMap f g z) := by
    filter_upwards [t.open_source.mem_nhds hxt] with z hz
    rw [hfg]
    exact (c.left_inv hz.2).symm
  have hm : ∀ᶠz in 𝓝 (e x),pullMetric (e.symm : Plane → M) z 0 0=transformA a b d f g z ∧
      pullMetric (e.symm : Plane → M) z 0 1=transformB a b d f g z ∧
      pullMetric (e.symm : Plane → M) z 1 1=transformC a b d f g z := by
    filter_upwards [hEq.eventually_nhds,t.open_source.mem_nhds hxt] with z hz hzt
    have hcz : coordMap f g z∈c.target:=by rw [hfg]; exact c.map_source hzt.2
    have hdz:=(ht.1.contDiffOn.contDiffAt (t.open_source.mem_nhds hzt))
    have hfp:=(smoothAt_component hdz 0).differentiableAt (by simp)
    have hgp:=(smoothAt_component hdz 1).differentiableAt (by simp)
    rw [pullMetric_congr hz]
    exact pullMetric_transform_three (hc.mdiff.mdifferentiableAt_symm hcz) hfp hgp
  have hUU : (U ∘ e.symm)=ᶠ[𝓝 (e x)]fun z=>(U ∘ c.symm) (coordMap f g z):=hEq.fun_comp U
  have hcong:=scalarLaplace_congr (hm.mono fun _ h=>h.1) (hm.mono fun _ h=>h.2.1)
    (hm.mono fun _ h=>h.2.2) hUU
  exact hcong.trans (by simpa only [chartScalarLaplace,a,b,d,hfg,htval] using hcov)

lemma laplaceBeltrami_in_chart_oai {e : OpenPartialHomeomorph M Plane} (he : ChartSmooth e)
    {x : M} (hx : x∈e.source) {U : M → ℝ} (hU : ContMDiff 𝓘(ℝ,Plane) 𝓘(ℝ) ∞ U) :
    laplaceBeltrami U x=chartScalarLaplace e U (e x) := by
  rw [laplaceBeltrami_eq_chartScalar]
  exact chartScalarLaplace_covariant (chartSmooth_chartAt x) he (mem_chart_source Plane x) hx hU

end SharpNodal.Geometry

end
end

end OAI
end

theorem solution.{u_1} : type_of% @OAI.SharpNodal.Geometry.laplaceBeltrami_in_chart_oai.{u_1} := @OAI.SharpNodal.Geometry.laplaceBeltrami_in_chart_oai.{u_1}
