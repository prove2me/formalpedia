-- Prove2me | solution 1 for OAI.HigherDimensionalBallPacking.Rigidity.densityResponse_contDiffAt
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-26T17:10:47.501901+00:00
-- url     : https://prove2.me/submissions/b18feb14-a723-42c4-9090-e19eab7b4cdb

import Mathlib
import Definitions.Def_BallPackingNecessity
import Definitions.Def_OAIQ10Bp009
import Theorems.Thm_OAI_HigherDimensionalBallPacking_Rigidity_responseFactor_contDiffAt

section
-- module Solutions.OAIQ10_BP.BallPacking_Necessity_DensityResidual
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped ContDiff Topology
open Set Function Filter
open scoped ContDiff Topology Manifold
open Set Function Filter MeasureTheory
open Set Function MeasureTheory
open Set Function
open SymplecticBallPacking.Hamiltonian (Plane planarCurl)
open SymplecticBallPacking.Hamiltonian (Plane planarCurl angularOneForm radiusSq planarArea planarArea_apply)
open SymplecticBallPacking.Hamiltonian (Plane planarCurl angularOneForm)
open SymplecticBallPacking.Hamiltonian (Plane angularOneForm)
open SymplecticBallPacking.Hamiltonian
open SymplecticBallPacking.Hamiltonian (Plane)
open Set Filter Function
open Set Filter MeasureTheory
open scoped Topology
open Set Filter Finset
open scoped ContDiff Topology Classical
open Set Filter
open scoped BoundedContinuousFunction ContDiff Topology
open Set Function Filter Topology
open scoped NNReal
open scoped ContDiff Topology BoundedContinuousFunction
open Function
open scoped Topology ContDiff
open scoped ContDiff Topology Convolution
open Set Filter Function MeasureTheory _root_.ContinuousLinearMap
open Set Filter Function MeasureTheory

open scoped ContDiff Topology
open Set Filter Function
namespace HigherDimensionalBallPacking.Rigidity








open scoped ContDiff Topology
open Set Filter Function
open HigherDimensionalBallPacking.Rigidity

 attribute [local instance] OAI.HigherDimensionalBallPacking.Rigidity.instNormedAddCommGroupCompactHolderSpace_2
attribute [local instance] OAI.HigherDimensionalBallPacking.Rigidity.instNormedSpaceRealCompactHolderSpace_2
theorem densitySlope_contDiff {n : ℕ} (p q : Phase n) (R : ℝ) :
    ContDiff ℝ ∞ (densitySlope p q R) := by
  let C := compactCRInverse (E := Phase n) R
  have h0 : ContDiff ℝ ∞ (fun g : CompactHolderSpace (Phase n) R => compactCRInverseValue R g 0) := ((c1HolderEval ((1:ℝ)/3) (0:ℂ)).comp C).contDiff
  have h1 : ContDiff ℝ ∞ (fun g : CompactHolderSpace (Phase n) R => compactCRInverseValue R g 1) := ((c1HolderEval ((1:ℝ)/3) (1:ℂ)).comp C).contDiff
  exact contDiff_const.sub (h1.sub h0)

end HigherDimensionalBallPacking.Rigidity

end

end OAI
end

section
-- module Solutions.OAIQ10_BP.BallPacking_Necessity_DensityMaps
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped ContDiff Topology
open Set Function Filter
open scoped ContDiff Topology Manifold
open Set Function Filter MeasureTheory
open Set Function MeasureTheory
open Set Function
open SymplecticBallPacking.Hamiltonian (Plane planarCurl)
open SymplecticBallPacking.Hamiltonian (Plane planarCurl angularOneForm radiusSq planarArea planarArea_apply)
open SymplecticBallPacking.Hamiltonian (Plane planarCurl angularOneForm)
open SymplecticBallPacking.Hamiltonian (Plane angularOneForm)
open SymplecticBallPacking.Hamiltonian
open SymplecticBallPacking.Hamiltonian (Plane)
open Set Filter Function
open Set Filter MeasureTheory
open scoped Topology
open Set Filter Finset
open scoped ContDiff Topology Classical
open Set Filter
open scoped BoundedContinuousFunction ContDiff Topology
open Set Function Filter Topology
open scoped NNReal
open scoped ContDiff Topology BoundedContinuousFunction
open Function
open scoped Topology ContDiff
open scoped ContDiff Topology Convolution
open Set Filter Function MeasureTheory _root_.ContinuousLinearMap
open Set Filter Function MeasureTheory

open scoped ContDiff Topology BoundedContinuousFunction
open Set Filter Function





open scoped ContDiff Topology BoundedContinuousFunction
open Set Filter Function





open scoped ContDiff Topology BoundedContinuousFunction
open Set Filter Function
namespace HigherDimensionalBallPacking.Rigidity
open HigherDimensionalBallPacking.Rigidity

 attribute [local instance] OAI.HigherDimensionalBallPacking.Rigidity.compactMapHGroup
attribute [local instance] OAI.HigherDimensionalBallPacking.Rigidity.compactMapHSpace
attribute [local instance] OAI.HigherDimensionalBallPacking.Rigidity.compactMapCompactGroup
attribute [local instance] OAI.HigherDimensionalBallPacking.Rigidity.compactMapCompactSpace
theorem responseCoords_contDiff {n : ℕ} (B : ContDiffBump (0:ℂ)) (p q : Phase n) (R : ℝ) :
    ContDiff ℝ ∞ (responseCoords B p q R) := by
  have h0 : ContDiff ℝ ∞ (fun y : ℝ × CompactHolderSpace (Phase n) R => compactCRInverseValue R y.2 0) :=
    (((c1HolderEval ((1:ℝ)/3) 0).comp (compactCRInverse (E := Phase n) R)).contDiff).comp contDiff_snd
  have ha : ContDiff ℝ ∞ (fun y : ℝ × CompactHolderSpace (Phase n) R => densitySlope p q R y.2) :=
    (densitySlope_contDiff p q R).comp contDiff_snd
  exact (contDiff_fst.prodMk ((contDiff_const.sub h0).prodMk ha)).prodMk
    (((cutoffValues B).comp (compactCRInverse (E := Phase n) R)).contDiff.comp contDiff_snd)

end HigherDimensionalBallPacking.Rigidity

end

end OAI
end

section
-- module Solutions.OAIQ10_BP.BallPacking_Necessity_DensityExistence
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped ContDiff Topology
open Set Function Filter
open scoped ContDiff Topology Manifold
open Set Function Filter MeasureTheory
open Set Function MeasureTheory
open Set Function
open SymplecticBallPacking.Hamiltonian (Plane planarCurl)
open SymplecticBallPacking.Hamiltonian (Plane planarCurl angularOneForm radiusSq planarArea planarArea_apply)
open SymplecticBallPacking.Hamiltonian (Plane planarCurl angularOneForm)
open SymplecticBallPacking.Hamiltonian (Plane angularOneForm)
open SymplecticBallPacking.Hamiltonian
open SymplecticBallPacking.Hamiltonian (Plane)
open Set Filter Function
open Set Filter MeasureTheory
open scoped Topology
open Set Filter Finset
open scoped ContDiff Topology Classical
open Set Filter
open scoped BoundedContinuousFunction ContDiff Topology
open Set Function Filter Topology
open scoped NNReal
open scoped ContDiff Topology BoundedContinuousFunction
open Function
open scoped Topology ContDiff
open scoped ContDiff Topology Convolution
open Set Filter Function MeasureTheory _root_.ContinuousLinearMap
open Set Filter Function MeasureTheory

open scoped ContDiff Topology
open Set Filter Function
namespace HigherDimensionalBallPacking.Rigidity
open HigherDimensionalBallPacking.Rigidity TwoPointContinuation

 attribute [local instance] OAI.HigherDimensionalBallPacking.Rigidity.responseLocalGroup
attribute [local instance] OAI.HigherDimensionalBallPacking.Rigidity.responseLocalSpace
attribute [local instance] OAI.HigherDimensionalBallPacking.Rigidity.responseLocalCompactGroup
attribute [local instance] OAI.HigherDimensionalBallPacking.Rigidity.responseLocalCompactSpace
theorem densityResponse_contDiffAt_oai {n : ℕ} (b B : ContDiffBump (0:ℂ)) (p q : Phase n)
    (A : ℝ × Phase n → End n) (hA : ContDiff ℝ ∞ A) (hc : HasCompactSupport A)
    (y : ℝ × CompactHolderSpace (Phase n) b.rOut)
    (hi : (cutoffFrozen b (responseCoefficient b B A hA hc (responseCoords B p q b.rOut y))).IsInvertible) :
    ContDiffAt ℝ ∞ (densityResponse b B p q A hA hc) y :=
  (responseFactor_contDiffAt b B A hA hc _ hi).comp y (responseCoords_contDiff B p q b.rOut).contDiffAt

end HigherDimensionalBallPacking.Rigidity

 

 

open scoped ContDiff Topology BoundedContinuousFunction
open Set Filter Function







open scoped ContDiff Topology BoundedContinuousFunction
open Set Filter Function

end

end OAI
end

theorem solution : type_of% @OAI.HigherDimensionalBallPacking.Rigidity.densityResponse_contDiffAt_oai := @OAI.HigherDimensionalBallPacking.Rigidity.densityResponse_contDiffAt_oai
