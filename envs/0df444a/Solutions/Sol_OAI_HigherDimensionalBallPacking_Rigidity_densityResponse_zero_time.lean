-- Prove2me | solution 1 for OAI.HigherDimensionalBallPacking.Rigidity.densityResponse_zero_time
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-26T17:12:19.811001+00:00
-- url     : https://prove2.me/submissions/686f011b-9dd4-4832-8308-6bf9080c5e4e

import Mathlib
import Definitions.Def_BallPackingNecessity
import Definitions.Def_OAIQ10Bp007

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

 theorem densityCurve_eq_profile {n : ℕ} (p q : Phase n) (R : ℝ)
    (g : CompactHolderSpace (Phase n) R) :
    densityCurve p q R g=c1HolderAffineCurve ((1:ℝ)/3)
      (p-compactCRInverseValue R g 0) (densityLinearSlope p q R g) (compactCRInverse R g) := by
  funext z
  change p+z • (q-p)+(compactCRInverseValue R g z-compactCRInverseValue R g 0-
    z • (compactCRInverseValue R g 1-compactCRInverseValue R g 0))=
    p-compactCRInverseValue R g 0+z • densitySlope p q R g+compactCRInverseValue R g z
  simp only [densitySlope,smul_sub]
  abel

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

 theorem responseCoefficient_value {n : ℕ} (b B : ContDiffBump (0:ℂ)) (hbB : b.rOut≤B.rIn)
    (p q : Phase n) (A : ℝ × Phase n → End n) (hA : ContDiff ℝ ∞ A) (hc : HasCompactSupport A)
    (y : ℝ × CompactHolderSpace (Phase n) b.rOut) (z : ℂ) :
    holderValue ((1:ℝ)/3) (responseCoefficient b B A hA hc (responseCoords B p q b.rOut y)) z=
      b z • A (y.1,densityCurve p q b.rOut y.2 z) := by
  change b z • holderValue ((1:ℝ)/3) (holderPost ((1:ℝ)/3) (by norm_num) A hA hc _) z=_
  rw [holderPost_apply]
  by_cases hz : b z=0
  · rw [hz]
    ext v
    simp
  have hzz : ‖z‖≤b.rOut := by
    by_contra hn
    exact hz (b.zero_of_le_dist (by simpa using (le_of_not_ge hn)))
  have hB : B z=1 := B.one_of_mem_closedBall (by simpa using hzz.trans hbB)
  congr 2
  rw [responseProfile,map_add,BoundedContinuousFunction.add_apply,holderConstantCLM_value,
    holderLinearPost_apply, map_add, BoundedContinuousFunction.add_apply, holderCutoffAffine_apply]
  change (y.1,0)+(ContinuousLinearMap.inr ℝ ℝ (Phase n))
    (B z • ((p-compactCRInverseValue b.rOut y.2 0)+affineSlope (densitySlope p q b.rOut y.2) z)+
      B z • compactCRInverseValue b.rOut y.2 z)=_
  rw [hB,one_smul,one_smul]
  apply Prod.ext
  · simp
  · simp only [Prod.snd_add, ContinuousLinearMap.inr_apply, zero_add]
    rw [densityCurve_eq_profile]
    rfl

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





open scoped ContDiff Topology BoundedContinuousFunction
open Set Filter Function
namespace HigherDimensionalBallPacking.Rigidity
open HigherDimensionalBallPacking.Rigidity

 set_option synthInstance.maxHeartbeats 400000 in
theorem densityResponse_zero_time_oai {n : ℕ} (b B : ContDiffBump (0:ℂ)) (hbB : b.rOut≤B.rIn)
    (p q : Phase n) (A : ℝ × Phase n → End n) (hA : ContDiff ℝ ∞ A) (hc : HasCompactSupport A)
    (hzero : ∀ x, A (0,x)=0) (g : CompactHolderSpace (Phase n) b.rOut) :
    densityResponse b B p q A hA hc (0,g)=0 := by
  have hH : responseCoefficient b B A hA hc (responseCoords B p q b.rOut (0,g))=0 := by
    apply holderValue_injective
    apply BoundedContinuousFunction.ext
    intro z
    rw [responseCoefficient_value b B hbB p q A hA hc (0,g) z,hzero]
    change b z • (0 : End n)=0
    ext v
    simp
  unfold densityResponse responseFactor frozenResponse
  rw [hH]
  have hv (a : Phase n) : holderCLM ((1:ℝ)/3) (0:HolderSpace ℂ (End n) ((1:ℝ)/3)) (holderConstantCLM ((1:ℝ)/3) a)=0 := by
    apply holderValue_injective
    apply BoundedContinuousFunction.ext
    intro z
    change (0:End n) a=0
    rfl
  rw [hv,map_zero,map_zero]

end HigherDimensionalBallPacking.Rigidity

 

 

 

open scoped ContDiff Topology BoundedContinuousFunction
open Set Filter Function

end

end OAI
end

theorem solution : type_of% @OAI.HigherDimensionalBallPacking.Rigidity.densityResponse_zero_time_oai := @OAI.HigherDimensionalBallPacking.Rigidity.densityResponse_zero_time_oai
