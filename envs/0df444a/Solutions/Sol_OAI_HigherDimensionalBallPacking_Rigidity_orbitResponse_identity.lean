-- Prove2me | solution 1 for OAI.HigherDimensionalBallPacking.Rigidity.orbitResponse_identity
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-26T17:22:24.853241+00:00
-- url     : https://prove2.me/submissions/43e954b9-8843-4606-b422-b438ba0c5ef7

import Mathlib
import Definitions.Def_BallPackingNecessity
import Definitions.Def_OAIQ10Bp009
import Theorems.Thm_OAI_HigherDimensionalBallPacking_Rigidity_c1_frozen_response

section
-- module Solutions.OAIQ10_BP.BallPacking_Necessity_OrbitRegularity
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





open scoped ContDiff Topology BoundedContinuousFunction
open Set Filter Function
namespace HigherDimensionalBallPacking.Rigidity
open HigherDimensionalBallPacking.Rigidity

 theorem orbitCoefficient_value {n : ℕ} (f : Phase n → End n) (hf : ContDiff ℝ ∞ f) (hc : HasCompactSupport f)
    (c a : Phase n) (v : C1HolderSpace (Phase n) ((1:ℝ)/3)) (h z : ℂ) :
    holderValue ((1:ℝ)/3) (orbitCoefficient f hf hc c a (h,holderShift ((1:ℝ)/3) h (c1HolderValue ((1:ℝ)/3) v))) z=
      f (c1HolderAffineCurve ((1:ℝ)/3) c (affineSlope a) v (z+h)) := by
  change f (c+h • a+z • a+holderValue ((1:ℝ)/3) (c1HolderValue ((1:ℝ)/3) v) (z+h))=_
  congr 1
  unfold c1HolderAffineCurve
  rw [affineSlope_apply,add_smul]
  abel

 theorem c1_shift_decay {n : ℕ} (v : C1HolderSpace (Phase n) ((1:ℝ)/3))
    (hl : Tendsto (holderValue ((1:ℝ)/3) (c1HolderValue ((1:ℝ)/3) v)) (cocompact ℂ) (𝓝 0)) (h : ℂ) :
    Tendsto (holderValue ((1:ℝ)/3) (c1HolderValue ((1:ℝ)/3) (c1HolderShift ((1:ℝ)/3) h v))) (cocompact ℂ) (𝓝 0) := by
  exact hl.comp ((Homeomorph.addRight h).isClosedEmbedding.tendsto_cocompact)

 theorem c1_shift_curl {n : ℕ} (v : C1HolderSpace (Phase n) ((1:ℝ)/3)) (h z : ℂ) :
    holderValue ((1:ℝ)/3) (c1StandardCurl (c1HolderShift ((1:ℝ)/3) h v)) z=
      holderValue ((1:ℝ)/3) (c1StandardCurl v) (z+h) := rfl

end HigherDimensionalBallPacking.Rigidity

 

 

open scoped ContDiff Topology BoundedContinuousFunction
open Set Filter Function
namespace HigherDimensionalBallPacking.Rigidity
open HigherDimensionalBallPacking.Rigidity

 theorem orbitResponse_identity_oai {n : ℕ} (b : ContDiffBump (0:ℂ))
    (f : Phase n → End n) (hf : ContDiff ℝ ∞ f) (hc : HasCompactSupport f)
    (c a : Phase n) (v : C1HolderSpace (Phase n) ((1:ℝ)/3)) (h : ℂ)
    (hs : ∀ z, b.rIn<‖z‖ → holderValue ((1:ℝ)/3)
      (orbitCoefficient f hf hc c a (h,holderShift ((1:ℝ)/3) h (c1HolderValue ((1:ℝ)/3) v))) z=0)
    (hi : (cutoffFrozen b (orbitCoefficient f hf hc c a (h,holderShift ((1:ℝ)/3) h (c1HolderValue ((1:ℝ)/3) v)))).IsInvertible)
    (hcurl : ∀ z, holderValue ((1:ℝ)/3) (c1StandardCurl v) z=
      f (c1HolderAffineCurve ((1:ℝ)/3) c (affineSlope a) v z)
        (a+holderValue ((1:ℝ)/3) (c1HolderDeriv ((1:ℝ)/3) v) z 1))
    (hlim : Tendsto (holderValue ((1:ℝ)/3) (c1HolderValue ((1:ℝ)/3) v)) (cocompact ℂ) (𝓝 0)) :
    c1HolderShift ((1:ℝ)/3) h v=
      orbitResponse b f hf hc c a (h,holderShift ((1:ℝ)/3) h (c1HolderValue ((1:ℝ)/3) v)) := by
  apply c1_frozen_response (n := n) b _ a _ hs hi _ (c1_shift_decay v hlim h)
  intro z
  rw [c1_shift_curl v h z,orbitCoefficient_value f hf hc c a v h z,hcurl (z+h)]
  rfl



end HigherDimensionalBallPacking.Rigidity

end

end OAI
end

theorem solution : type_of% @OAI.HigherDimensionalBallPacking.Rigidity.orbitResponse_identity_oai := @OAI.HigherDimensionalBallPacking.Rigidity.orbitResponse_identity_oai
