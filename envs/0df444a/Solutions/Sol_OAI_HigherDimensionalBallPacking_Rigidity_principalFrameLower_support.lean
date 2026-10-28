-- Prove2me | solution 1 for OAI.HigherDimensionalBallPacking.Rigidity.principalFrameLower_support
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-26T17:24:39.450373+00:00
-- url     : https://prove2.me/submissions/1c2846f0-e11e-4844-98a7-7ca405463242

import Mathlib
import Definitions.Def_BallPackingNecessity
import Definitions.Def_OAIQ10Bp009

section
-- module Solutions.OAIQ10_BP.BallPacking_Necessity_FrozenInverse
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
open SymplecticBallPacking.Hamiltonian





open scoped ContDiff Topology BoundedContinuousFunction
open Set Filter Function
open SymplecticBallPacking.Hamiltonian
namespace HigherDimensionalBallPacking.Rigidity
open HigherDimensionalBallPacking.Rigidity

 theorem constant_outside_fderiv {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (R : ℝ) {a : ℂ → E} {c : E} (hout : ∀ z, R<‖z‖ → a z=c) {z : ℂ} (hz : R<‖z‖) :
    fderiv ℝ a z=0 := by
  have he : a=ᶠ[𝓝 z] fun _ => c := by
    filter_upwards [(isOpen_lt continuous_const continuous_norm).mem_nhds hz] with w hw
    exact hout w hw
  rw [he.fderiv_eq,fderiv_const_apply]

 theorem principalFrameLower_value {n : ℕ} (R : ℝ) (K : HolderSpace ℂ (End n) ((1:ℝ)/3))
    (A : C1HolderSpace (End n) ((1:ℝ)/3))
    (hi : ∀ z, (holderValue ((1:ℝ)/3) (c1HolderValue ((1:ℝ)/3) A) z).IsInvertible)
    (hout : ∀ z, R<‖z‖ → holderValue ((1:ℝ)/3) (c1HolderValue ((1:ℝ)/3) A) z=ContinuousLinearMap.id ℝ (Phase n))
    (z : ℂ) (x : Phase n) :
    holderValue ((1:ℝ)/3) (principalFrameLower R K A hi hout) z x=
      (holderValue ((1:ℝ)/3) (c1HolderValue ((1:ℝ)/3) A) z).inverse
      (fderiv ℝ (holderValue ((1:ℝ)/3) (c1HolderValue ((1:ℝ)/3) A)) z Complex.I x-
        holderValue ((1:ℝ)/3) K z (fderiv ℝ (holderValue ((1:ℝ)/3) (c1HolderValue ((1:ℝ)/3) A)) z 1 x)) := by
  rw [(c1Holder_hasFDerivAt ((1:ℝ)/3) A z).fderiv]
  rfl

 theorem principalFrameLower_support_oai {n : ℕ} (R : ℝ) (K : HolderSpace ℂ (End n) ((1:ℝ)/3))
    (A : C1HolderSpace (End n) ((1:ℝ)/3))
    (hi : ∀ z, (holderValue ((1:ℝ)/3) (c1HolderValue ((1:ℝ)/3) A) z).IsInvertible)
    (hout : ∀ z, R<‖z‖ → holderValue ((1:ℝ)/3) (c1HolderValue ((1:ℝ)/3) A) z=ContinuousLinearMap.id ℝ (Phase n))
    (z : ℂ) (hz : R<‖z‖) : holderValue ((1:ℝ)/3) (principalFrameLower R K A hi hout) z=0 := by
  apply ContinuousLinearMap.ext
  intro x
  rw [principalFrameLower_value,constant_outside_fderiv R hout hz]
  simp

end HigherDimensionalBallPacking.Rigidity

 

 

open scoped ContDiff Topology BoundedContinuousFunction
open Set Filter Function

end

end OAI
end

theorem solution : type_of% @OAI.HigherDimensionalBallPacking.Rigidity.principalFrameLower_support_oai := @OAI.HigherDimensionalBallPacking.Rigidity.principalFrameLower_support_oai
