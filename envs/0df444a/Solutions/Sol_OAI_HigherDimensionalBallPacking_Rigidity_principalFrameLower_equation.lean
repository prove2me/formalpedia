-- Prove2me | solution 1 for OAI.HigherDimensionalBallPacking.Rigidity.principalFrameLower_equation
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-26T17:23:54.540579+00:00
-- url     : https://prove2.me/submissions/4e7e8298-66b5-44d8-872c-2c9f7a5a089b

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

end HigherDimensionalBallPacking.Rigidity

 

 

open scoped ContDiff Topology BoundedContinuousFunction
open Set Filter Function
namespace HigherDimensionalBallPacking.Rigidity
open HigherDimensionalBallPacking.Rigidity

 theorem principalFrameLower_equation_oai {n : ℕ} (R : ℝ) (K : HolderSpace ℂ (End n) ((1:ℝ)/3))
    (A : C1HolderSpace (End n) ((1:ℝ)/3))
    (hi : ∀ z, (holderValue ((1:ℝ)/3) (c1HolderValue ((1:ℝ)/3) A) z).IsInvertible)
    (hout : ∀ z, R<‖z‖ → holderValue ((1:ℝ)/3) (c1HolderValue ((1:ℝ)/3) A) z=ContinuousLinearMap.id ℝ (Phase n))
    (z : ℂ) (x : Phase n) :
    fderiv ℝ (holderValue ((1:ℝ)/3) (c1HolderValue ((1:ℝ)/3) A)) z Complex.I x-
      holderValue ((1:ℝ)/3) K z (fderiv ℝ (holderValue ((1:ℝ)/3) (c1HolderValue ((1:ℝ)/3) A)) z 1 x)=
        holderValue ((1:ℝ)/3) (c1HolderValue ((1:ℝ)/3) A) z
          (holderValue ((1:ℝ)/3) (principalFrameLower R K A hi hout) z x) := by
  let B := holderValue ((1:ℝ)/3) (c1HolderValue ((1:ℝ)/3) A) z
  let y := fderiv ℝ (holderValue ((1:ℝ)/3) (c1HolderValue ((1:ℝ)/3) A)) z Complex.I x-
    holderValue ((1:ℝ)/3) K z (fderiv ℝ (holderValue ((1:ℝ)/3) (c1HolderValue ((1:ℝ)/3) A)) z 1 x)
  have hh : holderValue ((1:ℝ)/3) (principalFrameLower R K A hi hout) z x=B.inverse y :=
    principalFrameLower_value R K A hi hout z x
  change y=B (holderValue ((1:ℝ)/3) (principalFrameLower R K A hi hout) z x)
  rw [hh]
  exact ((hi z).self_apply_inverse y).symm

end HigherDimensionalBallPacking.Rigidity

end

end OAI
end

theorem solution : type_of% @OAI.HigherDimensionalBallPacking.Rigidity.principalFrameLower_equation_oai := @OAI.HigherDimensionalBallPacking.Rigidity.principalFrameLower_equation_oai
