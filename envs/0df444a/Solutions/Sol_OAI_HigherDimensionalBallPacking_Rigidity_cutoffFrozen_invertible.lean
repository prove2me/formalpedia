-- Prove2me | solution 1 for OAI.HigherDimensionalBallPacking.Rigidity.cutoffFrozen_invertible
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-26T17:09:17.622244+00:00
-- url     : https://prove2.me/submissions/8a980fb9-a71f-491b-af47-ca326abfa06c

import Mathlib
import Definitions.Def_BallPackingNecessity
import Definitions.Def_OAIQ10Bp007
import Theorems.Thm_OAI_HigherDimensionalBallPacking_Rigidity_frozenPrincipal_isInvertible

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
namespace HigherDimensionalBallPacking.Rigidity
open HigherDimensionalBallPacking.Rigidity

 theorem frozenPrincipal_value {n : ℕ} (R : ℝ) (H : HolderSpace ℂ (End n) ((1:ℝ)/3))
    (hs : ∀ z : ℂ, R<‖z‖ → holderValue ((1:ℝ)/3) H z=0)
    (g : CompactHolderSpace (Phase n) R) (z : ℂ) :
    compactHolderValue R (frozenPrincipal R H hs g) z=compactHolderValue R g z-
      holderValue ((1:ℝ)/3) H z (fderiv ℝ (compactCRInverseValue R g) z 1) := by
  have hd : fderiv ℝ (compactCRInverseValue R g) z=
      holderValue ((1:ℝ)/3) (c1HolderDeriv ((1:ℝ)/3) (compactCRInverse R g)) z :=
    (c1Holder_hasFDerivAt ((1:ℝ)/3) (compactCRInverse R g) z).fderiv
  rw [hd]
  rfl

 theorem compactHolderValue_injective {n : ℕ} (R : ℝ) :
    Injective (compactHolderValue (E := Phase n) R) := by
  intro g h he
  apply Subtype.ext
  exact holderValue_injective ((1:ℝ)/3) he

end HigherDimensionalBallPacking.Rigidity

 

 

open scoped ContDiff Topology BoundedContinuousFunction
open Set Filter Function
open SymplecticBallPacking.Hamiltonian





open scoped ContDiff Topology BoundedContinuousFunction
open Set Filter Function

end

end OAI
end

section
-- module Solutions.OAIQ10_BP.BallPacking_Necessity_FrozenResponse
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
namespace HigherDimensionalBallPacking.Rigidity

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]

 theorem cutoffFrozen_value (b : ContDiffBump (0:ℂ))
    (H : HolderSpace ℂ (E →L[ℝ] E) ((1:ℝ)/3)) (g : CompactHolderSpace E b.rOut) (z : ℂ) :
    compactHolderValue b.rOut (cutoffFrozen b H g) z=compactHolderValue b.rOut g z-
      b z • holderValue ((1:ℝ)/3) H z (fderiv ℝ (compactCRInverseValue b.rOut g) z 1) := by
  have hd : fderiv ℝ (compactCRInverseValue b.rOut g) z=
      holderValue ((1:ℝ)/3) (c1HolderDeriv ((1:ℝ)/3) (compactCRInverse b.rOut g)) z :=
    (c1Holder_hasFDerivAt ((1:ℝ)/3) (compactCRInverse b.rOut g) z).fderiv
  rw [hd]
  rfl

end HigherDimensionalBallPacking.Rigidity
namespace HigherDimensionalBallPacking.Rigidity
open HigherDimensionalBallPacking.Rigidity
 theorem cutoffFrozen_eq {n : ℕ} (b : ContDiffBump (0:ℂ))
    (H : HolderSpace ℂ (End n) ((1:ℝ)/3))
    (hs : ∀ z : ℂ, b.rIn<‖z‖ → holderValue ((1:ℝ)/3) H z=0) :
    cutoffFrozen b H=frozenPrincipal b.rOut H (fun z hz => hs z (b.rIn_lt_rOut.trans hz)) := by
  apply ContinuousLinearMap.ext
  intro g
  apply compactHolderValue_injective
  apply BoundedContinuousFunction.ext
  intro z
  rw [cutoffFrozen_value,frozenPrincipal_value]
  by_cases hz : ‖z‖≤b.rIn
  · rw [b.one_of_mem_closedBall (by simpa using hz),one_smul]
  · rw [hs z (lt_of_not_ge hz),zero_apply,smul_zero]

end HigherDimensionalBallPacking.Rigidity

 

 

open scoped ContDiff Topology BoundedContinuousFunction
open Set Filter Function
namespace HigherDimensionalBallPacking.Rigidity
open HigherDimensionalBallPacking.Rigidity

 theorem cutoffFrozen_invertible_oai {n : ℕ} (b : ContDiffBump (0:ℂ))
    (H : C1HolderSpace (End n) ((1:ℝ)/3))
    (hs : ∀ z : ℂ, b.rIn<‖z‖ → holderValue ((1:ℝ)/3) (c1HolderValue ((1:ℝ)/3) H) z=0)
    (hK : ∀ z, Compatible (standardJ n+holderValue ((1:ℝ)/3) (c1HolderValue ((1:ℝ)/3) H) z)) :
    (cutoffFrozen b (c1HolderValue ((1:ℝ)/3) H)).IsInvertible := by
  rw [cutoffFrozen_eq b _ hs]
  let K := c1HolderConstantCLM ((1:ℝ)/3) (standardJ n)+H
  apply frozenPrincipal_isInvertible b.rOut K _ _
  · intro z
    rfl
  · exact hK

end HigherDimensionalBallPacking.Rigidity

end

end OAI
end

theorem solution : type_of% @OAI.HigherDimensionalBallPacking.Rigidity.cutoffFrozen_invertible_oai := @OAI.HigherDimensionalBallPacking.Rigidity.cutoffFrozen_invertible_oai
