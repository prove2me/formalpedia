-- Prove2me | solution 1 for OAI.HigherDimensionalBallPacking.Rigidity.c1_frozen_response
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-26T17:09:16.484407+00:00
-- url     : https://prove2.me/submissions/af18601f-e0d1-4a41-9b2e-7e69c2a34a13

import Mathlib
import Definitions.Def_BallPackingNecessity
import Definitions.Def_OAIQ10Bp007
import Theorems.Thm_OAI_HigherDimensionalBallPacking_Rigidity_cutoff_curl_reconstruct

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

 theorem frozenResponse_eq (b : ContDiffBump (0:ℂ))
    (H : HolderSpace ℂ (E →L[ℝ] E) ((1:ℝ)/3)) (a : E)
    (hi : (cutoffFrozen b H).IsInvertible) (g : CompactHolderSpace E b.rOut)
    (hg : cutoffFrozen b H g=cutoffCompact b (holderCLM ((1:ℝ)/3) H (holderConstantCLM ((1:ℝ)/3) a))) :
    frozenResponse b (H,a)=g := by
  change (cutoffFrozen b H).inverse _=g
  rw [←hg,hi.inverse_apply_self]

end HigherDimensionalBallPacking.Rigidity





open scoped ContDiff Topology BoundedContinuousFunction
open Set Filter Function
namespace HigherDimensionalBallPacking.Rigidity
open HigherDimensionalBallPacking.Rigidity

 theorem cutoffFrozen_equation {n : ℕ} (b : ContDiffBump (0:ℂ))
    (H : HolderSpace ℂ (End n) ((1:ℝ)/3)) (a : Phase n) (g : CompactHolderSpace (Phase n) b.rOut)
    (he : ∀ z, compactHolderValue b.rOut g z=b z • holderValue ((1:ℝ)/3) H z
      (a+fderiv ℝ (compactCRInverseValue b.rOut g) z 1)) :
    cutoffFrozen b H g=cutoffCompact b (holderCLM ((1:ℝ)/3) H (holderConstantCLM ((1:ℝ)/3) a)) := by
  apply compactHolderValue_injective
  apply BoundedContinuousFunction.ext
  intro z
  rw [cutoffFrozen_value b H g z,he z,cutoffCompact_value b _ z,holderCLM_apply,holderConstantCLM_value]
  rw [map_add,smul_add,add_sub_cancel_right]

 theorem c1_frozen_response_oai {n : ℕ} (b : ContDiffBump (0:ℂ))
    (v : C1HolderSpace (Phase n) ((1:ℝ)/3)) (a : Phase n)
    (H : HolderSpace ℂ (End n) ((1:ℝ)/3))
    (hs : ∀ z : ℂ, b.rIn<‖z‖ → holderValue ((1:ℝ)/3) H z=0)
    (hi : (cutoffFrozen b H).IsInvertible)
    (hcurl : ∀ z, holderValue ((1:ℝ)/3) (c1StandardCurl v) z=
      holderValue ((1:ℝ)/3) H z (a+holderValue ((1:ℝ)/3) (c1HolderDeriv ((1:ℝ)/3) v) z 1))
    (hlim : Tendsto (holderValue ((1:ℝ)/3) (c1HolderValue ((1:ℝ)/3) v)) (cocompact ℂ) (𝓝 0)) :
    v=compactCRInverse b.rOut (frozenResponse b (H,a)) := by
  let g := cutoffCompact b (c1StandardCurl v)
  have hcs (z : ℂ) (hz : b.rIn<‖z‖) : holderValue ((1:ℝ)/3) (c1StandardCurl v) z=0 := by
    rw [hcurl,hs z hz,zero_apply]
  have hveq : v=compactCRInverse b.rOut g := cutoff_curl_reconstruct b v hcs hlim
  have hg : cutoffFrozen b H g=cutoffCompact b (holderCLM ((1:ℝ)/3) H (holderConstantCLM ((1:ℝ)/3) a)) := by
    apply cutoffFrozen_equation
    intro z
    change b z • holderValue ((1:ℝ)/3) (c1StandardCurl v) z=_
    rw [hcurl,hveq]
    have hd : fderiv ℝ (compactCRInverseValue b.rOut g) z=
        holderValue ((1:ℝ)/3) (c1HolderDeriv ((1:ℝ)/3) (compactCRInverse b.rOut g)) z :=
      (c1Holder_hasFDerivAt ((1:ℝ)/3) (compactCRInverse b.rOut g) z).fderiv
    rw [hd]
  rw [frozenResponse_eq b H a hi g hg]
  exact hveq

end HigherDimensionalBallPacking.Rigidity

end

end OAI
end

theorem solution : type_of% @OAI.HigherDimensionalBallPacking.Rigidity.c1_frozen_response_oai := @OAI.HigherDimensionalBallPacking.Rigidity.c1_frozen_response_oai
