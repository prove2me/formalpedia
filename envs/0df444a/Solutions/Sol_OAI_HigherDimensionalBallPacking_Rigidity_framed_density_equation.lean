-- Prove2me | solution 1 for OAI.HigherDimensionalBallPacking.Rigidity.framed_density_equation
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-26T17:02:26.160704+00:00
-- url     : https://prove2.me/submissions/1aa18db0-807a-4a12-a678-6afb2ed5df70

import Mathlib
import Definitions.Def_BallPackingNecessity
import Definitions.Def_OAIQ10Bp007
import Theorems.Thm_OAI_HigherDimensionalBallPacking_Rigidity_framed_unmarked_surjective

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
namespace HigherDimensionalBallPacking.Rigidity
variable {E F : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]

 theorem holderInverse_value (α : ℝ) (hα : 0<α) (R : ℝ) (A : HolderSpace ℂ (E →L[ℝ] E) α)
    (hi : ∀ z, (holderValue α A z).IsInvertible)
    (hout : ∀ z, R<‖z‖ → holderValue α A z=ContinuousLinearMap.id ℝ E) (z : ℂ) :
    holderValue α (holderInverse α hα R A hi hout) z=(holderValue α A z).inverse := by
  rfl

end HigherDimensionalBallPacking.Rigidity

 

 

open scoped ContDiff Topology BoundedContinuousFunction
open Set Filter Function
open SymplecticBallPacking.Hamiltonian
namespace HigherDimensionalBallPacking.Rigidity
open HigherDimensionalBallPacking.Rigidity

 theorem unmarked_density_equation {n : ℕ} (R : ℝ)
    (M B : HolderSpace ℂ (End n) ((1:ℝ)/3))
    (hs : ∀ z : ℂ, R<‖z‖ → holderValue ((1:ℝ)/3) M z=0)
    (hsurj : Surjective (fun g : CompactHolderSpace (Phase n) R => g+unmarkedLower R M hs g))
    (f : CompactHolderSpace (Phase n) R) :
    ∃ d : CompactHolderSpace (Phase n) R, ∀ z,
      compactHolderValue R d z+holderValue ((1:ℝ)/3) M z (compactCRInverseValue R d z)=
        holderValue ((1:ℝ)/3) B z (compactHolderValue R f z) := by
  obtain ⟨d,hd⟩ := hsurj (compactHolderMul R B f)
  refine ⟨d,?_⟩
  intro z
  exact congrArg (fun g => compactHolderValue R g z) hd

 theorem framed_density_equation_oai {n : ℕ} (R : ℝ) (K : ℂ → End n)
    (hK : ∀ z, Compatible (K z)) (hKout : ∀ z : ℂ, R<‖z‖ → K z=standardJ n)
    (A : C1HolderSpace (End n) ((1:ℝ)/3)) (M : HolderSpace ℂ (End n) ((1:ℝ)/3))
    (hs : ∀ z : ℂ, R<‖z‖ → holderValue ((1:ℝ)/3) M z=0)
    (hAout : ∀ z : ℂ, R<‖z‖ → holderValue ((1:ℝ)/3) (c1HolderValue ((1:ℝ)/3) A) z=ContinuousLinearMap.id ℝ _)
    (hi : ∀ z, (holderValue ((1:ℝ)/3) (c1HolderValue ((1:ℝ)/3) A) z).IsInvertible)
    (hint : ∀ z x, holderValue ((1:ℝ)/3) (c1HolderValue ((1:ℝ)/3) A) z (Complex.I • x)=
      K z (holderValue ((1:ℝ)/3) (c1HolderValue ((1:ℝ)/3) A) z x))
    (hM : ∀ z x, fderiv ℝ (holderValue ((1:ℝ)/3) (c1HolderValue ((1:ℝ)/3) A)) z Complex.I x-
      K z (fderiv ℝ (holderValue ((1:ℝ)/3) (c1HolderValue ((1:ℝ)/3) A)) z 1 x)=
      holderValue ((1:ℝ)/3) (c1HolderValue ((1:ℝ)/3) A) z (holderValue ((1:ℝ)/3) M z x))
    (f : CompactHolderSpace (Phase n) R) :
    ∃ d : CompactHolderSpace (Phase n) R, ∀ z,
      compactHolderValue R d z+holderValue ((1:ℝ)/3) M z (compactCRInverseValue R d z)=
        (holderValue ((1:ℝ)/3) (c1HolderValue ((1:ℝ)/3) A) z).inverse (compactHolderValue R f z) := by
  let B : HolderSpace ℂ (End n) ((1:ℝ)/3) :=
    holderInverse (E := Phase n) ((1:ℝ)/3) (by norm_num) R
      (c1HolderValue (E := End n) ((1:ℝ)/3) A) hi hAout
  have hsurj : Surjective (fun g : CompactHolderSpace (Phase n) R =>
      g+unmarkedLower R M hs g) := framed_unmarked_surjective (n := n) R K hK hKout A M hs hAout
    (fun z => (hi z).injective) hint hM
  obtain ⟨d,hd⟩ := unmarked_density_equation (n := n) R M B hs hsurj f
  refine ⟨d,?_⟩
  intro z
  exact (hd z).trans (congrArg (fun operator : End n => operator (compactHolderValue R f z))
    (holderInverse_value (E := Phase n) ((1:ℝ)/3) (by norm_num) R
      (c1HolderValue (E := End n) ((1:ℝ)/3) A) hi hAout z))

end HigherDimensionalBallPacking.Rigidity

 

 

open scoped ContDiff Topology BoundedContinuousFunction
open Set Filter Function
open SymplecticBallPacking.Hamiltonian





open scoped ContDiff Topology BoundedContinuousFunction
open Set Filter Function

end

end OAI
end

theorem solution : type_of% @OAI.HigherDimensionalBallPacking.Rigidity.framed_density_equation_oai := @OAI.HigherDimensionalBallPacking.Rigidity.framed_density_equation_oai
