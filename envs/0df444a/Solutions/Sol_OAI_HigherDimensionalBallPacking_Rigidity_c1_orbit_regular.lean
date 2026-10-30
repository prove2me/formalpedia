-- Prove2me | solution 1 for OAI.HigherDimensionalBallPacking.Rigidity.c1_orbit_regular
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-30T03:54:53.770559+00:00
-- url     : https://prove2.me/submissions/e886dfb9-7711-4bbf-8ced-0a36040edd61

import Mathlib
import Definitions.Def_OAIQ10Bp008
import Theorems.Thm_OAI_HigherDimensionalBallPacking_Rigidity_c1_orbit_contDiff

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
namespace HigherDimensionalBallPacking.Rigidity
variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

 attribute [local instance] OAI.HigherDimensionalBallPacking.Rigidity.orbitC1Group
attribute [local instance] OAI.HigherDimensionalBallPacking.Rigidity.orbitC1Space
theorem c1_orbit_smooth_function (α : ℝ) (f : C1HolderSpace E α)
    (hf : ContDiffAt ℝ ∞ (fun h : ℂ => c1HolderShift α h f) 0) :
    ContDiff ℝ ∞ (holderValue α (c1HolderValue α f)) := by
  apply contDiff_iff_contDiffAt.mpr
  intro z
  have he : ContDiffAt ℝ ∞ (fun h : ℂ => holderValue α (c1HolderValue α f) (z+h)) 0 :=
    (c1HolderEval (E := E) α z).contDiff.contDiffAt.comp 0 hf
  have hz : ContDiffAt ℝ ∞ (fun h : ℂ => h-z) z := contDiffAt_id.sub contDiffAt_const
  have he' : ContDiffAt ℝ ∞ (fun h : ℂ => holderValue α (c1HolderValue α f) (z+h)) (z-z) := by simpa only [sub_self] using he
  have hh := he'.comp (f := fun h : ℂ => h-z) z hz
  convert hh using 1
  all_goals try with_reducible_and_instances rfl
  funext x
  congr 1
  dsimp only [Function.comp_def]
  abel

 attribute [local instance] OAI.HigherDimensionalBallPacking.Rigidity.orbitHolderGroup
attribute [local instance] OAI.HigherDimensionalBallPacking.Rigidity.orbitHolderSpace
theorem c1_orbit_regular_oai (α : ℝ) (hα : 0<α) (f : C1HolderSpace E α)
    (U : Set ℂ) (hU : IsOpen U) (h0 : (0:ℂ)∈U)
    (Φ : ℂ × HolderSpace ℂ E α → C1HolderSpace E α)
    (hΦ : ∀ h∈U, ContDiffAt ℝ ∞ Φ (h,holderShift α h (c1HolderValue α f)))
    (heq : ∀ h∈U, c1HolderShift α h f=Φ (h,holderShift α h (c1HolderValue α f))) :
    ContDiff ℝ ∞ (holderValue α (c1HolderValue α f)) :=
  c1_orbit_smooth_function α f (c1_orbit_contDiff α hα f U hU Φ hΦ heq 0 h0)

end HigherDimensionalBallPacking.Rigidity

 

 

open scoped ContDiff Topology BoundedContinuousFunction
open Set Filter Function





open scoped ContDiff Topology BoundedContinuousFunction
open Set Filter Function

end

end OAI
end

theorem solution : type_of% @OAI.HigherDimensionalBallPacking.Rigidity.c1_orbit_regular_oai := @OAI.HigherDimensionalBallPacking.Rigidity.c1_orbit_regular_oai
