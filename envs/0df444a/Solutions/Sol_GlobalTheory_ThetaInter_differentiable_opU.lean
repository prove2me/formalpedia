-- Prove2me | solution 1 for GlobalTheory.ThetaInter.differentiable_opU
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T08:24:31.92335+00:00
-- url     : https://prove2.me/submissions/258fe5f0-b563-4d88-8a9c-5a3fae187f02

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_QuadraticSemicharacters_IsSemiChar
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CuspFormEvaluations_IntegrableOnFundamentalDomainOfContinuous
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_IntegralDensEqZero

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.ThetaInter
open Formalism.L2.Th1.H Complex
open scoped BigOperators ComplexConjugate
variable {V : Type*} [AddCommGroup V] [Module ℂ V] {H : Sesq V}
variable {α : V → ℂ}
open MeasureTheory
variable {W : Type} [NormedAddCommGroup W] [NormedSpace ℂ W] [NormedSpace ℝ W] [IsScalarTower ℝ ℂ W]
  [FiniteDimensional ℝ W] {H : Sesq W} {α : W → ℂ}
namespace GlobalTheory.ThetaInter
theorem _root_.solution {F : W → ℂ} (hF : Differentiable ℂ F) (x : W) : Differentiable ℂ (opU H x F) := by
  have : FiniteDimensional ℂ W := Module.Finite.of_restrictScalars_finite ℝ ℂ W
  have h : Differentiable ℂ fun z => H z x := (LinearMap.toContinuousLinearMap (H.flip x)).differentiable
  unfold opU
  fun_prop
end GlobalTheory.ThetaInter
