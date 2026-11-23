-- Prove2me | solution 1 for GlobalTheory.ThetaInter.continuous_H
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T08:24:31.579037+00:00
-- url     : https://prove2.me/submissions/22f8caa3-30d0-4f06-8917-bf6885f1ba9d

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
theorem _root_.solution (H : Sesq W) (hH : IsHerm H) : Continuous fun p : W × W => H p.1 p.2 := by
  let B : W →ₗ[ℝ] W →ₗ[ℝ] ℂ := LinearMap.mk₂ ℝ (fun x y => H x y) (by simp)
    (fun t x y => by rw [real_smul_eq t, map_smul]; simp) (by simp)
    (fun t x y => by rw [real_smul_eq t, map_smulₛₗ]; simp)
  let B' : W →L[ℝ] W →L[ℝ] ℂ := LinearMap.toContinuousLinearMap
    ((LinearMap.toContinuousLinearMap : (W →ₗ[ℝ] ℂ) ≃ₗ[ℝ] W →L[ℝ] ℂ).toLinearMap ∘ₗ B)
  exact B'.continuous₂
end GlobalTheory.ThetaInter
