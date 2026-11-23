-- Prove2me | solution 1 for GlobalTheory.ThetaInter.continuous_rho
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T08:27:59.452442+00:00
-- url     : https://prove2.me/submissions/f163f2e4-9909-4081-b8d1-f7e84e223d2f

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_QuadraticSemicharacters_IsSemiChar
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CuspFormEvaluations_IntegrableOnFundamentalDomainOfContinuous
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_IntegralDensEqZero
import Theorems.Thm_GlobalTheory_ThetaInter_continuous_H

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
theorem _root_.solution (hH : IsHerm H) {F : W → ℂ} (hF : Continuous F) : Continuous (rho H F) := by
  have : Continuous fun z : W => H z z := (continuous_H H hH).comp (continuous_id.prodMk continuous_id)
  exact (hF.norm.pow 2).mul (Real.continuous_exp.comp (continuous_const.mul (Complex.continuous_re.comp this)))
end GlobalTheory.ThetaInter
