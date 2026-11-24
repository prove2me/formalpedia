-- Prove2me | solution 1 for GlobalTheory.ThetaInter.differentiable_inter
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T05:12:29.692328+00:00
-- url     : https://prove2.me/submissions/ddaab224-f9b2-4e31-a7cf-d08bb6eefe9b

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_QuadraticSemicharacters_IsSemiChar
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CuspFormEvaluations_IntegrableOnFundamentalDomainOfContinuous
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_IntegralDensEqZero
import Theorems.Thm_GlobalTheory_ThetaInter_inter_eq
import Theorems.Thm_GlobalTheory_ThetaInter_differentiable_opU

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
theorem _root_.solution (A₁ A₂ : AddSubgroup W) [Finite (A₂ ⧸ A₁.addSubgroupOf A₂)] {F : W → ℂ}
    (hF : Differentiable ℂ F) : Differentiable ℂ (inter H α A₁ A₂ F) := by
  have := Fintype.ofFinite (A₂ ⧸ A₁.addSubgroupOf A₂)
  rw [inter_eq]
  exact (Differentiable.fun_sum fun c _ => (differentiable_opU hF _).const_mul _).const_mul _
end GlobalTheory.ThetaInter
