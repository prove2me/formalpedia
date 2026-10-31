-- Prove2me | solution 1 for OAI.NuclearUltrapower.CuntzAveraging.jointDefect_tendsto
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-30T13:02:47.297229+00:00
-- url     : https://prove2.me/submissions/33dd53c8-a0dc-4663-b3c9-11ab7bcb1189

import Mathlib
import Definitions.Def_NuclearUltrapower
import Definitions.Def_OAIQ019N048
import Theorems.Thm_OAI_NuclearUltrapower_CuntzAveraging_defect_tendsto

section
-- module Solutions.OAIQ019_Nuc.NuclearUltrapower_CuntzWords
attribute [-instance] _root_.OAI.NuclearUltrapower.UltraPreHilbert.instAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.NuclearUltrapower.UltraPreHilbert.instSeminormedAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.NuclearUltrapower.VariableUltra.instCStarAlgebraAlgebra _root_.OAI.NuclearUltrapower.VariableUltra.instNormedAddCommGroupAlgebra _root_.OAI.NuclearUltrapower.VariableUltra.instNormedAlgebraComplexAlgebra _root_.OAI.NuclearUltrapower.VariableUltra.instNormedRingAlgebra _root_.OAI.NuclearUltrapower.VariableUltra.instStarAlgebra _root_.OAI.NuclearUltrapower.lp_finiteDimensional _root_.OAI.NuclearUltrapower.strongDualInner
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open scoped TensorProduct InnerProductSpace
namespace NuclearUltrapower.CuntzAveraging
open CuntzModel CuntzWords CuntzUniversal

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  (R : Algebra →⋆ₙₐ[ℂ] (H →L[ℂ] H))

/-- Arbitrary commuting operators intertwine with the second tensor coordinate. -/
theorem row_commuting (n : ℕ) (T : H →L[ℂ] H)
    (hT : ∀ a, Commute (R a) T) : (row R n).comp T = (right T).comp (row R n) := by
  ext x
  simp only [ContinuousLinearMap.comp_apply,row_apply,map_sum,right_coordinate]
  apply Finset.sum_congr rfl
  intro w _
  congr 1
  have h := congrArg (fun U : H →L[ℂ] H => U x) (hT (star (value generator w))).eq
  simpa only [map_star,mul_apply_eq_comp] using h

end NuclearUltrapower.CuntzAveraging
end
end

end OAI
end

section
-- module Solutions.OAIQ019_Nuc.NuclearUltrapower_CuntzIntertwining
attribute [-instance] _root_.OAI.NuclearUltrapower.UltraPreHilbert.instAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.NuclearUltrapower.UltraPreHilbert.instSeminormedAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.NuclearUltrapower.VariableUltra.instCStarAlgebraAlgebra _root_.OAI.NuclearUltrapower.VariableUltra.instNormedAddCommGroupAlgebra _root_.OAI.NuclearUltrapower.VariableUltra.instNormedAlgebraComplexAlgebra _root_.OAI.NuclearUltrapower.VariableUltra.instNormedRingAlgebra _root_.OAI.NuclearUltrapower.VariableUltra.instStarAlgebra _root_.OAI.NuclearUltrapower.lp_finiteDimensional _root_.OAI.NuclearUltrapower.strongDualInner _root_.OAI.NuclearUltrapower.tensorBoundedSMul
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open Filter
open scoped TensorProduct InnerProductSpace Topology
namespace NuclearUltrapower.CuntzAveraging
open CuntzModel CuntzWords CuntzUniversal

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  (R : Algebra →⋆ₙₐ[ℂ] (H →L[ℂ] H))

attribute [local instance] OAI.NuclearUltrapower.CuntzAveraging.instIsBoundedSMulComplexTensorProductSubtypePreLpIndexMemAddSubgroupSpace
attribute [local instance] OAI.NuclearUltrapower.CuntzAveraging.instNormedSpaceComplexTarget
/-- Second-coordinate intertwining is exact, even for a degenerate range. -/
theorem averaged_commuting (n : ℕ) (T : H →L[ℂ] H)
    (hT : ∀ a, Commute (R a) T) :
    (averaged R n).comp T = (right T).comp (averaged R n) := by
  ext x
  change weight n • rowSum R ((n+1)^2) (T x) =
    right T (weight n • rowSum R ((n+1)^2) x)
  rw [map_smul]
  congr 1
  simp only [rowSum_apply,map_sum]
  apply Finset.sum_congr rfl
  intro k _
  exact congrArg (fun U : H →L[ℂ] Target H => U x) (row_commuting R k T hT)

end NuclearUltrapower.CuntzAveraging
end
end

end OAI
end

section
-- module Solutions.OAIQ019_Nuc.NuclearUltrapower_CuntzNuclearity
attribute [-instance] _root_.OAI.NuclearUltrapower.UltraPreHilbert.instAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.NuclearUltrapower.UltraPreHilbert.instSeminormedAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.NuclearUltrapower.VariableUltra.instCStarAlgebraAlgebra _root_.OAI.NuclearUltrapower.VariableUltra.instCompleteSpaceAlgebra _root_.OAI.NuclearUltrapower.VariableUltra.instNormedAddCommGroupAlgebra _root_.OAI.NuclearUltrapower.VariableUltra.instNormedAlgebraComplexAlgebra _root_.OAI.NuclearUltrapower.VariableUltra.instNormedRingAlgebra _root_.OAI.NuclearUltrapower.VariableUltra.instStarAlgebra _root_.OAI.NuclearUltrapower.lp_finiteDimensional _root_.OAI.NuclearUltrapower.strongDualInner _root_.OAI.NuclearUltrapower.tensorBoundedSMul
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open Filter
open scoped TensorProduct Topology
namespace NuclearUltrapower
namespace CuntzAveraging
open CuntzUniversal CuntzModel

variable {C : Type} [NonUnitalCStarAlgebra C] (H : ComplexHilbert.{0})
  (R : Algebra →⋆ₙₐ[ℂ] (H →L[ℂ] H)) (S : C →⋆ₙₐ[ℂ] (H →L[ℂ] H))

attribute [local instance] OAI.NuclearUltrapower.CuntzAveraging.instIsBoundedSMulComplexTensorProductSubtypePreLpIndexMemAddSubgroupSpaceCarrier
attribute [local instance] OAI.NuclearUltrapower.CuntzAveraging.instNormedSpaceComplexTargetCarrier
theorem jointDefect_tmul (hRS : ∀ a c, Commute (R a) (S c)) (n : ℕ) (a : Algebra) (c : C) :
    jointDefect H R S n (a ⊗ₜ[ℂ] c) = (defect R n a).comp (S c) := by
  ext x
  change averaged R n (R a (S c x)) - amplified a (right (S c) (averaged R n x)) =
    averaged R n (R a (S c x)) - amplified a (averaged R n (S c x))
  have hh := congrArg (fun T : H →L[ℂ] Target H => T x)
    (averaged_commuting R n (S c) (fun a => hRS a c))
  change averaged R n (S c x) = right (S c) (averaged R n x) at hh
  exact congrArg (fun y => averaged R n (R a (S c x)) - amplified a y) hh.symm

/-- Norm convergence of the averaged intertwining errors for every algebraic
tensor; the second algebra is completely arbitrary and may be nonunital. -/
theorem jointDefect_tendsto_oai (hRS : ∀ a c, Commute (R a) (S c)) (x : Algebra ⊗[ℂ] C) :
    Tendsto (fun n => jointDefect H R S n x) atTop (𝓝 0) := by
  induction x using OAI.tensorInductionOn with
  | tmul a c =>
    have hc : Continuous (fun T : H →L[ℂ] Target H => T.comp (S c)) := by fun_prop
    have hh := hc.continuousAt.tendsto.comp (defect_tendsto R a)
    simpa only [Function.comp_def,ContinuousLinearMap.zero_comp,← jointDefect_tmul H R S hRS] using hh
  | add x y hx hy => simpa only [jointDefect_add,add_zero] using hx.add hy

end CuntzAveraging

end NuclearUltrapower
end
end

end OAI
end

theorem solution : type_of% @OAI.NuclearUltrapower.CuntzAveraging.jointDefect_tendsto_oai := @OAI.NuclearUltrapower.CuntzAveraging.jointDefect_tendsto_oai
