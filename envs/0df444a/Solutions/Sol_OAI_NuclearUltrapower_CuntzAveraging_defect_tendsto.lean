-- Prove2me | solution 1 for OAI.NuclearUltrapower.CuntzAveraging.defect_tendsto
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-30T12:58:24.020655+00:00
-- url     : https://prove2.me/submissions/94c9a8a8-a3da-4f5f-b77c-a8fa6ff430dd

import Mathlib
import Definitions.Def_OAIQ019N042
import Theorems.Thm_OAI_NuclearUltrapower_CuntzAveraging_averaged_norm_le
import Theorems.Thm_OAI_NuclearUltrapower_CuntzAveraging_defect_polynomial_tendsto

section
-- module Solutions.OAIQ019_Nuc.NuclearUltrapower_CuntzIntertwining
attribute [-instance] _root_.OAI.NuclearUltrapower.VariableUltra.instCStarAlgebraAlgebra _root_.OAI.NuclearUltrapower.VariableUltra.instNormedRingAlgebra _root_.OAI.NuclearUltrapower.VariableUltra.instStarAlgebra _root_.OAI.NuclearUltrapower.lp_finiteDimensional _root_.OAI.NuclearUltrapower.strongDualInner
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open Filter
open scoped Topology
namespace NuclearUltrapower

/-- A uniformly bounded sequence of linear maps converges to zero everywhere
once it does so on a dense range. This elementary argument requires no
separability or pointwise boundedness theorem. -/
theorem dense_bounded_tendsto_zero {A E P : Type*}
    [NormedAddCommGroup A] [NormedSpace ℂ A]
    [NormedAddCommGroup E] [NormedSpace ℂ E]
    (D : ℕ → A →ₗ[ℂ] E) (C : ℝ) (hC : 0 < C)
    (hbound : ∀ n a, ‖D n a‖ ≤ C * ‖a‖)
    (g : P → A) (hg : DenseRange g)
    (hlim : ∀ p, Tendsto (fun n => D n (g p)) atTop (𝓝 0)) (a : A) :
    Tendsto (fun n => D n a) atTop (𝓝 0) := by
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  obtain ⟨p,hp⟩ := hg.exists_dist_lt a (show 0 < ε/(2*C) by positivity)
  have hev := Metric.tendsto_nhds.mp (hlim p) (ε/2) (by positivity)
  filter_upwards [hev] with n hn
  rw [dist_zero_right] at hn ⊢
  rw [dist_eq_norm] at hp
  have hb : C * ‖a - g p‖ < ε/2 := by
    have hh := (lt_div_iff₀ (show 0 < 2*C by positivity)).mp hp
    nlinarith
  calc
    ‖D n a‖ = ‖D n (a-g p) + D n (g p)‖ := by rw [← map_add,sub_add_cancel]
    _ ≤ ‖D n (a-g p)‖ + ‖D n (g p)‖ := norm_add_le _ _
    _ ≤ C*‖a-g p‖ + ‖D n (g p)‖ := add_le_add (hbound n _) le_rfl
    _ < ε := by linarith

section Defects
variable {A H K : Type*} [CStarAlgebra A]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
  (R : A →⋆ₙₐ[ℂ] (H →L[ℂ] H)) (T : A →⋆ₙₐ[ℂ] (K →L[ℂ] K))

theorem intertwiningDefect_bound (W : H →L[ℂ] K) (hW : ‖W‖ ≤ 1) (a : A) :
    ‖intertwiningDefect R T W a‖ ≤ 2 * ‖a‖ := by
  have hR := NonUnitalStarAlgHom.norm_apply_le R a
  have hT := NonUnitalStarAlgHom.norm_apply_le T a
  calc
    _ ≤ ‖W.comp (R a)‖ + ‖(T a).comp W‖ := norm_sub_le _ _
    _ ≤ ‖W‖*‖R a‖ + ‖T a‖*‖W‖ :=
      add_le_add (ContinuousLinearMap.opNorm_comp_le _ _) (ContinuousLinearMap.opNorm_comp_le _ _)
    _ ≤ 2*‖a‖ := by
      have h₁ := mul_le_mul hW hR (norm_nonneg _) zero_le_one
      have h₂ := mul_le_mul hT hW (norm_nonneg _) (norm_nonneg _)
      nlinarith

end Defects
end NuclearUltrapower
end
end

end OAI
end

section
-- module Solutions.OAIQ019_Nuc.NuclearUltrapower_CuntzNuclearity
attribute [-instance] _root_.OAI.NuclearUltrapower.UltraPreHilbert.instAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.NuclearUltrapower.UltraPreHilbert.instSeminormedAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.NuclearUltrapower.VariableUltra.instCStarAlgebraAlgebra _root_.OAI.NuclearUltrapower.VariableUltra.instNormedAddCommGroupAlgebra _root_.OAI.NuclearUltrapower.VariableUltra.instNormedAlgebraComplexAlgebra _root_.OAI.NuclearUltrapower.VariableUltra.instNormedRingAlgebra _root_.OAI.NuclearUltrapower.VariableUltra.instStarAlgebra _root_.OAI.NuclearUltrapower.lp_finiteDimensional _root_.OAI.NuclearUltrapower.strongDualInner _root_.OAI.NuclearUltrapower.tensorBoundedSMul
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open Filter
open scoped Topology TensorProduct
namespace NuclearUltrapower.CuntzAveraging
open CuntzUniversal
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  (R : Algebra →⋆ₙₐ[ℂ] (H →L[ℂ] H))

local instance instIsBoundedSMulComplexTensorProductSubtypePreLpIndexMemAddSubgroupSpace_1 : IsBoundedSMul ℂ (CuntzModel.Space ⊗[ℂ] H) := NormedSpace.toIsBoundedSMul

attribute [local instance] OAI.NuclearUltrapower.CuntzAveraging.instNormedSpaceComplexTarget_1
/-- Uniform contractivity of the averages extends polynomial intertwining to
the norm completion, rather than just its algebraic dense subalgebra. -/
theorem defect_tendsto_oai (a : Algebra) :
    Tendsto (fun n => defect R n a) atTop (𝓝 0) := by
  apply dense_bounded_tendsto_zero (defect R) 2 (by norm_num) _ inclusion
    UniformSpace.Completion.denseRange_coe (defect_polynomial_tendsto R) a
  intro n b
  exact intertwiningDefect_bound R amplified.toNonUnitalStarAlgHom (averaged R n)
    (averaged_norm_le R n) b

end NuclearUltrapower.CuntzAveraging
end
end

end OAI
end

theorem solution.{u_1} : type_of% @OAI.NuclearUltrapower.CuntzAveraging.defect_tendsto_oai.{u_1} := @OAI.NuclearUltrapower.CuntzAveraging.defect_tendsto_oai.{u_1}
