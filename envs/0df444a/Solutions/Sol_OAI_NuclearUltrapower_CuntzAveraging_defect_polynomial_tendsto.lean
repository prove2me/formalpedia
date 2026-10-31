-- Prove2me | solution 1 for OAI.NuclearUltrapower.CuntzAveraging.defect_polynomial_tendsto
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-30T12:56:41.067991+00:00
-- url     : https://prove2.me/submissions/25fafeed-da1a-438a-94e2-136c42cbc96e

import Mathlib
import Definitions.Def_OAIQ019N042
import Theorems.Thm_OAI_NuclearUltrapower_CuntzAveraging_defect_adjoint_bound
import Theorems.Thm_OAI_NuclearUltrapower_CuntzAveraging_defect_generator_bound

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
open scoped Topology
namespace NuclearUltrapower

section Defects
variable {A H K : Type*} [CStarAlgebra A]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
  (R : A →⋆ₙₐ[ℂ] (H →L[ℂ] H)) (T : A →⋆ₙₐ[ℂ] (K →L[ℂ] K))

theorem intertwiningDefect_mul (W : H →L[ℂ] K) (a b : A) :
    intertwiningDefect R T W (a*b) =
      (intertwiningDefect R T W a).comp (R b) + (T a).comp (intertwiningDefect R T W b) := by
  ext x
  simp only [intertwiningDefect_apply,ContinuousLinearMap.comp_apply,map_mul,
    mul_apply_eq_comp,sub_apply,add_apply,map_sub]
  abel

/-- Approximate intertwining propagates through products without any finite
coordinate relation being silently imposed. -/
theorem intertwiningDefect_tendsto_mul (W : ℕ → H →L[ℂ] K) {a b : A}
    (ha : Tendsto (fun n => intertwiningDefect R T (W n) a) atTop (𝓝 0))
    (hb : Tendsto (fun n => intertwiningDefect R T (W n) b) atTop (𝓝 0)) :
    Tendsto (fun n => intertwiningDefect R T (W n) (a*b)) atTop (𝓝 0) := by
  have hc₁ : Continuous (fun U : H →L[ℂ] K => U.comp (R b)) := by fun_prop
  have hc₂ : Continuous (fun U : H →L[ℂ] K => (T a).comp U) := by fun_prop
  have hh := (hc₁.continuousAt.tendsto.comp ha).add (hc₂.continuousAt.tendsto.comp hb)
  simpa only [Function.comp_def,ContinuousLinearMap.zero_comp,ContinuousLinearMap.comp_zero,
    add_zero,← intertwiningDefect_mul] using hh
end Defects
end NuclearUltrapower
end
end

section

noncomputable section
open Filter
open scoped TensorProduct InnerProductSpace Topology
namespace NuclearUltrapower.CuntzAveraging
open CuntzModel CuntzWords CuntzUniversal

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  (R : Algebra →⋆ₙₐ[ℂ] (H →L[ℂ] H))

theorem inverse_weight_tendsto : Tendsto (fun n : ℕ => ((n : ℝ)+1)⁻¹ * 2) atTop (𝓝 0) := by
  have ht : Tendsto (fun n : ℕ => (n : ℝ)+1) atTop atTop :=
    Filter.tendsto_atTop_add_const_right atTop 1 tendsto_natCast_atTop_atTop
  simpa only [zero_mul,Function.comp_def] using (tendsto_inv_atTop_zero.comp ht).mul_const 2

attribute [local instance] OAI.NuclearUltrapower.CuntzAveraging.instIsBoundedSMulComplexTensorProductSubtypePreLpIndexMemAddSubgroupSpace
attribute [local instance] OAI.NuclearUltrapower.CuntzAveraging.instNormedSpaceComplexTarget
theorem defect_generator_tendsto (i : Fin 2) :
    Tendsto (fun n => defect R n (generator i)) atTop (𝓝 0) := by
  apply tendsto_zero_iff_norm_tendsto_zero.mpr
  exact squeeze_zero (fun n => norm_nonneg _) (fun n => defect_generator_bound R n i)
    inverse_weight_tendsto

theorem defect_adjoint_tendsto (i : Fin 2) :
    Tendsto (fun n => defect R n (star (generator i))) atTop (𝓝 0) := by
  apply tendsto_zero_iff_norm_tendsto_zero.mpr
  exact squeeze_zero (fun n => norm_nonneg _) (fun n => defect_adjoint_bound R n i)
    inverse_weight_tendsto

end NuclearUltrapower.CuntzAveraging
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
/-- The finite-level intertwining estimate extends to every star polynomial,
with no continuity assumption on a presentation of that polynomial. -/
theorem defect_polynomial_tendsto_oai (p : CuntzPolynomial.Poly) :
    Tendsto (fun n => defect R n (inclusion p)) atTop (𝓝 0) := by
  have hl (a : CuntzPolynomial.Letter) :
      Tendsto (fun n => defect R n (inclusion (MonoidAlgebra.of ℂ CuntzPolynomial.Word
        (FreeMonoid.of a)))) atTop (𝓝 0) := by
    rcases a with ⟨i,b⟩
    cases b
    · exact defect_generator_tendsto R i
    · have hg : (MonoidAlgebra.of ℂ CuntzPolynomial.Word (FreeMonoid.of (i,true)) : CuntzPolynomial.Poly) =
          star (CuntzPolynomial.generator i) := by
        rw [CuntzPolynomial.generator,CuntzPolynomial.star_single,CuntzPolynomial.star_word_of,star_one]
        rfl
      rw [hg,map_star]
      exact defect_adjoint_tendsto R i
  have hw (w : CuntzPolynomial.Word) :
      Tendsto (fun n => defect R n (inclusion (MonoidAlgebra.of ℂ CuntzPolynomial.Word w)))
        atTop (𝓝 0) := by
    induction w using FreeMonoid.recOn with
    | one => simpa only [map_one,defect_one] using (tendsto_const_nhds : Tendsto (fun _ : ℕ => (0 : H →L[ℂ] Target H)) atTop (𝓝 0))
    | of_mul a w ih =>
      simp only [map_mul]
      exact intertwiningDefect_tendsto_mul R amplified.toNonUnitalStarAlgHom (averaged R) (hl a) ih
  induction p using MonoidAlgebra.induction_on with
  | of w => exact hw w
  | add p q hp hq => simpa only [map_add,add_zero] using hp.add hq
  | smul c p hp => simpa only [map_smul,smul_zero] using hp.const_smul c

end NuclearUltrapower.CuntzAveraging
end
end

end OAI
end

theorem solution.{u_1} : type_of% @OAI.NuclearUltrapower.CuntzAveraging.defect_polynomial_tendsto_oai.{u_1} := @OAI.NuclearUltrapower.CuntzAveraging.defect_polynomial_tendsto_oai.{u_1}
