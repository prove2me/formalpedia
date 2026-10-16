-- Prove2me | solution 1 for OAI.PartialPermutation.leftKernel_l2
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-15T20:51:57.051993+00:00
-- url     : https://prove2.me/submissions/d1d9bbf4-c570-49bf-b24e-8d26c9f102b8

-- Generated from openai/math@1581d4c lean/OAI/RepresentationTheory/PartialPermutation/ConvolutionKernels.lean:L31-L57
-- (upload_full_project.md Phase 4): solution for node OAI.PartialPermutation.leftKernel_l2. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` has its type (`type_of%`) and is proved by it.
import Mathlib
import Definitions.Def_PartialPermutation
import Definitions.Def_OAI_RepresentationTheory_PartialPermutation_SchurAverage
import Definitions.Def_OAI_RepresentationTheory_PartialPermutation_ModuleTransport
import Definitions.Def_OAI_RepresentationTheory_PartialPermutation_Components
import Definitions.Def_OAI_RepresentationTheory_PartialPermutation_CentralKernels
import Definitions.Def_OAI_RepresentationTheory_PartialPermutation_CompleteKernels
import Definitions.Def_OAI_RepresentationTheory_PartialPermutation_RegularRepresentation
import Definitions.Def_OAI_RepresentationTheory_PartialPermutation_Plancherel
import Definitions.Def_OAI_RepresentationTheory_PartialPermutation_TrivialRepresentation
import Definitions.Def_OAI_RepresentationTheory_PartialPermutation_ConvolutionKernels
import Theorems.Thm_OAI_PartialPermutation_norm_sum_weighted_sq_le

-- ---- from OAI.RepresentationTheory.PartialPermutation.ConvolutionKernels ----
namespace OAI

section
open scoped Classical
open scoped BigOperators ComplexConjugate MonoidAlgebra
open scoped BigOperators ComplexConjugate
open scoped MonoidAlgebra BigOperators
open scoped BigOperators MonoidAlgebra Classical

attribute [local instance] Classical.propDecidable
namespace PartialPermutation
open scoped BigOperators ComplexConjugate

noncomputable section

section
variable {G : Type*} [Group G] [Fintype G]

lemma leftKernel_l2 (H : Subgroup G) (k : H → ℂ) (f : G → ℝ) (B : ℝ)
    (hf : ∀ g, 0 ≤ f g) (hcap : RightCosetCap f H B) :
    ∑ g, ‖leftKernel H k f g‖ ^ 2 ≤
      B / H.index * mass f * ∑ h : H, ‖k h‖ ^ 2 := by
  classical
  have hp (g : G) : ∑ h : H, f ((h : G)⁻¹ * g) ≤ B / H.index := by
    have he : ∑ h : H, f ((h : G)⁻¹ * g) = ∑ h : H, f ((h : G) * g) := by
      exact Fintype.sum_equiv (Equiv.inv H) _ _ (fun h => rfl)
    rw [he]
    exact hcap g
  have hpt (g : G) : ‖leftKernel H k f g‖ ^ 2 ≤
      B / H.index * ∑ h : H, f ((h : G)⁻¹ * g) * ‖k h‖ ^ 2 := by
    have h := norm_sum_weighted_sq_le (fun h : H => f ((h : G)⁻¹ * g))
      (fun h => hf _) k
    change ‖∑ h : H, k h * (f ((h : G)⁻¹ * g) : ℂ)‖ ^ 2 ≤ _
    simp_rw [mul_comm (k _)]
    exact h.trans (mul_le_mul_of_nonneg_right (hp g)
      (Finset.sum_nonneg fun h _ => mul_nonneg (hf _) (sq_nonneg _)))
  calc
    _ ≤ ∑ g, B / H.index * ∑ h : H, f ((h : G)⁻¹ * g) * ‖k h‖ ^ 2 :=
      Finset.sum_le_sum fun g _ => hpt g
    _ = _ := by
      rw [← Finset.mul_sum, Finset.sum_comm]
      have he (h : H) : ∑ g, f ((h : G)⁻¹ * g) = mass f := by
        exact Fintype.sum_equiv (Equiv.mulLeft (h : G)⁻¹) _ _ (fun g => rfl)
      simp_rw [← Finset.sum_mul, he]
      rw [← Finset.mul_sum, mul_assoc]

end
end
end PartialPermutation

end

end OAI

-- ---- platform node ----
open OAI OAI.PartialPermutation
open scoped Classical
open scoped BigOperators ComplexConjugate MonoidAlgebra
open scoped BigOperators ComplexConjugate
open scoped MonoidAlgebra BigOperators
open scoped BigOperators MonoidAlgebra Classical
attribute [local instance] Classical.propDecidable
open scoped BigOperators ComplexConjugate


theorem solution : type_of% @_root_.OAI.PartialPermutation.leftKernel_l2 := @_root_.OAI.PartialPermutation.leftKernel_l2
