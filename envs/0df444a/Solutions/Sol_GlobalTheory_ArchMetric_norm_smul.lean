-- Prove2me | solution 1 for GlobalTheory.ArchMetric.norm_smul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T17:36:35.720482+00:00
-- url     : https://prove2.me/submissions/962a3e0e-42f8-4e4a-9578-93de792d0fde

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_QuasicoherentCohomology_MemSaturatedOrderIsoSubspaceSpanSymmApply
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_FinrankMulDiscrRpowLeSumSqOfMemTraceDual
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ThetaMetrics_ExistsSmulMemOfMemSpanLattice
import Theorems.Thm_GlobalTheory_ArchMetric_form_smul_left
import Theorems.Thm_GlobalTheory_ArchMetric_form_smul_right
import Theorems.Thm_GlobalTheory_ArchMetric_form_self

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField Module Matrix
open scoped ComplexOrder ComplexConjugate
open GlobalTheory
open GlobalTheory.ArchMetric
variable {K : Type*} [Field K] {V V' V'' : Type*} [AddCommGroup V] [Module K V]
  [AddCommGroup V'] [Module K V'] [AddCommGroup V''] [Module K V'']
variable (h : ArchMetric K V)
namespace GlobalTheory.ArchMetric
theorem _root_.solution (σ : K →+* ℂ) (a : K) (x : V) : h.norm σ (a • x) = ‖σ a‖ * h.norm σ x := by
  refine (sq_eq_sq₀ (h.norm_nonneg _ _)
    (mul_nonneg (_root_.norm_nonneg _) (h.norm_nonneg _ _))).1 ?_
  apply Complex.ofReal_injective
  rw [← form_self, form_smul_left, form_smul_right, mul_pow, Complex.ofReal_mul, ← form_self,
    ← Complex.normSq_eq_norm_sq, ← Complex.mul_conj, mul_assoc]
end GlobalTheory.ArchMetric
