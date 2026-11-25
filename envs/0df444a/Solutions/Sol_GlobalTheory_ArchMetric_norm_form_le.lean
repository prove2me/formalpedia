-- Prove2me | solution 1 for GlobalTheory.ArchMetric.norm_form_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T05:59:43.277466+00:00
-- url     : https://prove2.me/submissions/851ecb93-3985-468e-9f85-8b5ac0abde55

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_QuasicoherentCohomology_MemSaturatedOrderIsoSubspaceSpanSymmApply
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_FinrankMulDiscrRpowLeSumSqOfMemTraceDual
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ThetaMetrics_ExistsSmulMemOfMemSpanLattice
import Theorems.Thm_GlobalTheory_ArchMetric_gramDet_nonneg
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
theorem _root_.solution (σ : K →+* ℂ) (x y : V) : ‖h.form σ x y‖ ≤ h.norm σ x * h.norm σ y := by
  have h1 := h.gramDet_nonneg σ ![x, y]
  have h2 : (h.gramDet σ ![x, y] : ℂ) =
      ((h.norm σ x ^ 2 * h.norm σ y ^ 2 - ‖h.form σ x y‖ ^ 2 : ℝ) : ℂ) := by
    rw [ofReal_gramDet, Matrix.det_fin_two, Complex.ofReal_sub, Complex.ofReal_mul, ← form_self,
      ← form_self, ← Complex.normSq_eq_norm_sq, ← Complex.mul_conj]
    simp
  rw [Complex.ofReal_injective h2, ← mul_pow, sub_nonneg] at h1
  exact (sq_le_sq₀ (_root_.norm_nonneg _)
    (mul_nonneg (h.norm_nonneg _ _) (h.norm_nonneg _ _))).1 h1
end GlobalTheory.ArchMetric
