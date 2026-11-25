-- Prove2me | solution 1 for GroundTheory.PAdicHodge.nrm_pow_sub_pow_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T01:35:21.729864+00:00
-- url     : https://prove2.me/submissions/2918c41c-087f-4528-add9-427571abae74

import Mathlib
import Definitions.Def_GroundTheory_LocalFields_SeparableClosure
import Definitions.Def_GroundTheory_PAdicHodge_FieldOfNormsTower
import Theorems.Thm_GroundTheory_PAdicHodge_nrm_nonneg
import Theorems.Thm_GroundTheory_PAdicHodge_nrm_mul
import Theorems.Thm_GroundTheory_PAdicHodge_nrm_pow
import Theorems.Thm_GroundTheory_PAdicHodge_nrm_sum_le

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
noncomputable section
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false
open GroundTheory GroundTheory.PAdicHodge
open GroundTheory.LocalField ValuativeRel Filter Topology
variable {K : Type*} [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
variable {Ω : Type*} [Field Ω] [Algebra K Ω] [Algebra.IsAlgebraic K Ω]
namespace GroundTheory.PAdicHodge
theorem _root_.solution {a b : Ω} (ha : nrm K a ≤ 1) (hb : nrm K b ≤ 1) (n : ℕ) :
    nrm K (a ^ n - b ^ n) ≤ nrm K (a - b) := by
  rw [← geom_sum₂_mul, nrm_mul]
  have : nrm K (∑ i ∈ Finset.range n, a ^ i * b ^ (n - 1 - i)) ≤ 1 := by
    refine nrm_sum_le zero_le_one fun i _ ↦ ?_
    rw [nrm_mul, nrm_pow, nrm_pow]
    exact mul_le_one₀ (pow_le_one₀ (nrm_nonneg _) ha) (pow_nonneg (nrm_nonneg _) _)
      (pow_le_one₀ (nrm_nonneg _) hb)
  calc _ ≤ 1 * nrm K (a - b) := mul_le_mul_of_nonneg_right this (nrm_nonneg _)
    _ = _ := one_mul _
end GroundTheory.PAdicHodge
