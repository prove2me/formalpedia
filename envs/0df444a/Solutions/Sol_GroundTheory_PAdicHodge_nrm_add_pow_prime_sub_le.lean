-- Prove2me | solution 1 for GroundTheory.PAdicHodge.nrm_add_pow_prime_sub_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T03:50:16.750679+00:00
-- url     : https://prove2.me/submissions/ed637bfb-ac7a-4673-a36b-127b0e8183ed

import Mathlib
import Definitions.Def_GroundTheory_LocalFields_SeparableClosure
import Definitions.Def_GroundTheory_PAdicHodge_FieldOfNormsTower
import Theorems.Thm_GroundTheory_PAdicHodge_nrm_nonneg
import Theorems.Thm_GroundTheory_PAdicHodge_nrm_mul
import Theorems.Thm_GroundTheory_PAdicHodge_nrm_mul_le_one
import Theorems.Thm_GroundTheory_PAdicHodge_nrm_binomialSum_le

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
variable {p : ℕ}
namespace GroundTheory.PAdicHodge
theorem _root_.solution (hp : p.Prime) {a b : Ω} (ha : nrm K a ≤ 1) (hb : nrm K b ≤ 1) :
    nrm K ((a + b) ^ p - a ^ p - b ^ p) ≤ nrm K (p : Ω) := by
  rw [add_pow_prime_eq hp a b]
  have e : a ^ p + b ^ p + (p : Ω) * a * b *
      ∑ k ∈ Finset.Ioo 0 p, a ^ (k - 1) * b ^ (p - k - 1) * ((p.choose k / p : ℕ) : Ω) - a ^ p - b ^ p
      = (p : Ω) * (a * b * ∑ k ∈ Finset.Ioo 0 p, a ^ (k - 1) * b ^ (p - k - 1) *
        ((p.choose k / p : ℕ) : Ω)) := by ring
  rw [e, nrm_mul]
  have := nrm_mul_le_one (nrm_mul_le_one ha hb) (nrm_binomialSum_le (p := p) a b ha hb)
  calc _ ≤ nrm K (p : Ω) * 1 := mul_le_mul_of_nonneg_left this (nrm_nonneg _)
    _ = _ := mul_one _
end GroundTheory.PAdicHodge
