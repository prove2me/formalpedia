-- Prove2me | solution 1 for GroundTheory.PAdicHodge.norm_le_one_of_eval_eq_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T00:19:07.603804+00:00
-- url     : https://prove2.me/submissions/7bbd3ac5-eb37-4ed6-9d4e-b97b37218d02

import Mathlib
import Definitions.Def_GroundTheory_PAdicHodge_TiltAlgebra
import Definitions.Def_GroundTheory_PAdicHodge_AxLemma
import Definitions.Def_GroundTheory_PAdicHodge_UntiltApproxLemmas
import Theorems.Thm_GroundTheory_PAdicHodge_norm_multiset_sum_le_of_forall_le
import Theorems.Thm_GroundTheory_PAdicHodge_tiltMap_algebraMap
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GroundTheory.PAdicHodge.tiltMap_algebraMap



set_option autoImplicit false
set_option maxSynthPendingDepth 1
noncomputable section
open GroundTheory GroundTheory.PAdicHodge
open Polynomial
variable {E : Type*} [NormedField E] [IsUltrametricDist E]
namespace GroundTheory.PAdicHodge
theorem _root_.solution {f : E[X]} (hf : f.Monic) (hc : ∀ n, ‖f.coeff n‖ ≤ 1)
    {r : E} (hr : f.eval r = 0) : ‖r‖ ≤ 1 := by
  by_contra hlt
  push Not at hlt
  set d := f.natDegree
  have hr0 : 0 < ‖r‖ := one_pos.trans hlt
  have hsum : ‖∑ i ∈ Finset.range d, f.coeff i * r ^ i‖ < ‖r‖ ^ d := by
    rcases Nat.eq_zero_or_pos d with hd | hd
    · rw [hd]; simp
    have hle : ∀ i ∈ Finset.range d, ‖f.coeff i * r ^ i‖ ≤ ‖r‖ ^ (d - 1) := by
      intro i hi
      rw [norm_mul, norm_pow]
      calc ‖f.coeff i‖ * ‖r‖ ^ i ≤ 1 * ‖r‖ ^ i := by gcongr; exact hc i
        _ = ‖r‖ ^ i := one_mul _
        _ ≤ ‖r‖ ^ (d - 1) := pow_le_pow_right₀ hlt.le (by
            have := Finset.mem_range.1 hi; omega)
    calc ‖∑ i ∈ Finset.range d, f.coeff i * r ^ i‖ ≤ ‖r‖ ^ (d - 1) := by
          have := norm_multiset_sum_le_of_forall_le (s := (Finset.range d).val.map
            fun i => f.coeff i * r ^ i) (pow_nonneg hr0.le _) (by
              intro a ha
              obtain ⟨i, hi, rfl⟩ := Multiset.mem_map.1 ha
              exact hle i hi)
          simpa [Finset.sum_eq_multiset_sum] using this
      _ < ‖r‖ ^ d := pow_lt_pow_right₀ hlt (by omega)
  have heval : f.eval r = ∑ i ∈ Finset.range d, f.coeff i * r ^ i + r ^ d := by
    rw [eval_eq_sum_range, Finset.sum_range_succ, hf.coeff_natDegree, one_mul]
  rw [heval] at hr
  have : ‖r ^ d‖ = ‖∑ i ∈ Finset.range d, f.coeff i * r ^ i‖ := by
    rw [eq_neg_of_add_eq_zero_right hr, norm_neg]
  rw [norm_pow] at this
  exact (lt_irrefl _) (this ▸ hsum)
end GroundTheory.PAdicHodge
