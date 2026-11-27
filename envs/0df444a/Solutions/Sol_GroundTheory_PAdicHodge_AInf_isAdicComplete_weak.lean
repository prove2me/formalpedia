-- Prove2me | solution 1 for GroundTheory.PAdicHodge.AInf.isAdicComplete_weak
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-27T04:48:50.62453+00:00
-- url     : https://prove2.me/submissions/5d97d8b2-950d-4f80-a3fe-0f59ef6e4598

import Mathlib
import Definitions.Def_GroundTheory_PAdicHodge_KerFontaineThetaCompFrobeniusEquivSymmPow
import Definitions.Def_GroundTheory_PAdicHodge_AInfTopology
import Theorems.Thm_GroundTheory_PAdicHodge_AInf_norm_coeff_sub_le_iff
import Theorems.Thm_GroundTheory_PAdicHodge_AInf_mem_span_pow_of_norm_coeff_le
import Theorems.Thm_GroundTheory_PAdicHodge_AInf_norm_coeff_le_of_mem_span_pow
import Theorems.Thm_GroundTheory_PAdicHodge_AInf_norm_coeff_sub_le_of_mem_span_pow
import Theorems.Thm_GroundTheory_PAdicHodge_AInf_smodEq_pow_iff

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
open WittVector Filter Topology
open GroundTheory GroundTheory.PAdicHodge
open GroundTheory.PAdicHodge.AInf
variable {K : Type*} [NontriviallyNormedField K] [IsUltrametricDist K]
variable {p : ℕ} [hp : Fact p.Prime] [IsPerfectoidField K p]
local notation "𝒪♭" => PreTilt (normInteger K) p
namespace GroundTheory.PAdicHodge.AInf
theorem _root_.solution (ϖ : 𝒪♭) (hϖ0 : ϖ ≠ 0) (hϖ1 : ‖ϖ‖ < 1) :
    IsAdicComplete (Ideal.span {(p : AInf K p), teichmuller p ϖ}) (AInf K p) := by
  set J := Ideal.span {(p : AInf K p), teichmuller p ϖ}
  have hr : 0 < ‖ϖ‖ := norm_pos_iff.2 hϖ0
  have ht := tendsto_pow_atTop_nhds_zero_of_lt_one hr.le hϖ1
  refine { haus' := fun x hx => ?_, prec' := fun f hf => ?_ }
  · ext i
    rw [zero_coeff, ← norm_le_zero_iff]
    refine ge_of_tendsto ht (eventually_atTop.2 ⟨i + 1, fun N hN => ?_⟩)
    have := (smodEq_pow_iff J (N + N) x 0).1 (hx (N + N))
    rw [sub_zero] at this
    exact norm_coeff_le_of_mem_span_pow ϖ N x this i hN
  · have hf' : ∀ m n, m ≤ n → f m - f n ∈ J ^ m := fun m n h => (smodEq_pow_iff J m _ _).1 (hf h)
    have hcauchy : ∀ i, CauchySeq fun m => (f m).coeff i := by
      intro i
      rw [Metric.cauchySeq_iff']
      intro ε hε
      obtain ⟨M, hM⟩ := exists_pow_lt_of_lt_one hε hϖ1
      refine ⟨(M + i + 1) + (M + i + 1), fun m hm => ?_⟩
      have h1 := norm_coeff_sub_le_of_mem_span_pow ϖ (M + i + 1) _ _ (hf' _ m hm) i (by omega)
      rw [dist_eq_norm, norm_sub_rev]
      exact h1.trans_lt ((pow_le_pow_of_le_one (norm_nonneg _) hϖ1.le (by omega)).trans_lt hM)
    choose c hc using fun i => cauchySeq_tendsto_of_complete (hcauchy i)
    refine ⟨WittVector.mk p c, fun n => ?_⟩
    rw [smodEq_pow_iff]
    set N := n * p ^ n
    have hev : ∀ᶠ m in atTop, ∀ i ∈ Finset.range N, ‖(f m).coeff i - c i‖ ≤ ‖ϖ‖ ^ N := by
      rw [Filter.eventually_all_finset]
      intro i _
      filter_upwards [(hc i).eventually (Metric.closedBall_mem_nhds (c i) (pow_pos hr N))] with m hm
      rwa [dist_eq_norm] at hm
    obtain ⟨m, hm, hmn⟩ := (hev.and (eventually_ge_atTop n)).exists
    have h2 : f m - WittVector.mk p c ∈ J ^ n := by
      apply mem_span_pow_of_norm_coeff_le ϖ n
      intro i hi
      refine (norm_coeff_sub_le_iff ϖ N N (f m) (WittVector.mk p c)).1 (fun j hj => ?_) i
        (hi.trans_le (Nat.le_mul_of_pos_right n (pow_pos hp.out.pos n)))
      rw [coeff_mk]
      exact hm j (Finset.mem_range.2 hj)
    have := add_mem (hf' n m hmn) h2
    rwa [sub_add_sub_cancel] at this
end GroundTheory.PAdicHodge.AInf
