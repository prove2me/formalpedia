-- Prove2me | solution 1 for GroundTheory.PAdicHodge.AInf.isAdicComplete_teichmuller
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-27T04:51:20.664075+00:00
-- url     : https://prove2.me/submissions/977b832f-fb71-49c4-b3af-99ec3e184584

import Mathlib
import Definitions.Def_GroundTheory_PAdicHodge_KerFontaineThetaCompFrobeniusEquivSymmPow
import Definitions.Def_GroundTheory_PAdicHodge_AInfTopology
import Theorems.Thm_P2M_GroundTheory_PAdicHodge_AInf_norm_coeff_sub_le_iff__1c580b85cbe3
import Theorems.Thm_GroundTheory_PAdicHodge_AInf_mem_span_teichmuller_pow_iff_norm_le
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
    IsAdicComplete (Ideal.span {(teichmuller p ϖ : AInf K p)}) (AInf K p) := by
  set I := Ideal.span {(teichmuller p ϖ : AInf K p)}
  have hr : 0 < ‖ϖ‖ := norm_pos_iff.2 hϖ0
  have ht := tendsto_pow_atTop_nhds_zero_of_lt_one hr.le hϖ1
  have hle : ∀ (n : ℕ) (d : AInf K p), d ∈ I ^ n → ∀ i, ‖d.coeff i‖ ≤ ‖ϖ‖ ^ n := by
    intro n d hd i
    refine ((mem_span_teichmuller_pow_iff_norm_le ϖ n d).1 hd i).trans ?_
    exact pow_le_pow_of_le_one (norm_nonneg _) hϖ1.le
      (Nat.le_mul_of_pos_right n (pow_pos hp.out.pos i))
  refine { haus' := fun x hx => ?_, prec' := fun f hf => ?_ }
  · ext i
    rw [zero_coeff, ← norm_le_zero_iff]
    refine ge_of_tendsto ht (Eventually.of_forall fun n => ?_)
    have := (smodEq_pow_iff I n x 0).1 (hx n)
    rw [sub_zero] at this
    exact hle n x this i
  · have hf' : ∀ m n, m ≤ n → ∀ i, ‖(f m).coeff i - (f n).coeff i‖ ≤ ‖ϖ‖ ^ m :=
      fun m n h => (norm_coeff_sub_le_iff' ϖ m _ _).2 (hle m _ ((smodEq_pow_iff I m _ _).1 (hf h)))
    have hcauchy : ∀ i, CauchySeq fun m => (f m).coeff i := by
      intro i
      rw [Metric.cauchySeq_iff']
      intro ε hε
      obtain ⟨M, hM⟩ := exists_pow_lt_of_lt_one hε hϖ1
      refine ⟨M, fun m hm => ?_⟩
      rw [dist_eq_norm, norm_sub_rev]
      exact (hf' M m hm i).trans_lt hM
    choose c hc using fun i => cauchySeq_tendsto_of_complete (hcauchy i)
    have hlim : ∀ m i, ‖(f m).coeff i - c i‖ ≤ ‖ϖ‖ ^ m := by
      intro m i
      exact le_of_tendsto (((hc i).const_sub ((f m).coeff i)).norm)
        (eventually_atTop.2 ⟨m, fun n hn => hf' m n hn i⟩)
    refine ⟨WittVector.mk p c, fun n => ?_⟩
    rw [smodEq_pow_iff, mem_span_teichmuller_pow_iff_norm_le]
    intro i
    set M := n * p ^ i
    have hnM : n ≤ M := Nat.le_mul_of_pos_right n (pow_pos hp.out.pos i)
    have hd : ‖(f n - f M).coeff i‖ ≤ ‖ϖ‖ ^ M :=
      (mem_span_teichmuller_pow_iff_norm_le ϖ n _).1
        ((smodEq_pow_iff I n _ _).1 (hf hnM)) i
    have he : ∀ j, ‖(f M - WittVector.mk p c).coeff j‖ ≤ ‖ϖ‖ ^ M :=
      (norm_coeff_sub_le_iff' ϖ M _ _).1 fun j => by rw [coeff_mk]; exact hlim M j
    have hde := (norm_coeff_sub_le_iff' ϖ M ((f n - f M) + (f M - WittVector.mk p c))
      (f n - f M)).2 (fun j => by rw [add_sub_cancel_left]; exact he j) i
    rw [sub_add_sub_cancel] at hde
    calc ‖(f n - WittVector.mk p c).coeff i‖
        = ‖((f n - WittVector.mk p c).coeff i - (f n - f M).coeff i) + (f n - f M).coeff i‖ := by
          rw [sub_add_cancel]
      _ ≤ max ‖(f n - WittVector.mk p c).coeff i - (f n - f M).coeff i‖ ‖(f n - f M).coeff i‖ :=
          IsUltrametricDist.norm_add_le_max _ _
      _ ≤ ‖ϖ‖ ^ M := max_le hde hd
end GroundTheory.PAdicHodge.AInf
