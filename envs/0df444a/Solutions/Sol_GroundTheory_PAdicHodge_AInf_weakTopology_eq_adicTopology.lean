-- Prove2me | solution 1 for GroundTheory.PAdicHodge.AInf.weakTopology_eq_adicTopology
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T01:14:58.305152+00:00
-- url     : https://prove2.me/submissions/4fea1f75-1b38-4028-9b0b-b679b0563698

import Mathlib
import Definitions.Def_GroundTheory_PAdicHodge_KerFontaineThetaCompFrobeniusEquivSymmPow
import Definitions.Def_GroundTheory_PAdicHodge_AInfTopology
import Theorems.Thm_GroundTheory_PAdicHodge_AInf_norm_coeff_sub_le_iff
import Theorems.Thm_GroundTheory_PAdicHodge_AInf_mem_span_pow_of_norm_coeff_le
import Theorems.Thm_GroundTheory_PAdicHodge_AInf_norm_coeff_sub_le_of_mem_span_pow
import Theorems.Thm_GroundTheory_PAdicHodge_AInf_continuous_coeff

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
    weakTopology K p = (Ideal.span {(p : AInf K p), teichmuller p ϖ}).adicTopology := by
  set J := Ideal.span {(p : AInf K p), teichmuller p ϖ}
  have hr : 0 < ‖ϖ‖ := norm_pos_iff.2 hϖ0
  apply le_antisymm
  · rw [le_iff_nhds]
    intro x
    rw [(J.hasBasis_nhds_adic x).ge_iff]
    intro n _
    let := weakTopology K p
    set N := n * p ^ n
    have hnN : n ≤ N := Nat.le_mul_of_pos_right n (pow_pos hp.out.pos n)
    have hmem : {y : AInf K p | ∀ i ∈ Finset.range N, ‖y.coeff i - x.coeff i‖ ≤ ‖ϖ‖ ^ N} ∈
        @nhds _ (weakTopology K p) x := by
      have : {y : AInf K p | ∀ i ∈ Finset.range N, ‖y.coeff i - x.coeff i‖ ≤ ‖ϖ‖ ^ N} =
          ⋂ i ∈ Finset.range N, {y : AInf K p | ‖y.coeff i - x.coeff i‖ ≤ ‖ϖ‖ ^ N} := by
        ext y; simp
      rw [this, @Filter.biInter_finset_mem]
      intro i _
      have hb : Metric.closedBall (x.coeff i) (‖ϖ‖ ^ N) ∈ 𝓝 (x.coeff i) :=
        Metric.closedBall_mem_nhds _ (pow_pos hr N)
      have := (continuous_coeff (K := K) (p := p) i).continuousAt (x := x) |>.preimage_mem_nhds hb
      convert this using 1
      ext y
      simp [Metric.mem_closedBall, dist_eq_norm]
    refine Filter.mem_of_superset hmem fun y hy => ⟨y - x, ?_, by simp⟩
    apply mem_span_pow_of_norm_coeff_le ϖ n
    intro i hi
    exact (norm_coeff_sub_le_iff ϖ N N y x).1 (fun j hj => hy j (Finset.mem_range.2 hj)) i
      (hi.trans_le hnN)
  · rw [le_iff_nhds]
    intro x s hs
    rw [(J.hasBasis_nhds_adic x).mem_iff]
    rw [weakTopology, nhds_induced, Filter.mem_comap] at hs
    obtain ⟨t, ht, hts⟩ := hs
    rw [nhds_pi, Filter.mem_pi'] at ht
    obtain ⟨I, u, hu, hIu⟩ := ht
    have hk : ∀ i, ∃ k : ℕ, ∀ z, ‖z - x.coeff i‖ ≤ ‖ϖ‖ ^ k → z ∈ u i := by
      intro i
      obtain ⟨ε, hε, hεu⟩ := Metric.mem_nhds_iff.1 (hu i)
      obtain ⟨k, hk⟩ := exists_pow_lt_of_lt_one hε hϖ1
      exact ⟨k, fun z hz => hεu (by rw [Metric.mem_ball, dist_eq_norm]; exact hz.trans_lt hk)⟩
    choose k hk using hk
    set N := max (I.sup id + 1) (I.sup k)
    refine ⟨N + N, trivial, ?_⟩
    rintro _ ⟨d, hd, rfl⟩
    apply hts
    apply hIu
    intro i hi
    have hiN : i < N := lt_of_lt_of_le (Nat.lt_succ_of_le (Finset.le_sup (f := id) hi))
      (le_max_left _ _)
    have hkN : k i ≤ N := (Finset.le_sup (f := k) hi).trans (le_max_right _ _)
    apply hk i
    have h1 := norm_coeff_sub_le_of_mem_span_pow ϖ N (x + d) x (by rwa [add_sub_cancel_left]) i hiN
    exact h1.trans (pow_le_pow_of_le_one (norm_nonneg _) (preTilt_norm_le_one _) hkN)
end GroundTheory.PAdicHodge.AInf
