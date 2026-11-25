-- Prove2me | solution 1 for GroundTheory.PAdicHodge.AInf.hasSum_teichmullerSeries
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T00:43:34.883052+00:00
-- url     : https://prove2.me/submissions/77549ad1-c5a0-4ff1-b442-afaa1c59ea1b

import Mathlib
import Definitions.Def_GroundTheory_PAdicHodge_KerFontaineThetaCompFrobeniusEquivSymmPow
import Definitions.Def_GroundTheory_PAdicHodge_AInfTopology
import Theorems.Thm_GroundTheory_PAdicHodge_WittVector_dvd_sub_sum_teichmullerSeries


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
theorem _root_.solution (a : ℕ → 𝒪♭) :
    @HasSum (AInf K p) ℕ _ (pAdicTopology K p) (fun n => teichmuller p (a n) * (p : AInf K p) ^ n)
      (WittVector.teichmullerSeries a) (SummationFilter.unconditional ℕ) := by
  let := pAdicTopology K p
  set I := Ideal.span {(p : AInf K p)}
  change Tendsto _ atTop _
  rw [(I.hasBasis_nhds_adic _).tendsto_right_iff]
  intro n _
  rcases n with _ | n
  · exact Eventually.of_forall fun s =>
      ⟨(∑ i ∈ s, teichmuller p (a i) * (p : AInf K p) ^ i) - WittVector.teichmullerSeries a,
        by simp, by simp⟩
  filter_upwards [eventually_ge_atTop (Finset.Iic n)] with s hs
  refine ⟨(∑ i ∈ s, teichmuller p (a i) * (p : AInf K p) ^ i) - WittVector.teichmullerSeries a,
    ?_, by simp⟩
  have h1 : WittVector.teichmullerSeries a -
      ∑ i ∈ Finset.Iic n, teichmuller p (a i) * (p : AInf K p) ^ i ∈ I ^ (n + 1) := by
    rw [Ideal.span_singleton_pow, Ideal.mem_span_singleton]
    exact WittVector.dvd_sub_sum_teichmullerSeries a n
  have h2 : ∑ i ∈ s \ Finset.Iic n, teichmuller p (a i) * (p : AInf K p) ^ i ∈
      I ^ (n + 1) := by
    refine Ideal.sum_mem _ fun i hi => ?_
    have hi' : n + 1 ≤ i := by
      have := (Finset.mem_sdiff.1 hi).2
      rw [Finset.mem_Iic, not_le] at this
      exact this
    rw [Ideal.span_singleton_pow]
    exact Ideal.mul_mem_left _ _ (Ideal.mem_span_singleton.2 (pow_dvd_pow _ hi'))
  rw [SetLike.mem_coe, ← Finset.sum_sdiff hs]
  have e : ∑ i ∈ s \ Finset.Iic n, teichmuller p (a i) * (p : AInf K p) ^ i +
      ∑ i ∈ Finset.Iic n, teichmuller p (a i) * (p : AInf K p) ^ i -
        WittVector.teichmullerSeries a =
      ∑ i ∈ s \ Finset.Iic n, teichmuller p (a i) * (p : AInf K p) ^ i -
        (WittVector.teichmullerSeries a -
          ∑ i ∈ Finset.Iic n, teichmuller p (a i) * (p : AInf K p) ^ i) := by ring
  rw [e]
  exact sub_mem h2 h1
end GroundTheory.PAdicHodge.AInf
