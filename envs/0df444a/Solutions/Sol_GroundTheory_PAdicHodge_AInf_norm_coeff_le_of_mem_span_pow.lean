-- Prove2me | solution 1 for GroundTheory.PAdicHodge.AInf.norm_coeff_le_of_mem_span_pow
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T00:58:23.423727+00:00
-- url     : https://prove2.me/submissions/326a7cd0-2b36-4b5f-92f9-9032a397f3a6

import Mathlib
import Definitions.Def_GroundTheory_PAdicHodge_KerFontaineThetaCompFrobeniusEquivSymmPow
import Definitions.Def_GroundTheory_PAdicHodge_AInfTopology
import Theorems.Thm_GroundTheory_PAdicHodge_WittVector_forall_lt_sub_coeff_mem_iff
import Theorems.Thm_GroundTheory_PAdicHodge_WittVector_coeff_mem_of_mem_span_teichmuller
import Theorems.Thm_GroundTheory_PAdicHodge_AInf_mem_span_pow_iff_norm_le
import Theorems.Thm_GroundTheory_PAdicHodge_WittVector_span_teichmuller_pow


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
theorem _root_.solution (ϖ : 𝒪♭) (N : ℕ) (d : AInf K p)
    (hd : d ∈ Ideal.span {(p : AInf K p), teichmuller p ϖ} ^ (N + N)) :
    ∀ i < N, ‖d.coeff i‖ ≤ ‖ϖ‖ ^ N := by
  rw [Ideal.span_insert] at hd
  obtain ⟨a, ha, b, hb, rfl⟩ := Submodule.mem_sup.1 (Ideal.sup_pow_add_le_pow_sup_pow hd)
  rw [Ideal.span_singleton_pow, mem_span_p_pow_iff_le_coeff_eq_zero] at ha
  rw [WittVector.span_teichmuller_pow] at hb
  have hb' := WittVector.coeff_mem_of_mem_span_teichmuller
    (Ideal.mem_span_singleton_self (ϖ ^ N)) hb
  have hab := (WittVector.forall_lt_sub_coeff_mem_iff (Ideal.span {ϖ ^ N}) N (a + b) b).2
    (fun i hi => by rw [add_sub_cancel_right, ha i hi]; exact Ideal.zero_mem _)
  intro i hi
  rw [← mem_span_pow_iff_norm_le]
  have := add_mem (hab i hi) (hb' i)
  rwa [sub_add_cancel] at this
end GroundTheory.PAdicHodge.AInf
