-- Prove2me | solution 1 for GroundTheory.PAdicHodge.AInf.mem_span_pow_of_norm_coeff_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T00:43:44.821539+00:00
-- url     : https://prove2.me/submissions/411a7ee6-c5f0-4903-9449-3abe0af9562d

import Mathlib
import Definitions.Def_GroundTheory_PAdicHodge_KerFontaineThetaCompFrobeniusEquivSymmPow
import Definitions.Def_GroundTheory_PAdicHodge_AInfTopology
import Theorems.Thm_GroundTheory_PAdicHodge_WittVector_dvd_sub_sum_teichmullerSeries
import Theorems.Thm_GroundTheory_PAdicHodge_WittVector_teichmullerSeries_coeff_eq
import Theorems.Thm_GroundTheory_PAdicHodge_frobeniusEquiv_symm_pow_apply_pow


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
theorem _root_.solution (ϖ : 𝒪♭) (n : ℕ) (d : AInf K p)
    (h : ∀ i < n, ‖d.coeff i‖ ≤ ‖ϖ‖ ^ (n * p ^ n)) :
    d ∈ Ideal.span {(p : AInf K p), teichmuller p ϖ} ^ n := by
  rcases n with _ | n
  · simp
  set c : ℕ → 𝒪♭ := fun i => ((_root_.frobeniusEquiv 𝒪♭ p).symm ^ i) (d.coeff i) with hc
  have hexp := WittVector.dvd_sub_sum_teichmullerSeries (p := p) c n
  rw [hc, WittVector.teichmullerSeries_coeff_eq, ← hc] at hexp
  obtain ⟨z, hz⟩ := hexp
  have hd : d = ∑ i ∈ Finset.Iic n, teichmuller p (c i) * (p : AInf K p) ^ i +
      (p : AInf K p) ^ (n + 1) * z := by
    rw [← hz]; ring
  rw [hd]
  have hpJ : (p : AInf K p) ∈ Ideal.span {(p : AInf K p), teichmuller p ϖ} :=
    Ideal.subset_span (by simp)
  have hϖJ : teichmuller p ϖ ∈ Ideal.span {(p : AInf K p), teichmuller p ϖ} :=
    Ideal.subset_span (by simp)
  refine add_mem (Ideal.sum_mem _ fun i hi => ?_) (Ideal.mul_mem_right _ _ (Ideal.pow_mem_pow hpJ _))
  have hin : i < n + 1 := Nat.lt_succ_of_le (Finset.mem_Iic.1 hi)
  have hci : ϖ ^ (n + 1) ∣ c i := by
    rw [preTilt_dvd_iff_norm_le, norm_pow]
    have h1 : ‖c i‖ ^ p ^ i = ‖d.coeff i‖ := by
      rw [← norm_pow, hc, frobeniusEquiv_symm_pow_apply_pow]
    have h2 : ‖ϖ‖ ^ ((n + 1) * p ^ (n + 1)) ≤ (‖ϖ‖ ^ (n + 1)) ^ p ^ i := by
      rw [← pow_mul]
      exact pow_le_pow_of_le_one (norm_nonneg _) (preTilt_norm_le_one ϖ)
        (Nat.mul_le_mul_left _ (Nat.pow_le_pow_right hp.out.pos hin.le))
    exact (pow_le_pow_iff_left₀ (norm_nonneg _) (by positivity)
      (pow_ne_zero _ hp.out.ne_zero)).1 (h1 ▸ (h i hin).trans h2)
  obtain ⟨e, he⟩ := hci
  rw [he, map_mul, map_pow]
  exact Ideal.mul_mem_right _ _ (Ideal.mul_mem_right _ _ (Ideal.pow_mem_pow hϖJ _))
end GroundTheory.PAdicHodge.AInf
