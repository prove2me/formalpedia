-- Prove2me | solution 1 for GroundTheory.PAdicHodge.AInf.hasSum_teichmuller_coeff
-- status  : ACCEPTED   (prove)
-- author  : @garyholm
-- created : 2026-11-26T15:35:37.713601+00:00
-- url     : https://prove2.me/submissions/d4395d10-5635-4fca-b273-711247b8d22e

import Mathlib
import Definitions.Def_GroundTheory_PAdicHodge_KerFontaineThetaCompFrobeniusEquivSymmPow
import Definitions.Def_GroundTheory_PAdicHodge_AInfTopology
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

open GroundTheory.PAdicHodge.AInf in
theorem solution (x : AInf K p) :
    @HasSum (AInf K p) ℕ _ (pAdicTopology K p)
      (fun n => teichmuller p (((_root_.frobeniusEquiv 𝒪♭ p).symm ^ n) (x.coeff n)) *
        (p : AInf K p) ^ n) x (SummationFilter.unconditional ℕ) := by
  let I : Ideal (AInf K p) := Ideal.span {(p : AInf K p)}
  let f : ℕ → AInf K p := fun n =>
    teichmuller p (((_root_.frobeniusEquiv 𝒪♭ p).symm ^ n) (x.coeff n)) * (p : AInf K p) ^ n
  have hf : f = fun n =>
      teichmuller p (((_root_.frobeniusEquiv 𝒪♭ p).symm ^ n) (x.coeff n)) * (p : AInf K p) ^ n := rfl
  let := pAdicTopology K p
  refine I.hasBasis_nhds_adic x |>.tendsto_right_iff.mpr ?_
  intro N _
  refine Filter.eventually_atTop.mpr ?_
  rcases Nat.eq_zero_or_pos N with hN | hN
  · subst hN
    refine ⟨∅, fun s _ => ?_⟩
    refine ⟨∑ i ∈ s, f i - x, ?_, ?_⟩
    · have : I ^ 0 = ⊤ := by simp [pow_zero, Ideal.one_eq_top]
      rw [this]
      trivial
    · exact add_sub_cancel x (∑ i ∈ s, f i)
  refine ⟨Finset.Iic (N - 1), fun s hs => ?_⟩
  have hdiv :
      (p : AInf K p) ^ N ∣ x - ∑ i ∈ Finset.Iic (N - 1), f i := by
    have h :=
      WittVector.dvd_sub_sum_teichmuller_iterateFrobeniusEquiv_coeff
        (R := 𝒪♭) (p := p) x (N - 1)
    convert h
    rw [Nat.sub_add_cancel hN]
  have hx : x - ∑ i ∈ Finset.Iic (N - 1), f i ∈ I ^ N := by
    rw [Ideal.span_singleton_pow]
    exact Ideal.mem_span_singleton.mpr hdiv
  have hsplit : s = Finset.Iic (N - 1) ∪ s \ Finset.Iic (N - 1) :=
    (Finset.union_sdiff_of_subset hs).symm
  have hextra : ∑ i ∈ s \ Finset.Iic (N - 1), f i ∈ I ^ N := by
    refine sum_mem fun i hi => ?_
    have hiN : N ≤ i := by
      have : N - 1 < i := by
        simp only [Finset.mem_sdiff, Finset.mem_Iic, not_le] at hi
        exact hi.2
      exact (Nat.sub_add_cancel hN) ▸ Nat.succ_le_of_lt this
    have hpow : (p : AInf K p) ^ i = (p : AInf K p) ^ N * (p : AInf K p) ^ (i - N) := by
      rw [← pow_add, Nat.add_sub_cancel' hiN]
    have : f i =
        (teichmuller p (((_root_.frobeniusEquiv 𝒪♭ p).symm ^ i) (x.coeff i)) *
          (p : AInf K p) ^ (i - N)) * (p : AInf K p) ^ N := by
      unfold f
      rw [hpow]
      ring
    rw [this]
    exact Ideal.mul_mem_left _ _ (by
      rw [Ideal.span_singleton_pow]
      exact Ideal.mem_span_singleton_self _)
  have hmem : x - ∑ i ∈ s, f i ∈ I ^ N := by
    rw [hsplit, Finset.sum_union Finset.disjoint_sdiff, sub_add_eq_sub_sub]
    exact sub_mem hx hextra
  refine ⟨∑ i ∈ s, f i - x, ?_, ?_⟩
  · simpa [sub_eq_add_neg, add_comm] using (neg_mem hmem)
  · exact add_sub_cancel x (∑ i ∈ s, f i)
