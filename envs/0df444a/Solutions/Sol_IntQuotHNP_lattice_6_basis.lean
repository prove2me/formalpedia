-- Prove2me | solution 1 for IntQuotHNP.lattice_6_basis
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-11-07T17:59:10.043784+00:00
-- url     : https://prove2.me/submissions/a7ca69c3-96de-4183-87ca-16384fbf3995

import Mathlib
import Definitions.Def_IntQuotHNP_MIHNPInput
import Definitions.Def_IntQuotHNP_MIHNPLattice

namespace Aux_IQH6

theorem card_lt (N : ℕ) : Fintype.card {q : Fin N × Fin N // q.1 < q.2} * 2 = N * (N - 1) := by
  rw [Fintype.card_subtype, Finset.card_filter, Fintype.sum_prod_type]
  have h1 : ∀ i : Fin N, (∑ j : Fin N, if i < j then 1 else 0) = N - 1 - i := by
    intro i
    rw [Finset.sum_boole, Finset.filter_lt_eq_Ioi, Fin.card_Ioi]
    simp
  simp only [h1]
  rw [Fin.sum_univ_eq_sum_range (fun i => N - 1 - i) N, Finset.sum_range_reflect (fun i => i) N,
    Finset.sum_range_id_mul_two]

end Aux_IQH6

open IntQuotHNP Aux_IQH6 in
theorem solution (I : MIHNPInput) (hI : IsPromised I) :
    LinearIndependent ℝ (latticeBasis I) ∧ Fintype.card (Mon I.N) = I.N * (I.N + 1) / 2 := by
  obtain ⟨hp, _, _, hX, _⟩ := hI
  have hXR : (0 : ℝ) < I.X := by exact_mod_cast hX
  have hpR : (0 : ℝ) < I.p := by exact_mod_cast hp.pos
  constructor
  · rw [Fintype.linearIndependent_iff]
    intro g hg
    have hc : ∀ c : Mon I.N, ∑ i, g i * (latticeBasis I i) c = 0 := by
      intro c
      have := congrArg (fun w : EuclideanSpace ℝ (Mon I.N) => w c) hg
      simpa using this
    have hinl : ∀ q, g (Sum.inl q) = 0 := by
      intro q
      have h := hc (Sum.inl q)
      rw [Fintype.sum_sum_type] at h
      simp only [latticeBasis, mul_ite, mul_zero, Finset.sum_ite_eq', Finset.mem_univ,
        if_true, Finset.sum_const_zero, add_zero] at h
      have hX2 : (I.X : ℝ) ^ 2 ≠ 0 := by positivity
      exact (mul_eq_zero.mp h).resolve_right hX2
    intro i
    rcases i with q | h'
    · exact hinl q
    · have h := hc (Sum.inr h')
      rw [Fintype.sum_sum_type] at h
      simp only [hinl, zero_mul, Finset.sum_const_zero, zero_add] at h
      simp only [latticeBasis, mul_ite, mul_zero, Finset.sum_ite_eq', Finset.mem_univ,
        if_true] at h
      have hpX : (I.p : ℝ) * I.X ≠ 0 := by positivity
      exact (mul_eq_zero.mp h).resolve_right hpX
  · rw [Fintype.card_sum, Fintype.card_fin]
    have h := card_lt I.N
    have hQ : I.N * (I.N + 1) = I.N * (I.N - 1) + 2 * I.N := by
      rcases Nat.eq_zero_or_pos I.N with h0 | h0
      · rw [h0]
      · obtain ⟨m, hm⟩ : ∃ m, I.N = m + 1 := ⟨I.N - 1, by omega⟩
        rw [hm]
        simp only [Nat.add_sub_cancel]
        ring
    omega
