-- Prove2me | solution 1 for GlobalTheory.FGIndex.relIndex_ne_zero_coprime
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T14:51:13.394793+00:00
-- url     : https://prove2.me/submissions/b2a80f76-b4f6-498b-831e-f035ec8eac11

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_RelIndexCoprimeOfTorsion

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain
open GlobalTheory GlobalTheory.FGIndex
namespace GlobalTheory.FGIndex
theorem _root_.solution {G : Type} [AddCommGroup G] (A B : AddSubgroup G) (l : ℕ) (hl : l.Prime)
    (_hAB : A ≤ B) (hB : B.FG) (h : ∀ z ∈ B, ∃ n : ℕ, n.Coprime l ∧ n • z ∈ A) :
    A.relIndex B ≠ 0 ∧ (A.relIndex B).Coprime l := by
  haveI : AddGroup.FG B := (AddGroup.fg_iff_addSubgroup_fg B).2 hB
  haveI : AddGroup.FG (B ⧸ A.addSubgroupOf B) :=
    AddGroup.fg_of_surjective (QuotientAddGroup.mk'_surjective _)
  have hq : ∀ q : B ⧸ A.addSubgroupOf B, ∃ n : ℕ, n.Coprime l ∧ n • q = 0 := by
    intro q
    induction q using QuotientAddGroup.induction_on with
    | H b =>
      obtain ⟨n, hn, hnA⟩ := h b b.2
      refine ⟨n, hn, ?_⟩
      rw [← QuotientAddGroup.mk_nsmul, QuotientAddGroup.eq_zero_iff, AddSubgroup.mem_addSubgroupOf]
      simpa using hnA
  haveI : Finite (B ⧸ A.addSubgroupOf B) := by
    apply AddCommGroup.finite_of_fg_torsion
    intro q
    obtain ⟨n, hn, hnq⟩ := hq q
    have hn0 : 0 < n := by
      rcases Nat.eq_zero_or_pos n with h0 | h0
      · rw [h0, Nat.coprime_zero_left] at hn; exact absurd hn hl.one_lt.ne'
      · exact h0
    exact isOfFinAddOrder_iff_nsmul_eq_zero.mpr ⟨n, hn0, hnq⟩
  have h0 : A.relIndex B ≠ 0 := by
    rw [AddSubgroup.relIndex, AddSubgroup.index]
    exact Nat.card_pos.ne'
  refine ⟨h0, ?_⟩
  rw [Nat.coprime_comm, Nat.Prime.coprime_iff_not_dvd hl]
  intro hd
  haveI : Fact l.Prime := ⟨hl⟩
  rw [AddSubgroup.relIndex, AddSubgroup.index] at hd
  obtain ⟨x, hx⟩ := exists_prime_addOrderOf_dvd_card' (G := B ⧸ A.addSubgroupOf B) l hd
  obtain ⟨n, hn, hnx⟩ := hq x
  have : l ∣ n := hx ▸ addOrderOf_dvd_of_nsmul_eq_zero hnx
  exact (Nat.Prime.coprime_iff_not_dvd hl).1 (Nat.coprime_comm.1 hn) this
end GlobalTheory.FGIndex
