-- Prove2me | solution 1 for GlobalTheory.ph_a_basis
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T23:28:51.27316+00:00
-- url     : https://prove2.me/submissions/fee71a41-d4e1-4382-9c8d-897a01ae15c1

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ExistsIndependentModPrimeOfPowLeCard
import Theorems.Thm_GlobalTheory_exists_linearIndependent_of_pow_le_card_zmod

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Polynomial
open GlobalTheory
namespace GlobalTheory
theorem _root_.solution : ∀ (l : ℕ) [Fact l.Prime] (V ι : Type) [AddCommGroup V] (K' : AddSubgroup V) (h : ℕ)
    (Z : Finset ι) (v : ι → V), (∀ x : V, l • x = 0) → l ^ h ≤ Z.card →
    (∀ i ∈ Z, ∀ i' ∈ Z, i ≠ i' → v i - v i' ∉ K') →
    ∃ x : Fin h → ι, (∀ a, x a ∈ Z) ∧ ∀ n : Fin h → ℕ, ∑ a, n a • v (x a) ∈ K' → ∀ a, l ∣ n a := by
  intro l _ V ι _ K' h Z v hl hcard hdist
  have hQ : ∀ y : V ⧸ K', l • y = 0 := by
    intro y
    induction y using QuotientAddGroup.induction_on with
    | H z => rw [← QuotientAddGroup.mk_nsmul, hl z]; rfl
  letI : Module (ZMod l) (V ⧸ K') := AddCommGroup.zmodModule hQ
  have hinj : Set.InjOn (fun i => (v i : V ⧸ K')) Z := by
    intro i hi i' hi' he
    by_contra hne
    exact hdist i hi i' hi' hne ((QuotientAddGroup.eq_iff_sub_mem).1 he)
  obtain ⟨x, hxZ, hli⟩ := exists_linearIndependent_of_pow_le_card_zmod l Z (fun i => (v i : V ⧸ K')) hinj h hcard
  refine ⟨x, hxZ, ?_⟩
  intro n hn a
  have hm : QuotientAddGroup.mk' K' (∑ a, n a • v (x a)) = 0 := (QuotientAddGroup.eq_zero_iff _).2 hn
  rw [map_sum] at hm
  simp only [map_nsmul, QuotientAddGroup.mk'_apply] at hm
  have hsum : ∑ a, (n a : ZMod l) • ((v (x a) : V ⧸ K')) = 0 := by
    rw [← hm]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [Nat.cast_smul_eq_nsmul]
  have hz := Fintype.linearIndependent_iff.1 hli (fun a => (n a : ZMod l)) hsum a
  exact (ZMod.natCast_eq_zero_iff _ _).1 hz
end GlobalTheory
