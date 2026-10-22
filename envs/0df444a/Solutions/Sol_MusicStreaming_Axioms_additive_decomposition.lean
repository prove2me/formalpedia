-- Prove2me | solution 1 for MusicStreaming.Axioms.additive_decomposition
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-21T08:59:54.986633+00:00
-- url     : https://prove2.me/submissions/28fbbd07-b608-4f7f-aec7-88d2b8c18d2d

import Mathlib
import Definitions.Def_MusicStreaming_Axioms_Setting

set_option autoImplicit false
open MusicStreaming.Axioms

section MSA2
variable {n : ℕ}

lemma msa2_I_zero (I : Index n) (hA : Additivity I) : I 0 = 0 := by
  funext i
  have h2 : I 0 i = I 0 i + I 0 i := by simpa using congrFun (hA 0 0 (by simp)) i
  show I 0 i = 0
  linarith

lemma msa2_decomp (I : Index n) (hA : Additivity I) :
    ∀ (N : ℕ) (t : Problem n), t.support.card = N → ∀ i,
      I t i = ∑ j ∈ t.support, I (Finsupp.single j (t j)) i := by
  intro N
  induction N with
  | zero =>
    intro t ht i
    have h1 : t.support = ∅ := Finset.card_eq_zero.mp ht
    have h2 : t = 0 := Finsupp.support_eq_empty.mp h1
    subst h2
    simp [msa2_I_zero I hA]
  | succ N ih =>
    intro t ht i
    obtain ⟨j, hj⟩ : t.support.Nonempty := Finset.card_pos.mp (by omega)
    have htj : t j ≠ 0 := Finsupp.mem_support_iff.mp hj
    have hsplit : t = Finsupp.single j (t j) + t.erase j := (Finsupp.single_add_erase j t).symm
    have hd : Disjoint (Finsupp.single j (t j)).support (t.erase j).support := by
      rw [Finsupp.support_single_ne_zero j htj, Finsupp.support_erase]; simp
    have hcard : (t.erase j).support.card = N := by
      rw [Finsupp.support_erase, Finset.card_erase_of_mem hj]; omega
    have h1 := congrFun (hA _ _ hd) i
    rw [← hsplit] at h1
    simp only [Pi.add_apply] at h1
    rw [h1, ih (t.erase j) hcard i, ← Finset.add_sum_erase t.support _ hj, Finsupp.support_erase]
    congr 1
    refine Finset.sum_congr rfl fun k hk => ?_
    rw [Finsupp.erase_ne (Finset.ne_of_mem_erase hk)]

end MSA2

theorem solution {n : ℕ} (I : Index n) (hA : Additivity I) :
    ∀ (t : Problem n) (i : Fin n), I t i = ∑ j ∈ t.support, I (Finsupp.single j (t j)) i :=
  fun t i => msa2_decomp I hA _ t rfl i
