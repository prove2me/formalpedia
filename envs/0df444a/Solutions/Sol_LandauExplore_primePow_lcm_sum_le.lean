-- Prove2me | solution 1 for LandauExplore.primePow_lcm_sum_le
-- status  : ACCEPTED   (prove)
-- author  : @pitimespi
-- created : 2026-10-31T23:55:46.641641+00:00
-- url     : https://prove2.me/submissions/87f91798-7d3b-4aad-a1cd-b64228221ddf

 /- Submission file for the new Prove2Me problem LandauExplore.primePow_lcm_sum_le
(theorem 4a3b566e, published Oct 31, 2026). Submitted with the user's explicit
per-item approval (Oct 31, 2026). The target statement is the prime-power
lemma: for a finite set `s` of positive naturals, the prime-power parts of
`lcm s` sum to at most the sum of `s`. The auxiliary lemmas are included
inline; `solution` is top-level and not wrapped in a namespace. -/
import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.Algebra.GCDMonoid.FinsetLemmas
import Mathlib.RingTheory.Coprime.Lemmas
import Mathlib.GroupTheory.Perm.Cycle.Type
import Mathlib.GroupTheory.Perm.Cycle.PossibleTypes

open Finset

/-- Auxiliary: a product of factors each ≥ 2 over a nonempty finset is ≥ 2. -/
lemma prod_ge_two_of_nonempty {ι : Type*} [DecidableEq ι] {t : Finset ι} {f : ι → ℕ}
    (ht : t.Nonempty) (hf : ∀ i ∈ t, 2 ≤ f i) : 2 ≤ ∏ i ∈ t, f i := by
  induction t using Finset.induction with
  | empty => exact absurd ht (by simp)
  | @insert a s ha ih =>
    rw [Finset.prod_insert ha]
    by_cases hs : s.Nonempty
    · have h1 := ih hs (fun i hi => hf i (Finset.mem_insert_of_mem hi))
      have h2 := hf a (Finset.mem_insert_self a s)
      exact le_trans (by decide : (2:ℕ) ≤ 2 * 2) (Nat.mul_le_mul h2 h1)
    · rw [Finset.not_nonempty_iff_eq_empty] at hs
      rw [hs]
      simp [hf a (Finset.mem_insert_self a s)]

/-- Sum ≤ product for factors each ≥ 2. -/
lemma sum_le_prod_of_two_le {ι : Type*} [DecidableEq ι] {t : Finset ι} {f : ι → ℕ}
    (hf : ∀ i ∈ t, 2 ≤ f i) : ∑ i ∈ t, f i ≤ ∏ i ∈ t, f i := by
  induction t using Finset.induction with
  | empty => simp
  | @insert a s ha ih =>
    have hf' : ∀ i ∈ s, 2 ≤ f i := fun i hi => hf i (Finset.mem_insert_of_mem hi)
    have ih' := ih hf'
    rw [Finset.sum_insert ha, Finset.prod_insert ha]
    by_cases hs : s.Nonempty
    · have hprod := prod_ge_two_of_nonempty hs hf'
      have ha2 := hf a (Finset.mem_insert_self a s)
      have hkey : (∏ i ∈ s, f i) + f a ≤ f a * (∏ i ∈ s, f i) := by
        have hge : f a ≤ (f a - 1) * (∏ i ∈ s, f i) := by
          calc f a ≤ (f a - 1) * 2 := by omega
            _ ≤ (f a - 1) * (∏ i ∈ s, f i) := Nat.mul_le_mul le_rfl hprod
        have e : f a * (∏ i ∈ s, f i) = (f a - 1) * (∏ i ∈ s, f i) + (∏ i ∈ s, f i) := by
          conv_lhs => rw [← Nat.sub_add_cancel (show 1 ≤ f a by omega)]
          rw [add_mul, one_mul]
        omega
      omega
    · rw [Finset.not_nonempty_iff_eq_empty] at hs
      rw [hs]
      simp

/-- Main step (A), arithmetic core: the prime-power parts of the lcm of a
finite set of positive integers sum to at most the sum of the set.
Equivalently, replacing a family of integers by the prime powers dividing
their lcm does not increase the total sum. -/
theorem solution (s : Finset ℕ) (hs : ∀ a ∈ s, a ≠ 0) :
    ∑ p ∈ (s.lcm id).primeFactors, p ^ (s.lcm id).factorization p ≤ ∑ a ∈ s, a := by
  classical
  by_cases hsempty : s = ∅
  · subst hsempty
    simp
  · have hsne : s.Nonempty := Finset.nonempty_iff_ne_empty.mpr hsempty
    set L := s.lcm id with hLdef
    have hL0 : L ≠ 0 := by
      rw [hLdef]
      exact Finset.lcm_ne_zero_iff.mpr hs
    set P := L.primeFactors with hPdef
    set q : ℕ → ℕ := fun p => p ^ L.factorization p with hqdef
    have hPmem : ∀ p ∈ P, p.Prime ∧ 0 < L.factorization p := by
      intro p hp
      have hp' := hp
      rw [hPdef] at hp'
      have hmem := Nat.mem_primeFactors.mp hp'
      exact ⟨hmem.1, hmem.1.factorization_pos_of_dvd hL0 hmem.2.1⟩
    have hq2 : ∀ p ∈ P, 2 ≤ q p := by
      intro p hp
      have hmem := hPmem p hp
      have hp2 : 2 ≤ p := hmem.1.two_le
      have hpos : 1 ≤ L.factorization p := hmem.2
      calc 2 ≤ p ^ 1 := by simpa using hp2
        _ ≤ p ^ L.factorization p := Nat.pow_le_pow_right (by omega) hpos
    have hwit : ∀ p ∈ P, ∃ a ∈ s, a.factorization p = L.factorization p := by
      intro p hp
      have hsup : L.factorization p = s.sup (fun a => a.factorization p) :=
        Finset.factorization_lcm hs p
      obtain ⟨a, ha, hEq⟩ := Finset.exists_mem_eq_sup s hsne (fun a => a.factorization p)
      exact ⟨a, ha, by rw [hsup]; exact hEq.symm⟩
    have hwit' : ∀ p : ℕ, ∃ a : ℕ, p ∈ P → (a ∈ s ∧ a.factorization p = L.factorization p) := by
      intro p
      by_cases hp : p ∈ P
      · obtain ⟨a, ha, hEq⟩ := hwit p hp
        exact ⟨a, fun _ => ⟨ha, hEq⟩⟩
      · exact ⟨0, fun h => absurd h hp⟩
    choose φ hφ using hwit'
    have hdvd : ∀ p ∈ P, q p ∣ φ p := by
      intro p hp
      have hφp := hφ p hp
      have hmem := hPmem p hp
      apply (Nat.factorization_le_iff_dvd (by
        have h2 := hq2 p hp
        omega) (hs _ hφp.1)).mp
      intro r
      simp only [hqdef, Nat.Prime.factorization_pow hmem.1, Finsupp.single_apply]
      by_cases hr : r = p
      · subst hr
        simp [hφp.2]
      · simp [Ne.symm hr]
    have hsum : ∑ p ∈ P, q p = ∑ a ∈ s, ∑ p ∈ P.filter (fun p => φ p = a), q p := by
      exact (Finset.sum_fiberwise_of_maps_to (t := s) (g := φ) (f := q)
        (fun p hp => (hφ p hp).1)).symm
    have hfiber : ∀ a ∈ s, ∑ p ∈ P.filter (fun p => φ p = a), q p ≤ a := by
      intro a ha
      have hle1 : ∑ p ∈ P.filter (fun p => φ p = a), q p
          ≤ ∏ p ∈ P.filter (fun p => φ p = a), q p :=
        sum_le_prod_of_two_le (fun p hp => hq2 p (Finset.mem_filter.mp hp).1)
      have hle2 : ∏ p ∈ P.filter (fun p => φ p = a), q p ≤ a := by
        have hprod_ne : (∏ p ∈ P.filter (fun p => φ p = a), q p) ≠ 0 := by
          apply Finset.prod_ne_zero_iff.mpr
          intro p hp
          have h2 := hq2 p (Finset.mem_filter.mp hp).1
          omega
        have hdvdprod : (∏ p ∈ P.filter (fun p => φ p = a), q p) ∣ a := by
          apply (Nat.factorization_le_iff_dvd hprod_ne (hs a ha)).mp
          intro r
          rw [Nat.factorization_prod (fun p hp => by
            have h2 := hq2 p (Finset.mem_filter.mp hp).1
            omega), Finsupp.finsetSum_apply]
          by_cases hr : r ∈ P.filter (fun p => φ p = a)
          · have hsingle : ∑ p ∈ P.filter (fun p => φ p = a), (q p).factorization r
                = (q r).factorization r := by
              apply Finset.sum_eq_single_of_mem r hr
              intro p hp hpr
              have hmem := hPmem p (Finset.mem_filter.mp hp).1
              simp only [hqdef, Nat.Prime.factorization_pow hmem.1, Finsupp.single_apply,
                if_neg hpr]
            rw [hsingle]
            have hmemr := hPmem r (Finset.mem_filter.mp hr).1
            simp only [hqdef, Nat.Prime.factorization_pow hmemr.1, Finsupp.single_apply]
            have hrφ := (Finset.mem_filter.mp hr).2
            have hφr := hφ r (Finset.mem_filter.mp hr).1
            rw [← hrφ]
            exact le_of_eq hφr.2.symm
          · have hzero : ∑ p ∈ P.filter (fun p => φ p = a), (q p).factorization r = 0 := by
              apply Finset.sum_eq_zero
              intro p hp
              have hmem := hPmem p (Finset.mem_filter.mp hp).1
              have hpr : p ≠ r := fun h => hr (h ▸ hp)
              simp only [hqdef, Nat.Prime.factorization_pow hmem.1, Finsupp.single_apply,
                if_neg hpr]
            rw [hzero]
            exact Nat.zero_le _
        exact Nat.le_of_dvd (Nat.pos_of_ne_zero (hs a ha)) hdvdprod
      exact le_trans hle1 hle2
    rw [hsum]
    exact Finset.sum_le_sum hfiber

