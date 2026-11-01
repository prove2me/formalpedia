-- Prove2me | solution 1 for LandauExplore.landau_primePow_decomp
-- status  : ACCEPTED   (prove)
-- author  : @pitimespi
-- created : 2026-11-01T00:31:21.31121+00:00
-- url     : https://prove2.me/submissions/98539063-9e2a-4d63-a1f9-12cb4dc60829

/- Proof of the platform problem LandauExplore.landau_primePow_decomp:
the Landau maximiser is a product of prime powers whose sum is at most n
(Landau step (A) bookkeeping: sup/max identification for the Landau function).
Published with the user's explicit per-item tap on Oct 31, 2026.
The definition landauLocal is the platform definition LandauExplore_landauLocal,
imported here. Proof body identical to the locally verified Sol_landau_decomp.lean,
with the in-file definition replaced by the platform import.
-/
import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Algebra.GCDMonoid.FinsetLemmas
import Mathlib.RingTheory.Coprime.Lemmas
import Mathlib.GroupTheory.Perm.Cycle.Type
import Mathlib.GroupTheory.Perm.Cycle.PossibleTypes
import Definitions.Def_LandauExplore_landauLocal

open Finset
open LandauExplore

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
lemma primePow_lcm_sum_le (s : Finset ℕ) (hs : ∀ a ∈ s, a ≠ 0) :
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

/-- Sum over the distinct elements of a multiset is at most the multiset sum. -/
lemma toFinset_sum_le_sum (m : Multiset ℕ) : ∑ a ∈ m.toFinset, a ≤ m.sum := by
  induction m using Multiset.induction with
  | empty => simp
  | cons a s ih =>
    rw [Multiset.sum_cons]
    by_cases ha : a ∈ s
    · have h1 : (a ::ₘ s).toFinset = s.toFinset := by
        rw [Multiset.toFinset_cons]
        simp [Multiset.mem_toFinset.mpr ha]
      rw [h1]
      omega
    · have h1 : (a ::ₘ s).toFinset = insert a s.toFinset := Multiset.toFinset_cons a s
      rw [h1, Finset.sum_insert (by
        intro h
        exact ha (Multiset.mem_toFinset.mp h))]
      exact Nat.add_le_add_left ih a

/-- Permutation corollary of the prime-power lemma: the prime-power parts
of the order of a permutation of `Fin n` sum to at most `n`. This is the
upper half of the Landau ↔ prime-powers identification: a permutation's
order is the product of these prime powers, and their sum is at most the
number of points moved. -/
lemma perm_order_primePow_sum_le {n : ℕ} (σ : Equiv.Perm (Fin n)) :
    ∑ p ∈ (orderOf σ).primeFactors, p ^ (orderOf σ).factorization p ≤ n := by
  have hlcm : σ.cycleType.toFinset.lcm id = orderOf σ := by
    rw [Finset.lcm_def, Multiset.toFinset_val, Multiset.map_id, Multiset.lcm_dedup,
      Equiv.Perm.lcm_cycleType]
  have h2 : ∀ a ∈ σ.cycleType.toFinset, a ≠ 0 := by
    intro a ha
    have hmem : a ∈ σ.cycleType := Multiset.mem_toFinset.mp ha
    have hle := Equiv.Perm.two_le_of_mem_cycleType hmem
    omega
  have hmain := primePow_lcm_sum_le σ.cycleType.toFinset h2
  rw [hlcm] at hmain
  have hle2 : σ.cycleType.sum ≤ n := by
    have h := Equiv.Perm.sum_cycleType_le σ
    simpa using h
  exact le_trans hmain (le_trans (toFinset_sum_le_sum σ.cycleType) hle2)

/-- The order of a permutation is the product of its prime-power parts. -/
lemma orderOf_eq_prod_primePow {n : ℕ} (σ : Equiv.Perm (Fin n)) :
    ∏ p ∈ (orderOf σ).primeFactors, p ^ (orderOf σ).factorization p = orderOf σ := by
  have h0 : orderOf σ ≠ 0 := by
    have hfin : IsOfFinOrder σ := isOfFinOrder_of_finite σ
    have hpos := hfin.orderOf_pos
    omega
  have h := Nat.prod_factorization_pow_eq_self h0
  rw [Nat.prod_factorization_eq_prod_primeFactors] at h
  exact h

/-- Lower half of (A): every family of prime powers for distinct primes
with sum at most `n` is realized as the order of a permutation of `Fin n`.
Combined with `perm_order_primePow_sum_le`, permutation orders are exactly
the products of prime-power families with sum at most `n`. -/
lemma exists_perm_order_eq_prod_primePow {n : ℕ} {t : Finset ℕ}
    (hf : ∃ f : ℕ → ℕ, (∀ q ∈ t, (f q).Prime ∧ ∃ k : ℕ, 1 ≤ k ∧ q = (f q) ^ k)
      ∧ Set.InjOn f t)
    (hsum : ∑ q ∈ t, q ≤ n) :
    ∃ σ : Equiv.Perm (Fin n), orderOf σ = ∏ q ∈ t, q := by
  obtain ⟨f, hfprime, hinj⟩ := hf
  have hge : ∀ q ∈ t, 2 ≤ q := by
    intro q hq
    obtain ⟨hp, k, hk, hqk⟩ := hfprime q hq
    rw [hqk]
    calc 2 ≤ f q ^ 1 := by simpa using hp.two_le
      _ ≤ f q ^ k := Nat.pow_le_pow_right (by have h2 := hp.two_le; omega) hk
  have hvalsum : t.val.sum = ∑ q ∈ t, q := by simp
  have hm : ∀ a ∈ t.val, 2 ≤ a := by
    intro a ha
    exact hge a (Finset.mem_val.mp ha)
  obtain ⟨σ, hσ⟩ := (Equiv.Perm.exists_with_cycleType_iff (α := Fin n)
    (m := t.val)).mpr ⟨by rw [Fintype.card_fin, hvalsum]; exact hsum, hm⟩
  refine ⟨σ, ?_⟩
  rw [← Equiv.Perm.lcm_cycleType, hσ]
  have hlcmprod : t.lcm id = ∏ q ∈ t, q := by
    apply Finset.lcm_eq_prod
    intro q hq r hr hqr
    obtain ⟨hp, k, hk, hqk⟩ := hfprime q hq
    obtain ⟨hp', k', hk', hrk⟩ := hfprime r hr
    have hne : f q ≠ f r := fun h => hqr (hinj hq hr h)
    show Nat.Coprime q r
    rw [hqk, hrk]
    exact Nat.coprime_pow_primes k k' hp hp' hne
  rw [Finset.lcm_def, Multiset.map_id] at hlcmprod
  exact hlcmprod


/-! ## Bookkeeping: from (A) to the platform `landau` definition

The definition `landauLocal` is the platform definition
`LandauExplore_landauLocal`: the `Finset.sup` of `orderOf` over all
permutations of `Fin n`.  The lemmas below connect it to (A), giving the
sup/max bookkeeping that (A) alone does not contain.
-/

lemma landauLocal_pos (n : ℕ) : 1 ≤ landauLocal n := by
  have h := Finset.le_sup (f := fun σ : Equiv.Perm (Fin n) => orderOf σ)
    (Finset.mem_univ (1 : Equiv.Perm (Fin n)))
  simp only [landauLocal] at h ⊢
  simpa using h

lemma landauLocal_attained (n : ℕ) :
    ∃ σ : Equiv.Perm (Fin n), orderOf σ = landauLocal n := by
  obtain ⟨σ, _, h⟩ := Finset.exists_mem_eq_sup (Finset.univ : Finset (Equiv.Perm (Fin n)))
    Finset.univ_nonempty (fun σ => orderOf σ)
  exact ⟨σ, by rw [landauLocal]; exact h.symm⟩

lemma landauLocal_le {n : ℕ} (σ : Equiv.Perm (Fin n)) :
    orderOf σ ≤ landauLocal n := by
  have h := Finset.le_sup (f := fun σ : Equiv.Perm (Fin n) => orderOf σ)
    (Finset.mem_univ σ)
  simpa [landauLocal] using h

/-- The maximiser's prime-power decomposition: `landau n` is a product of
prime powers whose sum is at most `n`.  This is the "max is attained at a
product of prime powers" half of the Landau ↔ knapsack identification. -/
theorem solution (n : ℕ) :
    ∃ t : Finset ℕ, (∀ q ∈ t, ∃ p k : ℕ, p.Prime ∧ 1 ≤ k ∧ q = p ^ k)
      ∧ ∑ q ∈ t, q ≤ n ∧ ∏ q ∈ t, q = landauLocal n := by
  obtain ⟨σ, hσ⟩ := landauLocal_attained n
  set m := orderOf σ with hm
  refine ⟨m.primeFactors.image (fun p => p ^ m.factorization p), ?_, ?_, ?_⟩
  · intro q hq
    rw [Finset.mem_image] at hq
    obtain ⟨p, hp, rfl⟩ := hq
    have hpm := Nat.mem_primeFactors.mp hp
    exact ⟨p, m.factorization p, hpm.1,
      hpm.1.factorization_pos_of_dvd hpm.2.2 hpm.2.1, rfl⟩
  · have hinj : Set.InjOn (fun p => p ^ m.factorization p) (m.primeFactors : Set ℕ) := by
      intro p hp r hr h
      have hp' := (Nat.mem_primeFactors.mp hp).1
      have hr' := (Nat.mem_primeFactors.mp hr).1
      have hposp : 1 ≤ m.factorization p :=
        hp'.factorization_pos_of_dvd (Nat.mem_primeFactors.mp hp).2.2 (Nat.mem_primeFactors.mp hp).2.1
      have hdvd : p ∣ r ^ m.factorization r := by
        dsimp only at h
        rw [← h]
        exact dvd_pow_self p (by omega : m.factorization p ≠ 0)
      have hpr : p = r :=
        (Nat.prime_dvd_prime_iff_eq hp' hr').mp (hp'.dvd_of_dvd_pow hdvd)
      exact hpr
    rw [Finset.sum_image (fun p hp r hr h => hinj hp hr h)]
    have hmain := perm_order_primePow_sum_le σ
    rw [← hm] at hmain
    exact hmain
  · have hinj : Set.InjOn (fun p => p ^ m.factorization p) (m.primeFactors : Set ℕ) := by
      intro p hp r hr h
      have hp' := (Nat.mem_primeFactors.mp hp).1
      have hr' := (Nat.mem_primeFactors.mp hr).1
      have hposp : 1 ≤ m.factorization p :=
        hp'.factorization_pos_of_dvd (Nat.mem_primeFactors.mp hp).2.2 (Nat.mem_primeFactors.mp hp).2.1
      have hdvd : p ∣ r ^ m.factorization r := by
        dsimp only at h
        rw [← h]
        exact dvd_pow_self p (by omega : m.factorization p ≠ 0)
      exact (Nat.prime_dvd_prime_iff_eq hp' hr').mp (hp'.dvd_of_dvd_pow hdvd)
    rw [Finset.prod_image (fun p hp r hr h => hinj hp hr h)]
    have hprod := orderOf_eq_prod_primePow σ
    rw [← hm] at hprod
    rw [hprod, hσ]

/-- Converse direction: every prime-power family with sum ≤ `n` is
dominated by `landau n`.  Together with `landauLocal_primePow_decomp`,
`landau n` is exactly the knapsack optimum over prime-power families. -/
lemma prod_primePow_le_landauLocal {n : ℕ} {t : Finset ℕ}
    (hf : ∃ f : ℕ → ℕ, (∀ q ∈ t, (f q).Prime ∧ ∃ k : ℕ, 1 ≤ k ∧ q = (f q) ^ k)
      ∧ Set.InjOn f t)
    (hsum : ∑ q ∈ t, q ≤ n) : ∏ q ∈ t, q ≤ landauLocal n := by
  obtain ⟨σ, hσ⟩ := exists_perm_order_eq_prod_primePow hf hsum
  rw [← hσ]
  exact landauLocal_le σ

