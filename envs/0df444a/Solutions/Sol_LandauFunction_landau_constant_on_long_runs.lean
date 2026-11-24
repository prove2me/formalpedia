-- Prove2me | solution 1 for LandauFunction.landau_constant_on_long_runs
-- status  : ACCEPTED   (prove)
-- author  : @CGTMoyano
-- created : 2026-11-24T13:54:47.215338+00:00
-- url     : https://prove2.me/submissions/0c915e1a-ef4a-4182-a292-e7dbe4ea66f2

import Mathlib
import Definitions.Def_LandauFunction_landau
import Theorems.Thm_LandauFunction_landau_eq_sup_partition_lcm

open LandauFunction

namespace P2ML

def c (p b : ℕ) : ℕ := if b = 0 then 0 else p ^ b

def ell (M : ℕ) : ℕ := ∑ p ∈ M.primeFactors, c p (M.factorization p)

noncomputable def wr (p a : ℕ) : ℝ := (c p (a + 1) : ℝ) - c p a

theorem c_pos' (p : ℕ) {b : ℕ} (h : b ≠ 0) : c p b = p ^ b := by simp [c, h]

theorem c_zero' (p : ℕ) : c p 0 = 0 := by simp [c]

theorem fact_zero {M p : ℕ} (hp : p ∉ M.primeFactors) : M.factorization p = 0 := by
  rwa [← Nat.support_factorization, Finsupp.notMem_support_iff] at hp

theorem fact_pos {M p : ℕ} (hp : p ∈ M.primeFactors) : M.factorization p ≠ 0 := by
  rw [← Nat.support_factorization] at hp
  exact Finsupp.mem_support_iff.1 hp

theorem ell_eq (M : ℕ) (S : Finset ℕ) (h : M.primeFactors ⊆ S) :
    ell M = ∑ p ∈ S, c p (M.factorization p) := by
  unfold ell
  refine Finset.sum_subset h fun p _ hp => ?_
  simp [c, fact_zero hp]

theorem sum_le_prod (f : ℕ → ℕ) (s : Finset ℕ) (h : ∀ i ∈ s, 2 ≤ f i) :
    ∑ i ∈ s, f i ≤ ∏ i ∈ s, f i ∧ (s.Nonempty → 2 ≤ ∏ i ∈ s, f i) := by
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    have h2 := h a (Finset.mem_insert_self a s)
    obtain ⟨i1, i2⟩ := ih (fun i hi => h i (Finset.mem_insert_of_mem hi))
    rw [Finset.sum_insert ha, Finset.prod_insert ha]
    rcases s.eq_empty_or_nonempty with rfl | hne
    · simp [h2]
    · have h3 := i2 hne
      constructor
      · nlinarith
      · intro _
        nlinarith

theorem ell_eq_pow (M : ℕ) : ell M = ∑ p ∈ M.primeFactors, p ^ M.factorization p := by
  unfold ell
  refine Finset.sum_congr rfl fun p hp => ?_
  simp [c, fact_pos hp]

theorem ell_le (M : ℕ) (hM : 0 < M) : ell M ≤ M := by
  have h2 : ∏ p ∈ M.primeFactors, p ^ M.factorization p = M := by
    have := Nat.prod_factorization_pow_eq_self hM.ne'
    rwa [Finsupp.prod, Nat.support_factorization] at this
  calc ell M = ∑ p ∈ M.primeFactors, p ^ M.factorization p := ell_eq_pow M
    _ ≤ ∏ p ∈ M.primeFactors, p ^ M.factorization p :=
      (sum_le_prod _ _ fun p hp =>
        le_trans (Nat.prime_of_mem_primeFactors hp).two_le (Nat.le_self_pow (fact_pos hp) p)).1
    _ = M := h2

theorem ell_lcm (a b : ℕ) (ha : 0 < a) (hb : 0 < b) : ell (Nat.lcm a b) ≤ ell a + ell b := by
  have hsub : (Nat.lcm a b).primeFactors ⊆ a.primeFactors ∪ b.primeFactors := by
    intro p hp
    have hpp := Nat.prime_of_mem_primeFactors hp
    have hd := (Nat.dvd_of_mem_primeFactors hp).trans (Nat.lcm_dvd_mul a b)
    rw [Finset.mem_union]
    rcases (Nat.Prime.dvd_mul hpp).1 hd with h | h
    · exact Or.inl (Nat.mem_primeFactors.2 ⟨hpp, h, ha.ne'⟩)
    · exact Or.inr (Nat.mem_primeFactors.2 ⟨hpp, h, hb.ne'⟩)
  rw [ell_eq _ _ hsub, ell_eq a _ Finset.subset_union_left, ell_eq b _ Finset.subset_union_right,
    ← Finset.sum_add_distrib]
  refine Finset.sum_le_sum fun p _ => ?_
  rw [Nat.factorization_lcm ha.ne' hb.ne', Finsupp.sup_apply]
  rcases le_total (a.factorization p) (b.factorization p) with h | h
  · rw [sup_of_le_right h]
    exact Nat.le_add_left _ _
  · rw [sup_of_le_left h]
    exact Nat.le_add_right _ _

theorem ell_multiset (s : Multiset ℕ) (h : ∀ x ∈ s, 0 < x) : ell s.lcm ≤ s.sum := by
  induction s using Multiset.induction_on with
  | empty => simp [ell]
  | cons a s ih =>
    have ha := h a (Multiset.mem_cons_self a s)
    have hs : ∀ x ∈ s, 0 < x := fun x hx => h x (Multiset.mem_cons_of_mem hx)
    have hl : 0 < s.lcm := Nat.pos_of_ne_zero (fun h0 =>
      lt_irrefl 0 (hs 0 ((Multiset.lcm_eq_zero_iff s).1 h0)))
    rw [Multiset.lcm_cons, Multiset.sum_cons]
    exact (ell_lcm a s.lcm ha hl).trans (add_le_add (ell_le a ha) (ih hs))

theorem c_step_mono (p : ℕ) (hp : 2 ≤ p) (a : ℕ) :
    c p (a + 1) + c p (a + 1) ≤ c p (a + 1 + 1) + c p a := by
  rw [c_pos' p (by omega : a + 1 ≠ 0), c_pos' p (by omega : a + 1 + 1 ≠ 0)]
  have e : p ^ (a + 1 + 1) = p * p ^ (a + 1) := by ring
  have h1 : 2 * p ^ (a + 1) ≤ p * p ^ (a + 1) := Nat.mul_le_mul_right _ hp
  linarith

theorem c_step_large (p : ℕ) (hp : 2 ≤ p) (a : ℕ) : c p a + a + 1 ≤ c p (a + 1) := by
  rw [c_pos' p (by omega : a + 1 ≠ 0)]
  rcases a with _ | k
  · rw [c_zero']
    simp
    omega
  · rw [c_pos' p (by omega : k + 1 ≠ 0)]
    have e : p ^ (k + 1 + 1) = p * p ^ (k + 1) := by ring
    have h1 : 2 * p ^ (k + 1) ≤ p * p ^ (k + 1) := Nat.mul_le_mul_right _ hp
    have h2 : k + 1 < 2 ^ (k + 1) := Nat.lt_two_pow_self
    have h3 : 2 ^ (k + 1) ≤ p ^ (k + 1) := Nat.pow_le_pow_left hp _
    linarith

theorem wr_mono (p : ℕ) (hp : 2 ≤ p) {a b : ℕ} (hab : a ≤ b) : wr p a ≤ wr p b := by
  refine monotone_nat_of_le_succ (f := wr p) (fun a => ?_) hab
  have h := c_step_mono p hp a
  have h' : ((c p (a + 1) + c p (a + 1) : ℕ) : ℝ) ≤ ((c p (a + 1 + 1) + c p a : ℕ) : ℝ) := by
    exact_mod_cast h
  push_cast at h'
  unfold wr
  linarith

theorem wr_large (p : ℕ) (hp : 2 ≤ p) (a : ℕ) : (a : ℝ) + 1 ≤ wr p a := by
  have h := c_step_large p hp a
  have h' : ((c p a + a + 1 : ℕ) : ℝ) ≤ ((c p (a + 1) : ℕ) : ℝ) := by exact_mod_cast h
  push_cast at h'
  unfold wr
  linarith

theorem ylog_sub_ell (y : ℝ) (M : ℕ) (S : Finset ℕ) (h : M.primeFactors ⊆ S) :
    y * Real.log M - ell M =
      ∑ p ∈ S, (y * (M.factorization p) * Real.log p - c p (M.factorization p)) := by
  have h1 : Real.log M = ∑ p ∈ S, (M.factorization p : ℝ) * Real.log p := by
    rw [Real.log_nat_eq_sum_factorization, Finsupp.sum, Nat.support_factorization]
    refine Finset.sum_subset h fun p _ hp => ?_
    simp [fact_zero hp]
  have h2 : ∀ p ∈ S, y * ((M.factorization p : ℝ) * Real.log p) =
      y * (M.factorization p) * Real.log p := fun p _ => by ring
  rw [ell_eq M S h, h1, Finset.sum_sub_distrib, Finset.mul_sum, Finset.sum_congr rfl h2]
  push_cast
  rfl

theorem plateau (m : ℕ) (hm : 1 ≤ m) (y : ℝ) (hy : 0 < y)
    (hT : ∀ p : ℕ, p.Prime → ∀ a : ℕ,
      y * Real.log p + m ≤ wr p a ∨ wr p a ≤ y * Real.log p - m) :
    ∃ n : ℕ, ∀ k ≤ m, landau (n + k) = landau n := by
  have hm' : (1 : ℝ) ≤ m := by exact_mod_cast hm
  have hA : ∀ p : ℕ, ∃ A : ℕ, (¬ p.Prime → A = 0) ∧ (y * Real.log p ≤ p → A = 0) ∧
      (p.Prime → (∀ b, A ≤ b → y * Real.log p + m ≤ wr p b) ∧
        (∀ b, b < A → wr p b ≤ y * Real.log p - m)) := by
    intro p
    by_cases hp : p.Prime
    · have hex : ∃ a : ℕ, y * Real.log p ≤ wr p a := by
        refine ⟨⌈y * Real.log p⌉₊, ?_⟩
        have h1 := wr_large p hp.two_le ⌈y * Real.log p⌉₊
        have h2 := Nat.le_ceil (y * Real.log p)
        linarith
      refine ⟨Nat.find hex, fun h => absurd hp h, fun h => ?_,
        fun _ => ⟨fun b hb => ?_, fun b hb => ?_⟩⟩
      · rw [Nat.find_eq_zero]
        simpa [wr, c] using h
      · have h1 := Nat.find_spec hex
        have h2 := wr_mono p hp.two_le hb
        rcases hT p hp b with h | h
        · exact h
        · linarith
      · have h1 := Nat.find_min hex hb
        rcases hT p hp b with h | h
        · exact absurd (by linarith) h1
        · exact h
    · exact ⟨0, fun _ => rfl, fun _ => rfl, fun h => absurd h hp⟩
  choose A hA0 hA1 hA2 using hA
  obtain ⟨Bnd, hBnd⟩ : ∃ Bnd : ℕ, ∀ p : ℕ, Bnd ≤ p → y * Real.log p ≤ p := by
    refine ⟨⌈4 * y ^ 2⌉₊ + 1, fun p hp => ?_⟩
    have hp1 : (4 * y ^ 2 : ℝ) ≤ p := by
      have h1 := Nat.le_ceil (4 * y ^ 2)
      have h2 : ((⌈4 * y ^ 2⌉₊ + 1 : ℕ) : ℝ) ≤ p := by exact_mod_cast hp
      push_cast at h2
      linarith
    have hp0 : (0 : ℝ) < p := by nlinarith [sq_nonneg y]
    have hs : 2 * y ≤ Real.sqrt p := by
      calc 2 * y = Real.sqrt ((2 * y) ^ 2) := (Real.sqrt_sq (by positivity)).symm
        _ ≤ Real.sqrt p := Real.sqrt_le_sqrt (by nlinarith)
    have hlog : Real.log p ≤ 2 * Real.sqrt p := by
      have h1 := Real.log_le_sub_one_of_pos (Real.sqrt_pos.2 hp0)
      have h2 : Real.log p = 2 * Real.log (Real.sqrt p) := by
        rw [Real.log_sqrt hp0.le]
        ring
      linarith
    have hsq : Real.sqrt p * Real.sqrt p = p := Real.mul_self_sqrt hp0.le
    nlinarith [mul_nonneg hy.le (sub_nonneg.2 hlog),
      mul_nonneg (Real.sqrt_nonneg (p : ℝ)) (sub_nonneg.2 hs)]
  let f : ℕ →₀ ℕ := Finsupp.onFinset (Finset.range Bnd) A (fun p hp => by
    rw [Finset.mem_range]
    by_contra h
    exact hp (hA1 p (hBnd p (by omega))))
  have hfA : ∀ p, f p = A p := fun p => rfl
  have hfprime : ∀ p ∈ f.support, p.Prime := by
    intro p hp
    by_contra h
    exact (Finsupp.mem_support_iff.1 hp) (hA0 p h)
  obtain ⟨G, hG⟩ : ∃ G : ℕ, G = f.prod (· ^ ·) := ⟨_, rfl⟩
  have hGf : G.factorization = f := by
    rw [hG]
    exact Nat.prod_pow_factorization_eq_self hfprime
  have hG0 : G ≠ 0 := by
    rw [hG, Finsupp.prod]
    exact Finset.prod_ne_zero_iff.2 fun p hp => pow_ne_zero _ (hfprime p hp).ne_zero
  have hphi : ∀ p : ℕ, p.Prime → ∀ b : ℕ,
      y * b * Real.log p - c p b + (if b = A p then 0 else (m : ℝ)) ≤
        y * (A p) * Real.log p - c p (A p) := by
    intro p hp b
    obtain ⟨hup, hdown⟩ := hA2 p hp
    have up : ∀ k : ℕ, y * ((A p + k : ℕ) : ℝ) * Real.log p - c p (A p + k) + m * k ≤
        y * (A p) * Real.log p - c p (A p) := by
      intro k
      induction k with
      | zero => simp
      | succ k ih =>
        have h1 := hup (A p + k) (by omega)
        unfold wr at h1
        have e2 : A p + (k + 1) = A p + k + 1 := rfl
        rw [e2]
        push_cast at ih h1 ⊢
        linarith
    have down : ∀ k : ℕ, ∀ b : ℕ, b + k = A p →
        y * b * Real.log p - c p b + m * k ≤ y * (A p) * Real.log p - c p (A p) := by
      intro k
      induction k with
      | zero =>
        intro b hb
        rw [← hb]
        simp
      | succ k ih =>
        intro b hb
        have h1 := hdown b (by omega)
        have h2 := ih (b + 1) (by omega)
        unfold wr at h1
        push_cast at h1 h2 ⊢
        linarith
    by_cases hb : b = A p
    · subst hb
      simp
    · rw [if_neg hb]
      rcases le_total (A p) b with h | h
      · obtain ⟨k, hk⟩ := Nat.exists_eq_add_of_le h
        subst hk
        have h1 := up k
        have hk1 : (1 : ℝ) ≤ k := by
          have : 1 ≤ k := by omega
          exact_mod_cast this
        have h2 : (m : ℝ) ≤ m * k := by nlinarith
        linarith
      · obtain ⟨k, hk⟩ := Nat.exists_eq_add_of_le h
        have h1 := down k b hk.symm
        have hk1 : (1 : ℝ) ≤ k := by
          have : 1 ≤ k := by omega
          exact_mod_cast this
        have h2 : (m : ℝ) ≤ m * k := by nlinarith
        linarith
  have hmain : ∀ M : ℕ, 0 < M → M ≠ G →
      y * Real.log M - ell M + m ≤ y * Real.log G - ell G := by
    intro M hM hne
    have hSprime : ∀ p ∈ M.primeFactors ∪ G.primeFactors, p.Prime := by
      intro p hp
      rcases Finset.mem_union.1 hp with h | h <;> exact Nat.prime_of_mem_primeFactors h
    rw [ylog_sub_ell y M _ Finset.subset_union_left, ylog_sub_ell y G _ Finset.subset_union_right]
    obtain ⟨q, hq⟩ : ∃ q, M.factorization q ≠ G.factorization q := by
      by_contra hcon
      push Not at hcon
      exact hne (Nat.eq_of_factorization_eq hM.ne' hG0 hcon)
    have hqS : q ∈ M.primeFactors ∪ G.primeFactors := by
      rw [Finset.mem_union, ← Nat.support_factorization, ← Nat.support_factorization,
        Finsupp.mem_support_iff, Finsupp.mem_support_iff]
      by_contra hcon
      push Not at hcon
      exact hq (hcon.1.trans hcon.2.symm)
    have hterm : ∀ p ∈ M.primeFactors ∪ G.primeFactors,
        0 ≤ (y * (G.factorization p) * Real.log p - c p (G.factorization p)) -
        (y * (M.factorization p) * Real.log p - c p (M.factorization p)) := by
      intro p hp
      have h1 := hphi p (hSprime p hp) (M.factorization p)
      rw [hGf, hfA]
      split_ifs at h1 <;> linarith
    have hq' : (m : ℝ) ≤ (y * (G.factorization q) * Real.log q - c q (G.factorization q)) -
        (y * (M.factorization q) * Real.log q - c q (M.factorization q)) := by
      have h1 := hphi q (hSprime q hqS) (M.factorization q)
      rw [hGf, hfA] at hq
      rw [hGf, hfA]
      rw [if_neg hq] at h1
      linarith
    have hsum := Finset.single_le_sum hterm hqS
    beta_reduce at hsum
    rw [Finset.sum_sub_distrib] at hsum
    linarith
  have hval : ∀ k ≤ m, landau (ell G + k) = G := by
    intro k hk
    rw [landau_eq_sup_partition_lcm]
    apply le_antisymm
    · refine Finset.sup_le fun π _ => ?_
      by_contra hcon
      push Not at hcon
      have hpos : ∀ x ∈ π.parts, 0 < x := fun x hx => π.parts_pos hx
      have hM : 0 < π.parts.lcm := lt_of_le_of_lt (Nat.zero_le _) hcon
      have h1 := ell_multiset π.parts hpos
      rw [π.parts_sum] at h1
      have h2 := hmain _ hM hcon.ne'
      have h3 : Real.log (G : ℝ) < Real.log ((π.parts.lcm : ℕ) : ℝ) :=
        Real.log_lt_log (by exact_mod_cast Nat.pos_of_ne_zero hG0) (by exact_mod_cast hcon)
      have h4 : ((ell π.parts.lcm : ℕ) : ℝ) ≤ ((ell G + k : ℕ) : ℝ) := by exact_mod_cast h1
      push_cast at h4
      have h5 : (k : ℝ) ≤ m := by exact_mod_cast hk
      have h6 := mul_lt_mul_of_pos_left h3 hy
      linarith
    · have hsum : ((G.primeFactors.val.map fun p => p ^ G.factorization p) +
          Multiset.replicate k 1).sum = ell G + k := by
        rw [Multiset.sum_add, Multiset.sum_replicate, smul_eq_mul, mul_one, ell_eq_pow]
        rfl
      have hpos : ∀ {i}, i ∈ (G.primeFactors.val.map fun p => p ^ G.factorization p) +
          Multiset.replicate k 1 → 0 < i := by
        intro i hi
        rcases Multiset.mem_add.1 hi with h | h
        · obtain ⟨p, hp, rfl⟩ := Multiset.mem_map.1 h
          exact pow_pos (Nat.prime_of_mem_primeFactors hp).pos _
        · rw [Multiset.eq_of_mem_replicate h]
          exact Nat.one_pos
      have hl0 : ((G.primeFactors.val.map fun p => p ^ G.factorization p) +
          Multiset.replicate k 1).lcm ≠ 0 :=
        fun h0 => lt_irrefl 0 (hpos ((Multiset.lcm_eq_zero_iff _).1 h0))
      have hdvd : G ∣ ((G.primeFactors.val.map fun p => p ^ G.factorization p) +
          Multiset.replicate k 1).lcm := by
        rw [← Nat.factorization_le_iff_dvd hG0 hl0]
        refine Finsupp.le_def.2 fun p => ?_
        by_cases hp : p ∈ G.primeFactors
        · have hpp := Nat.prime_of_mem_primeFactors hp
          rw [← hpp.pow_dvd_iff_le_factorization hl0]
          exact Multiset.dvd_lcm (Multiset.mem_add.2 (Or.inl (Multiset.mem_map.2 ⟨p, hp, rfl⟩)))
        · rw [fact_zero hp]
          exact Nat.zero_le _
      exact (Nat.le_of_dvd (Nat.pos_of_ne_zero hl0) hdvd).trans
        (Finset.le_sup (f := fun p : Nat.Partition (ell G + k) => p.parts.lcm)
          (Finset.mem_univ (⟨_, hpos, hsum⟩ : Nat.Partition (ell G + k))))
  exact ⟨ell G, fun k hk => (hval k hk).trans (hval 0 (Nat.zero_le m)).symm⟩

end P2ML

namespace P2ML

theorem card_ties (J : Finset ℕ) (α β γ : ℝ) (hβ : 0 < β) (hγ : 0 ≤ γ) :
    ((J.filter (fun j : ℕ => |α - j * β| < γ)).card : ℝ) ≤ 2 * γ / β + 1 := by
  rcases (J.filter (fun j : ℕ => |α - j * β| < γ)).eq_empty_or_nonempty with h | h
  · rw [h]
    simp only [Finset.card_empty, Nat.cast_zero]
    positivity
  · obtain ⟨j0, hj0⟩ : ∃ j0, j0 = (J.filter (fun j : ℕ => |α - j * β| < γ)).min' h := ⟨_, rfl⟩
    have hj0T : j0 ∈ J.filter (fun j : ℕ => |α - j * β| < γ) := by
      rw [hj0]
      exact Finset.min'_mem _ h
    have h0 : |α - j0 * β| < γ := (Finset.mem_filter.1 hj0T).2
    have hsub : J.filter (fun j : ℕ => |α - j * β| < γ) ⊆
        Finset.Icc j0 (j0 + ⌊2 * γ / β⌋₊) := by
      intro j hj
      have hj1 : j0 ≤ j := by
        rw [hj0]
        exact Finset.min'_le _ j hj
      have hj2 : |α - j * β| < γ := (Finset.mem_filter.1 hj).2
      rw [Finset.mem_Icc]
      refine ⟨hj1, ?_⟩
      have h3 : ((j - j0 : ℕ) : ℝ) ≤ 2 * γ / β := by
        rw [Nat.cast_sub hj1, le_div_iff₀ hβ]
        have t1 := abs_lt.1 h0
        have t2 := abs_lt.1 hj2
        linarith
      have := Nat.le_floor h3
      omega
    have hc := Finset.card_le_card hsub
    rw [Nat.card_Icc] at hc
    have e : j0 + ⌊2 * γ / β⌋₊ + 1 - j0 = ⌊2 * γ / β⌋₊ + 1 := by omega
    rw [e] at hc
    have hc' : ((J.filter (fun j : ℕ => |α - j * β| < γ)).card : ℝ) ≤
        ((⌊2 * γ / β⌋₊ + 1 : ℕ) : ℝ) := by exact_mod_cast hc
    push_cast at hc'
    have := Nat.floor_le (show 0 ≤ 2 * γ / β by positivity)
    linarith

theorem tie0_upper (Y s : ℕ) (L y : ℝ) (p : ℕ) (hs : 4 ≤ s) (hLY : L ≤ Y)
    (hY : (Y : ℝ) = 2 ^ (3 * s)) (hy2 : y ≤ 2 * Y) (hp : 2 ≤ p)
    (h : (p : ℝ) < y * Real.log p + L) : p < 16 * Y * s := by
  by_contra hcon
  push Not at hcon
  have hpR : ((16 * Y * s : ℕ) : ℝ) ≤ p := by exact_mod_cast hcon
  push_cast at hpR
  have hsR : (4 : ℝ) ≤ s := by exact_mod_cast hs
  have hYpos : (0 : ℝ) < Y := by
    rw [hY]
    positivity
  have hx0pos : (0 : ℝ) < 16 * Y * s := by positivity
  have hp0 : (0 : ℝ) < p := lt_of_lt_of_le hx0pos hpR
  have hlogp : 0 ≤ Real.log p := Real.log_nonneg (by exact_mod_cast (by omega : 1 ≤ p))
  have h1 : Real.log ((p : ℝ) / (16 * Y * s)) ≤ (p : ℝ) / (16 * Y * s) - 1 :=
    Real.log_le_sub_one_of_pos (by positivity)
  rw [Real.log_div hp0.ne' hx0pos.ne'] at h1
  have h2 : Real.log (16 * (Y : ℝ) * s) ≤ 4 * s + 15 := by
    have e : (16 * (Y : ℝ) * s) = 16 * (Y * s) := by ring
    rw [e, Real.log_mul (by norm_num) (by positivity), Real.log_mul hYpos.ne' (by positivity),
      hY, Real.log_pow]
    have a1 : Real.log 16 ≤ 16 - 1 := Real.log_le_sub_one_of_pos (by norm_num)
    have a2 : Real.log 2 ≤ 2 - 1 := Real.log_le_sub_one_of_pos (by norm_num)
    have a3 : Real.log s ≤ s - 1 := Real.log_le_sub_one_of_pos (by linarith)
    have a4 := mul_nonneg (by linarith : (0 : ℝ) ≤ s) (by linarith : 0 ≤ 1 - Real.log 2)
    push_cast
    nlinarith
  have h3 : (16 * (Y : ℝ) * s) * Real.log p ≤
      (16 * (Y : ℝ) * s) * Real.log (16 * (Y : ℝ) * s) + p - 16 * Y * s := by
    have t := mul_le_mul_of_nonneg_left h1 hx0pos.le
    have e : (16 * (Y : ℝ) * s) * ((p : ℝ) / (16 * Y * s) - 1) = p - 16 * Y * s := by
      field_simp
    rw [e] at t
    linarith
  have h4 : y * Real.log p ≤ 2 * Y * Real.log p := mul_le_mul_of_nonneg_right hy2 hlogp
  have h6 : (16 * (Y : ℝ) * s) * Real.log (16 * (Y : ℝ) * s) ≤ (16 * (Y : ℝ) * s) * (4 * s + 15) :=
    mul_le_mul_of_nonneg_left h2 hx0pos.le
  have h7 : 8 * (s : ℝ) * p < 8 * s * (2 * Y * Real.log p + Y) := by
    have : (p : ℝ) < 2 * Y * Real.log p + Y := by linarith
    exact mul_lt_mul_of_pos_left this (by positivity)
  have h8 : (8 * (s : ℝ) - 1) * (16 * Y * s) ≤ (8 * s - 1) * p :=
    mul_le_mul_of_nonneg_left hpR (by linarith)
  have h9 : 0 ≤ (Y : ℝ) * s * (64 * s - 248) :=
    mul_nonneg (mul_nonneg hYpos.le (by linarith)) (by linarith)
  nlinarith

theorem tie0_lower (Y s : ℕ) (L y : ℝ) (p : ℕ) (hs : 2 ≤ s) (hLY : 4 * L ≤ Y)
    (hY : (Y : ℝ) = 2 ^ (3 * s)) (hy1 : (Y : ℝ) ≤ y) (hp : 2 ≤ p)
    (h : y * Real.log p - L < p) : (s : ℝ) ≤ Real.log p := by
  have hl2 : (1 : ℝ) / 2 ≤ Real.log 2 := by
    have := Real.log_two_gt_d9
    linarith
  have hpR : (2 : ℝ) ≤ p := by exact_mod_cast hp
  have hlogp : Real.log 2 ≤ Real.log p := Real.log_le_log (by norm_num) hpR
  have hYpos : (0 : ℝ) < Y := by
    rw [hY]
    positivity
  have h1 : (Y : ℝ) * (1 / 2) ≤ y * Real.log p := by
    calc (Y : ℝ) * (1 / 2) ≤ Y * Real.log p :=
          mul_le_mul_of_nonneg_left (by linarith) hYpos.le
      _ ≤ y * Real.log p := mul_le_mul_of_nonneg_right hy1 (by linarith)
  have h2 : (Y : ℝ) / 4 < p := by linarith
  have e : (2 : ℝ) ^ (3 * s) = 2 ^ (3 * s - 2) * 4 := by
    have e1 : 3 * s = (3 * s - 2) + 2 := by omega
    conv_lhs => rw [e1, pow_add]
    norm_num
  have h3 : (2 : ℝ) ^ (3 * s - 2) < p := by
    rw [hY, e] at h2
    linarith
  have h4 : Real.log ((2 : ℝ) ^ (3 * s - 2)) ≤ Real.log p :=
    Real.log_le_log (by positivity) h3.le
  rw [Real.log_pow] at h4
  have h5 : ((3 * s - 2 : ℕ) : ℝ) = 3 * s - 2 := by
    rw [Nat.cast_sub (by omega)]
    push_cast
    ring
  rw [h5] at h4
  have hsR : (2 : ℝ) ≤ s := by exact_mod_cast hs
  have h6 := mul_le_mul_of_nonneg_left hl2 (by linarith : (0 : ℝ) ≤ 3 * s - 2)
  linarith

theorem tie1 (K Y s : ℕ) (L y : ℝ) (p a : ℕ) (hK : 11 ≤ K) (hKs : K = 2 ^ s) (hY : Y = K ^ 3)
    (hLY : L ≤ Y) (hy2 : y ≤ 2 * Y) (hp : 2 ≤ p) (ha : 1 ≤ a)
    (h : ((p : ℝ) ^ (a + 1) - (p : ℝ) ^ a) < y * Real.log p + L) :
    p < 5 * K ^ 2 ∧ a < 6 * s := by
  have hpR : (2 : ℝ) ≤ p := by exact_mod_cast hp
  have hp0 : (0 : ℝ) < p := by linarith
  have hKR : (11 : ℝ) ≤ K := by exact_mod_cast hK
  have hYR : (Y : ℝ) = (K : ℝ) ^ 3 := by
    rw [hY]
    norm_cast
  have hYpos : (0 : ℝ) < Y := by
    rw [hYR]
    positivity
  have hlog0 : 0 ≤ Real.log p := Real.log_nonneg (by linarith)
  have hr0 : 0 < Real.sqrt p := Real.sqrt_pos.2 hp0
  have hr1 : 1 ≤ Real.sqrt p := by
    rw [show (1 : ℝ) = Real.sqrt 1 by simp]
    exact Real.sqrt_le_sqrt (by linarith)
  have hsq : Real.sqrt p * Real.sqrt p = p := Real.mul_self_sqrt hp0.le
  have hlog1 : Real.log p ≤ 2 * Real.sqrt p := by
    have h1 := Real.log_le_sub_one_of_pos hr0
    have h2 : Real.log p = 2 * Real.log (Real.sqrt p) := by
      rw [Real.log_sqrt hp0.le]
      ring
    linarith
  have hlog2 : Real.log p ≤ p := by
    have := Real.log_le_sub_one_of_pos hp0
    linarith
  have hpa : (p : ℝ) ≤ (p : ℝ) ^ a := le_self_pow₀ (by linarith) (by omega)
  have hpow : (p : ℝ) ^ (a + 1) = (p : ℝ) ^ a * p := pow_succ _ _
  have hylog : y * Real.log p ≤ 2 * Y * Real.log p := mul_le_mul_of_nonneg_right hy2 hlog0
  have h1 : (p : ℝ) * p ≤ 2 * ((p : ℝ) ^ (a + 1) - (p : ℝ) ^ a) := by
    rw [hpow]
    have t1 := mul_le_mul_of_nonneg_right hpa (by linarith : (0 : ℝ) ≤ (p : ℝ) - 1)
    have t2 := mul_nonneg hp0.le (by linarith : (0 : ℝ) ≤ (p : ℝ) - 2)
    nlinarith
  have h2 : (p : ℝ) * p < 10 * Y * Real.sqrt p := by
    have t3 : 2 * (Y : ℝ) * Real.log p ≤ 2 * Y * (2 * Real.sqrt p) :=
      mul_le_mul_of_nonneg_left hlog1 (by positivity)
    have t4 : (Y : ℝ) ≤ Y * Real.sqrt p := by nlinarith
    nlinarith
  have h3 : Real.sqrt p ^ 3 < 10 * Y := by
    have t : Real.sqrt p ^ 3 * Real.sqrt p < 10 * Y * Real.sqrt p := by
      have e : Real.sqrt p ^ 3 * Real.sqrt p =
          (Real.sqrt p * Real.sqrt p) * (Real.sqrt p * Real.sqrt p) := by ring
      rw [e, hsq]
      exact h2
    exact lt_of_mul_lt_mul_right t hr0.le
  have h4 : (p : ℝ) ^ 3 < 100 * (Y : ℝ) ^ 2 := by
    have e : (p : ℝ) ^ 3 = (Real.sqrt p ^ 3) ^ 2 := by
      calc (p : ℝ) ^ 3 = (Real.sqrt p * Real.sqrt p) ^ 3 := by rw [hsq]
        _ = (Real.sqrt p ^ 3) ^ 2 := by ring
    rw [e]
    have t := mul_pos (sub_pos.2 h3) (by positivity : (0 : ℝ) < 10 * Y + Real.sqrt p ^ 3)
    nlinarith
  have h5 : p ^ 3 < 100 * Y ^ 2 := by exact_mod_cast h4
  have h6 : p < 5 * K ^ 2 := by
    apply lt_of_pow_lt_pow_left₀ 3 (Nat.zero_le _)
    have e1 : (5 * K ^ 2) ^ 3 = 125 * K ^ 6 := by ring
    have e2 : 100 * Y ^ 2 = 100 * K ^ 6 := by
      rw [hY]
      ring
    omega
  have hpK : (p : ℝ) ≤ 5 * (K : ℝ) ^ 2 := by
    have t : ((p : ℕ) : ℝ) ≤ ((5 * K ^ 2 : ℕ) : ℝ) := by exact_mod_cast h6.le
    push_cast at t
    exact t
  have h7 : (2 : ℝ) ^ a ≤ (p : ℝ) ^ a := pow_le_pow_left₀ (by norm_num) hpR a
  have h8 : (p : ℝ) ^ a ≤ (p : ℝ) ^ (a + 1) - (p : ℝ) ^ a := by
    rw [hpow]
    have t := mul_nonneg (pow_pos hp0 a).le (by linarith : (0 : ℝ) ≤ (p : ℝ) - 2)
    nlinarith
  have e6 : (K : ℝ) ^ 6 = (2 : ℝ) ^ (6 * s) := by
    rw [hKs]
    push_cast
    rw [← pow_mul, mul_comm]
  have h9 : (2 : ℝ) ^ a < (2 : ℝ) ^ (6 * s) := by
    rw [← e6]
    have t5 : 2 * (Y : ℝ) * Real.log p ≤ 2 * Y * (5 * K ^ 2) :=
      mul_le_mul_of_nonneg_left (hlog2.trans hpK) (by positivity)
    have k2 : (121 : ℝ) ≤ (K : ℝ) ^ 2 := by nlinarith
    have k3 := mul_nonneg (sq_nonneg (K : ℝ)) (sub_nonneg.2 hKR)
    have t7 : (10 * (K : ℝ) ^ 2 + 1) < (K : ℝ) ^ 3 := by nlinarith
    have t8 : (Y : ℝ) * (10 * K ^ 2 + 1) < Y * K ^ 3 := mul_lt_mul_of_pos_left t7 hYpos
    have hYK : (Y : ℝ) * (K : ℝ) ^ 3 = (K : ℝ) ^ 6 := by
      rw [hYR]
      ring
    nlinarith
  have h10 : a < 6 * s := (pow_lt_pow_iff_right₀ (by norm_num : (1 : ℝ) < 2)).1 h9
  exact ⟨h6, h10⟩

end P2ML

namespace P2ML

theorem pi_bound (Y s : ℕ) (hYR : (Y : ℝ) = 2 ^ (3 * s)) (hs4R : (4 : ℝ) ≤ s)
    (hsY : 16 * (s : ℝ) ≤ Y) :
    (((Finset.range (16 * Y * s + 1)).filter Nat.Prime).card : ℝ) ≤ 31 * Y := by
  have hYpos : (0 : ℝ) < Y := by linarith
  have hl2a : (0.69 : ℝ) < Real.log 2 := by
    have := Real.log_two_gt_d9
    linarith
  have hl2b : Real.log 2 < 0.6932 := by
    have := Real.log_two_lt_d9
    linarith
  have hpc : Nat.primeCounting (16 * Y * s) =
      ((Finset.range (16 * Y * s + 1)).filter Nat.Prime).card := by
    simp [Nat.primeCounting, Nat.primeCounting', Nat.count_eq_card_filter_range]
  rw [← hpc]
  have hYs : (4 : ℝ) ≤ (Y : ℝ) * s := by
    nlinarith [mul_nonneg (by linarith : (0 : ℝ) ≤ (Y : ℝ) - 1) (by linarith : (0 : ℝ) ≤ (s : ℝ) - 4)]
  have hx1 : (1 : ℝ) < ((16 * Y * s : ℕ) : ℝ) := by
    push_cast
    linarith
  have h2 := Chebyshev.pi_le_log4_mul_div hx1
  rw [Nat.floor_natCast] at h2
  push_cast at h2
  have hXpos : (0 : ℝ) < 16 * Y * s := by linarith
  have hsqrt : Real.sqrt (16 * (Y : ℝ) * s) ≤ Y := by
    calc Real.sqrt (16 * (Y : ℝ) * s) ≤ Real.sqrt ((Y : ℝ) ^ 2) :=
          Real.sqrt_le_sqrt (by nlinarith [mul_le_mul_of_nonneg_left hsY hYpos.le])
      _ = Y := Real.sqrt_sq hYpos.le
  have hlogY : Real.log (Y : ℝ) = 3 * s * Real.log 2 := by
    rw [hYR, Real.log_pow]
    push_cast
    ring
  have hlogX : 2 * (s : ℝ) ≤ Real.log (16 * (Y : ℝ) * s) := by
    have t1 : Real.log (Y : ℝ) ≤ Real.log (16 * (Y : ℝ) * s) :=
      Real.log_le_log hYpos (by nlinarith)
    have t2 := mul_nonneg (by linarith : (0 : ℝ) ≤ s) (by linarith : (0 : ℝ) ≤ Real.log 2 - 0.69)
    nlinarith
  have hls : (s : ℝ) ≤ Real.log (Real.sqrt (16 * (Y : ℝ) * s)) := by
    rw [Real.log_sqrt hXpos.le]
    linarith
  have hl4 : Real.log 4 = 2 * Real.log 2 := by
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]
    norm_num
  have hmain : Real.log 4 * (16 * (Y : ℝ) * s) / Real.log (Real.sqrt (16 * (Y : ℝ) * s)) ≤
      30 * Y := by
    rw [div_le_iff₀ (by linarith)]
    have t1 : Real.log 4 * (16 * (Y : ℝ) * s) ≤ 1.4 * (16 * (Y : ℝ) * s) :=
      mul_le_mul_of_nonneg_right (by linarith) hXpos.le
    have t2 : 30 * (Y : ℝ) * s ≤ 30 * Y * Real.log (Real.sqrt (16 * (Y : ℝ) * s)) :=
      mul_le_mul_of_nonneg_left hls (by positivity)
    have t3 : 0 ≤ (Y : ℝ) * s := by positivity
    linarith
  linarith

set_option maxHeartbeats 400000 in
theorem exists_y_core (m u s K Y : ℕ) (hK : K = 2 ^ s) (hY : Y = K ^ 3)
    (hmR : (1 : ℝ) ≤ m) (huR : (u : ℝ) = 1200 * m) (hsR : (s : ℝ) = 2 * u)
    (hKuR : (u : ℝ) * u < K) (hK11 : 11 ≤ K) (hs4R : (4 : ℝ) ≤ s) (hs4 : 4 ≤ s)
    (hYR : (Y : ℝ) = 2 ^ (3 * s)) (hYK : (Y : ℝ) = (K : ℝ) ^ 3) (hYpos : (0 : ℝ) < Y)
    (hLY : 4 * (m : ℝ) ≤ Y) (hsY : 16 * (s : ℝ) ≤ Y) :
    ∃ y : ℝ, 0 < y ∧ ∀ p : ℕ, p.Prime → ∀ a : ℕ,
      y * Real.log p + m ≤ wr p a ∨ wr p a ≤ y * Real.log p - m := by
  classical
  have hl2a : (0.69 : ℝ) < Real.log 2 := by
    have := Real.log_two_gt_d9
    linarith
  obtain ⟨J, hJ⟩ : ∃ J : Finset ℕ, J = Finset.Ico (Y * 200) (2 * Y * 200) := ⟨_, rfl⟩
  have hJcard : J.card = 200 * Y := by
    rw [hJ, Nat.card_Ico]
    omega
  obtain ⟨B, hB⟩ : ∃ B : ℕ → ℕ → Finset ℕ, ∀ p a, B p a =
      J.filter (fun j : ℕ => |wr p a - j * (Real.log p / 200)| < (m : ℝ)) :=
    ⟨fun p a => _, fun _ _ => rfl⟩
  obtain ⟨R0, hR0⟩ : ∃ R0 : Finset ℕ, R0 = (Finset.range (16 * Y * s + 1)).filter
      (fun p : ℕ => p.Prime ∧ (s : ℝ) ≤ Real.log p) := ⟨_, rfl⟩
  obtain ⟨R1, hR1⟩ : ∃ R1 : Finset (ℕ × ℕ), R1 =
      (Finset.Ico 2 (5 * K ^ 2)) ×ˢ (Finset.range (6 * s)) := ⟨_, rfl⟩
  have hB0 : ∀ p ∈ R0, ((B p 0).card : ℝ) ≤ 7 / 6 := by
    intro p hp
    rw [hR0, Finset.mem_filter] at hp
    obtain ⟨-, -, hlog⟩ := hp
    have hβ : 0 < Real.log p / 200 := by
      have : (0 : ℝ) < Real.log p := by linarith
      positivity
    have h1 := card_ties J (wr p 0) (Real.log p / 200) m hβ (by linarith)
    rw [hB]
    have h2 : 2 * (m : ℝ) / (Real.log p / 200) ≤ 1 / 6 := by
      rw [div_le_iff₀ hβ]
      linarith
    linarith
  have hB1 : ∀ x ∈ R1, ((B x.1 x.2).card : ℝ) ≤ 801 * m := by
    intro x hx
    rw [hR1, Finset.mem_product, Finset.mem_Ico] at hx
    have hx2 : (2 : ℝ) ≤ x.1 := by exact_mod_cast hx.1.1
    have hlog : Real.log 2 ≤ Real.log x.1 := Real.log_le_log (by norm_num) hx2
    have hβ : 0 < Real.log x.1 / 200 := by
      have : (0 : ℝ) < Real.log x.1 := by linarith
      positivity
    have h1 := card_ties J (wr x.1 x.2) (Real.log x.1 / 200) m hβ (by linarith)
    rw [hB]
    have h2 : 2 * (m : ℝ) / (Real.log x.1 / 200) ≤ 800 * m := by
      rw [div_le_iff₀ hβ]
      have := mul_nonneg (by linarith : (0 : ℝ) ≤ m)
        (by linarith : (0 : ℝ) ≤ Real.log x.1 - 1 / 2)
      nlinarith
    linarith
  have hR0card : (R0.card : ℝ) ≤ 31 * Y := by
    have hsub : R0 ⊆ (Finset.range (16 * Y * s + 1)).filter Nat.Prime := by
      rw [hR0]
      intro p hp
      rw [Finset.mem_filter] at hp ⊢
      exact ⟨hp.1, hp.2.1⟩
    have h1 : (R0.card : ℝ) ≤ (((Finset.range (16 * Y * s + 1)).filter Nat.Prime).card : ℝ) := by
      exact_mod_cast Finset.card_le_card hsub
    exact h1.trans (pi_bound Y s hYR hs4R hsY)
  have hR1card : (R1.card : ℝ) ≤ 30 * s * (K : ℝ) ^ 2 := by
    have h : R1.card ≤ (5 * K ^ 2) * (6 * s) := by
      rw [hR1, Finset.card_product, Nat.card_Ico, Finset.card_range]
      exact Nat.mul_le_mul_right _ (Nat.sub_le _ _)
    have h' : (R1.card : ℝ) ≤ (((5 * K ^ 2) * (6 * s) : ℕ) : ℝ) := by exact_mod_cast h
    push_cast at h'
    linarith
  obtain ⟨U, hU⟩ : ∃ U : Finset ℕ, U =
      (R0.biUnion fun p => B p 0) ∪ (R1.biUnion fun x => B x.1 x.2) := ⟨_, rfl⟩
  have hUcard : (U.card : ℝ) < 200 * Y := by
    have h1 : U.card ≤ ∑ p ∈ R0, (B p 0).card + ∑ x ∈ R1, (B x.1 x.2).card := by
      rw [hU]
      exact (Finset.card_union_le _ _).trans
        (add_le_add Finset.card_biUnion_le Finset.card_biUnion_le)
    have h2 : (U.card : ℝ) ≤
        ∑ p ∈ R0, ((B p 0).card : ℝ) + ∑ x ∈ R1, ((B x.1 x.2).card : ℝ) := by
      exact_mod_cast h1
    have h3 : ∑ p ∈ R0, ((B p 0).card : ℝ) ≤ R0.card * (7 / 6) := by
      have := Finset.sum_le_sum hB0
      rw [Finset.sum_const, nsmul_eq_mul] at this
      exact this
    have h4 : ∑ x ∈ R1, ((B x.1 x.2).card : ℝ) ≤ R1.card * (801 * m) := by
      have := Finset.sum_le_sum hB1
      rw [Finset.sum_const, nsmul_eq_mul] at this
      exact this
    have h5 : (R0.card : ℝ) * (7 / 6) ≤ 31 * Y * (7 / 6) := by linarith
    have h6 : (R1.card : ℝ) * (801 * m) ≤ 30 * s * (K : ℝ) ^ 2 * (801 * m) :=
      mul_le_mul_of_nonneg_right hR1card (by positivity)
    have hm_eq : (m : ℝ) = u / 1200 :=
      eq_div_of_mul_eq (by norm_num) (by rw [huR]; ring)
    have h7 : 30 * (s : ℝ) * (K : ℝ) ^ 2 * (801 * m) = 801 / 20 * ((u : ℝ) * u) * (K : ℝ) ^ 2 := by
      rw [hsR, hm_eq]
      ring
    have h8 : 801 / 20 * ((u : ℝ) * u) * (K : ℝ) ^ 2 ≤ 801 / 20 * K * (K : ℝ) ^ 2 := by
      have := mul_le_mul_of_nonneg_right hKuR.le (by positivity : (0 : ℝ) ≤ (K : ℝ) ^ 2)
      linarith only [this]
    have h9 : 801 / 20 * (K : ℝ) * (K : ℝ) ^ 2 = 801 / 20 * Y := by
      rw [hYK]
      ring
    linarith
  have hlt : U.card < J.card := by
    rw [hJcard]
    have : (U.card : ℝ) < ((200 * Y : ℕ) : ℝ) := by
      push_cast
      exact hUcard
    exact_mod_cast this
  obtain ⟨j, hjJ, hjU⟩ := Finset.exists_mem_notMem_of_card_lt_card hlt
  have hjJ' := hjJ
  rw [hJ, Finset.mem_Ico] at hjJ'
  have hj1 : (Y : ℝ) ≤ (j : ℝ) / 200 := by
    have : ((Y * 200 : ℕ) : ℝ) ≤ j := by exact_mod_cast hjJ'.1
    push_cast at this
    linarith
  have hj2 : (j : ℝ) / 200 ≤ 2 * Y := by
    have : (j : ℝ) ≤ ((2 * Y * 200 : ℕ) : ℝ) := by exact_mod_cast hjJ'.2.le
    push_cast at this
    linarith
  refine ⟨(j : ℝ) / 200, by linarith, fun p hp a => ?_⟩
  by_contra hcon
  push Not at hcon
  obtain ⟨c1, c2⟩ := hcon
  have habs : |wr p a - j * (Real.log p / 200)| < (m : ℝ) := by
    rw [abs_lt]
    constructor <;> linarith
  have hjB : j ∈ B p a := by
    rw [hB]
    exact Finset.mem_filter.2 ⟨hjJ, habs⟩
  apply hjU
  rw [hU, Finset.mem_union]
  rcases Nat.eq_zero_or_pos a with ha | ha
  · subst ha
    left
    have hw : wr p 0 = p := by simp [wr, c]
    rw [hw] at c1 c2
    have h1 := tie0_upper Y s m ((j : ℝ) / 200) p hs4 (by linarith) hYR hj2 hp.two_le c1
    have h2 := tie0_lower Y s m ((j : ℝ) / 200) p (by omega) hLY hYR hj1 hp.two_le c2
    refine Finset.mem_biUnion.2 ⟨p, ?_, hjB⟩
    rw [hR0, Finset.mem_filter, Finset.mem_range]
    exact ⟨by omega, hp, h2⟩
  · right
    have hw : wr p a = (p : ℝ) ^ (a + 1) - (p : ℝ) ^ a := by
      simp [wr, c_pos' p (by omega : a + 1 ≠ 0), c_pos' p (by omega : a ≠ 0)]
    rw [hw] at c1 c2
    have h1 := tie1 K Y s m ((j : ℝ) / 200) p a hK11 hK hY (by linarith) hj2 hp.two_le ha c1
    refine Finset.mem_biUnion.2 ⟨(p, a), ?_, hjB⟩
    rw [hR1, Finset.mem_product, Finset.mem_Ico, Finset.mem_range]
    exact ⟨⟨hp.two_le, h1.1⟩, h1.2⟩


theorem exists_y (m : ℕ) (hm : 1 ≤ m) : ∃ y : ℝ, 0 < y ∧ ∀ p : ℕ, p.Prime → ∀ a : ℕ,
      y * Real.log p + m ≤ wr p a ∨ wr p a ≤ y * Real.log p - m := by
  classical
  obtain ⟨u, hu⟩ : ∃ u : ℕ, u = 1200 * m := ⟨_, rfl⟩
  obtain ⟨s, hs⟩ : ∃ s : ℕ, s = 2 * u := ⟨_, rfl⟩
  obtain ⟨K, hK⟩ : ∃ K : ℕ, K = 2 ^ s := ⟨_, rfl⟩
  obtain ⟨Y, hY⟩ : ∃ Y : ℕ, Y = K ^ 3 := ⟨_, rfl⟩
  have hu1 : u < 2 ^ u := Nat.lt_two_pow_self
  have hKu : u * u < K := by
    rw [hK, hs, two_mul, pow_add]
    exact Nat.mul_lt_mul'' hu1 hu1
  have hmR : (1 : ℝ) ≤ m := by exact_mod_cast hm
  have huR : (u : ℝ) = 1200 * m := by exact_mod_cast hu
  have hsR : (s : ℝ) = 2 * u := by exact_mod_cast hs
  have hKuR : (u : ℝ) * u < K := by exact_mod_cast hKu
  have hu1200 : (1200 : ℝ) ≤ u := by linarith
  have huu : 1200 * (u : ℝ) ≤ u * u := by nlinarith
  have hK11R : (11 : ℝ) ≤ K := by linarith
  have hK11 : 11 ≤ K := by exact_mod_cast hK11R
  have hs4R : (4 : ℝ) ≤ s := by linarith
  have hs4 : 4 ≤ s := by exact_mod_cast hs4R
  have hYR : (Y : ℝ) = 2 ^ (3 * s) := by
    rw [hY, hK]
    push_cast
    rw [← pow_mul, mul_comm]
  have hYK : (Y : ℝ) = (K : ℝ) ^ 3 := by
    rw [hY]
    norm_cast
  have hK2 : (121 : ℝ) ≤ (K : ℝ) ^ 2 := by nlinarith
  have hKY : 121 * (K : ℝ) ≤ Y := by
    rw [hYK]
    nlinarith [mul_nonneg (by linarith : (0 : ℝ) ≤ K) (sub_nonneg.2 hK2)]
  have hYpos : (0 : ℝ) < Y := by linarith
  have hLY : 4 * (m : ℝ) ≤ Y := by linarith
  have hsY : 16 * (s : ℝ) ≤ Y := by linarith
  exact exists_y_core m u s K Y hK hY hmR huR hsR hKuR hK11 hs4R hs4 hYR hYK hYpos hLY hsY

end P2ML

theorem solution :
    ∀ m : ℕ, ∃ n : ℕ, ∀ k ≤ m, landau (n + k) = landau n := by
  intro m
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · exact ⟨0, fun k hk => by rw [Nat.le_zero.1 hk]⟩
  · obtain ⟨y, hy, hT⟩ := P2ML.exists_y m hm
    exact P2ML.plateau m hm y hy hT
