-- Prove2me | solution 1 for MultimodularDocks.fact_2
-- status  : ACCEPTED   (prove)
-- author  : @ducloc
-- created : 2026-11-21T07:18:33.314168+00:00
-- url     : https://prove2.me/submissions/635d09a9-15c8-4fdd-b0c2-64e02c81dca6

import Mathlib

theorem solution {S : Type*} [Fintype S] [DecidableEq S] (f : S → ℤ → ℝ) (cap : S → ℤ)
    (hconv : ∀ i k, 1 ≤ k → k + 1 ≤ cap i → 2 * f i k ≤ f i (k - 1) + f i (k + 1))
    (B : ℤ) (x y : S → ℤ)
    (hx : ∀ i, 0 ≤ x i ∧ x i ≤ cap i) (hxB : ∑ i, x i = B)
    (hy : ∀ i, 0 ≤ y i ∧ y i ≤ cap i) (hyB : ∑ i, y i = B)
    (hlt : ∑ i, f i (y i) < ∑ i, f i (x i)) :
    ∃ i j, i ≠ j ∧ x i + 1 ≤ cap i ∧ 1 ≤ x j ∧
      ∑ k, f k ((x + Pi.single i 1 - Pi.single j 1 : S → ℤ) k) < ∑ k, f k (x k) := by
  -- Discrete convexity: monotone first differences.
  have hmono : ∀ (g : ℤ → ℝ) (C : ℤ),
      (∀ k, 1 ≤ k → k + 1 ≤ C → 2 * g k ≤ g (k - 1) + g (k + 1)) →
      ∀ a b : ℤ, 1 ≤ a → a ≤ b → b ≤ C → g a - g (a - 1) ≤ g b - g (b - 1) := by
    intro g C hg a b ha hab
    refine Int.le_induction (m := a)
      (motive := fun n _ => n ≤ C → g a - g (a - 1) ≤ g n - g (n - 1)) ?_ ?_ b hab
    · intro _; exact le_rfl
    · intro n hn ih hbn
      have hnc : n ≤ C := by linarith
      have h1 : 1 ≤ n := le_trans ha hn
      have hstep : g n - g (n - 1) ≤ g (n + 1) - g n := by
        have := hg n h1 hbn
        linarith
      have hii := ih hnc
      have hsub : n + 1 - 1 = n := by ring
      rw [hsub]
      linarith
  -- Lower telescoping bound.
  have hlow : ∀ (g : ℤ → ℝ) (C : ℤ),
      (∀ k, 1 ≤ k → k + 1 ≤ C → 2 * g k ≤ g (k - 1) + g (k + 1)) →
      ∀ a b : ℤ, 0 ≤ a → a ≤ b → b ≤ C →
        ((b - a : ℤ) : ℝ) * (g (a + 1) - g a) ≤ g b - g a := by
    intro g C hg a b ha hab
    refine Int.le_induction (m := a)
      (motive := fun n _ => n ≤ C → ((n - a : ℤ) : ℝ) * (g (a + 1) - g a) ≤ g n - g a) ?_ ?_ b hab
    · intro _; simp
    · intro n hn ih hbn
      have hnc : n ≤ C := by linarith
      have hcast : ((n + 1 - a : ℤ) : ℝ) * (g (a + 1) - g a) =
          ((n - a : ℤ) : ℝ) * (g (a + 1) - g a) + (g (a + 1) - g a) := by
        push_cast
        ring
      have hs : g (a + 1) - g a ≤ g (n + 1) - g n := by
        have h := hmono g C hg (a + 1) (n + 1) (by linarith) (by linarith) hbn
        rw [show a + 1 - 1 = a from by ring, show n + 1 - 1 = n from by ring] at h
        exact h
      have hii := ih hnc
      rw [hcast]
      linarith
  -- Upper telescoping bound (right endpoint slope).
  have hup : ∀ (g : ℤ → ℝ) (C : ℤ),
      (∀ k, 1 ≤ k → k + 1 ≤ C → 2 * g k ≤ g (k - 1) + g (k + 1)) →
      ∀ a b : ℤ, 0 ≤ a → a ≤ b → b ≤ C →
        g b - g a ≤ ((b - a : ℤ) : ℝ) * (g b - g (b - 1)) := by
    intro g C hg a b ha hab
    refine Int.le_induction (m := a)
      (motive := fun n _ => n ≤ C → g n - g a ≤ ((n - a : ℤ) : ℝ) * (g n - g (n - 1))) ?_ ?_ b hab
    · intro _; simp
    · intro n hn ih hbn
      have hnc : n ≤ C := by linarith
      rcases lt_or_eq_of_le hn with hltn | heqn
      · have hn1 : 1 ≤ n := by linarith
        have hs : g n - g (n - 1) ≤ g (n + 1) - g n := by
          have := hg n hn1 hbn
          linarith
        have hna : (0 : ℝ) ≤ ((n - a : ℤ) : ℝ) := by
          have h : (0 : ℤ) ≤ n - a := by linarith
          exact_mod_cast h
        have hcast : ((n + 1 - a : ℤ) : ℝ) = ((n - a : ℤ) : ℝ) + 1 := by
          push_cast
          ring
        have hih := ih hnc
        have hmul : ((n - a : ℤ) : ℝ) * (g n - g (n - 1)) ≤
            ((n - a : ℤ) : ℝ) * (g (n + 1) - g n) :=
          mul_le_mul_of_nonneg_left hs hna
        have hsub : n + 1 - 1 = n := by ring
        rw [hsub, hcast]
        nlinarith
      · rw [← heqn]
        have hcast : ((a + 1 - a : ℤ) : ℝ) = 1 := by
          push_cast
          ring
        have hsub : a + 1 - 1 = a := by ring
        rw [hcast, hsub, one_mul]
  -- Differences and discrete slopes.
  set d : S → ℤ := fun i => y i - x i with hd
  set Δp : S → ℝ := fun i => f i (x i + 1) - f i (x i) with hΔp
  set Δm : S → ℝ := fun i => f i (x i) - f i (x i - 1) with hΔm
  -- Pointwise convexity bound.
  have hpoint : ∀ i, (if 0 < d i then (d i : ℝ) * Δp i else 0) -
      (if d i < 0 then (-(d i) : ℝ) * Δm i else 0) ≤ f i (y i) - f i (x i) := by
    intro i
    rcases lt_trichotomy (d i) 0 with hneg | hzero | hpos
    · have hyx : y i < x i := by rw [hd] at hneg; linarith
      have h1 : ¬ (0 < d i) := by linarith
      have hb : x i ≤ cap i := (hx i).2
      have hlowi := hup (f i) (cap i) (hconv i) (y i) (x i) (hy i).1 hyx.le hb
      have hcast : ((x i - y i : ℤ) : ℝ) = -(d i : ℝ) := by
        rw [hd]; push_cast; ring
      rw [hcast] at hlowi
      rw [if_neg h1, if_pos hneg]
      simp only [hΔm]
      linarith
    · have hyx : y i = x i := by rw [hd] at hzero; linarith
      rw [if_neg (by linarith : ¬ (0 < d i)), if_neg (by linarith : ¬ (d i < 0))]
      simp [hyx]
    · have hxy : x i < y i := by rw [hd] at hpos; linarith
      have hb : y i ≤ cap i := (hy i).2
      have hlowi := hlow (f i) (cap i) (hconv i) (x i) (y i) (hx i).1 hxy.le hb
      have hcast : ((y i - x i : ℤ) : ℝ) = (d i : ℝ) := by
        rw [hd]
      rw [hcast] at hlowi
      rw [if_pos hpos, if_neg (by linarith : ¬ (d i < 0))]
      simp only [hΔp]
      simpa using hlowi
  -- Sum the pointwise bounds.
  have hsum2 : ∑ i, (if 0 < d i then (d i : ℝ) * Δp i else 0) -
      ∑ i, (if d i < 0 then (-(d i) : ℝ) * Δm i else 0) ≤
      ∑ i, f i (y i) - ∑ i, f i (x i) := by
    rw [← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib]
    exact Finset.sum_le_sum (fun i _ => hpoint i)
  -- Split into positive and negative parts.
  set P : Finset S := Finset.univ.filter (fun i => 0 < d i) with hP
  set N : Finset S := Finset.univ.filter (fun i => d i < 0) with hN
  have hAif : ∑ i, (if 0 < d i then (d i : ℝ) * Δp i else 0) =
      ∑ i ∈ P, (d i : ℝ) * Δp i := by
    rw [← Finset.sum_filter]
  have hBif : ∑ i, (if d i < 0 then (-(d i) : ℝ) * Δm i else 0) =
      ∑ i ∈ N, (-(d i) : ℝ) * Δm i := by
    rw [← Finset.sum_filter]
  set A : ℝ := ∑ i ∈ P, (d i : ℝ) * Δp i with hA
  set Bm : ℝ := ∑ i ∈ N, (-(d i) : ℝ) * Δm i with hBm
  have hAB : A - Bm < 0 := by
    rw [hAif, hBif] at hsum2
    linarith
  -- The total positive and negative masses agree.
  have hdsumR : ∑ i, (d i : ℝ) = 0 := by
    rw [hd]
    simp only [Int.cast_sub]
    rw [Finset.sum_sub_distrib]
    have hx' : ∑ i, (x i : ℝ) = (B : ℝ) := by rw [← Int.cast_sum, hxB]
    have hy' : ∑ i, (y i : ℝ) = (B : ℝ) := by rw [← Int.cast_sum, hyB]
    rw [hy', hx', sub_self]
  have hsplit : ∑ i, (d i : ℝ) = ∑ i ∈ P, (d i : ℝ) + ∑ i ∈ N, (d i : ℝ) := by
    have hpt : ∀ i, (d i : ℝ) = (if 0 < d i then (d i : ℝ) else 0) +
        (if d i < 0 then (d i : ℝ) else 0) := by
      intro i
      rcases lt_trichotomy (d i) 0 with h | h | h
      · rw [if_neg (by linarith : ¬ (0 < d i)), if_pos h]; ring
      · rw [if_neg (by linarith : ¬ (0 < d i)), if_neg (by linarith : ¬ (d i < 0)), h]; ring
      · rw [if_pos h, if_neg (by linarith : ¬ (d i < 0))]; ring
    calc ∑ i, (d i : ℝ) = ∑ i, ((if 0 < d i then (d i : ℝ) else 0) +
          (if d i < 0 then (d i : ℝ) else 0)) := by
          apply Finset.sum_congr rfl
          intro i _
          exact hpt i
      _ = ∑ i, (if 0 < d i then (d i : ℝ) else 0) +
          ∑ i, (if d i < 0 then (d i : ℝ) else 0) := Finset.sum_add_distrib
      _ = ∑ i ∈ P, (d i : ℝ) + ∑ i ∈ N, (d i : ℝ) := by
          rw [← Finset.sum_filter, ← Finset.sum_filter]
  have hDn : ∑ j ∈ N, (-(d j) : ℝ) = ∑ i ∈ P, (d i : ℝ) := by
    have h1 : ∑ j ∈ N, (-(d j) : ℝ) = -(∑ j ∈ N, (d j : ℝ)) :=
      Finset.sum_neg_distrib (fun j => (d j : ℝ))
    rw [h1]
    linarith [hdsumR, hsplit]
  have hdne : d ≠ 0 := by
    intro hzero
    have hsame : ∑ i, f i (y i) = ∑ i, f i (x i) := by
      apply Finset.sum_congr rfl
      intro i _
      have hi : y i = x i := by
        have := congrFun hzero i
        rw [hd] at this
        simp at this
        linarith
      rw [hi]
    linarith
  have hPne : P.Nonempty := by
    rw [Finset.nonempty_iff_ne_empty]
    intro hempty
    have hall : ∀ i, d i ≤ 0 := by
      intro i
      have hmem : i ∉ P := by rw [hempty]; simp
      by_contra hgt
      have hgt' : 0 < d i := not_le.mp hgt
      exact hmem (by simp [hP, hgt'])
    obtain ⟨i, hi⟩ : ∃ i, d i ≠ 0 := by
      by_contra h
      push Not at h
      exact hdne (funext h)
    have hlti : d i < 0 := lt_of_le_of_ne (hall i) hi
    have hsumneg : ∑ k, d k < 0 := by
      have h := Finset.sum_lt_sum (f := d) (g := fun _ => (0 : ℤ)) (fun k _ => hall k)
        ⟨i, Finset.mem_univ i, hlti⟩
      simpa using h
    have hsum0 : ∑ k, d k = 0 := by
      rw [hd, Finset.sum_sub_distrib, hyB, hxB, sub_self]
    linarith
  have hNne : N.Nonempty := by
    rw [Finset.nonempty_iff_ne_empty]
    intro hempty
    have hall : ∀ i, 0 ≤ d i := by
      intro i
      have hmem : i ∉ N := by rw [hempty]; simp
      by_contra hlt'
      have hlt'' : d i < 0 := not_le.mp hlt'
      exact hmem (by simp [hN, hlt''])
    obtain ⟨i, hi⟩ : ∃ i, d i ≠ 0 := by
      by_contra h
      push Not at h
      exact hdne (funext h)
    have hlti : 0 < d i := lt_of_le_of_ne (hall i) (Ne.symm hi)
    have hsumpos : 0 < ∑ k, d k :=
      Finset.sum_pos' (fun k _ => hall k) ⟨i, Finset.mem_univ i, hlti⟩
    have hsum0 : ∑ k, d k = 0 := by
      rw [hd, Finset.sum_sub_distrib, hyB, hxB, sub_self]
    linarith
  -- Weighted-average step.
  have hex : ∃ i, i ∈ P ∧ ∃ j, j ∈ N ∧ Δp i < Δm j := by
    by_contra hcon
    push Not at hcon
    set M : ℝ := N.sup' hNne Δm with hM
    have hMle : ∀ i ∈ P, M ≤ Δp i := by
      intro i hi
      rw [hM]
      exact Finset.sup'_le hNne Δm (fun j hj => hcon i hi j hj)
    have hAle : M * (∑ i ∈ P, (d i : ℝ)) ≤ A := by
      rw [hA, Finset.mul_sum]
      apply Finset.sum_le_sum
      intro i hi
      have hdiZ : 0 < d i := by
        simp only [hP, Finset.mem_filter, Finset.mem_univ, true_and] at hi
        exact hi
      have hdi : (0 : ℝ) < (d i : ℝ) := by exact_mod_cast hdiZ
      calc M * (d i : ℝ) ≤ Δp i * (d i : ℝ) := mul_le_mul_of_nonneg_right (hMle i hi) hdi.le
        _ = (d i : ℝ) * Δp i := by ring
    have hBle : Bm ≤ M * (∑ i ∈ P, (d i : ℝ)) := by
      rw [hBm, ← hDn, Finset.mul_sum]
      apply Finset.sum_le_sum
      intro j hj
      have hdjZ : d j < 0 := by
        simp only [hN, Finset.mem_filter, Finset.mem_univ, true_and] at hj
        exact hj
      have hdj : (0 : ℝ) < (-(d j) : ℝ) := by
        have h : (0 : ℤ) < -(d j) := by linarith
        exact_mod_cast h
      have hMj : Δm j ≤ M := by
        rw [hM]
        exact Finset.le_sup' Δm hj
      calc (-(d j) : ℝ) * Δm j ≤ (-(d j) : ℝ) * M := mul_le_mul_of_nonneg_left hMj hdj.le
        _ = M * (-(d j) : ℝ) := by ring
    linarith
  obtain ⟨i, hiP, j, hjN, hijlt⟩ := hex
  have hdiZ : 0 < d i := by
    simp only [hP, Finset.mem_filter, Finset.mem_univ, true_and] at hiP
    exact hiP
  have hdjZ : d j < 0 := by
    simp only [hN, Finset.mem_filter, Finset.mem_univ, true_and] at hjN
    exact hjN
  have hxi_lt : x i < y i := by rw [hd] at hdiZ; linarith
  have hyj_lt : y j < x j := by rw [hd] at hdjZ; linarith
  have hij : i ≠ j := by
    intro heq
    subst heq
    linarith
  have hcap_i : x i + 1 ≤ cap i := by have := (hy i).2; omega
  have hpos_j : 1 ≤ x j := by have := (hy j).1; omega
  refine ⟨i, j, hij, hcap_i, hpos_j, ?_⟩
  -- Compute the value of the exchange.
  have hvi : (x + Pi.single i 1 - Pi.single j 1 : S → ℤ) i = x i + 1 := by
    simp [Pi.single_eq_same, Pi.single_eq_of_ne hij]
  have hvj : (x + Pi.single i 1 - Pi.single j 1 : S → ℤ) j = x j - 1 := by
    simp [Pi.single_eq_same, Pi.single_eq_of_ne (Ne.symm hij)]
  have hval : ∑ k, f k ((x + Pi.single i 1 - Pi.single j 1 : S → ℤ) k) - ∑ k, f k (x k) =
      Δp i - Δm j := by
    rw [← Finset.sum_sub_distrib]
    have hzero : ∀ k, k ∉ ({i, j} : Finset S) →
        f k ((x + Pi.single i 1 - Pi.single j 1 : S → ℤ) k) - f k (x k) = 0 := by
      intro k hk
      simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hk
      obtain ⟨hk1, hk2⟩ := hk
      have hz : (x + Pi.single i 1 - Pi.single j 1 : S → ℤ) k = x k := by
        simp [Pi.single_eq_of_ne hk1, Pi.single_eq_of_ne hk2]
      rw [hz, sub_self]
    have hsub : ∑ k, (f k ((x + Pi.single i 1 - Pi.single j 1 : S → ℤ) k) - f k (x k)) =
        ∑ k ∈ ({i, j} : Finset S),
          (f k ((x + Pi.single i 1 - Pi.single j 1 : S → ℤ) k) - f k (x k)) :=
      (Finset.sum_subset (Finset.subset_univ (s := ({i, j} : Finset S))) (by
        intro k _ hk
        exact hzero k hk)).symm
    rw [hsub, Finset.sum_insert (by simp [hij]), Finset.sum_singleton, hvi, hvj]
    simp only [hΔp, hΔm]
    ring
  rw [← sub_neg] at hijlt ⊢
  rw [hval]
  exact hijlt
