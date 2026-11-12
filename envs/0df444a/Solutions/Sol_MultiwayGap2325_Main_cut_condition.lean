-- Prove2me | solution 1 for MultiwayGap2325.Main.cut_condition
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-11T21:28:29.591575+00:00
-- url     : https://prove2.me/submissions/dd428beb-2b56-4ed4-8929-ec75a3fa5ff7

import Mathlib

section
set_option autoImplicit false

namespace MultiwayGap2325.Dev.CutCondition

open Finset

variable {r : ℕ}

/-- symmetric double sum is twice the sum over `i < j`. -/
lemma double_sum_eq (f : Fin r → Fin r → ℝ) (hs : ∀ i j, f i j = f j i) (hd : ∀ i, f i i = 0) :
    ∑ i, ∑ j, f i j = 2 * ∑ i, ∑ j ∈ univ.filter (fun j => i < j), f i j := by
  have h1 : ∀ i, ∑ j, f i j = (∑ j, if i < j then f i j else 0) + ∑ j, if j < i then f i j else 0 := by
    intro i
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl (fun j _ => ?_)
    rcases lt_trichotomy i j with h | h | h
    · simp [h, not_lt.mpr h.le]
    · subst h; simp [hd]
    · simp [h, not_lt.mpr h.le]
  simp_rw [h1]
  rw [Finset.sum_add_distrib]
  have h2 : ∑ i, ∑ j, (if j < i then f i j else 0) = ∑ i, ∑ j, (if i < j then f i j else 0) := by
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun j _ => ?_))
    by_cases h : i < j
    · simp [h, hs i j]
    · simp [h]
  rw [h2, two_mul]
  simp_rw [Finset.sum_filter]


section main

variable (z : Fin r → ℝ) (w : Fin r → Fin r → ℝ)

lemma const_case (hz : ∑ i, z i = 0) (ν : Fin r → ℝ) (h : (univ.image ν).card ≤ 1) :
    2 * |∑ i, ν i * z i| ≤ ∑ i, ∑ j, w i j * |ν i - ν j| := by
  have hc : ∀ i j, ν i = ν j := by
    intro i j
    have := Finset.card_le_one.mp h (ν i) (Finset.mem_image_of_mem _ (mem_univ i))
      (ν j) (Finset.mem_image_of_mem _ (mem_univ j))
    exact this
  have h0 : ∑ i, ν i * z i = 0 := by
    rcases Nat.eq_zero_or_pos r with hr | hr
    · subst hr; simp
    · have : ∀ i, ν i = ν ⟨0, hr⟩ := fun i => hc _ _
      simp_rw [this, ← Finset.mul_sum, hz]; simp
  have h1 : ∑ i, ∑ j, w i j * |ν i - ν j| = 0 := by
    refine Finset.sum_eq_zero (fun i _ => Finset.sum_eq_zero (fun j _ => ?_))
    rw [hc i j]; simp
  rw [h0, h1]; simp

/-- core: doubled inequality by induction on the number of distinct values. -/
lemma core (hz : ∑ i, z i = 0) (hsym : ∀ i j, i ≠ j → w i j = w j i)
    (hnonneg : ∀ i j, i ≠ j → 0 ≤ w i j)
    (hcut : ∀ I : Finset (Fin r), I.Nonempty → I ≠ Finset.univ →
      |∑ i ∈ I, z i| ≤ ∑ i ∈ I, ∑ j ∈ Finset.univ \ I, w i j) :
    ∀ n : ℕ, ∀ ν : Fin r → ℝ, (univ.image ν).card ≤ n + 1 →
      2 * |∑ i, ν i * z i| ≤ ∑ i, ∑ j, w i j * |ν i - ν j| := by
  intro n
  induction n with
  | zero => intro ν hν; exact const_case z w hz ν (by simpa using hν)
  | succ n ih =>
    intro ν hν
    by_cases h1 : (univ.image ν).card ≤ 1
    · exact const_case z w hz ν h1
    rw [not_le] at h1
    have hne : (univ.image ν).Nonempty := Finset.card_pos.mp (by omega)
    set m := (univ.image ν).min' hne with hm
    have hmle : ∀ i, m ≤ ν i := fun i => Finset.min'_le _ _ (Finset.mem_image_of_mem _ (mem_univ i))
    have hmmem : m ∈ univ.image ν := Finset.min'_mem _ _
    have hne2 : ((univ.image ν).filter (fun x => m < x)).Nonempty := by
      by_contra hcon
      rw [Finset.not_nonempty_iff_eq_empty] at hcon
      have : univ.image ν ⊆ {m} := by
        intro x hx
        rw [Finset.mem_singleton]
        by_contra hxm
        have : x ∈ (univ.image ν).filter (fun x => m < x) :=
          Finset.mem_filter.mpr ⟨hx, lt_of_le_of_ne (Finset.min'_le _ _ hx) (Ne.symm hxm)⟩
        rw [hcon] at this; simp at this
      have := Finset.card_le_card this
      simp at this; omega
    set m' := ((univ.image ν).filter (fun x => m < x)).min' hne2 with hm'
    have hm'mem : m' ∈ (univ.image ν).filter (fun x => m < x) := Finset.min'_mem _ _
    have hmm' : m < m' := (Finset.mem_filter.mp hm'mem).2
    have hm'img : m' ∈ univ.image ν := (Finset.mem_filter.mp hm'mem).1
    have hm'le : ∀ i, ν i ≠ m → m' ≤ ν i := by
      intro i hi
      apply Finset.min'_le
      exact Finset.mem_filter.mpr ⟨Finset.mem_image_of_mem _ (mem_univ i),
        lt_of_le_of_ne (hmle i) (Ne.symm hi)⟩
    set ν' : Fin r → ℝ := fun i => if ν i = m then m' else ν i with hν'
    have hcard : (univ.image ν').card ≤ n + 1 := by
      have hsub : univ.image ν' ⊆ (univ.image ν).erase m := by
        intro x hx
        obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hx
        rw [Finset.mem_erase]
        by_cases hi : ν i = m
        · simp only [hν', hi, if_true]; exact ⟨ne_of_gt hmm', hm'img⟩
        · simp only [hν', hi, if_false]; exact ⟨hi, Finset.mem_image_of_mem _ (mem_univ i)⟩
      have := Finset.card_le_card hsub
      rw [Finset.card_erase_of_mem hmmem] at this
      omega
    have IH := ih ν' hcard
    set A : Finset (Fin r) := univ.filter (fun i => ν i = m) with hA
    have hAne : A.Nonempty := by
      obtain ⟨i, _, hi⟩ := Finset.mem_image.mp hmmem
      exact ⟨i, by simp [hA, hi]⟩
    have hAne' : A ≠ univ := by
      intro hAu
      have : ∀ i, ν i = m := fun i => by
        have : i ∈ A := by rw [hAu]; exact mem_univ i
        simpa [hA] using this
      obtain ⟨i, _, hi⟩ := Finset.mem_image.mp hm'img
      have := this i
      linarith
    have hc := hcut A hAne hAne'
    set d := m' - m with hd
    have hdpos : 0 < d := by linarith
    -- first: linear part
    have hlin : ∑ i, ν i * z i = ∑ i, ν' i * z i + (m - m') * ∑ i ∈ A, z i := by
      have : ∀ i, ν i * z i = ν' i * z i + (m - m') * (if i ∈ A then z i else 0) := by
        intro i
        by_cases hi : ν i = m
        · simp [hν', hi, hA]; ring
        · simp [hν', hi, hA]
      simp_rw [this]
      rw [Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_ite_mem, Finset.univ_inter]
    -- second: quadratic part
    have hquad : ∑ i, ∑ j, w i j * |ν i - ν j| =
        ∑ i, ∑ j, w i j * |ν' i - ν' j| +
          d * (∑ i, ∑ j, w i j * ((if i ∈ A ∧ j ∉ A then 1 else 0) +
            (if i ∉ A ∧ j ∈ A then 1 else 0))) := by
      rw [Finset.mul_sum, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl (fun i _ => ?_)
      rw [Finset.mul_sum, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl (fun j _ => ?_)
      by_cases hi : ν i = m <;> by_cases hj : ν j = m
      · simp [hν', hi, hj, hA]
      · have := hm'le j hj
        have hj2 : ν j - m' ≥ 0 := by linarith
        simp [hν', hi, hj, hA]
        rw [abs_of_nonpos (by linarith), abs_of_nonpos (by linarith)]; ring
      · have := hm'le i hi
        simp [hν', hi, hj, hA]
        rw [abs_of_nonneg (by linarith), abs_of_nonneg (by linarith)]; ring
      · simp [hν', hi, hj, hA]
    have hcsym : ∑ i, ∑ j, w i j * ((if i ∈ A ∧ j ∉ A then 1 else 0) +
            (if i ∉ A ∧ j ∈ A then 1 else 0)) = 2 * ∑ i ∈ A, ∑ j ∈ univ \ A, w i j := by
      simp_rw [mul_add, Finset.sum_add_distrib]
      have e1 : ∑ i, ∑ j, w i j * (if i ∈ A ∧ j ∉ A then (1:ℝ) else 0) =
          ∑ i ∈ A, ∑ j ∈ univ \ A, w i j := by
        have key : ∀ i, ∑ j, w i j * (if i ∈ A ∧ j ∉ A then (1:ℝ) else 0) =
            if i ∈ A then ∑ j ∈ univ \ A, w i j else 0 := by
          intro i
          by_cases hi : i ∈ A
          · simp only [hi, if_true]
            calc _ = ∑ j, (if j ∈ univ \ A then w i j else 0) := by
                  refine Finset.sum_congr rfl (fun j _ => ?_)
                  by_cases hj : j ∈ A <;> simp [hj]
              _ = _ := by rw [Finset.sum_ite_mem, Finset.univ_inter]
          · simp [hi]
        simp_rw [key]
        rw [Finset.sum_ite_mem, Finset.univ_inter]
      have e2 : ∑ i, ∑ j, w i j * (if i ∉ A ∧ j ∈ A then (1:ℝ) else 0) =
          ∑ i ∈ A, ∑ j ∈ univ \ A, w i j := by
        have : ∀ i j, w i j * (if i ∉ A ∧ j ∈ A then (1:ℝ) else 0) =
            if j ∈ A then (if i ∈ univ \ A then w j i else 0) else 0 := by
          intro i j; by_cases hi : i ∈ A <;> by_cases hj : j ∈ A <;> simp [hi, hj]
          exact hsym i j (by rintro rfl; exact hi hj)
        simp_rw [this]
        rw [Finset.sum_comm]
        have key2 : ∀ j, ∑ i, (if j ∈ A then (if i ∈ univ \ A then w j i else 0) else 0) =
            if j ∈ A then ∑ i ∈ univ \ A, w j i else 0 := by
          intro j
          by_cases hj : j ∈ A
          · simp only [hj, if_true]; rw [Finset.sum_ite_mem, Finset.univ_inter]
          · simp [hj]
        simp_rw [key2]
        rw [Finset.sum_ite_mem, Finset.univ_inter]
      rw [e1, e2]; ring
    have hneg : ∑ i, ∑ j, w i j * |ν' i - ν' j| = ∑ i, ∑ j, w i j * |ν' i - ν' j| := rfl
    rw [hquad, hcsym, hlin]
    have habs : |∑ i, ν' i * z i + (m - m') * ∑ i ∈ A, z i| ≤
        |∑ i, ν' i * z i| + d * |∑ i ∈ A, z i| := by
      calc _ ≤ |∑ i, ν' i * z i| + |(m - m') * ∑ i ∈ A, z i| := abs_add_le _ _
        _ = _ := by rw [abs_mul, abs_of_neg (by linarith : m - m' < 0)]; congr 1; rw [hd]; ring
    nlinarith [mul_le_mul_of_nonneg_left hc hdpos.le]

end main

end MultiwayGap2325.Dev.CutCondition

namespace MultiwayGap2325.Main
open MultiwayGap2325.Dev.CutCondition in
theorem chk_cut_condition (r : ℕ) (hr : 2 ≤ r) (z : Fin r → ℝ) (w : Fin r → Fin r → ℝ)
    (hz : ∑ i, z i = 0)
    (hsym : ∀ i j, i ≠ j → w i j = w j i)
    (hnonneg : ∀ i j, i ≠ j → 0 ≤ w i j)
    (hcut : ∀ I : Finset (Fin r), I.Nonempty → I ≠ Finset.univ →
      |∑ i ∈ I, z i| ≤ ∑ i ∈ I, ∑ j ∈ Finset.univ \ I, w i j) :
    ∀ ν : Fin r → ℝ,
      |∑ i, ν i * z i| ≤ ∑ i, ∑ j ∈ Finset.univ.filter (fun j => i < j),
        w i j * |ν i - ν j| := by
  intro ν
  have h := core z w hz hsym hnonneg hcut r ν
    (by have := Finset.card_image_le (s := (Finset.univ : Finset (Fin r))) (f := ν); simp at this; omega)
  have h2 := double_sum_eq (fun i j => w i j * |ν i - ν j|)
    (fun i j => by
      by_cases hij : i = j
      · subst hij; simp
      · rw [hsym i j hij, abs_sub_comm])
    (fun i => by simp)
  linarith
end MultiwayGap2325.Main
end

theorem solution : type_of% @MultiwayGap2325.Main.chk_cut_condition := @MultiwayGap2325.Main.chk_cut_condition
