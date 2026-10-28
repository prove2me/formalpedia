-- Prove2me | solution 1 for MultiStoreAssort.SQR.lemmaB4_quasiconvex
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-24T13:41:01.970681+00:00
-- url     : https://prove2.me/submissions/4d3d2ca2-2ea1-4045-8cba-1508ac901b32

import Mathlib
import Definitions.Def_MultiStoreAssort_SQR_Model

namespace SQR2B4

/-- The sign-change claim in the proof of Lemma B.4: if every negative coefficient sits at a
smaller `d` than every positive one, then `∑ lᵢ/(dᵢ+y) ≤ 0` implies `∑ lᵢ/(dᵢ+x) ≤ 0` for `x < y`. -/
theorem claim {m : ℕ} (l d : Fin m → ℝ) (hd : ∀ i, 0 < d i)
    (hsep : ∀ i j, l i < 0 → 0 < l j → d i ≤ d j) (x y : ℝ) (hx : 0 ≤ x) (hxy : x < y)
    (hy : ∑ i, l i / (d i + y) ≤ 0) : ∑ i, l i / (d i + x) ≤ 0 := by
  classical
  by_cases hneg : ∃ i, l i < 0
  · have hne : (Finset.univ.filter (fun i => l i < 0)).Nonempty := by
      obtain ⟨i, hi⟩ := hneg; exact ⟨i, by simp [hi]⟩
    set D := (Finset.univ.filter (fun i => l i < 0)).sup' hne d
    have hDge : ∀ i, l i < 0 → d i ≤ D := fun i hi =>
      Finset.le_sup' d (by simp [hi])
    have hDle : ∀ j, 0 < l j → D ≤ d j := by
      intro j hj
      apply Finset.sup'_le
      intro i hi
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi
      exact hsep i j hi hj
    have hDpos : 0 < D := by
      obtain ⟨i, hi⟩ := hne
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi
      exact lt_of_lt_of_le (hd i) (hDge i hi)
    set ρ := (D + y) / (D + x)
    have hρ : 0 < ρ := div_pos (by linarith) (by linarith)
    have hterm : ∀ i, l i / (d i + x) ≤ ρ * (l i / (d i + y)) := by
      intro i
      have hdi := hd i
      have hsign : l i * (D - d i) ≤ 0 := by
        rcases lt_trichotomy (l i) 0 with h | h | h
        · have := hDge i h; nlinarith
        · rw [h]; simp
        · have := hDle i h; nlinarith
      have hid : l i / (d i + x) - ρ * (l i / (d i + y)) =
          l i * (D - d i) * (y - x) / ((d i + y) * (d i + x) * (D + x)) := by
        have h1 : d i + y ≠ 0 := by linarith
        have h2 : d i + x ≠ 0 := by linarith
        have h3 : D + x ≠ 0 := by linarith
        simp only [ρ]
        field_simp
        ring
      have : l i * (D - d i) * (y - x) / ((d i + y) * (d i + x) * (D + x)) ≤ 0 := by
        apply div_nonpos_of_nonpos_of_nonneg
        · exact mul_nonpos_of_nonpos_of_nonneg hsign (by linarith)
        · have : 0 < d i + y := by linarith
          have : 0 < d i + x := by linarith
          have : 0 < D + x := by linarith
          positivity
      linarith
    calc ∑ i, l i / (d i + x) ≤ ∑ i, ρ * (l i / (d i + y)) := Finset.sum_le_sum (fun i _ => hterm i)
      _ = ρ * ∑ i, l i / (d i + y) := by rw [Finset.mul_sum]
      _ ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hρ.le hy
  · push Not at hneg
    have hnn : ∀ i ∈ Finset.univ, 0 ≤ l i / (d i + y) := fun i _ =>
      div_nonneg (hneg i) (by linarith [hd i])
    have hz := (Finset.sum_eq_zero_iff_of_nonneg hnn).mp (le_antisymm hy (Finset.sum_nonneg hnn))
    apply le_of_eq
    apply Finset.sum_eq_zero
    intro i _
    have h1 := hz i (Finset.mem_univ _)
    have hdy : d i + y ≠ 0 := by linarith [hd i]
    have : l i = 0 := by
      rcases div_eq_zero_iff.mp h1 with h | h
      · exact h
      · exact absurd h hdy
    rw [this, zero_div]

end SQR2B4

open MultiStoreAssort.SQR in
theorem solution {m : ℕ} (a b d : Fin m → ℝ) (ha : ∀ i, 0 < a i) (hb : ∀ i, 0 < b i)
    (hab : Antitone (fun i => a i / b i)) (hd0 : ∀ i, 0 < d i) (hd : Monotone d) :
    QuasiconvexOn ℝ (Set.Ici (0 : ℝ)) (fun x => ∑ i, (a i + b i * x) / (d i + x)) := by
  set f : ℝ → ℝ := fun x => ∑ i, (a i + b i * x) / (d i + x) with hf
  set t : Fin m → ℝ := fun i => b i * d i - a i
  -- f y - f x = (y - x) ∑ tᵢ / ((dᵢ + x)(dᵢ + y))
  have hdiff : ∀ x y, 0 ≤ x → 0 ≤ y →
      f y - f x = (y - x) * ∑ i, t i / (d i + y) / (d i + x) := by
    intro x y hx hy
    simp only [hf, t]
    rw [← Finset.sum_sub_distrib, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    have h1 : d i + x ≠ 0 := by linarith [hd0 i]
    have h2 : d i + y ≠ 0 := by linarith [hd0 i]
    field_simp
    ring
  have hsep : ∀ z, 0 ≤ z → ∀ i j, t i / (d i + z) < 0 → 0 < t j / (d j + z) → d i ≤ d j := by
    intro z hz i j hi hj
    have hzi : 0 < d i + z := by linarith [hd0 i]
    have hzj : 0 < d j + z := by linarith [hd0 j]
    have hti : t i < 0 := by
      by_contra h; push Not at h; exact absurd hi (not_lt.mpr (div_nonneg h hzi.le))
    have htj : 0 < t j := by
      by_contra h; push Not at h; exact absurd hj (not_lt.mpr (div_nonpos_of_nonpos_of_nonneg h hzj.le))
    by_contra hlt
    push Not at hlt
    have hji : j ≤ i := by
      by_contra h; push Not at h; exact absurd (hd h.le) (not_le.mpr hlt)
    have hρ := hab hji
    simp only at hρ
    have hbi := hb i
    have hbj := hb j
    simp only [t] at hti htj
    have e1 : d i < a i / b i := by rw [lt_div_iff₀ hbi]; linarith
    have e2 : a j / b j < d j := by rw [div_lt_iff₀ hbj]; linarith
    linarith
  -- core: x < z < y
  have core : ∀ x z y, 0 ≤ x → x < z → z < y → f z ≤ max (f x) (f y) := by
    intro x z y hx hxz hzy
    have hz : 0 ≤ z := by linarith
    have hy0 : 0 ≤ y := by linarith
    by_contra hcon
    push Not at hcon
    obtain ⟨h1, h2⟩ := max_lt_iff.mp hcon
    have e1 := hdiff x z hx hz
    have e2 := hdiff z y hz hy0
    set l : Fin m → ℝ := fun i => t i / (d i + z)
    have s1 : 0 < ∑ i, l i / (d i + x) := by
      have : 0 < (z - x) * ∑ i, t i / (d i + z) / (d i + x) := by linarith
      exact pos_of_mul_pos_right this (by linarith)
    have s2 : ∑ i, l i / (d i + y) < 0 := by
      have hc : ∑ i, l i / (d i + y) = ∑ i, t i / (d i + y) / (d i + z) := by
        apply Finset.sum_congr rfl; intro i _; simp only [l]; rw [div_div, div_div, mul_comm]
      rw [hc]
      have : (y - z) * ∑ i, t i / (d i + y) / (d i + z) < 0 := by linarith
      exact neg_of_mul_neg_right this (by linarith)
    have := SQR2B4.claim l d hd0 (hsep z hz) x y hx (by linarith) s2.le
    linarith
  rw [quasiconvexOn_iff_le_max]
  refine ⟨convex_Ici 0, ?_⟩
  intro x hx y hy p q hp hq hpq
  simp only [Set.mem_Ici] at hx hy
  simp only [smul_eq_mul]
  set z := p * x + q * y
  have hq' : q = 1 - p := by linarith
  rcases lt_trichotomy x y with hxy | hxy | hxy
  · have hz1 : x ≤ z := by simp only [z, hq']; nlinarith
    have hz2 : z ≤ y := by simp only [z, hq']; nlinarith
    rcases hz1.lt_or_eq with h1 | h1
    · rcases hz2.lt_or_eq with h2 | h2
      · exact core x z y hx h1 h2
      · rw [h2]; exact le_max_right _ _
    · rw [← h1]; exact le_max_left _ _
  · have : z = x := by simp only [z, ← hxy]; rw [← add_mul, hpq, one_mul]
    rw [this]; exact le_max_left _ _
  · have hz1 : y ≤ z := by simp only [z, hq']; nlinarith
    have hz2 : z ≤ x := by simp only [z, hq']; nlinarith
    rcases hz1.lt_or_eq with h1 | h1
    · rcases hz2.lt_or_eq with h2 | h2
      · rw [max_comm]; exact core y z x hy h1 h2
      · rw [h2]; exact le_max_left _ _
    · rw [← h1]; exact le_max_right _ _
