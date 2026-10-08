-- Prove2me | solution 1 for HardyFiveAxioms.exponent_isNat_of_rpow_isNat
-- status  : ACCEPTED   (prove)
-- author  : @savarin
-- created : 2026-10-06T19:37:50.580773+00:00
-- url     : https://prove2.me/submissions/e4f23995-e94d-487e-88cf-6f64c1fe171b

import Mathlib

noncomputable def D : ℕ → ℝ → ℝ → ℝ
  | 0, β, x => x ^ β
  | k + 1, β, x => D k β (x + 1) - D k β x

lemma D_deriv (k : ℕ) : ∀ (β x : ℝ), 0 < x → HasDerivAt (D k β) (β * D k (β - 1) x) x := by
  induction k with
  | zero =>
    intro β x hx
    have : (fun y => D 0 β y) = fun y => y ^ β := rfl
    simp only [D]
    exact Real.hasDerivAt_rpow_const (Or.inl hx.ne')
  | succ k ih =>
    intro β x hx
    have h1 := (ih β (x + 1) (by linarith)).comp_add_const x 1
    have h2 := ih β x hx
    have : (fun y => D (k+1) β y) = fun y => D k β (y + 1) - D k β y := rfl
    show HasDerivAt (fun y => D (k+1) β y) _ x
    rw [this]
    refine (h1.sub h2).congr_deriv ?_
    rw [show D (k+1) (β-1) x = D k (β-1) (x+1) - D k (β-1) x from rfl]; ring

lemma D_mvt (k : ℕ) : ∀ (β x : ℝ), 0 < x → ∃ ξ, x ≤ ξ ∧ ξ ≤ x + k ∧
    D k β x = (∏ i ∈ Finset.range k, (β - i)) * ξ ^ (β - k) := by
  induction k with
  | zero => intro β x hx; exact ⟨x, le_rfl, by simp, by simp [D]⟩
  | succ k ih =>
    intro β x hx
    obtain ⟨η, hη, hη2⟩ : ∃ η ∈ Set.Ioo x (x + 1),
        β * D k (β - 1) η = (D k β (x + 1) - D k β x) / ((x + 1) - x) := by
      apply exists_hasDerivAt_eq_slope (D k β) (fun y => β * D k (β - 1) y) (by linarith)
      · intro y hy
        exact (D_deriv k β y (by linarith [hy.1])).continuousAt.continuousWithinAt
      · intro y hy
        exact D_deriv k β y (by linarith [hy.1])
    obtain ⟨ξ, h1, h2, h3⟩ := ih (β - 1) η (by linarith [hη.1])
    refine ⟨ξ, by linarith [hη.1], by push_cast; linarith [hη.2], ?_⟩
    have e : D (k+1) β x = D k β (x + 1) - D k β x := rfl
    rw [e, show (D k β (x + 1) - D k β x) = β * D k (β - 1) η by rw [hη2]; ring, h3,
      Finset.prod_range_succ']
    have : ∏ i ∈ Finset.range k, (β - ((i + 1 : ℕ) : ℝ)) = ∏ i ∈ Finset.range k, (β - 1 - i) := by
      apply Finset.prod_congr rfl; intro i _; push_cast; ring
    rw [this, show β - 1 - (k : ℝ) = β - ((k + 1 : ℕ) : ℝ) by push_cast; ring]
    simp; ring

lemma D_int (α : ℝ) (hint : ∀ n : ℕ, 1 ≤ n → ∃ m : ℕ, (n : ℝ) ^ α = m) (k : ℕ) :
    ∀ n : ℕ, 1 ≤ n → ∃ z : ℤ, D k α n = z := by
  induction k with
  | zero =>
    intro n hn; obtain ⟨m, hm⟩ := hint n hn; exact ⟨m, by simp [D, hm]⟩
  | succ k ih =>
    intro n hn
    obtain ⟨a, ha⟩ := ih (n + 1) (by omega)
    obtain ⟨b, hb⟩ := ih n hn
    refine ⟨a - b, ?_⟩
    have e : D (k+1) α n = D k α ((n : ℝ) + 1) - D k α n := rfl
    rw [e, hb, show ((n : ℝ) + 1) = ((n + 1 : ℕ) : ℝ) by push_cast; ring, ha]; push_cast; ring

/-- Hardy 2001, Section 8.1: if `α > 0` and `n^α` is a (natural) integer for every positive
integer `n`, then `α` is a positive integer. -/
theorem solution (α : ℝ) (hα : 0 < α)
    (hint : ∀ n : ℕ, 1 ≤ n → ∃ m : ℕ, (n : ℝ) ^ α = m) :
    ∃ r : ℕ, 1 ≤ r ∧ α = r := by
  by_contra hcon
  push Not at hcon
  set k := ⌊α⌋₊ + 1 with hk
  have hneg : α - k < 0 := by
    have := Nat.lt_floor_add_one α; rw [hk]; push_cast; linarith
  set P := ∏ i ∈ Finset.range k, (α - i) with hP
  have hP0 : P ≠ 0 := by
    rw [hP, Finset.prod_ne_zero_iff]
    intro i _ h
    rcases Nat.eq_zero_or_pos i with rfl | hi
    · simp at h; linarith
    · exact hcon i hi (by linarith)
  have hPpos : 0 < |P| := abs_pos.mpr hP0
  have ht : Filter.Tendsto (fun n : ℕ => ((n : ℝ)) ^ (-(k - α))) Filter.atTop (nhds 0) :=
    (tendsto_rpow_neg_atTop (by linarith)).comp tendsto_natCast_atTop_atTop
  have hev := ht.eventually (gt_mem_nhds (show (0:ℝ) < 1 / |P| by positivity))
  obtain ⟨n, hn1, hn2⟩ := (hev.and (Filter.eventually_ge_atTop 1)).exists
  obtain ⟨z, hz⟩ := D_int α hint k n hn2
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn2
  obtain ⟨ξ, hξ1, _, hξ⟩ := D_mvt k α n hn0
  have hξpos : 0 < ξ := by linarith
  have hle : ξ ^ (α - k) ≤ (n : ℝ) ^ (α - k) :=
    Real.rpow_le_rpow_of_nonpos hn0 hξ1 hneg.le
  have hpos : 0 < ξ ^ (α - k) := Real.rpow_pos_of_pos hξpos _
  simp only [neg_sub] at hn1
  have habs : |(z : ℝ)| < 1 := by
    rw [← hz, hξ, abs_mul, abs_of_pos hpos]
    calc |P| * ξ ^ (α - k) ≤ |P| * (n : ℝ) ^ (α - k) := by gcongr
      _ < |P| * (1 / |P|) := by gcongr
      _ = 1 := by field_simp
  have hz0 : (z : ℝ) ≠ 0 := by
    rw [← hz, hξ]; exact mul_ne_zero hP0 hpos.ne'
  have : |z| < 1 := by exact_mod_cast habs
  rw [Int.abs_lt_one_iff] at this
  exact hz0 (by simp [this])
