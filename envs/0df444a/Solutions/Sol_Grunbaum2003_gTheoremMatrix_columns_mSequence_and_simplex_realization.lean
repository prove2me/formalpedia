-- Prove2me | solution 1 for Grunbaum2003.gTheoremMatrix_columns_mSequence_and_simplex_realization
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-08T02:34:05.020826+00:00
-- url     : https://prove2.me/submissions/7d0a27b5-faa8-43a4-8492-4bf500a6f633

import Definitions.Def_Grunbaum2003_IsDPolytope
import Theorems.Thm_Grunbaum2003_exposed_edge_pair_and_simplex_faceCount_choose
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Definitions.Def_Grunbaum2003_IsSimplicialDPolytope
import Definitions.Def_Grunbaum2003_faceCount
import Definitions.Def_Grunbaum2003_IsMSequence
import Definitions.Def_Grunbaum2003_gTheoremMatrix
import Mathlib.Order.Interval.Finset.Nat

set_option autoImplicit false
open scoped BigOperators

open scoped BigOperators Classical
noncomputable section

namespace Grunbaum2003

theorem exists_simplicial_simplex_with_choose_faceCounts (d : ℕ) :
    ∃ P : Set (Fin d → ℝ),
      IsSimplicialDPolytope P ∧
      ∀ k : ℕ, faceCount P k = Nat.choose (d + 1) (k + 1) :=
  exposed_edge_pair_and_simplex_faceCount_choose.2.2.2 d

end Grunbaum2003

namespace Grunbaum2003

/-- Row `j = 0` of Björner's matrix `M_d` consists of the binomial coefficients
`Nat.choose (d + 1) k` for `0 ≤ k ≤ d`. -/
theorem gTheoremMatrix_zero_row (d : ℕ) (k : Fin (d + 1)) :
    gTheoremMatrix d 0 k.val = (Nat.choose (d + 1) k.val : ℤ) := by
  unfold gTheoremMatrix
  have hk : k.val ≤ d + 1 := Nat.le_of_lt k.isLt
  have hpos : 0 < d + 1 - k.val := Nat.sub_pos_of_lt k.isLt
  have h0 : Nat.choose 0 (d + 1 - k.val) = 0 := Nat.choose_eq_zero_of_lt hpos
  have hsymm : Nat.choose (d + 1) (d + 1 - k.val) = Nat.choose (d + 1) k.val :=
    Nat.choose_symm hk
  simp [h0, hsymm]

/-- Column `k = 0` of `M_d` is `1` at `j = 0` and `0` for `1 ≤ j ≤ d`. -/
theorem gTheoremMatrix_col_zero (d j : ℕ) (hj : j ≤ d) :
    gTheoremMatrix d j 0 = if j = 0 then 1 else 0 := by
  unfold gTheoremMatrix
  by_cases hj0 : j = 0
  · subst hj0
    simp
  · have hjpos : 0 < j := Nat.pos_of_ne_zero hj0
    have h1 : d + 1 - j < d + 1 := Nat.sub_lt (Nat.succ_pos d) hjpos
    have h2 : j < d + 1 := Nat.lt_succ_of_le hj
    have hc1 : Nat.choose (d + 1 - j) (d + 1) = 0 := Nat.choose_eq_zero_of_lt h1
    have hc2 : Nat.choose j (d + 1) = 0 := Nat.choose_eq_zero_of_lt h2
    simp [hj0, hc1, hc2]

/-- Column `k = 1` of `M_d` (for `d ≥ 2` and `j ≤ d / 2`) is `d + 1` at `j = 0`,
`1` at `j = 1`, and `0` for `2 ≤ j ≤ d / 2`. -/
theorem gTheoremMatrix_col_one (d j : ℕ) (hd : 2 ≤ d) (hj : j ≤ d / 2) :
    gTheoremMatrix d j 1 = if j = 0 then (d + 1 : ℤ) else if j = 1 then 1 else 0 := by
  unfold gTheoremMatrix
  have hjd : j < d := by omega
  have hc2 : Nat.choose j d = 0 := Nat.choose_eq_zero_of_lt hjd
  by_cases hj0 : j = 0
  · subst hj0
    simp [hc2]
  · by_cases hj1 : j = 1
    · subst hj1
      simp [hc2]
    · have h1 : d + 1 - j < d := by omega
      have hc1 : Nat.choose (d + 1 - j) d = 0 := Nat.choose_eq_zero_of_lt h1
      simp [hj0, hj1, hc1, hc2]

/-- The sequence `g = (1, 0, 0, ...)` is an `M`-sequence of any length `m`. -/
theorem isMSequence_zero_tail (m : ℕ) :
    IsMSequence m (fun j => if j = 0 then 1 else 0) := by
  refine ⟨by simp, ?_⟩
  intro k hk _
  left
  have hk0 : k ≠ 0 := Nat.ne_of_gt hk
  simp [hk0]

/-- For any `m, n : ℕ`, the sequence `g = (1, n, 0, 0, ...)` is an `M`-sequence of length `m`. -/
theorem isMSequence_one_step (m n : ℕ) :
    IsMSequence m (fun j => if j = 0 then 1 else if j = 1 then n else 0) := by
  refine ⟨by simp, ?_⟩
  intro k hk _
  have hk0 : k ≠ 0 := Nat.ne_of_gt hk
  by_cases hk1 : k = 1
  · subst hk1
    by_cases hn : n = 0
    · left
      simp [hn]
    · right
      refine ⟨1, fun _ => n, Nat.one_pos, le_rfl, Nat.pos_of_ne_zero hn, ?_, ?_, ?_⟩
      · intro r s hr hrs hs
        omega
      · simp [Nat.choose_one_right]
      · simp
  · left
    simp [hk0, hk1]

/-- For `m = 1` (which occurs in dimensions `d = 2` and `d = 3`), `IsMSequence 1 g` holds
if and only if `g 0 = 1`. -/
theorem isMSequence_one_iff (g : ℕ → ℕ) :
    IsMSequence 1 g ↔ g 0 = 1 := by
  constructor
  · exact fun h => h.1
  · intro hg0
    refine ⟨hg0, ?_⟩
    intro k hk1 hk2
    have hk : k = 1 := by omega
    subst hk
    by_cases hg1 : g 1 = 0
    · exact Or.inl hg1
    · right
      refine ⟨1, fun _ => g 1, Nat.one_pos, le_rfl, Nat.pos_of_ne_zero hg1, ?_, ?_, ?_⟩
      · intro r s hr hrs hs
        omega
      · simp [Nat.choose_one_right]
      · simp [hg0]

/-- For any `d : ℕ` and any `g : ℕ → ℕ` with `g 0 = 1`, the `k = 0` column sum of
`g` against `gTheoremMatrix d` is `1`. -/
theorem gTheoremMatrix_sum_col_zero (d : ℕ) (g : ℕ → ℕ) (hg0 : g 0 = 1) :
    (∑ j ∈ Finset.range (d / 2 + 1), (g j : ℤ) * gTheoremMatrix d j 0) = 1 := by
  have hcongr :
      ∀ j ∈ Finset.range (d / 2 + 1),
        (g j : ℤ) * gTheoremMatrix d j 0 = if j = 0 then (g 0 : ℤ) else 0 := by
    intro j hj
    have hjle : j ≤ d := by
      have : j < d / 2 + 1 := Finset.mem_range.mp hj
      omega
    rw [gTheoremMatrix_col_zero d j hjle]
    split_ifs with h
    · subst h; ring
    · ring
  rw [Finset.sum_congr rfl hcongr]
  simp [hg0]

/-- For any `d ≥ 2` and any `g : ℕ → ℕ` with `g 0 = 1`, the `k = 1` column sum of
`g` against `gTheoremMatrix d` is `(d + 1) + g 1`. -/
theorem gTheoremMatrix_sum_col_one (d : ℕ) (hd : 2 ≤ d) (g : ℕ → ℕ) (hg0 : g 0 = 1) :
    (∑ j ∈ Finset.range (d / 2 + 1), (g j : ℤ) * gTheoremMatrix d j 1) =
      (d + 1 : ℤ) + (g 1 : ℤ) := by
  have hcongr :
      ∀ j ∈ Finset.range (d / 2 + 1),
        (g j : ℤ) * gTheoremMatrix d j 1 =
          (if j = 0 then (d + 1 : ℤ) else 0) + (if j = 1 then (g 1 : ℤ) else 0) := by
    intro j hj
    have hjle : j ≤ d / 2 := Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)
    rw [gTheoremMatrix_col_one d j hd hjle]
    by_cases hj0 : j = 0
    · subst hj0
      simp [hg0]
    · by_cases hj1 : j = 1
      · subst hj1
        simp
      · simp [hj0, hj1]
  rw [Finset.sum_congr rfl hcongr, Finset.sum_add_distrib]
  have h0 : (0 : ℕ) ∈ Finset.range (d / 2 + 1) := Finset.mem_range.mpr (Nat.succ_pos _)
  have h1 : (1 : ℕ) ∈ Finset.range (d / 2 + 1) := by
    rw [Finset.mem_range]
    omega
  rw [Finset.sum_ite_eq' (Finset.range (d / 2 + 1)) 0 (fun _ => (d + 1 : ℤ)),
      Finset.sum_ite_eq' (Finset.range (d / 2 + 1)) 1 (fun _ => (g 1 : ℤ))]
  simp [h0, h1]

/-- For the zero-tail `M`-sequence `g = (1, 0, 0, ...)`, the `gTheoremMatrix` transform
equals `Nat.choose (d + 1) k` for every `k : Fin (d + 1)`. -/
theorem gTheoremMatrix_sum_zero_tail (d : ℕ) (k : Fin (d + 1)) :
    (∑ j ∈ Finset.range (d / 2 + 1),
      ((if j = 0 then (1 : ℕ) else 0 : ℕ) : ℤ) * gTheoremMatrix d j k.val) =
      (Nat.choose (d + 1) k.val : ℤ) := by
  have hcongr :
      ∀ j ∈ Finset.range (d / 2 + 1),
        ((if j = 0 then (1 : ℕ) else 0 : ℕ) : ℤ) * gTheoremMatrix d j k.val =
          if j = 0 then gTheoremMatrix d 0 k.val else 0 := by
    intro j _
    split_ifs with h
    · subst h; simp
    · simp
  rw [Finset.sum_congr rfl hcongr,
      Finset.sum_ite_eq' (Finset.range (d / 2 + 1)) 0 (fun _ => gTheoremMatrix d 0 k.val)]
  have h0 : (0 : ℕ) ∈ Finset.range (d / 2 + 1) := Finset.mem_range.mpr (Nat.succ_pos _)
  simp [h0, gTheoremMatrix_zero_row d k]

/-- Every dimension `d : ℕ` admits a simplicial `d`-polytope (the `d`-simplex) whose augmented
`f`-vector equals the `gTheoremMatrix` transform of the `M`-sequence `g = (1, 0, 0, ...)`. -/
theorem exists_simplex_realizing_zero_tail_mSequence (d : ℕ) :
    ∃ (P : Set (Fin d → ℝ)) (g : ℕ → ℕ),
      IsSimplicialDPolytope P ∧
      IsMSequence (d / 2) g ∧
      g 1 = 0 ∧
      (∀ j : Fin d, (faceCount P j.val : ℤ) =
        ∑ i ∈ Finset.range (d / 2 + 1),
          (g i : ℤ) * gTheoremMatrix d i j.succ.val) := by
  obtain ⟨P, hPSimp, hPCount⟩ := exists_simplicial_simplex_with_choose_faceCounts d
  refine ⟨P, fun j => if j = 0 then 1 else 0, hPSimp, isMSequence_zero_tail (d / 2), rfl, ?_⟩
  intro j
  rw [gTheoremMatrix_sum_zero_tail d j.succ]
  exact congrArg (Nat.cast : ℕ → ℤ) (hPCount j.val)

/-- In dimension `d = 2`, the `g`-theorem matrix transform condition for `f : Fin 3 → ℤ` with
`f 0 = 1` is equivalent to `∃ n : ℕ, f 1 = (n : ℤ) + 3 ∧ f 2 = (n : ℤ) + 3`. -/
theorem gTheorem_dim_two_rhs_iff (f : Fin (2 + 1) → ℤ) (hf0 : f 0 = 1) :
    (∃ g : ℕ → ℕ, IsMSequence (2 / 2) g ∧
      ∀ k : Fin (2 + 1),
        f k = ∑ j ∈ Finset.range (2 / 2 + 1),
          (g j : ℤ) * gTheoremMatrix 2 j k.val) ↔
    (∃ n : ℕ, f 1 = (n : ℤ) + 3 ∧ f 2 = (n : ℤ) + 3) := by
  constructor
  · rintro ⟨g, hgM, hfk⟩
    have hg0 : g 0 = 1 := hgM.1
    refine ⟨g 1, ?_, ?_⟩
    · have h1 := hfk 1
      rw [Finset.sum_range_succ, Finset.sum_range_one] at h1
      change f 1 = (g 0 : ℤ) * gTheoremMatrix 2 0 1 + (g 1 : ℤ) * gTheoremMatrix 2 1 1 at h1
      have hm01 : gTheoremMatrix 2 0 1 = 3 := by decide
      have hm11 : gTheoremMatrix 2 1 1 = 1 := by decide
      rw [h1, hg0, hm01, hm11]
      push_cast
      ring
    · have h2 := hfk 2
      rw [Finset.sum_range_succ, Finset.sum_range_one] at h2
      change f 2 = (g 0 : ℤ) * gTheoremMatrix 2 0 2 + (g 1 : ℤ) * gTheoremMatrix 2 1 2 at h2
      have hm02 : gTheoremMatrix 2 0 2 = 3 := by decide
      have hm12 : gTheoremMatrix 2 1 2 = 1 := by decide
      rw [h2, hg0, hm02, hm12]
      push_cast
      ring
  · rintro ⟨n, hf1, hf2⟩
    refine ⟨fun j => if j = 0 then 1 else if j = 1 then n else 0, isMSequence_one_step 1 n, ?_⟩
    intro k
    fin_cases k
    · rw [Finset.sum_range_succ, Finset.sum_range_one]
      have hm00 : gTheoremMatrix 2 0 0 = 1 := by decide
      have hm10 : gTheoremMatrix 2 1 0 = 0 := by decide
      simp [hf0, hm00, hm10]
    · rw [Finset.sum_range_succ, Finset.sum_range_one]
      change f 1 = _
      have hm01 : gTheoremMatrix 2 0 1 = 3 := by decide
      have hm11 : gTheoremMatrix 2 1 1 = 1 := by decide
      simp [hf1, hm01, hm11]
      ring
    · rw [Finset.sum_range_succ, Finset.sum_range_one]
      change f 2 = _
      have hm02 : gTheoremMatrix 2 0 2 = 3 := by decide
      have hm12 : gTheoremMatrix 2 1 2 = 1 := by decide
      simp [hf2, hm02, hm12]
      ring

/-- In dimension `d = 3`, the `g`-theorem matrix transform condition for `f : Fin 4 → ℤ` with
`f 0 = 1` is equivalent to `∃ n : ℕ, f 1 = (n : ℤ) + 4 ∧ f 2 = (n : ℤ) * 3 + 6 ∧ f 3 = (n : ℤ) * 2 + 4`. -/
theorem gTheorem_dim_three_rhs_iff (f : Fin (3 + 1) → ℤ) (hf0 : f 0 = 1) :
    (∃ g : ℕ → ℕ, IsMSequence (3 / 2) g ∧
      ∀ k : Fin (3 + 1),
        f k = ∑ j ∈ Finset.range (3 / 2 + 1),
          (g j : ℤ) * gTheoremMatrix 3 j k.val) ↔
    (∃ n : ℕ, f 1 = (n : ℤ) + 4 ∧ f 2 = (n : ℤ) * 3 + 6 ∧ f 3 = (n : ℤ) * 2 + 4) := by
  constructor
  · rintro ⟨g, hgM, hfk⟩
    have hg0 : g 0 = 1 := hgM.1
    refine ⟨g 1, ?_, ?_, ?_⟩
    · have h1 := hfk 1
      rw [Finset.sum_range_succ, Finset.sum_range_one] at h1
      change f 1 = (g 0 : ℤ) * gTheoremMatrix 3 0 1 + (g 1 : ℤ) * gTheoremMatrix 3 1 1 at h1
      have hm01 : gTheoremMatrix 3 0 1 = 4 := by decide
      have hm11 : gTheoremMatrix 3 1 1 = 1 := by decide
      rw [h1, hg0, hm01, hm11]
      push_cast
      ring
    · have h2 := hfk 2
      rw [Finset.sum_range_succ, Finset.sum_range_one] at h2
      change f 2 = (g 0 : ℤ) * gTheoremMatrix 3 0 2 + (g 1 : ℤ) * gTheoremMatrix 3 1 2 at h2
      have hm02 : gTheoremMatrix 3 0 2 = 6 := by decide
      have hm12 : gTheoremMatrix 3 1 2 = 3 := by decide
      rw [h2, hg0, hm02, hm12]
      push_cast
      ring
    · have h3 := hfk 3
      rw [Finset.sum_range_succ, Finset.sum_range_one] at h3
      change f 3 = (g 0 : ℤ) * gTheoremMatrix 3 0 3 + (g 1 : ℤ) * gTheoremMatrix 3 1 3 at h3
      have hm03 : gTheoremMatrix 3 0 3 = 4 := by decide
      have hm13 : gTheoremMatrix 3 1 3 = 2 := by decide
      rw [h3, hg0, hm03, hm13]
      push_cast
      ring
  · rintro ⟨n, hf1, hf2, hf3⟩
    refine ⟨fun j => if j = 0 then 1 else if j = 1 then n else 0, isMSequence_one_step 1 n, ?_⟩
    intro k
    fin_cases k
    · rw [Finset.sum_range_succ, Finset.sum_range_one]
      have hm00 : gTheoremMatrix 3 0 0 = 1 := by decide
      have hm10 : gTheoremMatrix 3 1 0 = 0 := by decide
      simp [hf0, hm00, hm10]
    · rw [Finset.sum_range_succ, Finset.sum_range_one]
      change f 1 = _
      have hm01 : gTheoremMatrix 3 0 1 = 4 := by decide
      have hm11 : gTheoremMatrix 3 1 1 = 1 := by decide
      simp [hf1, hm01, hm11]
      ring
    · rw [Finset.sum_range_succ, Finset.sum_range_one]
      change f 2 = _
      have hm02 : gTheoremMatrix 3 0 2 = 6 := by decide
      have hm12 : gTheoremMatrix 3 1 2 = 3 := by decide
      simp [hf2, hm02, hm12]
      ring
    · rw [Finset.sum_range_succ, Finset.sum_range_one]
      change f 3 = _
      have hm03 : gTheoremMatrix 3 0 3 = 4 := by decide
      have hm13 : gTheoremMatrix 3 1 3 = 2 := by decide
      simp [hf3, hm03, hm13]
      ring

end Grunbaum2003

namespace Grunbaum2003

theorem gTheoremMatrix_columns_mSequence_and_simplex_realization_proved :
  (∀ (d : ℕ) (k : Fin (d + 1)),
    gTheoremMatrix d 0 k.val = (Nat.choose (d + 1) k.val : ℤ)) ∧
  (∀ (d : ℕ) (g : ℕ → ℕ), g 0 = 1 →
    (∑ j ∈ Finset.range (d / 2 + 1), (g j : ℤ) * gTheoremMatrix d j 0) = 1) ∧
  (∀ (d : ℕ), 2 ≤ d → ∀ (g : ℕ → ℕ), g 0 = 1 →
    (∑ j ∈ Finset.range (d / 2 + 1), (g j : ℤ) * gTheoremMatrix d j 1) =
      (d + 1 : ℤ) + (g 1 : ℤ)) ∧
  (∀ m n : ℕ,
    IsMSequence m (fun j => if j = 0 then 1 else if j = 1 then n else 0)) ∧
  (∀ g : ℕ → ℕ, IsMSequence 1 g ↔ g 0 = 1) ∧
  (∀ d : ℕ,
    ∃ (P : Set (Fin d → ℝ)) (g : ℕ → ℕ),
      IsSimplicialDPolytope P ∧
      IsMSequence (d / 2) g ∧
      g 1 = 0 ∧
      (∀ j : Fin d, (faceCount P j.val : ℤ) =
        ∑ i ∈ Finset.range (d / 2 + 1),
          (g i : ℤ) * gTheoremMatrix d i j.succ.val)) ∧
  (∀ f : Fin (2 + 1) → ℤ, f 0 = 1 →
    ((∃ g : ℕ → ℕ, IsMSequence (2 / 2) g ∧
      ∀ k : Fin (2 + 1),
        f k = ∑ j ∈ Finset.range (2 / 2 + 1),
          (g j : ℤ) * gTheoremMatrix 2 j k.val) ↔
     (∃ n : ℕ, f 1 = (n : ℤ) + 3 ∧ f 2 = (n : ℤ) + 3))) ∧
  (∀ f : Fin (3 + 1) → ℤ, f 0 = 1 →
    ((∃ g : ℕ → ℕ, IsMSequence (3 / 2) g ∧
      ∀ k : Fin (3 + 1),
        f k = ∑ j ∈ Finset.range (3 / 2 + 1),
          (g j : ℤ) * gTheoremMatrix 3 j k.val) ↔
     (∃ n : ℕ, f 1 = (n : ℤ) + 4 ∧ f 2 = (n : ℤ) * 3 + 6 ∧ f 3 = (n : ℤ) * 2 + 4))) :=
  ⟨gTheoremMatrix_zero_row,
   gTheoremMatrix_sum_col_zero,
   gTheoremMatrix_sum_col_one,
   isMSequence_one_step,
   isMSequence_one_iff,
   exists_simplex_realizing_zero_tail_mSequence,
   gTheorem_dim_two_rhs_iff,
   gTheorem_dim_three_rhs_iff⟩

end Grunbaum2003

end

open Grunbaum2003 in
theorem solution :
  (∀ (d : ℕ) (k : Fin (d + 1)),
    gTheoremMatrix d 0 k.val = (Nat.choose (d + 1) k.val : ℤ)) ∧
  (∀ (d : ℕ) (g : ℕ → ℕ), g 0 = 1 →
    (∑ j ∈ Finset.range (d / 2 + 1), (g j : ℤ) * gTheoremMatrix d j 0) = 1) ∧
  (∀ (d : ℕ), 2 ≤ d → ∀ (g : ℕ → ℕ), g 0 = 1 →
    (∑ j ∈ Finset.range (d / 2 + 1), (g j : ℤ) * gTheoremMatrix d j 1) =
      (d + 1 : ℤ) + (g 1 : ℤ)) ∧
  (∀ m n : ℕ,
    IsMSequence m (fun j => if j = 0 then 1 else if j = 1 then n else 0)) ∧
  (∀ g : ℕ → ℕ, IsMSequence 1 g ↔ g 0 = 1) ∧
  (∀ d : ℕ,
    ∃ (P : Set (Fin d → ℝ)) (g : ℕ → ℕ),
      IsSimplicialDPolytope P ∧
      IsMSequence (d / 2) g ∧
      g 1 = 0 ∧
      (∀ j : Fin d, (faceCount P j.val : ℤ) =
        ∑ i ∈ Finset.range (d / 2 + 1),
          (g i : ℤ) * gTheoremMatrix d i j.succ.val)) ∧
  (∀ f : Fin (2 + 1) → ℤ, f 0 = 1 →
    ((∃ g : ℕ → ℕ, IsMSequence (2 / 2) g ∧
      ∀ k : Fin (2 + 1),
        f k = ∑ j ∈ Finset.range (2 / 2 + 1),
          (g j : ℤ) * gTheoremMatrix 2 j k.val) ↔
     (∃ n : ℕ, f 1 = (n : ℤ) + 3 ∧ f 2 = (n : ℤ) + 3))) ∧
  (∀ f : Fin (3 + 1) → ℤ, f 0 = 1 →
    ((∃ g : ℕ → ℕ, IsMSequence (3 / 2) g ∧
      ∀ k : Fin (3 + 1),
        f k = ∑ j ∈ Finset.range (3 / 2 + 1),
          (g j : ℤ) * gTheoremMatrix 3 j k.val) ↔
     (∃ n : ℕ, f 1 = (n : ℤ) + 4 ∧ f 2 = (n : ℤ) * 3 + 6 ∧ f 3 = (n : ℤ) * 2 + 4))) :=
  Grunbaum2003.gTheoremMatrix_columns_mSequence_and_simplex_realization_proved
