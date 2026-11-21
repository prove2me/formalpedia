-- Prove2me | solution 1 for MomentSearch.rakhmanov_grid_kernel_sum
-- status  : ACCEPTED   (prove)
-- author  : @nmegow
-- created : 2026-11-20T23:04:18.415793+00:00
-- url     : https://prove2.me/submissions/738ca785-49ab-4bc9-8bbe-0ab418aa9cc5

import Mathlib

open scoped BigOperators

private noncomputable def radialKernel (R : ℝ) (i : ℕ) : ℝ :=
  1 / (max 1 (i : ℝ) * max 1 ((i : ℝ) / R))

private lemma radialKernel_sum (R : ℝ) (hR : 2 ≤ R) (s : Finset ℕ) :
    (∑ i ∈ s, radialKernel R i) ≤ 8 * Real.logb 2 R := by
  let L := ⌊R⌋₊
  let K := s.sup id + 1
  have hR0 : 0 < R := by linarith
  have hL : 2 ≤ L := (Nat.le_floor_iff' (by decide : (2 : ℕ) ≠ 0)).2 (by exact_mod_cast hR)
  have hL0 : (0 : ℝ) < (L : ℝ) := by exact_mod_cast (show 0 < L by omega)
  have hLR : (L : ℝ) ≤ R := Nat.floor_le hR0.le
  have hRL : R ≤ 2 * (L : ℝ) := by
    have h := Nat.lt_floor_add_one R
    change R < (L : ℝ) + 1 at h
    have h' : (2 : ℝ) ≤ (L : ℝ) := by exact_mod_cast hL
    linarith
  have hsub : s ⊆ Finset.range (L + K) := by
    intro i hi
    have h := Finset.le_sup (f := id) hi
    change i ≤ s.sup id at h
    exact Finset.mem_range.mpr (by dsimp [K]; omega)
  have hhead (i : ℕ) : radialKernel R i ≤ 2 * ((i : ℝ) + 1)⁻¹ := by
    have hmax : (i : ℝ) + 1 ≤ 2 * max 1 (i : ℝ) := by
      linarith [le_max_left (1 : ℝ) (i : ℝ), le_max_right (1 : ℝ) (i : ℝ)]
    have hd : (i : ℝ) + 1 ≤ 2 * (max 1 (i : ℝ) * max 1 ((i : ℝ) / R)) := by
      have h := mul_le_mul_of_nonneg_left (le_max_left (1 : ℝ) ((i : ℝ) / R))
        (show 0 ≤ max 1 (i : ℝ) by positivity)
      rw [mul_one] at h
      linarith
    unfold radialKernel
    rw [← div_eq_mul_inv]
    apply (div_le_div_iff₀ (by positivity) (by positivity)).2
    simpa using hd
  have htail (i : ℕ) (hi : L ≤ i) :
      radialKernel R i ≤ 2 * R * ((i : ℝ)⁻¹ - ((i : ℝ) + 1)⁻¹) := by
    have hi1 : (1 : ℝ) ≤ (i : ℝ) := by exact_mod_cast (show 1 ≤ i by omega)
    have hi0 : (0 : ℝ) < (i : ℝ) := by linarith
    calc
      radialKernel R i ≤ 1 / ((i : ℝ) * ((i : ℝ) / R)) := by
        unfold radialKernel
        apply one_div_le_one_div_of_le (by positivity)
        exact mul_le_mul (le_max_right _ _) (le_max_right _ _) (by positivity) (by positivity)
      _ = R / (i : ℝ)^2 := by field_simp
      _ ≤ 2 * R * ((i : ℝ)⁻¹ - ((i : ℝ) + 1)⁻¹) := by
        have hi2 : (i : ℝ) + 1 ≤ 2 * (i : ℝ) := by linarith
        have haux : 1 / (i : ℝ)^2 ≤ 2 / ((i : ℝ) * ((i : ℝ) + 1)) := by
          apply (div_le_div_iff₀ (by positivity) (by positivity)).2
          simpa only [one_mul, pow_two, mul_left_comm] using
            mul_le_mul_of_nonneg_left hi2 hi0.le
        have heq : 2 / ((i : ℝ) * ((i : ℝ) + 1)) =
            2 * ((i : ℝ)⁻¹ - ((i : ℝ) + 1)⁻¹) := by
          field_simp
          ring
        rw [heq] at haux
        calc
          R / (i : ℝ)^2 = R * (1 / (i : ℝ)^2) := by ring
          _ ≤ R * (2 * ((i : ℝ)⁻¹ - ((i : ℝ) + 1)⁻¹)) :=
            mul_le_mul_of_nonneg_left haux hR0.le
          _ = _ := by ring
  have hharm : (∑ i ∈ Finset.range L, ((i : ℝ) + 1)⁻¹) ≤ 1 + Real.log R := by
    calc
      _ = (harmonic L : ℝ) := by
        simp [harmonic, Rat.cast_sum, Rat.cast_inv]
      _ ≤ 1 + Real.log (L : ℝ) := harmonic_le_one_add_log L
      _ ≤ _ := add_le_add_right (Real.log_le_log hL0 hLR) 1
  have htailSum : (∑ i ∈ Finset.range K, radialKernel R (L + i)) ≤ 4 := by
    calc
      _ ≤ ∑ i ∈ Finset.range K,
          2 * R * (((L + i : ℕ) : ℝ)⁻¹ - (((L + i : ℕ) : ℝ) + 1)⁻¹) := by
        exact Finset.sum_le_sum (fun i _ => htail (L + i) (by omega))
      _ = 2 * R * ((L : ℝ)⁻¹ - (((L + K : ℕ) : ℝ))⁻¹) := by
        rw [← Finset.mul_sum]
        congr 1
        simpa only [Nat.cast_add, Nat.cast_one, Nat.cast_zero, add_assoc, add_zero] using
          (Finset.sum_range_sub' (fun i : ℕ => ((L : ℝ) + (i : ℝ))⁻¹) K)
      _ ≤ 2 * R * (L : ℝ)⁻¹ := mul_le_mul_of_nonneg_left (sub_le_self _ (by positivity)) (by positivity)
      _ ≤ 4 := by
        rw [← div_eq_mul_inv, div_le_iff₀ hL0]
        linarith
  have hlog1 : 1 ≤ Real.logb 2 R := by
    rw [← Real.logb_self_eq_one (by norm_num : (1 : ℝ) < 2)]
    exact Real.logb_le_logb_of_le (by norm_num) (by norm_num) hR
  have hlog2 : Real.log R ≤ Real.logb 2 R := by
    rw [Real.logb, le_div_iff₀ (Real.log_pos (by norm_num))]
    have hlogTwo := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
    have hlogR : 0 ≤ Real.log R := Real.log_nonneg (by linarith)
    nlinarith
  calc
    _ ≤ ∑ i ∈ Finset.range (L + K), radialKernel R i :=
      Finset.sum_le_sum_of_subset_of_nonneg hsub (fun i _ _ => by unfold radialKernel; positivity)
    _ = (∑ i ∈ Finset.range L, radialKernel R i) +
        ∑ i ∈ Finset.range K, radialKernel R (L + i) := Finset.sum_range_add _ _ _
    _ ≤ 2 * (1 + Real.log R) + 4 := by
      apply add_le_add _ htailSum
      calc
        _ ≤ ∑ i ∈ Finset.range L, 2 * ((i : ℝ) + 1)⁻¹ :=
          Finset.sum_le_sum (fun i _ => hhead i)
        _ = 2 * (∑ i ∈ Finset.range L, ((i : ℝ) + 1)⁻¹) := by rw [Finset.mul_sum]
        _ ≤ _ := mul_le_mul_of_nonneg_left hharm (by norm_num)
    _ ≤ _ := by linarith

private lemma sum_via_ranks (R : ℝ) (hR : 2 ≤ R) (s : Finset ℕ) (rank : ℕ → ℕ)
    (hinj : Set.InjOn rank ↑s) (f : ℕ → ℝ)
    (hbound : ∀ i ∈ s, f i ≤ 3 * radialKernel R (rank i)) :
    (∑ i ∈ s, f i) ≤ 24 * Real.logb 2 R := by
  calc
    _ ≤ ∑ i ∈ s, 3 * radialKernel R (rank i) := Finset.sum_le_sum hbound
    _ = 3 * ∑ i ∈ s.image rank, radialKernel R i := by
      rw [Finset.mul_sum, Finset.sum_image hinj]
    _ ≤ _ := by
      have h := radialKernel_sum R hR (s.image rank)
      linarith

theorem solution :
    ∃ D : ℝ, 0 < D ∧
      ∀ N : ℕ, 0 < N → ∀ M x y : ℝ, 0 < M → M ≤ (N : ℝ) / 2 → |x - y| ≤ 2 / M →
        (∑ j ∈ Finset.Icc 1 N,
          1 / (max 1 ((N : ℝ) * |(-1 + (2 * (j : ℝ) - 1) / (N : ℝ)) - x|) *
            max 1 (M * |(-1 + (2 * (j : ℝ) - 1) / (N : ℝ)) - y|))) ≤
          D * Real.logb 2 ((N : ℝ) / M) := by
  refine ⟨48, by norm_num, ?_⟩
  intro N hN M x y hM hMN hxy
  classical
  have hNr : 0 < (N : ℝ) := by exact_mod_cast hN
  let R := (N : ℝ) / M
  have hR : 2 ≤ R := (le_div_iff₀ hM).2 (by linarith)
  have hR0 : 0 < R := by linarith
  let ζ (j : ℕ) : ℝ := -1 + (2 * (j : ℝ) - 1) / (N : ℝ)
  let f (j : ℕ) : ℝ :=
    1 / (max 1 ((N : ℝ) * |ζ j - x|) * max 1 (M * |ζ j - y|))
  let t : ℝ := ((N : ℝ) * (x + 1) + 1) / 2
  let m : ℤ := ⌊t⌋
  have hfloor : (m : ℝ) ≤ t := Int.floor_le t
  have hceil : t < (m : ℝ) + 1 := Int.lt_floor_add_one t
  let s : Finset ℕ := Finset.Icc 1 N
  let left := s.filter (fun j : ℕ => (j : ℤ) ≤ m)
  let right := s.filter (fun j : ℕ => ¬ (j : ℤ) ≤ m)
  let rankL (j : ℕ) : ℕ := (m - (j : ℤ)).toNat
  let rankR (j : ℕ) : ℕ := ((j : ℤ) - (m + 1)).toNat
  have hL (j : ℕ) (hj : j ∈ left) : (rankL j : ℤ) = m - (j : ℤ) :=
    Int.toNat_of_nonneg (sub_nonneg.mpr (Finset.mem_filter.mp hj).2)
  have hR' (j : ℕ) (hj : j ∈ right) : (rankR j : ℤ) = (j : ℤ) - (m + 1) :=
    Int.toNat_of_nonneg (by have h := (Finset.mem_filter.mp hj).2; omega)
  have hdist (j : ℕ) : (N : ℝ) * |ζ j - x| = 2 * |(j : ℝ) - t| := by
    have heq : (N : ℝ) * (ζ j - x) = 2 * ((j : ℝ) - t) := by
      dsimp [ζ, t]
      field_simp
      ring
    have h := congrArg (fun z : ℝ => |z|) heq
    simpa only [abs_mul, abs_of_pos hNr, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)] using h
  have bound (j i : ℕ) (hi : (i : ℝ) ≤ (N : ℝ) * |ζ j - x|) :
      f j ≤ 3 * radialKernel R i := by
    have hiM : (i : ℝ) / R ≤ M * |ζ j - x| := by
      apply (div_le_iff₀ hR0).2
      have hscale : M * |ζ j - x| * R = (N : ℝ) * |ζ j - x| := by
        dsimp [R]
        field_simp
      rwa [hscale]
    have hshift : M * |ζ j - x| ≤ M * |ζ j - y| + 2 := by
      have htriangle : |ζ j - x| ≤ |ζ j - y| + |x - y| := by
        simpa only [abs_sub_comm y x] using (abs_sub_le (ζ j) y x)
      have hmul := mul_le_mul_of_nonneg_left htriangle hM.le
      rw [mul_add] at hmul
      have hmove := (le_div_iff₀ hM).1 hxy
      linarith
    have hmax : max 1 ((i : ℝ) / R) ≤ 3 * max 1 (M * |ζ j - y|) := by
      have ha := le_max_left (1 : ℝ) (M * |ζ j - y|)
      have hb := le_max_right (1 : ℝ) (M * |ζ j - y|)
      exact max_le (by linarith) (by linarith)
    have hmul : max 1 (i : ℝ) * max 1 ((i : ℝ) / R) ≤
        3 * (max 1 ((N : ℝ) * |ζ j - x|) * max 1 (M * |ζ j - y|)) := by
      calc
        _ ≤ max 1 ((N : ℝ) * |ζ j - x|) * (3 * max 1 (M * |ζ j - y|)) :=
          mul_le_mul (max_le_max le_rfl hi) hmax (by positivity) (by positivity)
        _ = _ := by ring
    unfold f radialKernel
    rw [← mul_div_assoc, mul_one]
    apply (div_le_div_iff₀ (by positivity) (by positivity)).2
    simpa only [one_mul] using hmul
  have hleft : ∑ j ∈ left, f j ≤ 24 * Real.logb 2 R := by
    apply sum_via_ranks R hR left rankL
    · intro i hi j hj hij
      have hi' := hL i hi
      have hj' := hL j hj
      omega
    · intro j hj
      apply bound
      rw [hdist]
      have heq : (rankL j : ℝ) = (m : ℝ) - (j : ℝ) := by exact_mod_cast hL j hj
      have hjm : (j : ℝ) ≤ (m : ℝ) := by
        exact_mod_cast (Finset.mem_filter.mp hj).2
      rw [heq, abs_of_nonpos (sub_nonpos.mpr (hjm.trans hfloor))]
      linarith
  have hright : ∑ j ∈ right, f j ≤ 24 * Real.logb 2 R := by
    apply sum_via_ranks R hR right rankR
    · intro i hi j hj hij
      have hi' := hR' i hi
      have hj' := hR' j hj
      omega
    · intro j hj
      apply bound
      rw [hdist]
      have heq : (rankR j : ℝ) = (j : ℝ) - ((m : ℝ) + 1) := by exact_mod_cast hR' j hj
      have hjm : (m : ℝ) + 1 ≤ (j : ℝ) := by
        have h : m + 1 ≤ (j : ℤ) := by
          have h := (Finset.mem_filter.mp hj).2
          omega
        exact_mod_cast h
      rw [heq, abs_of_nonneg (sub_nonneg.mpr (hceil.le.trans hjm))]
      linarith
  change (∑ j ∈ s, f j) ≤ 48 * Real.logb 2 R
  rw [← Finset.sum_filter_add_sum_filter_not s (fun j : ℕ => (j : ℤ) ≤ m) f]
  exact (add_le_add hleft hright).trans_eq (by ring)
