-- Prove2me | solution 1 for L1Sparsifiers.Main.lemma_18
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-23T04:34:29.988233+00:00
-- url     : https://prove2.me/submissions/57daf592-7e3e-4eb2-a23a-61b31d23bb87

import Definitions.Def_PSDPolyApprox_expect
import Definitions.Def_PSDPolyApprox_lpNorm
import Definitions.Def_L1Sparsifiers_Main_UniformCube
import Definitions.Def_L1Sparsifiers_Main_SeparatelyConvex
import Theorems.Thm_L1Sparsifiers_Main_lemma_11

open PSDPolyApprox L1Sparsifiers.Main

namespace AuxLemma18

lemma unit_cast_cases (u : ℤˣ) : ((u : ℤ) : ℝ) = 1 ∨ ((u : ℤ) : ℝ) = -1 := by
  rcases Int.units_eq_one_or u with rfl | rfl <;> simp

lemma unit_cast_neg (u : ℤˣ) : (((-u : ℤˣ) : ℤ) : ℝ) = -((u : ℤ) : ℝ) := by
  rcases Int.units_eq_one_or u with rfl | rfl <;> norm_num

lemma sum_units_int {α : Type*} [AddCommMonoid α] (g : ℤˣ → α) :
    ∑ u : ℤˣ, g u = g 1 + g (-1) := by
  have huniv : (Finset.univ : Finset ℤˣ) = {1, -1} := by
    ext u
    simp [Int.units_eq_one_or u]
  rw [huniv, Finset.sum_pair (by decide : (1 : ℤˣ) ≠ -1)]

lemma card_cube (m : ℕ) : Fintype.card (Cube m) = 2 ^ m := by
  have h2 : Fintype.card ℤˣ = 2 := by
    have huniv : (Finset.univ : Finset ℤˣ) = {1, -1} := by
      ext u; simp [Int.units_eq_one_or u]
    change (Finset.univ : Finset ℤˣ).card = 2
    rw [huniv, Finset.card_pair (by decide : (1 : ℤˣ) ≠ -1)]
  simp [Cube, h2]

lemma sum_cube_succ {m : ℕ} (H : Cube (m + 1) → ℝ) :
    ∑ x : Cube (m + 1), H x =
      ∑ y : Cube m, (H (Fin.cons 1 y) + H (Fin.cons (-1) y)) := by
  rw [← (Fin.consEquiv (fun _ : Fin (m + 1) => ℤˣ)).sum_comp]
  rw [Fintype.sum_prod_type_right]
  refine Finset.sum_congr rfl (fun y _ => ?_)
  rw [sum_units_int]
  rfl

noncomputable def T {m : ℕ} (ρ : ℝ) (g : Cube m → ℝ) (τ : Cube m) : ℝ :=
  ((2 : ℝ) ^ m)⁻¹ * ∑ σ : Cube m, (∏ i : Fin m, (1 + ρ * (vertex τ i * vertex σ i))) * g σ

lemma T_zero (ρ : ℝ) (g : Cube 0 → ℝ) (τ : Cube 0) : T ρ g τ = g τ := by
  unfold T
  have huniv : (Finset.univ : Finset (Cube 0)) = {τ} := by
    ext σ
    simp only [Finset.mem_univ, Finset.mem_singleton, true_iff]
    exact Subsingleton.elim σ τ
  rw [huniv]
  simp

lemma T_succ {m : ℕ} (ρ : ℝ) (g : Cube (m + 1) → ℝ) (y : Cube m) :
    T ρ g (Fin.cons 1 y) =
        (1 + ρ) / 2 * T ρ (fun z => g (Fin.cons 1 z)) y +
          (1 - ρ) / 2 * T ρ (fun z => g (Fin.cons (-1) z)) y ∧
      T ρ g (Fin.cons (-1) y) =
        (1 - ρ) / 2 * T ρ (fun z => g (Fin.cons 1 z)) y +
          (1 + ρ) / 2 * T ρ (fun z => g (Fin.cons (-1) z)) y := by
  constructor
  · unfold T
    rw [sum_cube_succ]
    have h1 : ∀ z : Cube m,
        (∏ i : Fin (m + 1), (1 + ρ * (vertex (Fin.cons 1 y) i * vertex (Fin.cons 1 z) i))) *
            g (Fin.cons 1 z) +
          (∏ i : Fin (m + 1), (1 + ρ * (vertex (Fin.cons 1 y) i * vertex (Fin.cons (-1) z) i))) *
            g (Fin.cons (-1) z) =
        (1 + ρ) * ((∏ i : Fin m, (1 + ρ * (vertex y i * vertex z i))) * g (Fin.cons 1 z)) +
          (1 - ρ) * ((∏ i : Fin m, (1 + ρ * (vertex y i * vertex z i))) * g (Fin.cons (-1) z)) := by
      intro z
      rw [Fin.prod_univ_succ, Fin.prod_univ_succ]
      simp only [vertex, Fin.cons_zero, Fin.cons_succ, Units.val_one, Int.cast_one,
        Units.val_neg, Int.cast_neg]
      ring
    simp_rw [h1, Finset.sum_add_distrib, ← Finset.mul_sum]
    rw [pow_succ]
    ring
  · unfold T
    rw [sum_cube_succ]
    have h2 : ∀ z : Cube m,
        (∏ i : Fin (m + 1), (1 + ρ * (vertex (Fin.cons (-1) y) i * vertex (Fin.cons 1 z) i))) *
            g (Fin.cons 1 z) +
          (∏ i : Fin (m + 1), (1 + ρ * (vertex (Fin.cons (-1) y) i * vertex (Fin.cons (-1) z) i))) *
            g (Fin.cons (-1) z) =
        (1 - ρ) * ((∏ i : Fin m, (1 + ρ * (vertex y i * vertex z i))) * g (Fin.cons 1 z)) +
          (1 + ρ) * ((∏ i : Fin m, (1 + ρ * (vertex y i * vertex z i))) * g (Fin.cons (-1) z)) := by
      intro z
      rw [Fin.prod_univ_succ, Fin.prod_univ_succ]
      simp only [vertex, Fin.cons_zero, Fin.cons_succ, Units.val_one, Int.cast_one,
        Units.val_neg, Int.cast_neg]
      ring
    simp_rw [h2, Finset.sum_add_distrib, ← Finset.mul_sum]
    rw [pow_succ]
    ring

/-! ### 1D two-point Bonami inequality for `(p, 2)` -/

lemma one_plus_c_x_sq_le {c : ℝ} (hc0 : 0 < c) (hc1 : c < 1) {x : ℝ}
    (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    (1 + c * x ^ 2) ^ ((1 + c) / 2) ≤ ((1 + x) ^ (1 + c) + (1 - x) ^ (1 + c)) / 2 := by
  set p : ℝ := 1 + c
  have hp1 : 1 < p := by linarith
  have hp2 : p < 2 := by linarith
  have hp0 : 0 < p := by linarith
  let d0 : ℝ → ℝ := fun t => ((1 + t) ^ p + (1 - t) ^ p) / 2 - (1 + c * t ^ 2) ^ (p / 2)
  let d1 : ℝ → ℝ := fun t =>
    p / 2 * ((1 + t) ^ (p - 1) - (1 - t) ^ (p - 1)) - p * c * t * (1 + c * t ^ 2) ^ (p / 2 - 1)
  let d2 : ℝ → ℝ := fun t =>
    p * c / 2 * ((1 + t) ^ (p - 2) + (1 - t) ^ (p - 2)) -
      p * c * (1 + c * t ^ 2) ^ (p / 2 - 2) * (1 + c ^ 2 * t ^ 2)
  have hd_quad : ∀ t : ℝ, HasDerivAt (fun s => 1 + c * s ^ 2) (2 * c * t) t := by
    intro t
    have hp := (hasDerivAt_pow 2 t).const_mul c
    have heq : c * (((2 : ℕ) : ℝ) * t ^ (2 - 1)) = 2 * c * t := by norm_num; ring
    rw [heq] at hp
    have hadd := (hasDerivAt_const t (1 : ℝ)).add hp
    have heq2 : (0 : ℝ) + 2 * c * t = 2 * c * t := zero_add _
    rwa [heq2] at hadd
  have hd0_deriv : ∀ t < (1 : ℝ), -1 < t → HasDerivAt d0 (d1 t) t := by
    intro t ht1 htm1
    have h1p : 0 < 1 + t := by linarith
    have h1m : 0 < 1 - t := by linarith
    have h1c : 0 < 1 + c * t ^ 2 := by positivity
    have hd_a : HasDerivAt (fun s => (1 + s) ^ p) (p * (1 + t) ^ (p - 1)) t := by
      have h2 := ((hasDerivAt_const t (1 : ℝ)).add (hasDerivAt_id t)).rpow_const
        (p := p) (Or.inl h1p.ne')
      change HasDerivAt (fun s => (1 + s) ^ p) ((0 + 1) * p * (1 + t) ^ (p - 1)) t at h2
      have heq : (0 + 1) * p * (1 + t) ^ (p - 1) = p * (1 + t) ^ (p - 1) := by ring
      rwa [heq] at h2
    have hd_b : HasDerivAt (fun s => (1 - s) ^ p) (-p * (1 - t) ^ (p - 1)) t := by
      have h2 := ((hasDerivAt_const t (1 : ℝ)).sub (hasDerivAt_id t)).rpow_const
        (p := p) (Or.inl h1m.ne')
      change HasDerivAt (fun s => (1 - s) ^ p) ((0 - 1) * p * (1 - t) ^ (p - 1)) t at h2
      have heq : (0 - 1) * p * (1 - t) ^ (p - 1) = -p * (1 - t) ^ (p - 1) := by ring
      rwa [heq] at h2
    have hd_c : HasDerivAt (fun s => (1 + c * s ^ 2) ^ (p / 2))
        (p * c * t * (1 + c * t ^ 2) ^ (p / 2 - 1)) t := by
      have h2 := (hd_quad t).rpow_const (p := p / 2) (Or.inl h1c.ne')
      have heq : 2 * c * t * (p / 2) * (1 + c * t ^ 2) ^ (p / 2 - 1) =
          p * c * t * (1 + c * t ^ 2) ^ (p / 2 - 1) := by ring
      rwa [heq] at h2
    have hall : HasDerivAt d0
        ((p * (1 + t) ^ (p - 1) + -p * (1 - t) ^ (p - 1)) / 2 -
          p * c * t * (1 + c * t ^ 2) ^ (p / 2 - 1)) t :=
      ((hd_a.add hd_b).div_const 2).sub hd_c
    have heq : (p * (1 + t) ^ (p - 1) + -p * (1 - t) ^ (p - 1)) / 2 -
        p * c * t * (1 + c * t ^ 2) ^ (p / 2 - 1) = d1 t := by
      simp only [d1]; ring
    rwa [heq] at hall
  have hd1_deriv : ∀ t < (1 : ℝ), -1 < t → HasDerivAt d1 (d2 t) t := by
    intro t ht1 htm1
    have h1p : 0 < 1 + t := by linarith
    have h1m : 0 < 1 - t := by linarith
    have h1c : 0 < 1 + c * t ^ 2 := by positivity
    have hd_a : HasDerivAt (fun s => (1 + s) ^ (p - 1)) ((p - 1) * (1 + t) ^ (p - 2)) t := by
      have h2 := ((hasDerivAt_const t (1 : ℝ)).add (hasDerivAt_id t)).rpow_const
        (p := p - 1) (Or.inl h1p.ne')
      change HasDerivAt (fun s => (1 + s) ^ (p - 1)) ((0 + 1) * (p - 1) * (1 + t) ^ (p - 1 - 1)) t at h2
      have heq : (0 + 1) * (p - 1) * (1 + t) ^ (p - 1 - 1) = (p - 1) * (1 + t) ^ (p - 2) := by
        have : p - 1 - 1 = p - 2 := by ring
        rw [this]; ring
      rwa [heq] at h2
    have hd_b : HasDerivAt (fun s => (1 - s) ^ (p - 1)) (-(p - 1) * (1 - t) ^ (p - 2)) t := by
      have h2 := ((hasDerivAt_const t (1 : ℝ)).sub (hasDerivAt_id t)).rpow_const
        (p := p - 1) (Or.inl h1m.ne')
      change HasDerivAt (fun s => (1 - s) ^ (p - 1)) ((0 - 1) * (p - 1) * (1 - t) ^ (p - 1 - 1)) t at h2
      have heq : (0 - 1) * (p - 1) * (1 - t) ^ (p - 1 - 1) = -(p - 1) * (1 - t) ^ (p - 2) := by
        have : p - 1 - 1 = p - 2 := by ring
        rw [this]; ring
      rwa [heq] at h2
    have hd_rpow : HasDerivAt (fun s => (1 + c * s ^ 2) ^ (p / 2 - 1))
        ((p / 2 - 1) * (1 + c * t ^ 2) ^ (p / 2 - 2) * (2 * c * t)) t := by
      have h2 := (hd_quad t).rpow_const (p := p / 2 - 1) (Or.inl h1c.ne')
      have heq : 2 * c * t * (p / 2 - 1) * (1 + c * t ^ 2) ^ (p / 2 - 1 - 1) =
          (p / 2 - 1) * (1 + c * t ^ 2) ^ (p / 2 - 2) * (2 * c * t) := by
        have : p / 2 - 1 - 1 = p / 2 - 2 := by ring
        rw [this]; ring
      rwa [heq] at h2
    have hd_prod : HasDerivAt (fun s => p * c * s * (1 + c * s ^ 2) ^ (p / 2 - 1))
        (p * c * (1 + c * t ^ 2) ^ (p / 2 - 1) +
          p * c * t * ((p / 2 - 1) * (1 + c * t ^ 2) ^ (p / 2 - 2) * (2 * c * t))) t := by
      have hlin : HasDerivAt (fun s => p * c * s) (p * c) t := by
        simpa using (hasDerivAt_id t).const_mul (p * c)
      exact hlin.mul hd_rpow
    have hall : HasDerivAt d1
        (p / 2 * ((p - 1) * (1 + t) ^ (p - 2) - -(p - 1) * (1 - t) ^ (p - 2)) -
          (p * c * (1 + c * t ^ 2) ^ (p / 2 - 1) +
            p * c * t * ((p / 2 - 1) * (1 + c * t ^ 2) ^ (p / 2 - 2) * (2 * c * t)))) t :=
      ((hd_a.sub hd_b).const_mul (p / 2)).sub hd_prod
    have hp_sub_1 : p - 1 = c := by simp [p]
    have hsplit : (1 + c * t ^ 2) ^ (p / 2 - 1) =
        (1 + c * t ^ 2) ^ (p / 2 - 2) * (1 + c * t ^ 2) := by
      rw [← Real.rpow_add_one h1c.ne']
      congr 1
      ring
    have heq : p / 2 * ((p - 1) * (1 + t) ^ (p - 2) - -(p - 1) * (1 - t) ^ (p - 2)) -
        (p * c * (1 + c * t ^ 2) ^ (p / 2 - 1) +
          p * c * t * ((p / 2 - 1) * (1 + c * t ^ 2) ^ (p / 2 - 2) * (2 * c * t))) = d2 t := by
      rw [hp_sub_1, hsplit]
      simp only [d2]
      ring
    rwa [heq] at hall
  have hd2_nn : ∀ t ∈ Set.Ioo (0 : ℝ) 1, 0 ≤ d2 t := by
    intro t ⟨ht0, ht1⟩
    have h1p : 0 < 1 + t := by linarith
    have h1m : 0 < 1 - t := by linarith
    have h1t2_pos : 0 < 1 - t ^ 2 := by nlinarith
    have h1t2_le1 : 1 - t ^ 2 ≤ 1 := by nlinarith
    set A := (1 + t) ^ (p - 2)
    set B := (1 - t) ^ (p - 2)
    have hA : 0 < A := Real.rpow_pos_of_pos h1p _
    have hB : 0 < B := Real.rpow_pos_of_pos h1m _
    have hAB : A * B = (1 - t ^ 2) ^ (p - 2) := by
      simp only [A, B]
      rw [← Real.mul_rpow h1p.le h1m.le]
      congr 1
      ring
    have hAB_ge1 : 1 ≤ A * B := by
      rw [hAB]
      exact Real.one_le_rpow_of_pos_of_le_one_of_nonpos h1t2_pos h1t2_le1 (by linarith)
    have hsum_ge2 : 2 ≤ A + B := by
      have hsq : 0 ≤ (Real.sqrt A - Real.sqrt B) ^ 2 := sq_nonneg _
      have hexp : (Real.sqrt A - Real.sqrt B) ^ 2 = A + B - 2 * (Real.sqrt A * Real.sqrt B) := by
        calc (Real.sqrt A - Real.sqrt B) ^ 2
            = Real.sqrt A ^ 2 + Real.sqrt B ^ 2 - 2 * (Real.sqrt A * Real.sqrt B) := by ring
          _ = A + B - 2 * (Real.sqrt A * Real.sqrt B) := by
              rw [Real.sq_sqrt hA.le, Real.sq_sqrt hB.le]
      have hmul_sqrt : 1 ≤ Real.sqrt A * Real.sqrt B := by
        rw [← Real.sqrt_mul hA.le]
        exact Real.one_le_sqrt.mpr hAB_ge1
      linarith
    have h1c_ge1 : 1 ≤ 1 + c * t ^ 2 := by nlinarith
    have h1c_pos : 0 < 1 + c * t ^ 2 := by positivity
    have hrpow_le : (1 + c * t ^ 2) ^ (p / 2 - 2) ≤ (1 + c * t ^ 2) ^ (-1 : ℝ) :=
      Real.rpow_le_rpow_of_exponent_le h1c_ge1 (by linarith)
    have hc2_le : 1 + c ^ 2 * t ^ 2 ≤ 1 + c * t ^ 2 := by
      have : c ^ 2 ≤ c := by nlinarith
      linarith [mul_le_mul_of_nonneg_right this (sq_nonneg t)]
    have hprod_le1 : (1 + c * t ^ 2) ^ (p / 2 - 2) * (1 + c ^ 2 * t ^ 2) ≤ 1 := by
      calc (1 + c * t ^ 2) ^ (p / 2 - 2) * (1 + c ^ 2 * t ^ 2)
          ≤ (1 + c * t ^ 2) ^ (-1 : ℝ) * (1 + c * t ^ 2) :=
            mul_le_mul hrpow_le hc2_le (by positivity)
              (Real.rpow_nonneg h1c_pos.le _)
        _ = 1 := by
            rw [Real.rpow_neg_one, inv_mul_cancel₀ h1c_pos.ne']
    have hpc_pos : 0 ≤ p * c := by positivity
    simp only [d2]
    nlinarith
  have hd1_mono : MonotoneOn d1 (Set.Ico 0 1) := by
    apply monotoneOn_of_deriv_nonneg (convex_Ico 0 1)
    · intro t ht
      exact (hd1_deriv t ht.2 (by linarith [ht.1])).continuousAt.continuousWithinAt
    · intro t ht
      rw [interior_Ico] at ht
      exact (hd1_deriv t ht.2 (by linarith [ht.1])).differentiableAt.differentiableWithinAt
    · intro t ht
      rw [interior_Ico] at ht
      rw [(hd1_deriv t ht.2 (by linarith [ht.1])).deriv]
      exact hd2_nn t ht
  have hd1_nn : ∀ t ∈ Set.Ioo (0 : ℝ) 1, 0 ≤ d1 t := by
    intro t ht
    have hd1_0 : d1 0 = 0 := by simp [d1]
    rw [← hd1_0]
    exact hd1_mono (Set.left_mem_Ico.mpr zero_lt_one) ⟨ht.1.le, ht.2⟩ ht.1.le
  have hd0_cont : ContinuousOn d0 (Set.Icc 0 1) := by
    have h1 : ContinuousOn (fun t : ℝ => (1 + t) ^ p) (Set.Icc 0 1) :=
      (continuousOn_const.add continuousOn_id).rpow_const (fun _ _ => Or.inr hp0.le)
    have h2 : ContinuousOn (fun t : ℝ => (1 - t) ^ p) (Set.Icc 0 1) :=
      (continuousOn_const.sub continuousOn_id).rpow_const (fun _ _ => Or.inr hp0.le)
    have h3 : ContinuousOn (fun t : ℝ => (1 + c * t ^ 2) ^ (p / 2)) (Set.Icc 0 1) :=
      (continuousOn_const.add (continuousOn_const.mul (continuousOn_pow 2))).rpow_const
        (fun _ _ => Or.inr (by positivity))
    exact ((h1.add h2).div_const 2).sub h3
  have hd0_mono : MonotoneOn d0 (Set.Icc 0 1) := by
    apply monotoneOn_of_deriv_nonneg (convex_Icc 0 1) hd0_cont
    · intro t ht
      rw [interior_Icc] at ht
      exact (hd0_deriv t ht.2 (by linarith [ht.1])).differentiableAt.differentiableWithinAt
    · intro t ht
      rw [interior_Icc] at ht
      rw [(hd0_deriv t ht.2 (by linarith [ht.1])).deriv]
      exact hd1_nn t ht
  have hd0_0 : d0 0 = 0 := by simp [d0]
  have hd0_x : 0 ≤ d0 x := by
    rw [← hd0_0]
    exact hd0_mono (Set.left_mem_Icc.mpr zero_le_one) ⟨hx0, hx1⟩ hx0
  simp only [d0, p] at hd0_x
  linarith

lemma two_point_bonami {ρ : ℝ} (hρ0 : 0 < ρ) (hρ1 : ρ < 1) (u v : ℝ) :
    (((1 + ρ) / 2 * u + (1 - ρ) / 2 * v) ^ 2 +
        ((1 - ρ) / 2 * u + (1 + ρ) / 2 * v) ^ 2) / 2 ≤
      ((|u| ^ (1 + ρ ^ 2) + |v| ^ (1 + ρ ^ 2)) / 2) ^ (2 / (1 + ρ ^ 2)) := by
  set c : ℝ := ρ ^ 2
  set p : ℝ := 1 + c
  have hc0 : 0 < c := sq_pos_of_pos hρ0
  have hc1 : c < 1 := by nlinarith
  have hp0 : 0 < p := by linarith
  set a : ℝ := (u + v) / 2
  set b : ℝ := (u - v) / 2
  have hlhs : (((1 + ρ) / 2 * u + (1 - ρ) / 2 * v) ^ 2 +
      ((1 - ρ) / 2 * u + (1 + ρ) / 2 * v) ^ 2) / 2 = a ^ 2 + c * b ^ 2 := by
    simp only [a, b, c]
    ring
  rw [hlhs]
  have huv_abs : |u| ^ p + |v| ^ p = (|a| + |b|) ^ p + |(|a| - |b|)| ^ p := by
    have hu_eq : u = a + b := by simp only [a, b]; ring
    have hv_eq : v = a - b := by simp only [a, b]; ring
    rw [hu_eq, hv_eq]
    rcases le_total 0 (a * b) with hab | hab
    · have h1 : |a + b| = |a| + |b| := by
        rw [← sq_eq_sq₀ (abs_nonneg _) (by positivity), sq_abs]
        have : |a| * |b| = a * b := by rw [← abs_mul, abs_of_nonneg hab]
        nlinarith [sq_abs a, sq_abs b]
      have h2 : |a - b| = |(|a| - |b|)| := by
        rw [← sq_eq_sq₀ (abs_nonneg _) (abs_nonneg _), sq_abs, sq_abs]
        have : |a| * |b| = a * b := by rw [← abs_mul, abs_of_nonneg hab]
        nlinarith [sq_abs a, sq_abs b]
      rw [h1, h2]
    · have hab' : 0 ≤ a * (-b) := by linarith
      have h1 : |a - b| = |a| + |b| := by
        have hnb : |-b| = |b| := abs_neg b
        rw [sub_eq_add_neg, ← hnb, ← sq_eq_sq₀ (abs_nonneg _) (by positivity), sq_abs]
        have : |a| * |-b| = a * (-b) := by rw [← abs_mul, abs_of_nonneg hab']
        nlinarith [sq_abs a, sq_abs (-b)]
      have h2 : |a + b| = |(|a| - |b|)| := by
        have hnb : |-b| = |b| := abs_neg b
        rw [← hnb, ← sq_eq_sq₀ (abs_nonneg _) (abs_nonneg _), sq_abs, sq_abs]
        have : |a| * |-b| = a * (-b) := by rw [← abs_mul, abs_of_nonneg hab']
        nlinarith [sq_abs a, sq_abs (-b)]
      rw [h1, h2, add_comm]
  rw [huv_abs]
  by_cases hab0 : |a| = 0 ∧ |b| = 0
  · rcases hab0 with ⟨ha0, hb0⟩
    have ha : a = 0 := abs_eq_zero.mp ha0
    have hb : b = 0 := abs_eq_zero.mp hb0
    rw [ha, hb]
    simp [Real.zero_rpow hp0.ne', Real.zero_rpow (by positivity : (2 / p) ≠ 0)]
  rcases le_or_gt |b| |a| with hba | hab
  · have ha_pos : 0 < |a| := by
      by_contra hle
      have ha0 : |a| = 0 := le_antisymm (not_lt.mp hle) (abs_nonneg a)
      have hb0 : |b| = 0 := le_antisymm (hba.trans_eq ha0) (abs_nonneg b)
      exact hab0 ⟨ha0, hb0⟩
    set x := |b| / |a|
    have hx0 : 0 ≤ x := div_nonneg (abs_nonneg b) ha_pos.le
    have hx1 : x ≤ 1 := (div_le_one ha_pos).mpr hba
    have hkey := one_plus_c_x_sq_le hc0 hc1 hx0 hx1
    have hkey2 : 1 + c * x ^ 2 ≤ (((1 + x) ^ p + (1 - x) ^ p) / 2) ^ (2 / p) := by
      have hbase_nn : 0 ≤ 1 + c * x ^ 2 := by positivity
      calc 1 + c * x ^ 2
          = ((1 + c * x ^ 2) ^ (p / 2)) ^ (2 / p) := by
              rw [← Real.rpow_mul hbase_nn]
              have : (p / 2) * (2 / p) = 1 := by field_simp
              rw [this, Real.rpow_one]
        _ ≤ (((1 + x) ^ p + (1 - x) ^ p) / 2) ^ (2 / p) :=
              Real.rpow_le_rpow (Real.rpow_nonneg hbase_nn _) hkey (by positivity)
    have hmul := mul_le_mul_of_nonneg_left hkey2 (sq_nonneg |a|)
    have hl : |a| ^ 2 * (1 + c * x ^ 2) = a ^ 2 + c * b ^ 2 := by
      simp only [x, div_pow]
      field_simp [ha_pos.ne']
      rw [sq_abs, sq_abs]
    have hr : |a| ^ 2 * (((1 + x) ^ p + (1 - x) ^ p) / 2) ^ (2 / p) =
        (((|a| + |b|) ^ p + |(|a| - |b|)| ^ p) / 2) ^ (2 / p) := by
      have ha2 : |a| ^ 2 = (|a| ^ p) ^ (2 / p) := by
        rw [← Real.rpow_mul (abs_nonneg a)]
        have : p * (2 / p) = (2 : ℝ) := by field_simp
        rw [this, Real.rpow_two]
      have h1mx : 0 ≤ 1 - x := by linarith
      have hrhs_nn : 0 ≤ ((1 + x) ^ p + (1 - x) ^ p) / 2 :=
        div_nonneg (add_nonneg (Real.rpow_nonneg (by linarith) _) (Real.rpow_nonneg h1mx _)) (by norm_num)
      rw [ha2, ← Real.mul_rpow (Real.rpow_nonneg (abs_nonneg a) _) hrhs_nn]
      congr 1
      have h1 : |a| ^ p * (1 + x) ^ p = (|a| + |b|) ^ p := by
        rw [← Real.mul_rpow (abs_nonneg a) (by linarith)]
        congr 1
        simp only [x]
        field_simp [ha_pos.ne']
      have h2 : |a| ^ p * (1 - x) ^ p = |(|a| - |b|)| ^ p := by
        rw [← Real.mul_rpow (abs_nonneg a) h1mx]
        congr 1
        have hab_sub : 0 ≤ |a| - |b| := sub_nonneg.mpr hba
        rw [abs_of_nonneg hab_sub]
        simp only [x]
        field_simp [ha_pos.ne']
      linarith
    rwa [hl, hr] at hmul
  · have hb_pos : 0 < |b| := lt_of_le_of_lt (abs_nonneg a) hab
    set x := |a| / |b|
    have hx0 : 0 ≤ x := div_nonneg (abs_nonneg a) hb_pos.le
    have hx1 : x ≤ 1 := (div_le_one hb_pos).mpr hab.le
    have hswap : x ^ 2 + c ≤ 1 + c * x ^ 2 := by
      have : 0 ≤ (1 - c) * (1 - x ^ 2) := mul_nonneg (by linarith) (by nlinarith)
      linarith
    have hkey := one_plus_c_x_sq_le hc0 hc1 hx0 hx1
    have hkey2 : x ^ 2 + c ≤ (((1 + x) ^ p + (1 - x) ^ p) / 2) ^ (2 / p) := by
      have hbase_nn : 0 ≤ 1 + c * x ^ 2 := by positivity
      calc x ^ 2 + c
          ≤ 1 + c * x ^ 2 := hswap
        _ = ((1 + c * x ^ 2) ^ (p / 2)) ^ (2 / p) := by
              rw [← Real.rpow_mul hbase_nn]
              have : (p / 2) * (2 / p) = 1 := by field_simp
              rw [this, Real.rpow_one]
        _ ≤ (((1 + x) ^ p + (1 - x) ^ p) / 2) ^ (2 / p) :=
              Real.rpow_le_rpow (Real.rpow_nonneg hbase_nn _) hkey (by positivity)
    have hmul := mul_le_mul_of_nonneg_left hkey2 (sq_nonneg |b|)
    have hl : |b| ^ 2 * (x ^ 2 + c) = a ^ 2 + c * b ^ 2 := by
      simp only [x, div_pow]
      field_simp [hb_pos.ne']
      rw [sq_abs, sq_abs]
      ring
    have hr : |b| ^ 2 * (((1 + x) ^ p + (1 - x) ^ p) / 2) ^ (2 / p) =
        (((|a| + |b|) ^ p + |(|a| - |b|)| ^ p) / 2) ^ (2 / p) := by
      have hb2 : |b| ^ 2 = (|b| ^ p) ^ (2 / p) := by
        rw [← Real.rpow_mul (abs_nonneg b)]
        have : p * (2 / p) = (2 : ℝ) := by field_simp
        rw [this, Real.rpow_two]
      have h1mx : 0 ≤ 1 - x := by linarith
      have hrhs_nn : 0 ≤ ((1 + x) ^ p + (1 - x) ^ p) / 2 :=
        div_nonneg (add_nonneg (Real.rpow_nonneg (by linarith) _) (Real.rpow_nonneg h1mx _)) (by norm_num)
      rw [hb2, ← Real.mul_rpow (Real.rpow_nonneg (abs_nonneg b) _) hrhs_nn]
      congr 1
      have h1 : |b| ^ p * (1 + x) ^ p = (|a| + |b|) ^ p := by
        rw [← Real.mul_rpow (abs_nonneg b) (by linarith)]
        congr 1
        simp only [x]
        field_simp [hb_pos.ne']
        ring
      have h2 : |b| ^ p * (1 - x) ^ p = |(|a| - |b|)| ^ p := by
        rw [← Real.mul_rpow (abs_nonneg b) h1mx]
        congr 1
        have hba_sub : |a| - |b| ≤ 0 := sub_nonpos.mpr hab.le
        rw [abs_of_nonpos hba_sub]
        simp only [x]
        field_simp [hb_pos.ne']
        ring
      linarith
    rwa [hl, hr] at hmul

/-! ### `(p, 2)` hypercontractivity on `Cube m` by induction on `m` -/

lemma bonami_cube_rpow : ∀ (m : ℕ) {ρ : ℝ} (_ : 0 < ρ) (_ : ρ < 1) (g : Cube m → ℝ),
    (expect (fun τ => |T ρ g τ| ^ (2 : ℝ))) ^ ((1 + ρ ^ 2) / 2) ≤
      expect (fun τ => |g τ| ^ (1 + ρ ^ 2))
  | 0, ρ, _, _, g => by
    set p : ℝ := 1 + ρ ^ 2
    unfold expect
    have huniv : (Finset.univ : Finset (Cube 0)) = {Fin.elim0} := by
      ext σ
      simp only [Finset.mem_univ, Finset.mem_singleton, true_iff]
      exact Subsingleton.elim σ Fin.elim0
    rw [huniv]
    simp only [pow_zero, inv_one, one_mul, Finset.sum_singleton, T_zero]
    rw [← Real.rpow_mul (abs_nonneg _)]
    have : (2 : ℝ) * (p / 2) = p := by ring
    rw [this]
  | m + 1, ρ, hρ0, hρ1, g => by
    set p : ℝ := 1 + ρ ^ 2
    have hp1 : 1 < p := by nlinarith [sq_pos_of_pos hρ0]
    have hp2 : p < 2 := by nlinarith
    have hp0 : 0 < p := by linarith
    set r : ℝ := 2 / p
    have hr1 : 1 ≤ r := (one_le_div hp0).mpr hp2.le
    let g1 : Cube m → ℝ := fun y => g (Fin.cons 1 y)
    let g2 : Cube m → ℝ := fun y => g (Fin.cons (-1) y)
    let F1 : Cube m → ℝ := T ρ g1
    let F2 : Cube m → ℝ := T ρ g2
    have hpt : ∀ y : Cube m,
        (|T ρ g (Fin.cons 1 y)| ^ (2 : ℝ) + |T ρ g (Fin.cons (-1) y)| ^ (2 : ℝ)) / 2 ≤
          ((|F1 y| ^ p + |F2 y| ^ p) / 2) ^ r := by
      intro y
      obtain ⟨ht1, ht2⟩ := T_succ ρ g y
      rw [Real.rpow_two, Real.rpow_two, sq_abs, sq_abs, ht1, ht2]
      exact two_point_bonami hρ0 hρ1 (F1 y) (F2 y)
    have hexp_T : expect (fun τ => |T ρ g τ| ^ (2 : ℝ)) =
        ((2 : ℝ) ^ m)⁻¹ * ∑ y : Cube m,
          (|T ρ g (Fin.cons 1 y)| ^ (2 : ℝ) + |T ρ g (Fin.cons (-1) y)| ^ (2 : ℝ)) / 2 := by
      unfold expect
      rw [sum_cube_succ, pow_succ, ← Finset.sum_div]
      ring
    have hsum_le : ∑ y : Cube m,
          (|T ρ g (Fin.cons 1 y)| ^ (2 : ℝ) + |T ρ g (Fin.cons (-1) y)| ^ (2 : ℝ)) / 2 ≤
        ∑ y : Cube m, ((|F1 y| ^ p + |F2 y| ^ p) / 2) ^ r :=
      Finset.sum_le_sum (fun y _ => hpt y)
    let X : Cube m → ℝ := fun y => |F1 y| ^ p / 2
    let Y : Cube m → ℝ := fun y => |F2 y| ^ p / 2
    have hXY : ∀ y : Cube m, ((|F1 y| ^ p + |F2 y| ^ p) / 2) ^ r = |X y + Y y| ^ r := by
      intro y
      have hnn : 0 ≤ (|F1 y| ^ p + |F2 y| ^ p) / 2 :=
        div_nonneg (add_nonneg (Real.rpow_nonneg (abs_nonneg _) _)
          (Real.rpow_nonneg (abs_nonneg _) _)) (by norm_num)
      have heq : (|F1 y| ^ p + |F2 y| ^ p) / 2 = X y + Y y := by simp only [X, Y]; ring
      rw [← heq, abs_of_nonneg hnn]
    have hmink : (∑ y : Cube m, ((|F1 y| ^ p + |F2 y| ^ p) / 2) ^ r) ^ (1 / r) ≤
        (∑ y : Cube m, |X y| ^ r) ^ (1 / r) + (∑ y : Cube m, |Y y| ^ r) ^ (1 / r) := by
      simp_rw [hXY]
      exact Real.Lp_add_le Finset.univ X Y hr1
    have h1r : 1 / r = p / 2 := by simp only [r]; field_simp
    have hX_simp : ∀ y : Cube m, |X y| ^ r = (2 : ℝ) ^ (-r) * |F1 y| ^ (2 : ℝ) := by
      intro y
      have hnn : 0 ≤ |F1 y| ^ p := Real.rpow_nonneg (abs_nonneg _) _
      simp only [X]
      rw [abs_of_nonneg (div_nonneg hnn (by norm_num)), div_eq_mul_inv,
        Real.mul_rpow hnn (by norm_num), mul_comm]
      congr 1
      · rw [Real.inv_rpow (by norm_num), ← Real.rpow_neg (by norm_num)]
      · rw [← Real.rpow_mul (abs_nonneg _)]
        have : p * r = (2 : ℝ) := by simp only [r]; field_simp
        rw [this]
    have hY_simp : ∀ y : Cube m, |Y y| ^ r = (2 : ℝ) ^ (-r) * |F2 y| ^ (2 : ℝ) := by
      intro y
      have hnn : 0 ≤ |F2 y| ^ p := Real.rpow_nonneg (abs_nonneg _) _
      simp only [Y]
      rw [abs_of_nonneg (div_nonneg hnn (by norm_num)), div_eq_mul_inv,
        Real.mul_rpow hnn (by norm_num), mul_comm]
      congr 1
      · rw [Real.inv_rpow (by norm_num), ← Real.rpow_neg (by norm_num)]
      · rw [← Real.rpow_mul (abs_nonneg _)]
        have : p * r = (2 : ℝ) := by simp only [r]; field_simp
        rw [this]
    have hfactor : ∀ S : ℝ, 0 ≤ S → ((2 : ℝ) ^ (-r) * S) ^ (1 / r) = 2⁻¹ * S ^ (p / 2) := by
      intro S hS
      rw [Real.mul_rpow (by positivity) hS, ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2), h1r]
      have : -r * (p / 2) = (-1 : ℝ) := by simp only [r]; field_simp
      rw [this, Real.rpow_neg_one]
    have hih1 := bonami_cube_rpow m hρ0 hρ1 g1
    have hih2 := bonami_cube_rpow m hρ0 hρ1 g2
    have hwm_pos : (0 : ℝ) ≤ ((2 : ℝ) ^ m)⁻¹ := by positivity
    have hsum1_nn : 0 ≤ ∑ y : Cube m, |F1 y| ^ (2 : ℝ) :=
      Finset.sum_nonneg (fun _ _ => Real.rpow_nonneg (abs_nonneg _) _)
    have hsum2_nn : 0 ≤ ∑ y : Cube m, |F2 y| ^ (2 : ℝ) :=
      Finset.sum_nonneg (fun _ _ => Real.rpow_nonneg (abs_nonneg _) _)
    have hsum_lhs_nn : 0 ≤ ∑ y : Cube m,
        (|T ρ g (Fin.cons 1 y)| ^ (2 : ℝ) + |T ρ g (Fin.cons (-1) y)| ^ (2 : ℝ)) / 2 :=
      Finset.sum_nonneg (fun _ _ => div_nonneg
        (add_nonneg (Real.rpow_nonneg (abs_nonneg _) _) (Real.rpow_nonneg (abs_nonneg _) _))
        (by norm_num))
    calc (expect (fun τ => |T ρ g τ| ^ (2 : ℝ))) ^ (p / 2)
        = (((2 : ℝ) ^ m)⁻¹) ^ (p / 2) *
            (∑ y : Cube m,
              (|T ρ g (Fin.cons 1 y)| ^ (2 : ℝ) + |T ρ g (Fin.cons (-1) y)| ^ (2 : ℝ)) / 2) ^ (1 / r) := by
            rw [hexp_T, Real.mul_rpow hwm_pos hsum_lhs_nn, h1r]
      _ ≤ (((2 : ℝ) ^ m)⁻¹) ^ (p / 2) *
            (∑ y : Cube m, ((|F1 y| ^ p + |F2 y| ^ p) / 2) ^ r) ^ (1 / r) :=
            mul_le_mul_of_nonneg_left
              (Real.rpow_le_rpow hsum_lhs_nn hsum_le (by positivity))
              (Real.rpow_nonneg hwm_pos _)
      _ ≤ (((2 : ℝ) ^ m)⁻¹) ^ (p / 2) *
            ((∑ y : Cube m, |X y| ^ r) ^ (1 / r) + (∑ y : Cube m, |Y y| ^ r) ^ (1 / r)) :=
            mul_le_mul_of_nonneg_left hmink (Real.rpow_nonneg hwm_pos _)
      _ = (((2 : ℝ) ^ m)⁻¹) ^ (p / 2) *
            (2⁻¹ * (∑ y : Cube m, |F1 y| ^ (2 : ℝ)) ^ (p / 2) +
              2⁻¹ * (∑ y : Cube m, |F2 y| ^ (2 : ℝ)) ^ (p / 2)) := by
            simp_rw [hX_simp, hY_simp, ← Finset.mul_sum]
            rw [hfactor _ hsum1_nn, hfactor _ hsum2_nn]
      _ = 2⁻¹ * ((expect (fun y => |F1 y| ^ (2 : ℝ))) ^ (p / 2) +
            (expect (fun y => |F2 y| ^ (2 : ℝ))) ^ (p / 2)) := by
            unfold expect
            rw [Real.mul_rpow hwm_pos hsum1_nn, Real.mul_rpow hwm_pos hsum2_nn]
            ring
      _ ≤ 2⁻¹ * (expect (fun y => |g1 y| ^ p) + expect (fun y => |g2 y| ^ p)) := by
            exact mul_le_mul_of_nonneg_left (add_le_add hih1 hih2) (by norm_num)
      _ = expect (fun τ => |g τ| ^ p) := by
            unfold expect
            rw [sum_cube_succ, pow_succ, Finset.sum_add_distrib]
            simp only [g1, g2]
            ring

lemma bonami_p_2 {m : ℕ} {ρ : ℝ} (hρ0 : 0 < ρ) (hρ1 : ρ < 1) (g : Cube m → ℝ) :
    lpNorm 2 (T ρ g) ≤ lpNorm (1 + ρ ^ 2) g := by
  set p : ℝ := 1 + ρ ^ 2
  have hp0 : 0 < p := by nlinarith [sq_pos_of_pos hρ0]
  have hpow := bonami_cube_rpow m hρ0 hρ1 g
  have hexp2_nn : 0 ≤ expect (fun τ => |T ρ g τ| ^ (2 : ℝ)) := by
    unfold expect
    exact mul_nonneg (by positivity) (Finset.sum_nonneg (fun _ _ => Real.rpow_nonneg (abs_nonneg _) _))
  unfold lpNorm
  calc (expect (fun τ => |T ρ g τ| ^ (2 : ℝ))) ^ (1 / (2 : ℝ))
      = (((expect (fun τ => |T ρ g τ| ^ (2 : ℝ))) ^ (p / 2))) ^ (1 / p) := by
          rw [← Real.rpow_mul hexp2_nn]
          congr 1
          field_simp
    _ ≤ (expect (fun τ => |g τ| ^ p)) ^ (1 / p) :=
          Real.rpow_le_rpow (Real.rpow_nonneg hexp2_nn _) hpow (by positivity)

/-! ### Separate convexity Jensen inequality on `[-1, 1]^m` -/

lemma sepConvex_jensen_cube {m : ℕ} {f : (Fin m → ℝ) → ℝ}
    (hsep : SepConvexOn (Set.Icc (-1 : ℝ) 1) f) {q : Fin m → ℝ} (hq : q ∈ cube m) :
    f q ≤ ((2 : ℝ) ^ m)⁻¹ *
      ∑ σ : Cube m, (∏ i : Fin m, (1 + q i * vertex σ i)) * f (vertex σ) := by
  classical
  have hq_mem : ∀ i : Fin m, q i ∈ Set.Icc (-1 : ℝ) 1 := fun i =>
    ⟨(hq.1 i), (hq.2 i)⟩
  let G : Finset (Fin m) → ℝ := fun S =>
    ((2 : ℝ) ^ m)⁻¹ * ∑ σ : Cube m,
      (∏ i ∈ S, (1 + q i * vertex σ i)) * f (fun i => if i ∈ S then vertex σ i else q i)
  have hG_empty : G ∅ = f q := by
    simp only [G, Finset.prod_empty, Finset.notMem_empty, ↓reduceIte, one_mul,
      Finset.sum_const, Finset.card_univ, card_cube, nsmul_eq_mul]
    rw [Nat.cast_pow, Nat.cast_ofNat, inv_mul_cancel_left₀ (by positivity)]
  have hG_univ : G Finset.univ = ((2 : ℝ) ^ m)⁻¹ *
      ∑ σ : Cube m, (∏ i : Fin m, (1 + q i * vertex σ i)) * f (vertex σ) := by
    simp only [G, Finset.mem_univ, ↓reduceIte]
  have hG_step : ∀ (S : Finset (Fin m)) (j : Fin m), j ∉ S → G S ≤ G (insert j S) := by
    intro S j hjS
    let flip : Cube m → Cube m := fun σ => Function.update σ j (-σ j)
    have hflip_bij : Function.Bijective flip := by
      refine Function.Involutive.bijective (fun σ => ?_)
      ext i
      by_cases hij : i = j
      · subst hij; simp [flip]
      · simp [flip, hij]
    let term : Finset (Fin m) → Cube m → ℝ := fun T σ =>
      (∏ i ∈ T, (1 + q i * vertex σ i)) * f (fun i => if i ∈ T then vertex σ i else q i)
    have hsum_flip : ∑ σ : Cube m, term (insert j S) σ =
        2⁻¹ * ∑ σ : Cube m, (term (insert j S) σ + term (insert j S) (flip σ)) := by
      rw [Finset.sum_add_distrib]
      have heq : ∑ σ : Cube m, term (insert j S) (flip σ) = ∑ σ : Cube m, term (insert j S) σ :=
        Fintype.sum_bijective flip hflip_bij _ _ (fun _ => rfl)
      rw [heq]
      ring
    have hpair : ∀ σ : Cube m,
        term S σ ≤ 2⁻¹ * (term (insert j S) σ + term (insert j S) (flip σ)) := by
      intro σ
      let w : Fin m → ℝ := fun i => if i ∈ S then vertex σ i else q i
      have hw : ∀ i, w i ∈ Set.Icc (-1 : ℝ) 1 := by
        intro i
        simp only [w]
        split_ifs
        · rcases unit_cast_cases (σ i) with h1 | hm1
          · simp [vertex, h1]
          · simp [vertex, hm1]
        · exact hq_mem i
      have hw_j : Function.update w j (q j) = w := by
        ext i
        by_cases hij : i = j
        · subst hij; simp [w, hjS]
        · simp [hij]
      have hconv := hsep w hw j
      have ha_nn : 0 ≤ (1 + q j) / 2 := by linarith [(hq_mem j).1]
      have hb_nn : 0 ≤ (1 - q j) / 2 := by linarith [(hq_mem j).2]
      have hab : (1 + q j) / 2 + (1 - q j) / 2 = 1 := by ring
      have h1_mem : (1 : ℝ) ∈ Set.Icc (-1 : ℝ) 1 := by norm_num
      have hm1_mem : (-1 : ℝ) ∈ Set.Icc (-1 : ℝ) 1 := by norm_num
      have hjens : f w ≤ (1 + q j) / 2 * f (Function.update w j 1) +
          (1 - q j) / 2 * f (Function.update w j (-1)) := by
        have h := hconv.2 h1_mem hm1_mem ha_nn hb_nn hab
        simp only [smul_eq_mul] at h
        have hcomb : (1 + q j) / 2 * 1 + (1 - q j) / 2 * -1 = q j := by ring
        rwa [hcomb, hw_j] at h
      have hprod_nn : 0 ≤ ∏ i ∈ S, (1 + q i * vertex σ i) := by
        refine Finset.prod_nonneg (fun i _ => ?_)
        rcases unit_cast_cases (σ i) with h1 | hm1
        · simp only [vertex, h1, mul_one]; linarith [(hq_mem i).1]
        · simp only [vertex, hm1, mul_neg, mul_one]; linarith [(hq_mem i).2]
      have hprod_flip : ∏ i ∈ S, (1 + q i * vertex (flip σ) i) =
          ∏ i ∈ S, (1 + q i * vertex σ i) := by
        refine Finset.prod_congr rfl (fun i hi => ?_)
        have hij : i ≠ j := fun h => hjS (h ▸ hi)
        simp [flip, vertex, hij]
      have hvec_σ : (fun i => if i ∈ insert j S then vertex σ i else q i) =
          Function.update w j (vertex σ j) := by
        ext i
        by_cases hij : i = j
        · subst hij; simp
        · simp [w, hij]
      have hvec_flip : (fun i => if i ∈ insert j S then vertex (flip σ) i else q i) =
          Function.update w j (-vertex σ j) := by
        ext i
        by_cases hij : i = j
        · subst hij; simp [flip, vertex]
        · simp [w, flip, vertex, hij]
      have hflip_j : vertex (flip σ) j = -vertex σ j := by
        simp [flip, vertex]
      have hrhs_eq : 2⁻¹ * (term (insert j S) σ + term (insert j S) (flip σ)) =
          (∏ i ∈ S, (1 + q i * vertex σ i)) *
            ((1 + q j) / 2 * f (Function.update w j 1) +
              (1 - q j) / 2 * f (Function.update w j (-1))) := by
        simp only [term, Finset.prod_insert hjS, hprod_flip, hvec_σ, hvec_flip, hflip_j]
        rcases unit_cast_cases (σ j) with h1 | hm1
        · simp only [vertex] at h1 ⊢
          rw [h1]
          norm_num
          ring
        · simp only [vertex] at hm1 ⊢
          rw [hm1]
          norm_num
          ring
      rw [hrhs_eq]
      exact mul_le_mul_of_nonneg_left hjens hprod_nn
    simp only [G]
    rw [hsum_flip]
    have hsum_le : ∑ σ : Cube m, term S σ ≤
        2⁻¹ * ∑ σ : Cube m, (term (insert j S) σ + term (insert j S) (flip σ)) := by
      rw [Finset.mul_sum]
      exact Finset.sum_le_sum (fun σ _ => hpair σ)
    exact mul_le_mul_of_nonneg_left hsum_le (by positivity)
  have hmono : ∀ S : Finset (Fin m), G ∅ ≤ G S := by
    intro S
    induction S using Finset.induction_on with
    | empty => exact le_rfl
    | @insert j S hjS ih => exact ih.trans (hG_step S j hjS)
  have hfinal := hmono Finset.univ
  rwa [hG_empty, hG_univ] at hfinal

end AuxLemma18

theorem solution {m : ℕ} {n : ℝ} (hn : 0 ≤ n) (f : (Fin m → ℝ) → ℝ) (hnn : ∀ x ∈ cube m, 0 ≤ f x)
    (hsep : SepConvexOn (Set.Icc (-1 : ℝ) 1) f) (hnz : ∃ x ∈ cube m, f x ≠ 0)
    (hhom : ∀ σ : Cube m, ∀ ρ : ℝ, 0 ≤ ρ → ρ ≤ 1 → f (ρ • vertex σ) = ρ ^ n * f (vertex σ)) :
    Real.exp (-2 * n) ≤ expect (fun σ : Cube m => if 0 < f (vertex σ) then (1 : ℝ) else 0) := by
  have hvert_mem : ∀ σ : Cube m, vertex σ ∈ cube m := by
    intro σ
    refine ⟨fun i => ?_, fun i => ?_⟩
    · rcases AuxLemma18.unit_cast_cases (σ i) with h1 | hm1
      · simp [vertex, h1]
      · simp [vertex, hm1]
    · rcases AuxLemma18.unit_cast_cases (σ i) with h1 | hm1
      · simp [vertex, h1]
      · simp [vertex, hm1]
  let g : Cube m → ℝ := fun σ => f (vertex σ)
  have hg_nn : ∀ σ : Cube m, 0 ≤ g σ := fun σ => hnn (vertex σ) (hvert_mem σ)
  obtain ⟨x0, hx0_mem, hx0_nz⟩ := hnz
  have hx0_pos : 0 < f x0 := lt_of_le_of_ne (hnn x0 hx0_mem) (Ne.symm hx0_nz)
  have hjens0 := AuxLemma18.sepConvex_jensen_cube hsep hx0_mem
  have hex_pos : ∃ σ0 : Cube m, 0 < g σ0 := by
    by_contra hall
    have hall' : ∀ σ : Cube m, g σ ≤ 0 := fun σ => not_lt.mp (fun h => hall ⟨σ, h⟩)
    have hg0 : ∀ σ : Cube m, g σ = 0 := fun σ => le_antisymm (hall' σ) (hg_nn σ)
    have hsum0 : ∑ σ : Cube m, (∏ i : Fin m, (1 + x0 i * vertex σ i)) * f (vertex σ) = 0 := by
      refine Finset.sum_eq_zero (fun σ _ => ?_)
      change _ * g σ = 0
      rw [hg0 σ, mul_zero]
    rw [hsum0, mul_zero] at hjens0
    linarith
  obtain ⟨σ0, hσ0_pos⟩ := hex_pos
  have hnorm2_pos : 0 < lpNorm 2 g := by
    unfold lpNorm expect
    apply Real.rpow_pos_of_pos
    apply mul_pos (by positivity)
    refine Finset.sum_pos' (fun σ _ => Real.rpow_nonneg (abs_nonneg _) _) ⟨σ0, Finset.mem_univ _, ?_⟩
    exact Real.rpow_pos_of_pos (abs_pos.mpr hσ0_pos.ne') _
  set α : ℝ := expect (fun σ : Cube m => if 0 < f (vertex σ) then (1 : ℝ) else 0)
  have hα_eq : α = expect (fun σ : Cube m => if g σ ≠ 0 then (1 : ℝ) else 0) := by
    unfold α expect
    congr 1
    refine Finset.sum_congr rfl (fun σ _ => ?_)
    have h0 := hg_nn σ
    by_cases h : g σ = 0
    · simp [g, h] at *
    · have hp : 0 < f (vertex σ) := lt_of_le_of_ne h0 (Ne.symm h)
      simp [g, h, hp]
  have hα_pos : 0 < α := by
    unfold α expect
    apply mul_pos (by positivity)
    refine Finset.sum_pos' (fun σ _ => by split_ifs <;> norm_num) ⟨σ0, Finset.mem_univ _, ?_⟩
    simp [show 0 < f (vertex σ0) from hσ0_pos]
  have hbound_ρ : ∀ ρ : ℝ, 0 < ρ → ρ < 1 →
      Real.exp (-2 * n * (1 + ρ ^ 2) / (ρ * (1 + ρ))) ≤ α := by
    intro ρ hρ0 hρ1
    set p : ℝ := 1 + ρ ^ 2
    have hp1 : 1 ≤ p := by nlinarith [sq_pos_of_pos hρ0]
    have hp2 : p < 2 := by nlinarith
    have hpt : ∀ τ : Cube m, ρ ^ n * g τ ≤ AuxLemma18.T ρ g τ := by
      intro τ
      have hq_mem : ρ • vertex τ ∈ cube m := by
        refine ⟨fun i => ?_, fun i => ?_⟩
        · rcases AuxLemma18.unit_cast_cases (τ i) with h1 | hm1
          · simp [vertex, h1]; linarith
          · simp [vertex, hm1]; linarith
        · rcases AuxLemma18.unit_cast_cases (τ i) with h1 | hm1
          · simp [vertex, h1]; linarith
          · simp [vertex, hm1]; linarith
      have hjens := AuxLemma18.sepConvex_jensen_cube hsep hq_mem
      rw [hhom τ ρ hρ0.le hρ1.le] at hjens
      refine hjens.trans_eq ?_
      unfold AuxLemma18.T
      congr 1
      refine Finset.sum_congr rfl (fun σ _ => ?_)
      simp only [Pi.smul_apply, smul_eq_mul, g]
      congr 1
      refine Finset.prod_congr rfl (fun i _ => by ring)
    have hT_nn : ∀ τ : Cube m, 0 ≤ AuxLemma18.T ρ g τ := fun τ =>
      (mul_nonneg (Real.rpow_nonneg hρ0.le _) (hg_nn τ)).trans (hpt τ)
    have hl2 : ρ ^ n * lpNorm 2 g ≤ lpNorm 2 (AuxLemma18.T ρ g) := by
      unfold lpNorm expect
      have hsum : ∑ τ : Cube m, |ρ ^ n * g τ| ^ (2 : ℝ) ≤
          ∑ τ : Cube m, |AuxLemma18.T ρ g τ| ^ (2 : ℝ) := by
        refine Finset.sum_le_sum (fun τ _ => ?_)
        have h1 : 0 ≤ ρ ^ n * g τ := mul_nonneg (Real.rpow_nonneg hρ0.le _) (hg_nn τ)
        rw [abs_of_nonneg h1, abs_of_nonneg (hT_nn τ)]
        exact Real.rpow_le_rpow h1 (hpt τ) (by norm_num)
      have hfactor : ρ ^ n * (((2 : ℝ) ^ m)⁻¹ * ∑ τ : Cube m, |g τ| ^ (2 : ℝ)) ^ (1 / (2 : ℝ)) =
          (((2 : ℝ) ^ m)⁻¹ * ∑ τ : Cube m, |ρ ^ n * g τ| ^ (2 : ℝ)) ^ (1 / (2 : ℝ)) := by
        have hρn : 0 ≤ ρ ^ n := Real.rpow_nonneg hρ0.le _
        have hρn_sq : ρ ^ n = ((ρ ^ n) ^ (2 : ℝ)) ^ (1 / (2 : ℝ)) := by
          rw [← Real.rpow_mul hρn]
          norm_num
        have hexp_nn : 0 ≤ ((2 : ℝ) ^ m)⁻¹ * ∑ τ : Cube m, |g τ| ^ (2 : ℝ) :=
          mul_nonneg (by positivity) (Finset.sum_nonneg (fun _ _ => Real.rpow_nonneg (abs_nonneg _) _))
        conv_lhs => rw [hρn_sq]
        rw [← Real.mul_rpow (Real.rpow_nonneg hρn _) hexp_nn]
        congr 1
        rw [← mul_assoc, mul_comm ((ρ ^ n) ^ (2 : ℝ)), mul_assoc, Finset.mul_sum]
        congr 1
        refine Finset.sum_congr rfl (fun τ _ => ?_)
        rw [abs_mul, abs_of_nonneg hρn, Real.mul_rpow hρn (abs_nonneg _)]
      rw [hfactor]
      exact Real.rpow_le_rpow
        (mul_nonneg (by positivity) (Finset.sum_nonneg (fun _ _ => Real.rpow_nonneg (abs_nonneg _) _)))
        (mul_le_mul_of_nonneg_left hsum (by positivity))
        (by norm_num)
    have hbon := AuxLemma18.bonami_p_2 hρ0 hρ1 g
    have hlem11 := L1Sparsifiers.Main.lemma_11 g p hp1 hp2
    rw [← hα_eq] at hlem11
    have hchain : ρ ^ n * lpNorm 2 g ≤ α ^ (1 / p - 1 / 2) * lpNorm 2 g :=
      (hl2.trans hbon).trans hlem11
    have hρ_le : ρ ^ n ≤ α ^ (1 / p - 1 / 2) :=
      le_of_mul_le_mul_right hchain hnorm2_pos
    have hexp_val : 1 / p - 1 / 2 = (1 - ρ ^ 2) / (2 * (1 + ρ ^ 2)) := by
      simp only [p]; field_simp; ring
    rw [hexp_val] at hρ_le
    set q_exp : ℝ := 2 * (1 + ρ ^ 2) / (1 - ρ ^ 2)
    have hq_pos : 0 < q_exp := by
      have : 0 < 1 - ρ ^ 2 := by nlinarith
      positivity
    have hpow_q := Real.rpow_le_rpow (Real.rpow_nonneg hρ0.le _) hρ_le hq_pos.le
    rw [← Real.rpow_mul hρ0.le, ← Real.rpow_mul hα_pos.le] at hpow_q
    have hcancel : (1 - ρ ^ 2) / (2 * (1 + ρ ^ 2)) * q_exp = 1 := by
      simp only [q_exp]
      have h1 : 1 - ρ ^ 2 ≠ 0 := by nlinarith
      have h2 : 2 * (1 + ρ ^ 2) ≠ 0 := by positivity
      field_simp
    rw [hcancel, Real.rpow_one] at hpow_q
    rw [Real.rpow_def_of_pos hρ0] at hpow_q
    refine le_trans ?_ hpow_q
    apply Real.exp_le_exp.mpr
    have hlog_ge : -(1 - ρ) / ρ ≤ Real.log ρ := by
      have h := Real.one_sub_inv_le_log_of_pos hρ0
      have heq : 1 - ρ⁻¹ = -(1 - ρ) / ρ := by field_simp; ring
      linarith
    have hnq_nn : 0 ≤ n * q_exp := mul_nonneg hn hq_pos.le
    have hmul_log : -(1 - ρ) / ρ * (n * q_exp) ≤ Real.log ρ * (n * q_exp) :=
      mul_le_mul_of_nonneg_right hlog_ge hnq_nn
    have hsimp : -(1 - ρ) / ρ * (n * q_exp) = -2 * n * (1 + ρ ^ 2) / (ρ * (1 + ρ)) := by
      simp only [q_exp]
      have h1mp : 1 - ρ ≠ 0 := by linarith
      have h1pp : 1 + ρ ≠ 0 := by linarith
      have hdiff : 1 - ρ ^ 2 = (1 - ρ) * (1 + ρ) := by ring
      rw [hdiff]
      field_simp
    linarith
  by_contra hnot
  have hlt : α < Real.exp (-2 * n) := not_le.mp hnot
  have hlog_lt : Real.log α < -2 * n := by
    have := Real.log_lt_log hα_pos hlt
    rwa [Real.log_exp] at this
  by_cases hn0 : n = 0
  · subst hn0
    have hρ_half := hbound_ρ (1 / 2) (by norm_num) (by norm_num)
    norm_num at hρ_half hlt
    linarith
  have hn_pos : 0 < n := lt_of_le_of_ne hn (Ne.symm hn0)
  set δ : ℝ := (-2 * n - Real.log α) / (8 * n)
  have hδ_pos : 0 < δ := by
    simp only [δ]
    apply div_pos <;> linarith
  set ρ : ℝ := max (1 / 2) (1 / (1 + δ))
  have hρ0 : 0 < ρ := lt_of_lt_of_le (by norm_num) (le_max_left _ _)
  have hρ_δ : 1 / (1 + δ) ≤ ρ := le_max_right _ _
  have hρ1 : ρ < 1 := by
    apply max_lt (by norm_num)
    rw [div_lt_one (by linarith)]
    linarith
  have hα_ge := hbound_ρ ρ hρ0 hρ1
  have hlog_ge : -2 * n * (1 + ρ ^ 2) / (ρ * (1 + ρ)) ≤ Real.log α := by
    have := Real.log_le_log (Real.exp_pos _) hα_ge
    rwa [Real.log_exp] at this
  have hrat_le : (1 + ρ ^ 2) / (ρ * (1 + ρ)) ≤ 1 + δ := by
    have h1 : 1 + ρ ^ 2 ≤ 1 + ρ := by nlinarith
    have h2 : (1 + ρ ^ 2) / (ρ * (1 + ρ)) ≤ 1 / ρ := by
      rw [div_le_div_iff₀ (by positivity) hρ0]
      nlinarith
    have h3 : 1 / ρ ≤ 1 + δ := by
      rw [div_le_iff₀ hρ0]
      have := (div_le_iff₀ (by linarith : 0 < 1 + δ)).mp hρ_δ
      linarith
    exact h2.trans h3
  have hbound_fin : -2 * n * (1 + δ) ≤ -2 * n * (1 + ρ ^ 2) / (ρ * (1 + ρ)) := by
    have : -2 * n * (1 + ρ ^ 2) / (ρ * (1 + ρ)) = (-2 * n) * ((1 + ρ ^ 2) / (ρ * (1 + ρ))) := by ring
    rw [this]
    nlinarith
  have : -2 * n * (1 + δ) = -2 * n - (-2 * n - Real.log α) / 4 := by
    simp only [δ]
    field_simp [hn_pos.ne']
    ring
  linarith
