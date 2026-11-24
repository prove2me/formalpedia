-- Prove2me | solution 1 for KissingNumber.kissing_number_two
-- status  : ACCEPTED   (prove)
-- author  : @Secousses
-- created : 2026-11-24T00:36:42.84674+00:00
-- url     : https://prove2.me/submissions/388ece32-d944-4cc6-9e64-4f235a68b212

import Definitions.Def_KissingNumber
set_option autoImplicit false
open KissingNumber
open scoped InnerProductSpace

private lemma inner_two (x y : Ambient 2) : ⟪x, y⟫_ℝ = x 0 * y 0 + x 1 * y 1 := by
  simp [PiLp.inner_apply, Fin.sum_univ_two, mul_comm]

private lemma norm_sq_two (x : Ambient 2) : ‖x‖ ^ 2 = x 0 ^ 2 + x 1 ^ 2 := by
  rw [EuclideanSpace.norm_sq_eq, Fin.sum_univ_two, Real.norm_eq_abs, Real.norm_eq_abs, sq_abs, sq_abs]

/-- The point as a complex number. -/
private def toC (x : Ambient 2) : ℂ := ⟨x 0, x 1⟩

private lemma norm_toC (x : Ambient 2) (hx : ‖x‖ = 1) : ‖toC x‖ = 1 := by
  have h : ‖toC x‖ ^ 2 = 1 := by
    have h2 := norm_sq_two x
    rw [hx] at h2
    rw [Complex.sq_norm, Complex.normSq_mk]; simp only [toC]; nlinarith
  have := norm_nonneg (toC x)
  nlinarith

private lemma cos_arg_toC (x : Ambient 2) (hx : ‖x‖ = 1) : Real.cos (Complex.arg (toC x)) = x 0 := by
  have h0 : toC x ≠ 0 := by
    intro h; have := norm_toC x hx; rw [h, norm_zero] at this; norm_num at this
  rw [Complex.cos_arg h0, norm_toC x hx]; simp [toC]

private lemma sin_arg_toC (x : Ambient 2) (hx : ‖x‖ = 1) : Real.sin (Complex.arg (toC x)) = x 1 := by
  rw [Complex.sin_arg, norm_toC x hx]; simp [toC]

private lemma inner_eq_cos (x y : Ambient 2) (hx : ‖x‖ = 1) (hy : ‖y‖ = 1) :
    ⟪x, y⟫_ℝ = Real.cos (Complex.arg (toC x) - Complex.arg (toC y)) := by
  rw [Real.cos_sub, cos_arg_toC x hx, cos_arg_toC y hy, sin_arg_toC x hx, sin_arg_toC y hy,
    inner_two]

private noncomputable def bucket (x : Ambient 2) : ℤ := ⌈3 * Complex.arg (toC x) / Real.pi⌉

private lemma bucket_mem (x : Ambient 2) : bucket x ∈ Finset.Icc (-2 : ℤ) 3 := by
  have h1 := Complex.neg_pi_lt_arg (toC x)
  have h2 := Complex.arg_le_pi (toC x)
  have hp := Real.pi_pos
  rw [Finset.mem_Icc]
  constructor
  · have : (-3 : ℝ) < 3 * Complex.arg (toC x) / Real.pi := by
      rw [lt_div_iff₀ hp]; linarith
    have h := Int.lt_ceil.mpr (show ((-3 : ℤ) : ℝ) < 3 * Complex.arg (toC x) / Real.pi by
      push_cast; exact this)
    unfold bucket; omega
  · apply Int.ceil_le.mpr
    rw [div_le_iff₀ hp]; push_cast; linarith

private lemma close_of_bucket_eq (x y : Ambient 2) (h : bucket x = bucket y) :
    |Complex.arg (toC x) - Complex.arg (toC y)| < Real.pi / 3 := by
  have hp := Real.pi_pos
  set a := 3 * Complex.arg (toC x) / Real.pi
  set b := 3 * Complex.arg (toC y) / Real.pi
  have ha1 := Int.le_ceil a
  have ha2 := Int.ceil_lt_add_one a
  have hb1 := Int.le_ceil b
  have hb2 := Int.ceil_lt_add_one b
  have hab : |a - b| < 1 := by
    unfold bucket at h
    rw [abs_lt]
    have : (⌈a⌉ : ℝ) = ⌈b⌉ := by exact_mod_cast h
    constructor <;> linarith
  have e : Complex.arg (toC x) - Complex.arg (toC y) = (Real.pi / 3) * (a - b) := by
    simp only [a, b]; field_simp
  rw [e, abs_mul, abs_of_pos (by positivity)]
  have : 0 < Real.pi / 3 := by positivity
  nlinarith

private lemma card_le_six (C : KissingConfig 2) : C.points.card ≤ 6 := by
  by_contra hlt
  push Not at hlt
  have ht : (Finset.Icc (-2 : ℤ) 3).card = 6 := by simp
  obtain ⟨x, hx, y, hy, hne, hxy⟩ := Finset.exists_ne_map_eq_of_card_lt_of_maps_to
    (s := C.points) (t := Finset.Icc (-2 : ℤ) 3) (f := bucket) (by rw [ht]; exact hlt)
    (fun x _ => bucket_mem x)
  have hc := close_of_bucket_eq x y hxy
  have hin := C.inner_le x hx y hy hne
  rw [inner_eq_cos x y (C.unit_norm x hx) (C.unit_norm y hy), ← Real.cos_abs] at hin
  have hlt' : Real.cos (Real.pi / 3) < Real.cos |Complex.arg (toC x) - Complex.arg (toC y)| :=
    Real.cos_lt_cos_of_nonneg_of_le_pi (abs_nonneg _) (by linarith [Real.pi_pos]) hc
  rw [Real.cos_pi_div_three] at hlt'
  linarith

/-- The regular hexagon. -/
private noncomputable def hexC : Fin 6 → ℝ := ![1, 1 / 2, -1 / 2, -1, -1 / 2, 1 / 2]
private noncomputable def hexS : Fin 6 → ℝ :=
  ![0, Real.sqrt 3 / 2, Real.sqrt 3 / 2, 0, -(Real.sqrt 3 / 2), -(Real.sqrt 3 / 2)]
private noncomputable def hex (k : Fin 6) : Ambient 2 := !₂[hexC k, hexS k]

private lemma hex_inner (k l : Fin 6) : ⟪hex k, hex l⟫_ℝ = hexC k * hexC l + hexS k * hexS l := by
  rw [inner_two]; rfl

private lemma hex_inner_self (k : Fin 6) : ⟪hex k, hex k⟫_ℝ = 1 := by
  have h3 : Real.sqrt 3 * Real.sqrt 3 = 3 := Real.mul_self_sqrt (by norm_num)
  rw [hex_inner]
  fin_cases k <;> simp [hexC, hexS] <;> nlinarith

private lemma hex_inner_le (k l : Fin 6) (h : k ≠ l) : ⟪hex k, hex l⟫_ℝ ≤ 1 / 2 := by
  have h3 : Real.sqrt 3 * Real.sqrt 3 = 3 := Real.mul_self_sqrt (by norm_num)
  rw [hex_inner]
  fin_cases k <;> fin_cases l <;> simp [hexC, hexS] at h ⊢ <;> nlinarith [h3]

theorem solution : kissingNumber 2 = (6 : ℕ∞) := by
  have hinj : Set.InjOn hex (Finset.univ : Finset (Fin 6)) := by
    intro p _ q _ hpq
    by_contra hne
    have h1 := hex_inner_le p q hne
    rw [hpq, hex_inner_self q] at h1
    norm_num at h1
  let C : KissingConfig 2 :=
    { points := Finset.univ.image hex
      unit_norm := by
        intro x hx
        obtain ⟨p, -, rfl⟩ := Finset.mem_image.mp hx
        have h := hex_inner_self p
        rw [real_inner_self_eq_norm_sq] at h
        have h0 := norm_nonneg (hex p)
        nlinarith
      inner_le := by
        intro x hx y hy hxy
        obtain ⟨p, -, rfl⟩ := Finset.mem_image.mp hx
        obtain ⟨q, -, rfl⟩ := Finset.mem_image.mp hy
        exact hex_inner_le p q (fun h => hxy (by rw [h])) }
  have hcard : C.points.card = 6 := by
    show (Finset.univ.image hex).card = 6
    rw [Finset.card_image_of_injOn hinj, Finset.card_univ, Fintype.card_fin]
  apply le_antisymm
  · refine iSup_le fun D => ?_
    exact_mod_cast card_le_six D
  · have := le_iSup (fun C : KissingConfig 2 => (C.points.card : ℕ∞)) C
    simp only [hcard] at this
    exact_mod_cast this
