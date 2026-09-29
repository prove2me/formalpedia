-- Prove2me | solution 1 for LanglandsTunnell.RankinSelberg.integral_matrixTwo_eq_setIntegral_iwasawaInv_unconditional
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:08.670037+00:00
-- url     : https://prove2.me/submissions/2939701b-3c4f-57a6-be35-ec5e6b3b7391

import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.MeasureTheory.Function.Jacobian
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Analysis.SpecialFunctions.Complex.Arg
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_LanglandsTunnell_RankinSelberg_integral_matrixTwo_eq_setIntegral_iwasawaInv_unconditional

set_option autoImplicit false

open MeasureTheory

namespace Ws23K1A

abbrev P : Type := ℝ × ℝ × ℝ × ℝ

def coord : P ≃ₗ[ℝ] (Fin 4 → ℝ) where
  toFun p := ![p.1, p.2.1, p.2.2.1, p.2.2.2]
  invFun v := (v 0, v 1, v 2, v 3)
  map_add' p q := by ext i; fin_cases i <;> rfl
  map_smul' c p := by ext i; fin_cases i <;> rfl
  left_inv p := rfl
  right_inv v := by ext i; fin_cases i <;> rfl

theorem coord_apply (p : P) : coord p = ![p.1, p.2.1, p.2.2.1, p.2.2.2] := rfl
theorem coord_symm_apply (v : Fin 4 → ℝ) : coord.symm v = (v 0, v 1, v 2, v 3) := rfl

def mat4 (f : P →ₗ[ℝ] P) : Matrix (Fin 4) (Fin 4) ℝ := Matrix.of fun i j => coord (f (coord.symm (Pi.single j 1))) i

theorem det_eq_det_mat4 (f : P →ₗ[ℝ] P) : LinearMap.det f = (mat4 f).det := by
  rw [← LinearMap.det_conj f coord, ← LinearMap.det_toMatrix']
  congr 1

theorem det_fin_four (A : Matrix (Fin 4) (Fin 4) ℝ) :
    A.det =
      A 0 0 * (A 1 1 * A 2 2 * A 3 3 - A 1 1 * A 2 3 * A 3 2 - A 1 2 * A 2 1 * A 3 3 + A 1 2 * A 2 3 * A 3 1 + A 1 3 * A 2 1 * A 3 2 - A 1 3 * A 2 2 * A 3 1)
      - A 0 1 * (A 1 0 * A 2 2 * A 3 3 - A 1 0 * A 2 3 * A 3 2 - A 1 2 * A 2 0 * A 3 3 + A 1 2 * A 2 3 * A 3 0 + A 1 3 * A 2 0 * A 3 2 - A 1 3 * A 2 2 * A 3 0)
      + A 0 2 * (A 1 0 * A 2 1 * A 3 3 - A 1 0 * A 2 3 * A 3 1 - A 1 1 * A 2 0 * A 3 3 + A 1 1 * A 2 3 * A 3 0 + A 1 3 * A 2 0 * A 3 1 - A 1 3 * A 2 1 * A 3 0)
      - A 0 3 * (A 1 0 * A 2 1 * A 3 2 - A 1 0 * A 2 2 * A 3 1 - A 1 1 * A 2 0 * A 3 2 + A 1 1 * A 2 2 * A 3 0 + A 1 2 * A 2 0 * A 3 1 - A 1 2 * A 2 1 * A 3 0) := by
  rw [Matrix.det_succ_row_zero]
  simp [Fin.sum_univ_succ, Matrix.det_fin_three, Matrix.submatrix, Fin.succAbove]
  ring

def π₁ : P →L[ℝ] ℝ := ContinuousLinearMap.fst ℝ ℝ (ℝ × ℝ × ℝ)
def π₂ : P →L[ℝ] ℝ := (ContinuousLinearMap.fst ℝ ℝ (ℝ × ℝ)).comp (ContinuousLinearMap.snd ℝ ℝ (ℝ × ℝ × ℝ))
def π₃ : P →L[ℝ] ℝ :=
  (ContinuousLinearMap.fst ℝ ℝ ℝ).comp ((ContinuousLinearMap.snd ℝ ℝ (ℝ × ℝ)).comp (ContinuousLinearMap.snd ℝ ℝ (ℝ × ℝ × ℝ)))
def π₄ : P →L[ℝ] ℝ :=
  (ContinuousLinearMap.snd ℝ ℝ ℝ).comp ((ContinuousLinearMap.snd ℝ ℝ (ℝ × ℝ)).comp (ContinuousLinearMap.snd ℝ ℝ (ℝ × ℝ × ℝ)))

@[scoped simp] theorem π₁_apply (p : P) : π₁ p = p.1 := rfl
@[scoped simp] theorem π₂_apply (p : P) : π₂ p = p.2.1 := rfl
@[scoped simp] theorem π₃_apply (p : P) : π₃ p = p.2.2.1 := rfl
@[scoped simp] theorem π₄_apply (p : P) : π₄ p = p.2.2.2 := rfl

theorem hasFDerivAt_π₁ (p : P) : HasFDerivAt (fun q : P => q.1) π₁ p := hasFDerivAt_fst
theorem hasFDerivAt_π₂ (p : P) : HasFDerivAt (fun q : P => q.2.1) π₂ p := hasFDerivAt_fst.comp p hasFDerivAt_snd
theorem hasFDerivAt_π₃ (p : P) : HasFDerivAt (fun q : P => q.2.2.1) π₃ p :=
  hasFDerivAt_fst.comp p (hasFDerivAt_snd.comp p hasFDerivAt_snd)
theorem hasFDerivAt_π₄ (p : P) : HasFDerivAt (fun q : P => q.2.2.2) π₄ p :=
  hasFDerivAt_snd.comp p (hasFDerivAt_snd.comp p hasFDerivAt_snd)

noncomputable def Φ (p : P) : P :=
  (Real.cos p.2.2.2 / p.2.1,
    (-(p.1 * Real.cos p.2.2.2) / p.2.1 + Real.sin p.2.2.2 / p.2.2.1,
      (-(Real.sin p.2.2.2) / p.2.1, p.1 * Real.sin p.2.2.2 / p.2.1 + Real.cos p.2.2.2 / p.2.2.1)))

noncomputable def Φ' (p : P) : P →L[ℝ] P :=
  let x := p.1; let y₁ := p.2.1; let y₂ := p.2.2.1; let c := Real.cos p.2.2.2; let s := Real.sin p.2.2.2
  ((-(c / y₁ ^ 2)) • π₂ + (-(s / y₁)) • π₄).prod
    (((-(c / y₁)) • π₁ + (x * c / y₁ ^ 2) • π₂ + (-(s / y₂ ^ 2)) • π₃ + (x * s / y₁ + c / y₂) • π₄).prod
      (((s / y₁ ^ 2) • π₂ + (-(c / y₁)) • π₄).prod
        ((s / y₁) • π₁ + (-(x * s / y₁ ^ 2)) • π₂ + (-(c / y₂ ^ 2)) • π₃ + (x * c / y₁ - s / y₂) • π₄)))

theorem hasFDerivAt_Φ {p : P} (h₁ : p.2.1 ≠ 0) (h₂ : p.2.2.1 ≠ 0) : HasFDerivAt Φ (Φ' p) p := by
  have hx := hasFDerivAt_π₁ p
  have hy₁ := hasFDerivAt_π₂ p
  have hy₂ := hasFDerivAt_π₃ p
  have hθ := hasFDerivAt_π₄ p
  have hc := (Real.hasDerivAt_cos p.2.2.2).comp_hasFDerivAt p hθ
  have hs := (Real.hasDerivAt_sin p.2.2.2).comp_hasFDerivAt p hθ
  have hi₁ := (hasDerivAt_inv h₁).comp_hasFDerivAt p hy₁
  have hi₂ := (hasDerivAt_inv h₂).comp_hasFDerivAt p hy₂
  have hall := (hc.fun_mul hi₁).prodMk ((((hx.fun_mul hc).fun_neg.fun_mul hi₁).fun_add (hs.fun_mul hi₂)).prodMk
    ((hs.fun_neg.fun_mul hi₁).prodMk (((hx.fun_mul hs).fun_mul hi₁).fun_add (hc.fun_mul hi₂))))
  convert hall using 2 <;> try with_reducible_and_instances rfl
  · first | rfl | (simp only [Φ, Function.comp_apply, div_eq_mul_inv]; ring_nf)
  refine ContinuousLinearMap.ext fun v => ?_
  obtain ⟨a, b, d, t⟩ := v
  simp only [Φ']
  simp only [ContinuousLinearMap.prod_apply, ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply,
    ContinuousLinearMap.neg_apply, π₁_apply, π₂_apply, π₃_apply, π₄_apply, smul_eq_mul, Prod.mk.injEq,
    Pi.mul_apply, Pi.neg_apply, Function.comp_apply]
  refine ⟨?_, ?_, ?_, ?_⟩ <;> field_simp <;> ring

theorem Φ'_apply (p : P) (v : P) : Φ' p v =
    (-(Real.cos p.2.2.2 / p.2.1 ^ 2) * v.2.1 + -(Real.sin p.2.2.2 / p.2.1) * v.2.2.2,
      (-(Real.cos p.2.2.2 / p.2.1) * v.1 + p.1 * Real.cos p.2.2.2 / p.2.1 ^ 2 * v.2.1 + -(Real.sin p.2.2.2 / p.2.2.1 ^ 2) * v.2.2.1 +
          (p.1 * Real.sin p.2.2.2 / p.2.1 + Real.cos p.2.2.2 / p.2.2.1) * v.2.2.2,
        (Real.sin p.2.2.2 / p.2.1 ^ 2 * v.2.1 + -(Real.cos p.2.2.2 / p.2.1) * v.2.2.2,
          Real.sin p.2.2.2 / p.2.1 * v.1 + -(p.1 * Real.sin p.2.2.2 / p.2.1 ^ 2) * v.2.1 + -(Real.cos p.2.2.2 / p.2.2.1 ^ 2) * v.2.2.1 +
            (p.1 * Real.cos p.2.2.2 / p.2.1 - Real.sin p.2.2.2 / p.2.2.1) * v.2.2.2))) := by
  simp only [Φ', ContinuousLinearMap.prod_apply, ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply,
    π₁_apply, π₂_apply, π₃_apply, π₄_apply, smul_eq_mul]

theorem mat4_Φ' (p : P) : mat4 (Φ' p : P →ₗ[ℝ] P) =
    !![0, -(Real.cos p.2.2.2 / p.2.1 ^ 2), 0, -(Real.sin p.2.2.2 / p.2.1);
       -(Real.cos p.2.2.2 / p.2.1), p.1 * Real.cos p.2.2.2 / p.2.1 ^ 2, -(Real.sin p.2.2.2 / p.2.2.1 ^ 2), p.1 * Real.sin p.2.2.2 / p.2.1 + Real.cos p.2.2.2 / p.2.2.1;
       0, Real.sin p.2.2.2 / p.2.1 ^ 2, 0, -(Real.cos p.2.2.2 / p.2.1);
       Real.sin p.2.2.2 / p.2.1, -(p.1 * Real.sin p.2.2.2 / p.2.1 ^ 2), -(Real.cos p.2.2.2 / p.2.2.1 ^ 2), p.1 * Real.cos p.2.2.2 / p.2.1 - Real.sin p.2.2.2 / p.2.2.1] := by
  ext i j
  simp only [mat4, Matrix.of_apply, ContinuousLinearMap.coe_coe, Φ'_apply, coord_symm_apply, coord_apply]
  fin_cases i <;> fin_cases j <;> simp

theorem det_Φ' {p : P} (h₁ : p.2.1 ≠ 0) (h₂ : p.2.2.1 ≠ 0) :
    (Φ' p).det = (p.2.1 ^ 4 * p.2.2.1 ^ 2)⁻¹ := by
  have hsc := Real.sin_sq_add_cos_sq p.2.2.2
  have key : (Φ' p).det = (Real.sin p.2.2.2 ^ 2 + Real.cos p.2.2.2 ^ 2) ^ 2 * (p.2.1 ^ 4 * p.2.2.1 ^ 2)⁻¹ := by
    rw [ContinuousLinearMap.det, det_eq_det_mat4, mat4_Φ', det_fin_four]
    simp only [Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.empty_val',
      Matrix.cons_val_fin_one, Matrix.cons_val_two, Matrix.cons_val_three,
      Matrix.vecHead, Matrix.vecTail, Function.comp_apply, Fin.succ_zero_eq_one, Fin.succ_one_eq_two]
    field_simp
    ring
  rw [key, hsc, one_pow, one_mul]

def dom : Set P := {p | p.2.1 ≠ 0 ∧ 0 < p.2.2.1 ∧ p.2.2.2 ∈ Set.Ioo 0 (2 * Real.pi)}

theorem isOpen_dom : IsOpen dom := by
  refine (isOpen_ne_fun (continuous_fst.comp continuous_snd) continuous_const).inter
    ((isOpen_lt continuous_const (continuous_fst.comp (continuous_snd.comp continuous_snd))).inter ?_)
  exact isOpen_Ioo.preimage (continuous_snd.comp (continuous_snd.comp continuous_snd))

theorem measurableSet_dom : MeasurableSet dom := isOpen_dom.measurableSet

theorem angle_eq_of_cos_eq_of_sin_eq {a b : ℝ} (ha : a ∈ Set.Ioo 0 (2 * Real.pi)) (hb : b ∈ Set.Ioo 0 (2 * Real.pi))
    (hc : Real.cos a = Real.cos b) (hs : Real.sin a = Real.sin b) : a = b := by
  have h : Complex.exp (a * Complex.I) = Complex.exp (b * Complex.I) := by
    rw [Complex.exp_mul_I, Complex.exp_mul_I, ← Complex.ofReal_cos, ← Complex.ofReal_sin, ← Complex.ofReal_cos,
      ← Complex.ofReal_sin, hc, hs]
  obtain ⟨n, hn⟩ := Complex.exp_eq_exp_iff_exists_int.1 h
  have hr : a = b + n * (2 * Real.pi) := by
    have := congrArg Complex.im hn
    simp at this
    linarith
  have hn0 : n = 0 := by
    have h1 : (n : ℝ) * (2 * Real.pi) < 2 * Real.pi := by linarith [ha.2, hb.1]
    have h2 : -(2 * Real.pi) < (n : ℝ) * (2 * Real.pi) := by linarith [ha.1, hb.2]
    have h1' : (n : ℝ) < 1 := by nlinarith [Real.pi_pos]
    have h2' : (-1 : ℝ) < n := by nlinarith [Real.pi_pos]
    have : (-1 : ℤ) < n := by exact_mod_cast h2'
    have : n < (1 : ℤ) := by exact_mod_cast h1'
    omega
  rw [hr, hn0]; simp

theorem Φ_det (p : P) (h₁ : p.2.1 ≠ 0) (h₂ : p.2.2.1 ≠ 0) :
    (Φ p).1 * (Φ p).2.2.2 - (Φ p).2.1 * (Φ p).2.2.1 = (p.2.1 * p.2.2.1)⁻¹ := by
  have hsc := Real.sin_sq_add_cos_sq p.2.2.2
  simp only [Φ]
  field_simp
  linear_combination p.2.1 * hsc

theorem Φ_colnorm (p : P) (h₁ : p.2.1 ≠ 0) :
    (Φ p).1 ^ 2 + (Φ p).2.2.1 ^ 2 = (p.2.1 ^ 2)⁻¹ := by
  have hsc := Real.sin_sq_add_cos_sq p.2.2.2
  simp only [Φ]
  field_simp
  linear_combination hsc

theorem injOn_Φ : Set.InjOn Φ dom := by
  rintro ⟨x, y₁, y₂, θ⟩ ⟨hy₁, hy₂, hθ⟩ ⟨x', y₁', y₂', θ'⟩ ⟨hy₁', hy₂', hθ'⟩ heq
  simp only at hy₁ hy₂ hθ hy₁' hy₂' hθ'
  have hd := Φ_det (x, y₁, y₂, θ) hy₁ hy₂.ne'
  have hd' := Φ_det (x', y₁', y₂', θ') hy₁' hy₂'.ne'
  have hn := Φ_colnorm (x, y₁, y₂, θ) hy₁
  have hn' := Φ_colnorm (x', y₁', y₂', θ') hy₁'
  rw [heq] at hd hn
  simp only at hd hd' hn hn'

  have hsq : y₁ ^ 2 = y₁' ^ 2 := by
    have := hn.symm.trans hn'; rwa [inv_inj] at this
  have hprod : y₁ * y₂ = y₁' * y₂' := by
    have := hd.symm.trans hd'; rwa [inv_inj] at this
  have hy₁eq : y₁ = y₁' := by
    rcases sq_eq_sq_iff_eq_or_eq_neg.1 hsq with h | h
    · exact h
    · exfalso
      rw [h] at hprod
      have : y₁' * (y₂ + y₂') = 0 := by linarith
      rcases mul_eq_zero.1 this with h0 | h0
      · exact hy₁' h0
      · linarith
  subst hy₁eq
  have hy₂eq : y₂ = y₂' := by
    have := mul_left_cancel₀ hy₁ hprod; exact this
  subst hy₂eq

  have hΦ := heq
  simp only [Φ, Prod.mk.injEq] at hΦ
  obtain ⟨e00, e01, e10, e11⟩ := hΦ
  have hc : Real.cos θ = Real.cos θ' := by
    field_simp at e00; linarith
  have hs : Real.sin θ = Real.sin θ' := by
    field_simp at e10; linarith
  have hθeq := angle_eq_of_cos_eq_of_sin_eq hθ hθ' hc hs
  subst hθeq

  have hx : x = x' := by
    have hsc := Real.sin_sq_add_cos_sq θ
    field_simp at e01 e11
    have h1 : Real.cos θ * (y₂ * (x - x')) = 0 := by linear_combination (-1 : ℝ) * e01
    have h2 : Real.sin θ * (y₂ * (x - x')) = 0 := by linear_combination e11
    have h3 : y₂ * (x - x') = 0 := by linear_combination Real.cos θ * h1 + Real.sin θ * h2 - (y₂ * (x - x')) * hsc
    rcases mul_eq_zero.1 h3 with h | h
    · exact absurd h hy₂.ne'
    · linarith
  subst hx
  rfl

def good : Set P := {q | q.2.2.1 ≠ 0 ∧ q.2.2.2 ≠ 0 ∧ q.1 * q.2.2.2 - q.2.1 * q.2.2.1 ≠ 0}

theorem good_subset_image : good ⊆ Φ '' dom := by
  rintro ⟨a, b, c, d⟩ ⟨hc, hd, hdet⟩
  simp only at hc hd hdet
  set r : ℝ := Real.sqrt (a ^ 2 + c ^ 2) with hr
  have hr0 : 0 < r := Real.sqrt_pos.2 (by positivity)
  have hr2 : r ^ 2 = a ^ 2 + c ^ 2 := Real.sq_sqrt (by positivity)
  set δ : ℝ := a * d - b * c with hδ
  set σ : ℝ := if 0 < δ then 1 else -1 with hσ
  have hσ2 : σ ^ 2 = 1 := by rw [hσ]; split_ifs <;> norm_num
  have hσδ : σ * δ = |δ| := by
    rw [hσ]; split_ifs with h
    · rw [one_mul, abs_of_pos h]
    · rw [neg_one_mul, abs_of_nonpos (le_of_not_gt h)]
  have hδabs : 0 < |δ| := abs_pos.2 hdet

  set ζ : ℂ := ⟨σ * a / r, -(σ * c) / r⟩ with hζ
  have hζn : Complex.normSq ζ = 1 := by
    simp only [hζ, Complex.normSq_mk]
    field_simp
    linear_combination (a ^ 2 + c ^ 2) * hσ2 - hr2
  have hζ0 : ζ ≠ 0 := fun h => by rw [h, Complex.normSq_zero] at hζn; exact zero_ne_one hζn
  have hζabs : ‖ζ‖ = 1 := by
    rw [Complex.norm_def, hζn, Real.sqrt_one]
  set θ₀ : ℝ := Complex.arg ζ with hθ₀
  have hcos0 : Real.cos θ₀ = σ * a / r := by rw [hθ₀, Complex.cos_arg hζ0, hζabs, div_one]
  have hsin0 : Real.sin θ₀ = -(σ * c) / r := by rw [hθ₀, Complex.sin_arg, hζabs, div_one]
  have hsin0ne : Real.sin θ₀ ≠ 0 := by
    rw [hsin0]
    have : σ ≠ 0 := by rw [hσ]; split_ifs <;> norm_num
    exact div_ne_zero (neg_ne_zero.2 (mul_ne_zero this hc)) hr0.ne'
  set θ : ℝ := if 0 < θ₀ then θ₀ else θ₀ + 2 * Real.pi with hθdef
  have hcos : Real.cos θ = σ * a / r := by
    rw [hθdef]; split_ifs
    · exact hcos0
    · rw [Real.cos_add_two_pi]; exact hcos0
  have hsin : Real.sin θ = -(σ * c) / r := by
    rw [hθdef]; split_ifs
    · exact hsin0
    · rw [Real.sin_add_two_pi]; exact hsin0
  have hθmem : θ ∈ Set.Ioo 0 (2 * Real.pi) := by
    have hle : θ₀ ≤ Real.pi := Complex.arg_le_pi ζ
    have hgt : -Real.pi < θ₀ := Complex.neg_pi_lt_arg ζ
    rw [hθdef]; split_ifs with h
    · exact ⟨h, by linarith [Real.pi_pos]⟩
    · refine ⟨by linarith, ?_⟩
      have : θ₀ ≠ 0 := fun h0 => by rw [h0, Real.sin_zero] at hsin0ne; exact hsin0ne rfl
      rcases lt_or_gt_of_ne this with hlt | hgt'
      · linarith
      · exact absurd hgt' h

  refine ⟨(-(a * b + c * d) / r ^ 2, (σ * r)⁻¹, r / |δ|, θ), ⟨?_, by positivity, hθmem⟩, ?_⟩
  · have : σ ≠ 0 := by rw [hσ]; split_ifs <;> norm_num
    exact inv_ne_zero (mul_ne_zero this hr0.ne')
  · have hσne : σ ≠ 0 := by rw [hσ]; split_ifs <;> norm_num
    have habs : |δ| = σ * (a * d - b * c) := by rw [← hδ, hσδ]
    simp only [Φ, hcos, hsin, Prod.mk.injEq]
    refine ⟨?_, ?_, ?_, ?_⟩
    · field_simp
      linear_combination a * hσ2
    · rw [habs]
      field_simp
      linear_combination (b * (a ^ 2 + c ^ 2)) * hσ2 - b * hr2
    · field_simp
      linear_combination hσ2
    · rw [habs]
      field_simp
      linear_combination (d * (a ^ 2 + c ^ 2)) * hσ2 - d * hr2

scoped instance instHaar2 : (volume : Measure (ℝ × ℝ)).IsAddHaarMeasure := Measure.prod.instIsAddHaarMeasure _ _
scoped instance instHaar3 : (volume : Measure (ℝ × ℝ × ℝ)).IsAddHaarMeasure := Measure.prod.instIsAddHaarMeasure _ _
scoped instance instHaar4 : (volume : Measure P).IsAddHaarMeasure := Measure.prod.instIsAddHaarMeasure _ _

theorem volume_univ_prod_null {α : Type*} [MeasureSpace α] [SFinite (volume : Measure α)] {s : Set α} (hs : volume s = 0) :
    volume ((Set.univ : Set ℝ) ×ˢ s) = 0 := by
  rw [Measure.volume_eq_prod, Measure.prod_prod, hs, mul_zero]

theorem volume_null_y₁ : volume {q : P | q.2.1 = 0} = 0 := by
  have : {q : P | q.2.1 = 0} = (Set.univ : Set ℝ) ×ˢ (({0} : Set ℝ) ×ˢ (Set.univ : Set (ℝ × ℝ))) := by
    ext q; simp
  rw [this]
  refine volume_univ_prod_null ?_
  rw [Measure.volume_eq_prod, Measure.prod_prod, Real.volume_singleton, zero_mul]

theorem volume_null_e₁₀ : volume {q : P | q.2.2.1 = 0} = 0 := by
  have : {q : P | q.2.2.1 = 0} = (Set.univ : Set ℝ) ×ˢ ((Set.univ : Set ℝ) ×ˢ (({0} : Set ℝ) ×ˢ (Set.univ : Set ℝ))) := by
    ext q; simp
  rw [this]
  refine volume_univ_prod_null (volume_univ_prod_null ?_)
  rw [Measure.volume_eq_prod, Measure.prod_prod, Real.volume_singleton, zero_mul]

theorem volume_null_last (a : ℝ) : volume {q : P | q.2.2.2 = a} = 0 := by
  have : {q : P | q.2.2.2 = a} = (Set.univ : Set ℝ) ×ˢ ((Set.univ : Set ℝ) ×ˢ ((Set.univ : Set ℝ) ×ˢ ({a} : Set ℝ))) := by
    ext q; simp
  rw [this]
  refine volume_univ_prod_null (volume_univ_prod_null ?_)
  rw [Measure.volume_eq_prod, Measure.prod_prod, Real.volume_singleton, mul_zero]

theorem volume_null_graph : volume {q : P | q.2.2.2 ≠ 0 ∧ q.1 = q.2.1 * q.2.2.1 / q.2.2.2} = 0 := by
  have hmeas : MeasurableSet {q : P | q.2.2.2 ≠ 0 ∧ q.1 = q.2.1 * q.2.2.1 / q.2.2.2} := by
    refine (measurableSet_eq_fun (measurable_snd.comp (measurable_snd.comp measurable_snd)) measurable_const).compl.inter ?_
    exact measurableSet_eq_fun measurable_fst
      (((measurable_fst.comp measurable_snd).mul (measurable_fst.comp (measurable_snd.comp measurable_snd))).div
        (measurable_snd.comp (measurable_snd.comp measurable_snd)))
  rw [Measure.volume_eq_prod, Measure.prod_apply_symm hmeas]
  refine lintegral_eq_zero_of_ae_eq_zero (ae_of_all _ fun w => ?_)
  simp only [Set.preimage_setOf_eq, Pi.zero_apply]
  refine measure_mono_null (t := {w.1 * w.2.1 / w.2.2}) (fun a ha => ?_) Real.volume_singleton
  exact ha.2

theorem compl_good_null : volume goodᶜ = 0 := by
  refine measure_mono_null (t := {q : P | q.2.2.1 = 0} ∪ {q : P | q.2.2.2 = 0} ∪
    {q : P | q.2.2.2 ≠ 0 ∧ q.1 = q.2.1 * q.2.2.1 / q.2.2.2}) ?_ ?_
  · intro q hq
    simp only [good, Set.mem_compl_iff, Set.mem_setOf_eq, not_and_or, not_not] at hq
    simp only [Set.mem_union, Set.mem_setOf_eq]
    rcases hq with h | h | h
    · exact Or.inl (Or.inl h)
    · exact Or.inl (Or.inr h)
    · by_cases h4 : q.2.2.2 = 0
      · exact Or.inl (Or.inr h4)
      · right; refine ⟨h4, ?_⟩; field_simp; linarith
  · rw [measure_union_null_iff, measure_union_null_iff]
    exact ⟨⟨volume_null_e₁₀, volume_null_last 0⟩, volume_null_graph⟩

theorem image_ae_eq_univ : Φ '' dom =ᵐ[volume] (Set.univ : Set P) := by
  rw [ae_eq_univ]
  exact measure_mono_null (Set.compl_subset_compl.2 good_subset_image) compl_good_null

def region : Set P := Set.univ ×ˢ (Set.univ ×ˢ (Set.Ioi (0 : ℝ) ×ˢ Set.Ioc (0 : ℝ) (2 * Real.pi)))

theorem dom_ae_eq_region : dom =ᵐ[volume] region := by
  have hsub : dom ⊆ region := fun q hq => ⟨trivial, trivial, hq.2.1, hq.2.2.1, hq.2.2.2.le⟩
  have hdiff : region \ dom ⊆ {q : P | q.2.1 = 0} ∪ {q : P | q.2.2.2 = 2 * Real.pi} := by
    rintro q ⟨⟨-, -, h2, h3, h4⟩, hnot⟩
    by_contra hcon
    simp only [Set.mem_union, Set.mem_setOf_eq, not_or] at hcon
    exact hnot ⟨hcon.1, h2, h3, lt_of_le_of_ne h4 hcon.2⟩
  refine (ae_eq_set).2 ⟨?_, ?_⟩
  · rw [Set.diff_eq_empty.2 hsub]; exact measure_empty
  · exact measure_mono_null hdiff (measure_union_null_iff.2 ⟨volume_null_y₁, volume_null_last _⟩)

theorem measurableSet_region : MeasurableSet region :=
  MeasurableSet.univ.prod (MeasurableSet.univ.prod (measurableSet_Ioi.prod measurableSet_Ioc))

abbrev M : Type := Fin 2 → Fin 2 → ℝ

def T : M ≃ᵐ P :=
  (MeasurableEquiv.finTwoArrow.trans (MeasurableEquiv.prodCongr MeasurableEquiv.finTwoArrow MeasurableEquiv.finTwoArrow)).trans
    MeasurableEquiv.prodAssoc

theorem T_apply (e : M) : T e = (e 0 0, e 0 1, e 1 0, e 1 1) := rfl

theorem T_symm_apply (q : P) : T.symm q = fun i j => (!![q.1, q.2.1; q.2.2.1, q.2.2.2] : Matrix (Fin 2) (Fin 2) ℝ) i j := by
  apply T.injective
  rw [MeasurableEquiv.apply_symm_apply, T_apply]
  simp

theorem measurePreserving_T : MeasurePreserving T volume volume := by
  have h1 := volume_preserving_finTwoArrow (Fin 2 → ℝ)
  have h2 : MeasurePreserving (MeasurableEquiv.prodCongr (MeasurableEquiv.finTwoArrow (α := ℝ)) (MeasurableEquiv.finTwoArrow (α := ℝ)))
      (volume : Measure ((Fin 2 → ℝ) × (Fin 2 → ℝ))) (volume : Measure ((ℝ × ℝ) × (ℝ × ℝ))) :=
    (volume_preserving_finTwoArrow ℝ).prod (volume_preserving_finTwoArrow ℝ)
  have h3 : MeasurePreserving (MeasurableEquiv.prodAssoc : (ℝ × ℝ) × (ℝ × ℝ) ≃ᵐ P) volume volume :=
    measurePreserving_prodAssoc volume volume volume
  exact h3.comp (h2.comp h1)

noncomputable def H (F : M → ℂ) (p : P) : ℂ :=
  F (fun i j => (!![Real.cos p.2.2.2 / p.2.1, -(p.1 * Real.cos p.2.2.2) / p.2.1 + Real.sin p.2.2.2 / p.2.2.1;
                  -(Real.sin p.2.2.2) / p.2.1, p.1 * Real.sin p.2.2.2 / p.2.1 + Real.cos p.2.2.2 / p.2.2.1] : Matrix (Fin 2) (Fin 2) ℝ) i j) *
    ((p.2.2.1 ^ 2 * (|p.2.1 * p.2.2.1| ^ 4)⁻¹ : ℝ) : ℂ)

theorem hderiv : ∀ p ∈ dom, HasFDerivWithinAt Φ (Φ' p) dom p :=
  fun _ hp => (hasFDerivAt_Φ hp.1 hp.2.1.ne').hasFDerivWithinAt

theorem jacobian_smul_eq (F : M → ℂ) {p : P} (hp : p ∈ dom) :
    |(Φ' p).det| • F (T.symm (Φ p)) = H F p := by
  have h₁ : p.2.1 ≠ 0 := hp.1
  have h₂ : p.2.2.1 ≠ 0 := hp.2.1.ne'
  rw [det_Φ' h₁ h₂, T_symm_apply, H, Complex.real_smul, mul_comm]
  have habs : |(p.2.1 ^ 4 * p.2.2.1 ^ 2)⁻¹| = p.2.2.1 ^ 2 * (|p.2.1 * p.2.2.1| ^ 4)⁻¹ := by
    rw [abs_inv, abs_mul, abs_pow, abs_pow, abs_mul, mul_pow]
    have : |p.2.2.1| ^ 4 = |p.2.2.1| ^ 2 * p.2.2.1 ^ 2 := by rw [← sq_abs p.2.2.1]; ring
    rw [this]
    field_simp
  rw [habs]
  rfl

theorem integral_eq (F : M → ℂ) : (∫ e, F e) = ∫ p in region, H F p := by
  have hT := measurePreserving_T.symm T
  rw [← hT.integral_comp T.symm.measurableEmbedding, ← setIntegral_univ, ← setIntegral_congr_set image_ae_eq_univ,
    integral_image_eq_integral_abs_det_fderiv_smul volume measurableSet_dom hderiv injOn_Φ,
    ← setIntegral_congr_set dom_ae_eq_region]
  exact setIntegral_congr_fun measurableSet_dom fun p hp => jacobian_smul_eq F hp

theorem integrable_iff (F : M → ℂ) : Integrable F ↔ IntegrableOn (H F) region := by
  have hT := measurePreserving_T.symm T
  rw [← hT.integrable_comp_emb T.symm.measurableEmbedding, ← integrableOn_univ]
  rw [show IntegrableOn (F ∘ T.symm) Set.univ volume ↔ IntegrableOn (F ∘ T.symm) (Φ '' dom) volume from
    ⟨fun h => h.congr_set_ae image_ae_eq_univ, fun h => h.congr_set_ae image_ae_eq_univ.symm⟩,
    integrableOn_image_iff_integrableOn_abs_det_fderiv_smul volume measurableSet_dom hderiv injOn_Φ]
  rw [show IntegrableOn (fun x => |(Φ' x).det| • (F ∘ ⇑T.symm) (Φ x)) dom volume ↔ IntegrableOn (H F) dom volume from
    integrableOn_congr_fun (fun p hp => jacobian_smul_eq F hp) measurableSet_dom]
  exact ⟨fun h => h.congr_set_ae dom_ae_eq_region.symm, fun h => h.congr_set_ae dom_ae_eq_region⟩

end Ws23K1A
p2m_reactivate "P2MW.S_LanglandsTunnell_RankinSelberg_integral_matrixTwo_eq_setIntegral_iwasawaInv_unconditional.Ws23K1A"

open Ws23K1A in
theorem solution
    (F : (Fin 2 → Fin 2 → ℝ) → ℂ) :
    (Integrable F ↔ IntegrableOn
        (fun p : ℝ × ℝ × ℝ × ℝ =>
          F (fun i j => (!![Real.cos p.2.2.2 / p.2.1, -(p.1 * Real.cos p.2.2.2) / p.2.1 + Real.sin p.2.2.2 / p.2.2.1;
                          -(Real.sin p.2.2.2) / p.2.1, p.1 * Real.sin p.2.2.2 / p.2.1 + Real.cos p.2.2.2 / p.2.2.1] : Matrix (Fin 2) (Fin 2) ℝ) i j) *
            ((p.2.2.1 ^ 2 * (|p.2.1 * p.2.2.1| ^ 4)⁻¹ : ℝ) : ℂ))
        (Set.univ ×ˢ (Set.univ ×ˢ (Set.Ioi (0 : ℝ) ×ˢ Set.Ioc (0 : ℝ) (2 * Real.pi))))) ∧
    (∫ e : Fin 2 → Fin 2 → ℝ, F e) =
      ∫ p : ℝ × ℝ × ℝ × ℝ in Set.univ ×ˢ (Set.univ ×ˢ (Set.Ioi (0 : ℝ) ×ˢ Set.Ioc (0 : ℝ) (2 * Real.pi))),
        F (fun i j => (!![Real.cos p.2.2.2 / p.2.1, -(p.1 * Real.cos p.2.2.2) / p.2.1 + Real.sin p.2.2.2 / p.2.2.1;
                        -(Real.sin p.2.2.2) / p.2.1, p.1 * Real.sin p.2.2.2 / p.2.1 + Real.cos p.2.2.2 / p.2.2.1] : Matrix (Fin 2) (Fin 2) ℝ) i j) *
          ((p.2.2.1 ^ 2 * (|p.2.1 * p.2.2.1| ^ 4)⁻¹ : ℝ) : ℂ) :=
  ⟨Ws23K1A.integrable_iff F, Ws23K1A.integral_eq F⟩

#print axioms solution

end S_LanglandsTunnell_RankinSelberg_integral_matrixTwo_eq_setIntegral_iwasawaInv_unconditional
end P2MW
export P2MW.S_LanglandsTunnell_RankinSelberg_integral_matrixTwo_eq_setIntegral_iwasawaInv_unconditional (solution)
