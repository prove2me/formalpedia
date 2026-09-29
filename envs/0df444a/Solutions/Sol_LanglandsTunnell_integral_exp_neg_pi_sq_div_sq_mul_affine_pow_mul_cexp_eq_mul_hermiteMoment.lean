-- Prove2me | solution 1 for LanglandsTunnell.integral_exp_neg_pi_sq_div_sq_mul_affine_pow_mul_cexp_eq_mul_hermiteMoment
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:08.670037+00:00
-- url     : https://prove2.me/submissions/c895be20-6aee-5ac2-93b8-39d8d078f18b

import Mathlib.Analysis.Fourier.FourierTransformDeriv
import Mathlib.Analysis.SpecialFunctions.Gaussian.FourierTransform
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
import Mathlib
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_LanglandsTunnell_integral_exp_neg_pi_sq_div_sq_mul_affine_pow_mul_cexp_eq_mul_hermiteMoment

set_option autoImplicit false

open MeasureTheory Complex FourierTransform
open Set Filter Topology

noncomputable section

namespace HM9

def J (k : ℕ) (η t : ℝ) : ℂ :=
  ∫ u : ℝ, (Real.exp (-(Real.pi * u ^ 2)) : ℂ) * cexp (2 * Real.pi * I * η * u) * ((t : ℂ) + I * u) ^ k

def j (k : ℕ) (η t : ℝ) (u : ℝ) : ℂ :=
  (Real.exp (-(Real.pi * u ^ 2)) : ℂ) * cexp (2 * Real.pi * I * η * u) * ((t : ℂ) + I * u) ^ k

lemma norm_cexp_phase (η u : ℝ) : ‖cexp (2 * Real.pi * I * η * u)‖ = 1 := by
  rw [norm_exp]
  have : (2 * (Real.pi : ℂ) * I * η * u).re = 0 := by simp [mul_re, mul_im]
  rw [this, Real.exp_zero]

lemma integrable_exp_neg_mul_abs {a : ℝ} (ha : 0 < a) : Integrable (fun u : ℝ => Real.exp (-(a * |u|))) := by
  have h1 : IntegrableOn (fun t : ℝ => Real.exp (-(a * t))) (Ioi 0) := by
    have := integrableOn_rpow_mul_exp_neg_mul_rpow (s := 0) (p := 1) (by norm_num) (zero_lt_one' ℝ) ha
    refine this.congr_fun (fun x hx => ?_) measurableSet_Ioi
    dsimp only
    rw [Real.rpow_zero, Real.rpow_one, one_mul, neg_mul]
  have h1' : IntegrableOn (fun t : ℝ => Real.exp (-(a * |t|))) (Ioi 0) :=
    h1.congr_fun (fun x hx => by rw [abs_of_pos (mem_Ioi.mp hx)]) measurableSet_Ioi
  have h2 : IntegrableOn (fun t : ℝ => Real.exp (-(a * |t|))) (Iic 0) := by
    rw [← Measure.map_neg_eq_self (volume : Measure ℝ)]
    let m : MeasurableEmbedding fun x : ℝ => -x := (Homeomorph.neg ℝ).measurableEmbedding
    rw [m.integrableOn_map_iff]
    simp_rw [Function.comp_def, abs_neg, Set.neg_preimage, Set.neg_Iic, neg_zero]
    exact (integrableOn_Ici_iff_integrableOn_Ioi).mpr h1'
  have := h2.union h1'
  rwa [Iic_union_Ioi, integrableOn_univ] at this

lemma norm_j_le (k : ℕ) (η t u : ℝ) :
    ‖j k η t u‖ ≤ (k.factorial : ℝ) * Real.exp (|t| + Real.pi / 4) * Real.exp (-((Real.pi - 1) * |u|)) := by
  unfold j
  rw [norm_mul, norm_mul, norm_cexp_phase, mul_one, Complex.norm_real, Real.norm_of_nonneg (Real.exp_pos _).le,
    norm_pow]
  have hnorm : ‖(t : ℂ) + I * u‖ ≤ |t| + |u| := by
    calc ‖(t : ℂ) + I * u‖ ≤ ‖(t : ℂ)‖ + ‖I * (u : ℂ)‖ := norm_add_le _ _
      _ = |t| + |u| := by rw [norm_mul, Complex.norm_I, one_mul, Complex.norm_real, Complex.norm_real,
            Real.norm_eq_abs, Real.norm_eq_abs]
  have hx : 0 ≤ |t| + |u| := by positivity
  have hpow : ‖(t : ℂ) + I * u‖ ^ k ≤ (k.factorial : ℝ) * Real.exp (|t| + |u|) := by
    have h1 : ‖(t : ℂ) + I * u‖ ^ k ≤ (|t| + |u|) ^ k := pow_le_pow_left₀ (norm_nonneg _) hnorm k
    have h2 := Real.pow_div_factorial_le_exp (|t| + |u|) hx k
    rw [div_le_iff₀ (by positivity)] at h2
    linarith
  have hgauss : Real.exp (-(Real.pi * u ^ 2)) ≤ Real.exp (Real.pi / 4 - Real.pi * |u|) := by
    rw [Real.exp_le_exp]
    have : |u| ^ 2 = u ^ 2 := sq_abs u
    nlinarith [sq_nonneg (|u| - 1 / 2), Real.pi_pos]
  calc Real.exp (-(Real.pi * u ^ 2)) * ‖(t : ℂ) + I * u‖ ^ k
      ≤ Real.exp (Real.pi / 4 - Real.pi * |u|) * ((k.factorial : ℝ) * Real.exp (|t| + |u|)) :=
        mul_le_mul hgauss hpow (by positivity) (Real.exp_pos _).le
    _ = (k.factorial : ℝ) * Real.exp (|t| + Real.pi / 4) * Real.exp (-((Real.pi - 1) * |u|)) := by
        rw [mul_comm, mul_assoc, mul_assoc, ← Real.exp_add, ← Real.exp_add]; congr 2; ring

lemma continuous_j (k : ℕ) (η t : ℝ) : Continuous (j k η t) := by
  unfold j; fun_prop

lemma integrable_j (k : ℕ) (η t : ℝ) : Integrable (j k η t) := by
  refine Integrable.mono' ((integrable_exp_neg_mul_abs (a := Real.pi - 1) (by linarith [Real.pi_gt_three])).const_mul
    ((k.factorial : ℝ) * Real.exp (|t| + Real.pi / 4))) (continuous_j k η t).aestronglyMeasurable
    (ae_of_all _ fun u => ?_)
  exact norm_j_le k η t u

lemma tendsto_j_zero (k : ℕ) (η t : ℝ) :
    Tendsto (j k η t) atTop (𝓝 0) ∧ Tendsto (j k η t) atBot (𝓝 0) := by
  have hK : ∀ l : Filter ℝ, Tendsto (fun u : ℝ => |u|) l atTop →
      Tendsto (j k η t) l (𝓝 0) := by
    intro l hl
    refine squeeze_zero_norm (fun u => norm_j_le k η t u) ?_
    have h1 : Tendsto (fun u : ℝ => Real.exp (-((Real.pi - 1) * |u|))) l (𝓝 0) := by
      have := Real.tendsto_exp_neg_atTop_nhds_zero.comp
        (hl.const_mul_atTop (by linarith [Real.pi_gt_three] : (0:ℝ) < Real.pi - 1))
      exact this
    simpa using h1.const_mul ((k.factorial : ℝ) * Real.exp (|t| + Real.pi / 4))
  exact ⟨hK atTop tendsto_abs_atTop_atTop, hK atBot tendsto_abs_atBot_atTop⟩

lemma hasDerivAt_j (k : ℕ) (η t u : ℝ) :
    HasDerivAt (j k η t)
      ((Real.exp (-(Real.pi * u ^ 2)) : ℂ) * cexp (2 * Real.pi * I * η * u) *
        ((-(2 * Real.pi * (u : ℂ)) + 2 * Real.pi * I * η) * ((t : ℂ) + I * u) ^ k
          + I * ((k : ℕ) : ℂ) * ((t : ℂ) + I * u) ^ (k - 1))) u := by

  have hg : HasDerivAt (fun u : ℝ => (Real.exp (-(Real.pi * u ^ 2)) : ℂ))
      (((-(Real.pi * (2 * u))) * Real.exp (-(Real.pi * u ^ 2)) : ℝ) : ℂ) u := by
    have h1 : HasDerivAt (fun u : ℝ => -(Real.pi * u ^ 2)) (-(Real.pi * (2 * u))) u := by
      have := ((hasDerivAt_pow 2 u).const_mul Real.pi).fun_neg
      simpa using this
    have h2 := (Real.hasDerivAt_exp _).comp u h1
    have h3 := h2.ofReal_comp
    convert h3 using 1 <;> try with_reducible_and_instances rfl
    · funext y; simp [Complex.ofReal_exp]
    · push_cast; ring
  have hE : HasDerivAt (fun u : ℝ => cexp (2 * Real.pi * I * η * u)) (cexp (2 * Real.pi * I * η * u) * (2 * Real.pi * I * η)) u := by
    have h1 : HasDerivAt (fun u : ℝ => (2 * Real.pi * I * η * u : ℂ)) (2 * Real.pi * I * η) u := by
      have := (hasDerivAt_id (u : ℝ)).ofReal_comp.const_mul (2 * Real.pi * I * η : ℂ)
      simpa using this
    exact (Complex.hasDerivAt_exp _).comp u h1
  have hP : HasDerivAt (fun u : ℝ => ((t : ℂ) + I * u) ^ k)
      (((k : ℕ) : ℂ) * ((t : ℂ) + I * u) ^ (k - 1) * I) u := by
    have h1 : HasDerivAt (fun u : ℝ => (t : ℂ) + I * u) I u := by
      have := ((hasDerivAt_id (u : ℝ)).ofReal_comp.const_mul I).const_add (t : ℂ)
      simpa using this
    exact h1.pow k
  have hprod := (hg.mul hE).mul hP
  unfold j
  convert hprod using 1 <;> try with_reducible_and_instances rfl
  simp only [Pi.mul_apply]
  push_cast
  ring

theorem J_rec (k : ℕ) (η t : ℝ) :
    J (k + 1) η t = ((t - η : ℝ) : ℂ) * J k η t - (((k : ℕ) : ℂ) / (2 * Real.pi)) * J (k - 1) η t := by
  set D' : ℝ → ℂ := fun u => 2 * Real.pi * I * j (k + 1) η t u - 2 * Real.pi * I * ((t - η : ℝ) : ℂ) * j k η t u
    + I * ((k : ℕ) : ℂ) * j (k - 1) η t u with hD'
  have hderiv : ∀ u : ℝ, HasDerivAt (j k η t) (D' u) u := by
    intro u
    have h := hasDerivAt_j k η t u
    refine h.congr_deriv ?_
    simp only [hD', j]
    push_cast
    rcases Nat.eq_zero_or_pos k with hk | hk
    · subst hk
      simp only [pow_zero, Nat.cast_zero, mul_zero, zero_mul, add_zero, zero_add, pow_one]
      linear_combination (-(2 * Real.pi * (u : ℂ)) * cexp (-(Real.pi * u ^ 2)) * cexp (2 * Real.pi * I * η * u)) * Complex.I_sq
    · obtain ⟨k', rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
      simp only [Nat.add_sub_cancel]
      linear_combination (-(2 * Real.pi * (u : ℂ)) * cexp (-(Real.pi * u ^ 2)) * cexp (2 * Real.pi * I * η * u) *
        ((t : ℂ) + I * u) ^ (k' + 1)) * Complex.I_sq
  have hD'i : Integrable D' := by
    simp only [hD']
    exact (((integrable_j (k + 1) η t).const_mul _).sub ((integrable_j k η t).const_mul _)).add
      ((integrable_j (k - 1) η t).const_mul _)
  obtain ⟨htop, hbot⟩ := tendsto_j_zero k η t
  have h0 := integral_of_hasDerivAt_of_tendsto hderiv hD'i hbot htop
  rw [sub_self] at h0
  have hsplit : ∫ u, D' u = 2 * Real.pi * I * J (k + 1) η t - 2 * Real.pi * I * ((t - η : ℝ) : ℂ) * J k η t
      + I * ((k : ℕ) : ℂ) * J (k - 1) η t := by
    simp only [hD', J]
    rw [integral_add, integral_sub, integral_const_mul, integral_const_mul, integral_const_mul]
    · rfl
    · exact (integrable_j (k + 1) η t).const_mul _
    · exact (integrable_j k η t).const_mul _
    · exact ((integrable_j (k + 1) η t).const_mul _).sub ((integrable_j k η t).const_mul _)
    · exact (integrable_j (k - 1) η t).const_mul _
  rw [hsplit] at h0
  have hI : I * I = -1 := Complex.I_mul_I
  have key : (2 * Real.pi : ℂ) * J (k + 1) η t = 2 * Real.pi * ((t - η : ℝ) : ℂ) * J k η t - ((k : ℕ) : ℂ) * J (k - 1) η t := by
    linear_combination (-I) * h0 + (2 * Real.pi * J (k + 1) η t - 2 * Real.pi * ((t - η : ℝ) : ℂ) * J k η t
      + ((k : ℕ) : ℂ) * J (k - 1) η t) * hI
  have hπ : (2 * Real.pi : ℂ) ≠ 0 := by exact_mod_cast (by positivity : (2 * Real.pi : ℝ) ≠ 0)
  field_simp
  linear_combination key

theorem J_zero (η t : ℝ) : J 0 η t = cexp (-(Real.pi * η ^ 2)) := by
  have h := congrFun (fourier_gaussian_pi' (b := 1) (by simp) (I * η)) 0
  rw [Real.fourier_real_eq] at h
  simp only [mul_zero, neg_zero, AddChar.map_zero_eq_one, one_smul, Complex.ofReal_zero, zero_add,
    one_cpow, div_one, one_mul, mul_one] at h
  unfold J
  have hint : ∀ v : ℝ, (Real.exp (-(Real.pi * v ^ 2)) : ℂ) * cexp (2 * Real.pi * I * η * v) * ((t : ℂ) + I * v) ^ 0 =
      cexp (-Real.pi * v ^ 2 + 2 * Real.pi * (I * η) * v) := by
    intro v
    rw [pow_zero, mul_one, Complex.ofReal_exp, ← Complex.exp_add]
    congr 1; push_cast; ring
  simp_rw [hint]
  rw [h]
  congr 1
  rw [show (I * (I * (η : ℂ))) = -η by rw [← mul_assoc, Complex.I_mul_I]; ring]
  ring

theorem J_shift (k : ℕ) (η t : ℝ) : J k η t = cexp (-(Real.pi * η ^ 2)) * J k 0 (t - η) := by
  have two : ∀ n : ℕ, J n η t = cexp (-(Real.pi * η ^ 2)) * J n 0 (t - η) ∧
      J (n + 1) η t = cexp (-(Real.pi * η ^ 2)) * J (n + 1) 0 (t - η) := by
    intro n
    induction n with
    | zero =>
      refine ⟨by rw [J_zero, J_zero]; simp, ?_⟩
      rw [J_rec 0 η t, J_rec 0 0 (t - η), J_zero, J_zero]
      push_cast; simp; ring
    | succ n ih =>
      obtain ⟨ih0, ih1⟩ := ih
      refine ⟨ih1, ?_⟩
      rw [show n + 1 + 1 = (n + 1) + 1 from rfl, J_rec (n + 1) η t, J_rec (n + 1) 0 (t - η), Nat.add_sub_cancel,
        ih0, ih1]
      push_cast; ring
  exact (two k).1

end HM9

end

theorem solution
    (α c : ℝ) {y₁ : ℝ} (hy₁ : y₁ ≠ 0) (m : ℕ) :
    ∫ x : ℝ, (Real.exp (-(Real.pi * (x ^ 2 / y₁ ^ 2))) : ℂ) *
        (((α : ℝ) : ℂ) + (Complex.I * (((1 / y₁ : ℝ)) : ℂ)) * (x : ℂ)) ^ m *
        Complex.exp (2 * Real.pi * Complex.I * (c : ℂ) * (x : ℂ)) =
      ((|y₁| : ℝ) : ℂ) * (Real.exp (-(Real.pi * (c ^ 2 * y₁ ^ 2))) : ℂ) *
        ∫ u : ℝ, (Real.exp (-(Real.pi * u ^ 2)) : ℂ) * ((((α - c * y₁ : ℝ)) : ℂ) + Complex.I * (u : ℂ)) ^ m := by

  set f : ℝ → ℂ := fun x => (Real.exp (-(Real.pi * (x ^ 2 / y₁ ^ 2))) : ℂ) *
        (((α : ℝ) : ℂ) + (Complex.I * (((1 / y₁ : ℝ)) : ℂ)) * (x : ℂ)) ^ m *
        Complex.exp (2 * Real.pi * Complex.I * (c : ℂ) * (x : ℂ)) with hf
  have hsub := Measure.integral_comp_mul_left f y₁
  rw [abs_inv, Complex.real_smul] at hsub
  have hay : (|y₁| : ℝ) ≠ 0 := abs_ne_zero.mpr hy₁
  have hL : ∫ x, f x = ((|y₁| : ℝ) : ℂ) * ∫ u : ℝ, f (y₁ * u) := by
    rw [hsub, ← mul_assoc, show ((|y₁| : ℝ) : ℂ) * ((|y₁|⁻¹ : ℝ) : ℂ) = 1 by
      rw [← Complex.ofReal_mul, mul_inv_cancel₀ hay, Complex.ofReal_one], one_mul]
  have hfj : ∀ u : ℝ, f (y₁ * u) = HM9.j m (c * y₁) α u := by
    intro u
    simp only [hf, HM9.j]
    have e1 : (y₁ * u) ^ 2 / y₁ ^ 2 = u ^ 2 := by field_simp
    have hy₁' : (y₁ : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hy₁
    have e2 : I * (((1 / y₁ : ℝ)) : ℂ) * ((y₁ * u : ℝ) : ℂ) = I * (u : ℂ) := by
      push_cast; field_simp
    have e3 : cexp (2 * Real.pi * I * (c : ℂ) * ((y₁ * u : ℝ) : ℂ)) = cexp (2 * Real.pi * I * ((c * y₁ : ℝ) : ℂ) * (u : ℂ)) := by
      push_cast; ring_nf
    rw [e1, e2, e3]
    ring
  show ∫ x, f x = _
  rw [hL]
  simp_rw [hfj]
  rw [show (∫ u, HM9.j m (c * y₁) α u) = HM9.J m (c * y₁) α from rfl, HM9.J_shift]
  unfold HM9.J
  simp only [Complex.ofReal_zero, mul_zero, zero_mul, Complex.exp_zero, mul_one]
  rw [← mul_assoc]
  congr 2
  rw [Complex.ofReal_exp]
  congr 1
  push_cast
  ring

end S_LanglandsTunnell_integral_exp_neg_pi_sq_div_sq_mul_affine_pow_mul_cexp_eq_mul_hermiteMoment
end P2MW
export P2MW.S_LanglandsTunnell_integral_exp_neg_pi_sq_div_sq_mul_affine_pow_mul_cexp_eq_mul_hermiteMoment (solution)
