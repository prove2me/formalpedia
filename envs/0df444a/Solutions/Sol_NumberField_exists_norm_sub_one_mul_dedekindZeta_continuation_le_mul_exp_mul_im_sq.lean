-- Prove2me | solution 1 for NumberField.exists_norm_sub_one_mul_dedekindZeta_continuation_le_mul_exp_mul_im_sq
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.93214+00:00
-- url     : https://prove2.me/submissions/89161f64-b067-5704-b345-9d734246764c

import Mathlib
import Theorems.Thm_NumberField_exists_completedDedekindZeta_package
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_NumberField_exists_norm_sub_one_mul_dedekindZeta_continuation_le_mul_exp_mul_im_sq

set_option autoImplicit false

noncomputable section

open NumberField Complex Filter Set
open scoped Topology Real

namespace R4Z2a

theorem norm_sin_le_exp_abs_im (z : ℂ) : ‖Complex.sin z‖ ≤ Real.exp |z.im| := by
  rw [Complex.sin]
  have h1 : ‖Complex.exp (-z * I)‖ = Real.exp z.im := by
    rw [Complex.norm_exp]; congr 1; simp
  have h2 : ‖Complex.exp (z * I)‖ = Real.exp (-z.im) := by
    rw [Complex.norm_exp]; congr 1; simp
  have hle1 : Real.exp z.im ≤ Real.exp |z.im| := Real.exp_le_exp.mpr (le_abs_self _)
  have hle2 : Real.exp (-z.im) ≤ Real.exp |z.im| := Real.exp_le_exp.mpr (neg_le_abs _)
  calc ‖(Complex.exp (-z * I) - Complex.exp (z * I)) * I / 2‖
      = ‖Complex.exp (-z * I) - Complex.exp (z * I)‖ / 2 := by
        rw [norm_div, norm_mul, Complex.norm_I, mul_one]; simp
    _ ≤ (‖Complex.exp (-z * I)‖ + ‖Complex.exp (z * I)‖) / 2 := by
        gcongr; exact norm_sub_le _ _
    _ ≤ Real.exp |z.im| := by rw [h1, h2]; linarith

theorem norm_Gamma_le_real_Gamma (w : ℂ) (hw : 0 < w.re) : ‖Gamma w‖ ≤ Real.Gamma w.re := by
  rw [Complex.Gamma_eq_integral hw, Complex.GammaIntegral, Real.Gamma_eq_integral hw]
  refine (MeasureTheory.norm_integral_le_integral_norm _).trans (le_of_eq ?_)
  refine MeasureTheory.setIntegral_congr_fun measurableSet_Ioi fun x hx => ?_
  have hx' : 0 < x := hx
  rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (Real.exp_pos _).le,
    Complex.norm_cpow_eq_rpow_re_of_pos hx', sub_re, one_re]

theorem norm_Gamma_le_norm_Gamma_add_nat (w : ℂ) (hw : 1 ≤ |w.im|) (m : ℕ) :
    ‖Gamma w‖ ≤ ‖Gamma (w + m)‖ := by
  induction m with
  | zero => simp
  | succ m ih =>
    have hne : w + m ≠ 0 := by
      intro h
      have := congrArg Complex.im h
      simp at this
      rw [this] at hw; norm_num at hw
    have hnorm : 1 ≤ ‖w + m‖ := by
      calc (1 : ℝ) ≤ |w.im| := hw
        _ = |(w + m).im| := by simp
        _ ≤ ‖w + m‖ := abs_im_le_norm _
    have hstep : Gamma (w + (m + 1 : ℕ)) = (w + m) * Gamma (w + m) := by
      rw [show w + ((m + 1 : ℕ) : ℂ) = (w + m) + 1 by push_cast; ring]
      exact Complex.Gamma_add_one _ hne
    rw [hstep, norm_mul]
    calc ‖Gamma w‖ ≤ ‖Gamma (w + m)‖ := ih
      _ = 1 * ‖Gamma (w + m)‖ := (one_mul _).symm
      _ ≤ ‖w + m‖ * ‖Gamma (w + m)‖ := mul_le_mul_of_nonneg_right hnorm (norm_nonneg _)

theorem real_Gamma_le_max (x X : ℝ) (h1 : 1 ≤ x) (h2 : x ≤ X) : Real.Gamma x ≤ max 1 (Real.Gamma X) := by
  have hX : 1 ≤ X := h1.trans h2
  have hseg : x ∈ segment ℝ (1 : ℝ) X := by rw [segment_eq_Icc hX]; exact ⟨h1, h2⟩
  have h := Real.convexOn_Gamma.le_on_segment (by norm_num : (1 : ℝ) ∈ Set.Ioi 0)
    (show X ∈ Set.Ioi (0 : ℝ) from lt_of_lt_of_le one_pos hX) hseg
  rwa [Real.Gamma_one] at h

theorem norm_inv_Gamma_le (a b : ℝ) :
    ∃ B : ℝ, 0 < B ∧ ∀ s : ℂ, a ≤ s.re → s.re ≤ b → 1 ≤ |s.im| →
      ‖(Gamma s)⁻¹‖ ≤ B * Real.exp (Real.pi * |s.im|) := by
  set m : ℕ := Nat.ceil b with hm
  set X : ℝ := 1 + m - a with hX
  refine ⟨max 1 (Real.Gamma X), lt_of_lt_of_le one_pos (le_max_left _ _), ?_⟩
  intro s hsa hsb hsi
  have hmb : b ≤ m := Nat.le_ceil b
  have him0 : s.im ≠ 0 := by
    intro h; rw [h] at hsi; norm_num at hsi

  have hsin : Complex.sin (Real.pi * s) ≠ 0 := by
    rw [Ne, Complex.sin_eq_zero_iff, not_exists]
    intro k hk
    have := congrArg Complex.im hk
    simp at this
    exact him0 this
  have hΓ : Gamma s ≠ 0 := by
    refine Complex.Gamma_ne_zero fun n h => ?_
    have := congrArg Complex.im h
    simp at this
    exact him0 this

  have hrefl := Complex.Gamma_mul_Gamma_one_sub s
  have hπ0 : (Real.pi : ℂ) ≠ 0 := ofReal_ne_zero.mpr Real.pi_ne_zero
  have hinv : (Gamma s)⁻¹ = Gamma (1 - s) * Complex.sin (Real.pi * s) / Real.pi := by
    have h1 : Gamma s * (Gamma (1 - s) * Complex.sin (Real.pi * s) / Real.pi) = 1 := by
      rw [← mul_div_assoc, ← mul_assoc, hrefl]
      field_simp
    exact (eq_inv_of_mul_eq_one_right h1).symm

  have h1s_im : 1 ≤ |(1 - s).im| := by simpa using hsi
  have hshift := norm_Gamma_le_norm_Gamma_add_nat (1 - s) h1s_im m
  have hre : (1 - s + m).re = 1 + m - s.re := by simp; ring
  have hre_pos : 0 < (1 - s + m).re := by rw [hre]; linarith
  have hreal := norm_Gamma_le_real_Gamma (1 - s + m) hre_pos
  rw [hre] at hreal
  have hmax := real_Gamma_le_max (1 + m - s.re) X (by linarith) (by rw [hX]; linarith)
  have hΓ1s : ‖Gamma (1 - s)‖ ≤ max 1 (Real.Gamma X) := hshift.trans (hreal.trans hmax)

  have hsinle : ‖Complex.sin (Real.pi * s)‖ ≤ Real.exp (Real.pi * |s.im|) := by
    have := norm_sin_le_exp_abs_im (Real.pi * s)
    have him : |((Real.pi : ℂ) * s).im| = Real.pi * |s.im| := by
      simp [abs_mul, abs_of_pos Real.pi_pos]
    rwa [him] at this
  rw [hinv, norm_div, norm_mul, Complex.norm_real, Real.norm_of_nonneg Real.pi_pos.le]
  have hπ1 : (1 : ℝ) ≤ Real.pi := by linarith [Real.pi_gt_three]
  calc ‖Gamma (1 - s)‖ * ‖Complex.sin (Real.pi * s)‖ / Real.pi
      ≤ ‖Gamma (1 - s)‖ * ‖Complex.sin (Real.pi * s)‖ / 1 :=
        div_le_div_of_nonneg_left (by positivity) one_pos hπ1
    _ ≤ max 1 (Real.Gamma X) * Real.exp (Real.pi * |s.im|) := by
        rw [div_one]
        exact mul_le_mul hΓ1s hsinle (norm_nonneg _) (zero_le_one.trans (le_max_left _ _))

def GaussBdd (a b : ℝ) (f : ℂ → ℂ) : Prop :=
  ∃ B C : ℝ, 0 ≤ B ∧ 0 ≤ C ∧ ∀ s : ℂ, a ≤ s.re → s.re ≤ b → 2 ≤ |s.im| →
    ‖f s‖ ≤ B * Real.exp (C * s.im ^ 2)

theorem GaussBdd.mul {a b : ℝ} {f g : ℂ → ℂ} (hf : GaussBdd a b f) (hg : GaussBdd a b g) :
    GaussBdd a b (fun s => f s * g s) := by
  obtain ⟨B₁, C₁, hB₁, hC₁, h₁⟩ := hf
  obtain ⟨B₂, C₂, hB₂, hC₂, h₂⟩ := hg
  refine ⟨B₁ * B₂, C₁ + C₂, mul_nonneg hB₁ hB₂, add_nonneg hC₁ hC₂, fun s hsa hsb hsi => ?_⟩
  rw [norm_mul, add_mul, Real.exp_add]
  calc ‖f s‖ * ‖g s‖ ≤ (B₁ * Real.exp (C₁ * s.im ^ 2)) * (B₂ * Real.exp (C₂ * s.im ^ 2)) :=
        mul_le_mul (h₁ s hsa hsb hsi) (h₂ s hsa hsb hsi) (norm_nonneg _) (by positivity)
    _ = B₁ * B₂ * (Real.exp (C₁ * s.im ^ 2) * Real.exp (C₂ * s.im ^ 2)) := by ring

theorem GaussBdd.pow {a b : ℝ} {f : ℂ → ℂ} (hf : GaussBdd a b f) (n : ℕ) :
    GaussBdd a b (fun s => f s ^ n) := by
  induction n with
  | zero => exact ⟨1, 0, zero_le_one, le_rfl, fun s _ _ _ => by simp⟩
  | succ n ih =>
    have := ih.mul hf
    simpa [pow_succ] using this

theorem gaussBdd_of_norm_le {a b : ℝ} {f : ℂ → ℂ} (M : ℝ) (hM : 0 ≤ M)
    (h : ∀ s : ℂ, a ≤ s.re → s.re ≤ b → 2 ≤ |s.im| → ‖f s‖ ≤ M) : GaussBdd a b f :=
  ⟨M, 0, hM, le_rfl, fun s hsa hsb hsi => by simpa using h s hsa hsb hsi⟩

theorem abs_le_one_add_sq (t : ℝ) : |t| ≤ 1 + t ^ 2 := by
  rcases le_or_gt |t| 1 with h | h
  · nlinarith [sq_nonneg t]
  · have : |t| ≤ |t| ^ 2 := by nlinarith
    rw [sq_abs] at this; linarith

theorem gaussBdd_of_norm_le_exp {a b : ℝ} {f : ℂ → ℂ} (M c : ℝ) (hM : 0 ≤ M) (hc : 0 ≤ c)
    (h : ∀ s : ℂ, a ≤ s.re → s.re ≤ b → 2 ≤ |s.im| → ‖f s‖ ≤ M * Real.exp (c * |s.im|)) :
    GaussBdd a b f := by
  refine ⟨M * Real.exp c, c, by positivity, hc, fun s hsa hsb hsi => ?_⟩
  refine (h s hsa hsb hsi).trans ?_
  rw [mul_assoc, ← Real.exp_add]
  refine mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ?_) hM
  have := abs_le_one_add_sq s.im
  nlinarith

section ident
variable (K : Type) [Field K] [NumberField K]

def D : ℝ := ((|NumberField.discr K| : ℤ) : ℝ)

theorem D_pos : 0 < D K := by
  unfold D
  exact_mod_cast abs_pos.mpr (NumberField.discr_ne_zero K)

theorem D_cast : (((|NumberField.discr K| : ℤ)) : ℂ) = ((D K : ℝ) : ℂ) := by
  unfold D; exact (Complex.ofReal_intCast _).symm

theorem one_le_D : 1 ≤ D K := by
  unfold D
  have h := NumberField.discr_ne_zero K
  have : (1 : ℤ) ≤ |NumberField.discr K| := Int.one_le_abs h
  exact_mod_cast this

def invGammaFactor (s : ℂ) : ℂ :=
  (((D K : ℝ) : ℂ) ^ (s / 2))⁻¹ * (Gammaℝ s)⁻¹ ^ NumberField.InfinitePlace.nrRealPlaces K *
    (Gammaℂ s)⁻¹ ^ NumberField.InfinitePlace.nrComplexPlaces K

theorem differentiable_Gammaℂ_inv : Differentiable ℂ (fun s : ℂ => (Gammaℂ s)⁻¹) := by
  have : (fun s : ℂ => (Gammaℂ s)⁻¹) = fun s => (Gammaℝ s)⁻¹ * (Gammaℝ (s + 1))⁻¹ := by
    funext s; rw [← Gammaℝ_mul_Gammaℝ_add_one, mul_inv]
  rw [this]
  exact differentiable_Gammaℝ_inv.mul (differentiable_Gammaℝ_inv.comp (differentiable_id.add_const 1))

theorem differentiable_invGammaFactor : Differentiable ℂ (invGammaFactor K) := by
  unfold invGammaFactor
  refine ((Differentiable.inv ?_ ?_).mul (differentiable_Gammaℝ_inv.pow _)).mul
    (differentiable_Gammaℂ_inv.pow _)
  · exact Differentiable.const_cpow (differentiable_id.div_const 2)
      (Or.inl (ofReal_ne_zero.mpr (D_pos K).ne'))
  · intro s
    rw [Ne, cpow_eq_zero_iff, not_and_or]
    exact Or.inl (ofReal_ne_zero.mpr (D_pos K).ne')

theorem isOpen_compl01 : IsOpen ({(0 : ℂ), 1}ᶜ : Set ℂ) :=
  (Set.toFinite _).isClosed.isOpen_compl

theorem isPreconnected_compl01 : IsPreconnected ({(0 : ℂ), 1}ᶜ : Set ℂ) := by
  have hc : ({(0 : ℂ), 1} : Set ℂ).Countable := (Set.toFinite _).countable
  have hr : 1 < Module.rank ℝ ℂ := by simp
  exact (hc.isConnected_compl_of_one_lt_rank hr).isPreconnected

theorem R_eq (R : ℂ → ℂ) (hR : Differentiable ℂ R)
    (hRζ : ∀ s : ℂ, 1 < s.re → R s = (s - 1) * NumberField.dedekindZeta K s)
    (Λ : ℂ → ℂ) (hΛd : DifferentiableOn ℂ Λ ({(0 : ℂ), 1}ᶜ))
    (hΛeq : ∀ s : ℂ, 1 < s.re → Λ s =
        (((|NumberField.discr K| : ℤ) : ℂ)) ^ (s / 2)
          * Complex.Gammaℝ s ^ NumberField.InfinitePlace.nrRealPlaces K
          * Complex.Gammaℂ s ^ NumberField.InfinitePlace.nrComplexPlaces K
          * NumberField.dedekindZeta K s) :
    Set.EqOn R (fun s => (s - 1) * Λ s * invGammaFactor K s) ({(0 : ℂ), 1}ᶜ) := by
  set g : ℂ → ℂ := fun s => (s - 1) * Λ s * invGammaFactor K s with hg
  have hRan : AnalyticOnNhd ℂ R ({(0 : ℂ), 1}ᶜ) := (hR.differentiableOn).analyticOnNhd (isOpen_compl01)
  have hgd : DifferentiableOn ℂ g ({(0 : ℂ), 1}ᶜ) :=
    (((differentiable_id.sub_const 1).differentiableOn).mul hΛd).mul
      (differentiable_invGammaFactor K).differentiableOn
  have hgan : AnalyticOnNhd ℂ g ({(0 : ℂ), 1}ᶜ) := hgd.analyticOnNhd isOpen_compl01
  have h2mem : (2 : ℂ) ∈ ({(0 : ℂ), 1}ᶜ : Set ℂ) := by
    simp only [Set.mem_compl_iff, Set.mem_insert_iff, Set.mem_singleton_iff, not_or]
    norm_num
  have hVopen : IsOpen {s : ℂ | 1 < s.re} := isOpen_lt continuous_const continuous_re
  have hagree : ∀ s : ℂ, 1 < s.re → R s = g s := by
    intro s hs
    have hs0 : 0 < s.re := by linarith
    have hΓℝ : Gammaℝ s ≠ 0 := Gammaℝ_ne_zero_of_re_pos hs0
    have hΓℂ : Gammaℂ s ≠ 0 := by
      rw [Gammaℂ_def]
      refine mul_ne_zero (mul_ne_zero two_ne_zero ?_) (Complex.Gamma_ne_zero_of_re_pos hs0)
      rw [Ne, cpow_eq_zero_iff, not_and_or]
      exact Or.inl (mul_ne_zero two_ne_zero (ofReal_ne_zero.mpr Real.pi_ne_zero))
    have hD : ((D K : ℝ) : ℂ) ^ (s / 2) ≠ 0 := by
      rw [Ne, cpow_eq_zero_iff, not_and_or]
      exact Or.inl (ofReal_ne_zero.mpr (D_pos K).ne')
    rw [hRζ s hs]
    show (s - 1) * dedekindZeta K s = (s - 1) * Λ s * invGammaFactor K s
    rw [hΛeq s hs, D_cast]
    unfold invGammaFactor
    set r₁ : ℕ := NumberField.InfinitePlace.nrRealPlaces K
    set r₂ : ℕ := NumberField.InfinitePlace.nrComplexPlaces K
    have e1 : ((D K : ℝ) : ℂ) ^ (s / 2) * (((D K : ℝ) : ℂ) ^ (s / 2))⁻¹ = 1 := mul_inv_cancel₀ hD
    have e2 : Gammaℝ s ^ r₁ * (Gammaℝ s)⁻¹ ^ r₁ = 1 := by
      rw [← mul_pow, mul_inv_cancel₀ hΓℝ, one_pow]
    have e3 : Gammaℂ s ^ r₂ * (Gammaℂ s)⁻¹ ^ r₂ = 1 := by
      rw [← mul_pow, mul_inv_cancel₀ hΓℂ, one_pow]
    calc (s - 1) * dedekindZeta K s
        = (s - 1) * dedekindZeta K s * (((D K : ℝ) : ℂ) ^ (s / 2) * (((D K : ℝ) : ℂ) ^ (s / 2))⁻¹) *
            (Gammaℝ s ^ r₁ * (Gammaℝ s)⁻¹ ^ r₁) * (Gammaℂ s ^ r₂ * (Gammaℂ s)⁻¹ ^ r₂) := by
          rw [e1, e2, e3]; ring
      _ = (s - 1) * (((D K : ℝ) : ℂ) ^ (s / 2) * Gammaℝ s ^ r₁ * Gammaℂ s ^ r₂ * dedekindZeta K s) *
            ((((D K : ℝ) : ℂ) ^ (s / 2))⁻¹ * (Gammaℝ s)⁻¹ ^ r₁ * (Gammaℂ s)⁻¹ ^ r₂) := by ring
  have hev : R =ᶠ[𝓝 (2 : ℂ)] g :=
    Filter.eventuallyEq_of_mem (hVopen.mem_nhds (by norm_num : (1 : ℝ) < (2 : ℂ).re)) fun z hz => hagree z hz
  exact hRan.eqOn_of_preconnected_of_eventuallyEq hgan (isPreconnected_compl01) h2mem hev

end ident

section pieces
variable (K : Type) [Field K] [NumberField K]

theorem norm_le_of_strip {a b : ℝ} (s : ℂ) (hsa : a ≤ s.re) (hsb : s.re ≤ b) :
    ‖s‖ ≤ (|a| + |b|) + |s.im| := by
  have hre : |s.re| ≤ |a| + |b| := by
    rcases le_or_gt 0 s.re with h | h
    · rw [abs_of_nonneg h]; linarith [le_abs_self b, abs_nonneg a]
    · rw [abs_of_neg h]; linarith [neg_le_abs a, abs_nonneg b]
  linarith [norm_le_abs_re_add_abs_im s]

theorem gaussBdd_D_inv (a b : ℝ) : GaussBdd a b (fun s => (((D K : ℝ) : ℂ) ^ (s / 2))⁻¹) := by
  refine gaussBdd_of_norm_le ((D K) ^ ((|a| + |b|) / 2)) (Real.rpow_nonneg (D_pos K).le _) ?_
  intro s hsa hsb _
  rw [norm_inv, Complex.norm_cpow_eq_rpow_re_of_pos (D_pos K), ← Real.rpow_neg (D_pos K).le]
  refine Real.rpow_le_rpow_of_exponent_le (one_le_D K) ?_
  have : (s / 2).re = s.re / 2 := by simp
  rw [this]
  have hre : -s.re ≤ |a| + |b| := by linarith [neg_abs_le a, le_abs_self b, abs_nonneg b, abs_nonneg a]
  linarith

theorem gaussBdd_Gammaℝ_inv (a b : ℝ) : GaussBdd a b (fun s => (Gammaℝ s)⁻¹) := by
  obtain ⟨B, hB, hΓ⟩ := norm_inv_Gamma_le (a / 2) (b / 2)
  set P : ℝ := Real.pi ^ ((|a| + |b|) / 2) with hP
  have hP0 : 0 ≤ P := Real.rpow_nonneg Real.pi_pos.le _
  refine gaussBdd_of_norm_le_exp (P * B) (Real.pi / 2) (by positivity) (by positivity) ?_
  intro s hsa hsb hsi
  have hs2 : (s / 2).re = s.re / 2 := by simp
  have hs2i : (s / 2).im = s.im / 2 := by simp
  have h1 : a / 2 ≤ (s / 2).re := by rw [hs2]; linarith
  have h2 : (s / 2).re ≤ b / 2 := by rw [hs2]; linarith
  have h3 : 1 ≤ |(s / 2).im| := by rw [hs2i, abs_div, abs_two]; linarith
  have hΓs := hΓ (s / 2) h1 h2 h3
  rw [hs2i, abs_div, abs_two] at hΓs
  rw [Gammaℝ_def, mul_inv, norm_mul, norm_inv,
    Complex.norm_cpow_eq_rpow_re_of_pos Real.pi_pos, ← Real.rpow_neg Real.pi_pos.le]
  have hexp : (-(-s / 2)).re ≤ (|a| + |b|) / 2 := by
    have : (-(-s / 2)).re = s.re / 2 := by simp [neg_div]
    rw [this]
    linarith [le_abs_self b, abs_nonneg a]
  have hπ1 : (1 : ℝ) ≤ Real.pi := by linarith [Real.pi_gt_three]
  have hpow : Real.pi ^ (-(-s / 2)).re ≤ P := Real.rpow_le_rpow_of_exponent_le hπ1 hexp
  calc Real.pi ^ (-(-s / 2)).re * ‖(Gamma (s / 2))⁻¹‖ ≤ P * (B * Real.exp (Real.pi * (|s.im| / 2))) :=
        mul_le_mul hpow hΓs (norm_nonneg _) hP0
    _ = P * B * Real.exp (Real.pi / 2 * |s.im|) := by ring_nf

theorem gaussBdd_Gammaℂ_inv (a b : ℝ) : GaussBdd a b (fun s => (Gammaℂ s)⁻¹) := by
  obtain ⟨B, hB, hΓ⟩ := norm_inv_Gamma_le a b
  set P : ℝ := (2 * Real.pi) ^ (|a| + |b|) with hP
  have h2π1 : (1 : ℝ) ≤ 2 * Real.pi := by linarith [Real.pi_gt_three]
  have h2π0 : (0 : ℝ) < 2 * Real.pi := by linarith
  have hP0 : 0 ≤ P := Real.rpow_nonneg h2π0.le _
  refine gaussBdd_of_norm_le_exp (P * B) Real.pi (by positivity) Real.pi_pos.le ?_
  intro s hsa hsb hsi
  have hΓs := hΓ s hsa hsb (by linarith)
  have hcast : ((2 : ℂ) * (Real.pi : ℝ)) = ((2 * Real.pi : ℝ) : ℂ) := by push_cast; ring
  rw [Gammaℂ_def, mul_inv, mul_inv, norm_mul, norm_mul, norm_inv, norm_inv, hcast,
    Complex.norm_cpow_eq_rpow_re_of_pos h2π0, ← Real.rpow_neg h2π0.le]
  have hexp : -(-s).re ≤ |a| + |b| := by
    have : -(-s).re = s.re := by simp
    rw [this]; linarith [le_abs_self b, abs_nonneg a]
  have hpow : (2 * Real.pi) ^ (-(-s).re) ≤ P := Real.rpow_le_rpow_of_exponent_le h2π1 hexp
  have h2 : ‖(2 : ℂ)‖⁻¹ ≤ 1 := by norm_num
  calc ‖(2 : ℂ)‖⁻¹ * (2 * Real.pi) ^ (-(-s).re) * ‖(Gamma s)⁻¹‖
      ≤ 1 * P * (B * Real.exp (Real.pi * |s.im|)) :=
        mul_le_mul (mul_le_mul h2 hpow (Real.rpow_nonneg h2π0.le _) zero_le_one) hΓs (norm_nonneg _)
          (by positivity)
    _ = P * B * Real.exp (Real.pi * |s.im|) := by ring

theorem gaussBdd_invGammaFactor (a b : ℝ) : GaussBdd a b (invGammaFactor K) := by
  unfold invGammaFactor
  exact ((gaussBdd_D_inv K a b).mul ((gaussBdd_Gammaℝ_inv a b).pow _)).mul
    ((gaussBdd_Gammaℂ_inv a b).pow _)

theorem gaussBdd_inv (a b : ℝ) : GaussBdd a b (fun s : ℂ => s⁻¹) := by
  refine gaussBdd_of_norm_le 1 zero_le_one fun s _ _ hsi => ?_
  rw [norm_inv]
  have : (2 : ℝ) ≤ ‖s‖ := hsi.trans (abs_im_le_norm s)
  exact inv_le_one_of_one_le₀ (by linarith)

theorem gaussBdd_of_order_one (a b : ℝ) (ξ : ℂ → ℂ) (C : ℝ)
    (hξ : ∀ s : ℂ, 2 ≤ ‖s‖ → Real.log ‖ξ s‖ ≤ C * ‖s‖ * Real.log ‖s‖) : GaussBdd a b ξ := by
  set M : ℝ := |a| + |b| with hM
  have hM0 : 0 ≤ M := by positivity
  refine ⟨Real.exp (2 * |C| * M ^ 2), 2 * |C|, (Real.exp_pos _).le, by positivity, ?_⟩
  intro s hsa hsb hsi
  have hs2 : (2 : ℝ) ≤ ‖s‖ := hsi.trans (abs_im_le_norm s)
  have hs0 : 0 < ‖s‖ := by linarith
  have hlog := hξ s hs2
  have hlogs : Real.log ‖s‖ ≤ ‖s‖ := by linarith [Real.log_le_sub_one_of_pos hs0]
  have hlogs0 : 0 ≤ Real.log ‖s‖ := Real.log_nonneg (by linarith)
  have h1 : C * ‖s‖ * Real.log ‖s‖ ≤ |C| * ‖s‖ ^ 2 := by
    calc C * ‖s‖ * Real.log ‖s‖ ≤ |C| * ‖s‖ * Real.log ‖s‖ := by
          apply mul_le_mul_of_nonneg_right _ hlogs0
          exact mul_le_mul_of_nonneg_right (le_abs_self C) hs0.le
      _ ≤ |C| * ‖s‖ * ‖s‖ := mul_le_mul_of_nonneg_left hlogs (by positivity)
      _ = |C| * ‖s‖ ^ 2 := by ring
  have hns : ‖s‖ ≤ M + |s.im| := norm_le_of_strip s hsa hsb
  have h2 : ‖s‖ ^ 2 ≤ 2 * M ^ 2 + 2 * s.im ^ 2 := by
    have hsq : ‖s‖ ^ 2 ≤ (M + |s.im|) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) hns 2
    have := sq_abs s.im
    nlinarith [sq_nonneg (M - |s.im|)]
  by_cases hξ0 : ξ s = 0
  · rw [hξ0, norm_zero]; positivity
  · have hpos : 0 < ‖ξ s‖ := norm_pos_iff.mpr hξ0
    rw [← Real.exp_log hpos, ← Real.exp_add, Real.exp_le_exp]
    have h3 : |C| * ‖s‖ ^ 2 ≤ |C| * (2 * M ^ 2 + 2 * s.im ^ 2) := mul_le_mul_of_nonneg_left h2 (abs_nonneg C)
    nlinarith

end pieces

section main
variable (K : Type) [Field K] [NumberField K]

theorem isCompact_rect (a b : ℝ) : IsCompact (Set.Icc a b ×ℂ Set.Icc (-2 : ℝ) 2) :=
  Metric.isCompact_of_isClosed_isBounded (isClosed_Icc.reProdIm isClosed_Icc)
    ((Metric.isBounded_Icc a b).reProdIm (Metric.isBounded_Icc _ _))

theorem main (R : ℂ → ℂ) (hR : Differentiable ℂ R)
    (hRζ : ∀ s : ℂ, 1 < s.re → R s = (s - 1) * NumberField.dedekindZeta K s) (a b : ℝ) :
    ∃ B C : ℝ, ∀ s : ℂ, a ≤ s.re → s.re ≤ b → ‖R s‖ ≤ B * Real.exp (C * s.im ^ 2) := by
  obtain ⟨Λ, hΛd, -, hΛeq, ⟨ξ, hξd, hξeq, Cξ, hξgr⟩, -, -⟩ := NumberField.exists_completedDedekindZeta_package K

  have hRid := R_eq K R hR hRζ Λ hΛd hΛeq
  have hRξ : ∀ s : ℂ, a ≤ s.re → s.re ≤ b → 2 ≤ |s.im| →
      R s = ξ s * s⁻¹ * invGammaFactor K s := by
    intro s _ _ hsi
    have him0 : s.im ≠ 0 := by intro h; rw [h] at hsi; norm_num at hsi
    have hs0 : s ≠ 0 := by intro h; apply him0; rw [h]; simp
    have hs1 : s ≠ 1 := by intro h; apply him0; rw [h]; simp
    have hmem : s ∈ ({(0 : ℂ), 1}ᶜ : Set ℂ) := by
      simp only [Set.mem_compl_iff, Set.mem_insert_iff, Set.mem_singleton_iff, not_or]
      exact ⟨hs0, hs1⟩
    have h := hRid hmem
    simp only at h
    rw [h, hξeq s hs0 hs1]
    field_simp

  have hG : GaussBdd a b (fun s => ξ s * s⁻¹ * invGammaFactor K s) :=
    ((gaussBdd_of_order_one a b ξ Cξ hξgr).mul (gaussBdd_inv a b)).mul (gaussBdd_invGammaFactor K a b)
  obtain ⟨B₁, C₁, hB₁, hC₁, hG₁⟩ := hG

  obtain ⟨B₀, hB₀⟩ := (isCompact_rect a b).exists_bound_of_continuousOn hR.continuous.continuousOn
  refine ⟨max B₀ B₁, C₁, fun s hsa hsb => ?_⟩
  have hexp1 : 1 ≤ Real.exp (C₁ * s.im ^ 2) := Real.one_le_exp (by positivity)
  rcases le_or_gt 2 |s.im| with hbig | hsmall
  · rw [hRξ s hsa hsb hbig]
    calc ‖ξ s * s⁻¹ * invGammaFactor K s‖ ≤ B₁ * Real.exp (C₁ * s.im ^ 2) := hG₁ s hsa hsb hbig
      _ ≤ max B₀ B₁ * Real.exp (C₁ * s.im ^ 2) :=
          mul_le_mul_of_nonneg_right (le_max_right _ _) (Real.exp_pos _).le
  · have hmem : s ∈ (Set.Icc a b ×ℂ Set.Icc (-2 : ℝ) 2) := by
      refine ⟨⟨hsa, hsb⟩, ?_⟩
      have := abs_lt.mp hsmall
      exact ⟨this.1.le, this.2.le⟩
    have h0 := hB₀ s hmem
    have hB₀0 : 0 ≤ B₀ := (norm_nonneg _).trans h0
    calc ‖R s‖ ≤ B₀ := h0
      _ ≤ max B₀ B₁ := le_max_left _ _
      _ = max B₀ B₁ * 1 := (mul_one _).symm
      _ ≤ max B₀ B₁ * Real.exp (C₁ * s.im ^ 2) :=
          mul_le_mul_of_nonneg_left hexp1 (hB₀0.trans (le_max_left _ _))

end main

end R4Z2a

end

theorem solution
    (K : Type) [Field K] [NumberField K] (R : ℂ → ℂ) (hR : Differentiable ℂ R)
    (hRζ : ∀ s : ℂ, 1 < s.re → R s = (s - 1) * NumberField.dedekindZeta K s) (a b : ℝ) :
    ∃ B C : ℝ, ∀ s : ℂ, a ≤ s.re → s.re ≤ b → ‖R s‖ ≤ B * Real.exp (C * s.im ^ 2) :=
  R4Z2a.main K R hR hRζ a b

end S_NumberField_exists_norm_sub_one_mul_dedekindZeta_continuation_le_mul_exp_mul_im_sq
end P2MW
export P2MW.S_NumberField_exists_norm_sub_one_mul_dedekindZeta_continuation_le_mul_exp_mul_im_sq (solution)
