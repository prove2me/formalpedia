-- Prove2me | solution 1 for LanglandsTunnell.Converse.ArchDatumR.continuousOn_gaussian_mul_integral_W_diagOne_torusKernel
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:08.353894+00:00
-- url     : https://prove2.me/submissions/bf816989-6cad-5695-860d-7be50b3ea5bd

import Definitions.Def_LanglandsTunnell_CubicInduction_JacquetVector3
import Mathlib.Analysis.MellinTransform
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_LanglandsTunnell_Converse_ArchDatumR_continuousOn_gaussian_mul_integral_W_diagOne_torusKernel

set_option autoImplicit false

open NumberField AutomorphicForm LanglandsTunnell LanglandsTunnell.Converse MeasureTheory

namespace Ws23HCont

open LanglandsTunnell.Converse.ArchR Set

theorem isK_one : IsK (1 : Matrix (Fin 2) (Fin 2) ℝ) := by
  unfold IsK; exact Submonoid.one_mem _

theorem exists_bound_torus {P : RealArchParam} (D : ArchDatumR P) :
    ∃ C σD : ℝ, 0 ≤ C ∧ 0 ≤ σD ∧ ∀ τ : ℝ, τ ≠ 0 → ‖D.W (diagOne τ)‖ ≤ C * (1 + |τ| ^ (-σD)) := by
  obtain ⟨C₁, h₁⟩ := D.decay_top 0 0
  obtain ⟨C₂, σ, h₂⟩ := D.decay_zero 0
  have hval : ∀ τ : ℝ, ‖iteratedFDerivWithin ℝ 0 (asPi D.W) glSet (diagOneMulCoords τ 1)‖ = ‖D.W (diagOne τ)‖ := by
    intro τ
    rw [norm_iteratedFDerivWithin_zero]
    simp [asPi, diagOneMulCoords]
  refine ⟨|C₁| + |C₂|, max σ 0, by positivity, le_max_right _ _, fun τ hτ => ?_⟩
  have hτ' : 0 < |τ| := abs_pos.2 hτ
  have hp : 0 ≤ |τ| ^ (-max σ 0) := Real.rpow_nonneg hτ'.le _
  rcases le_or_gt 1 |τ| with h | h
  · have := h₁ τ 1 isK_one h
    rw [hval] at this
    simp only [CharP.cast_eq_zero, neg_zero, Real.rpow_zero, mul_one] at this
    calc ‖D.W (diagOne τ)‖ ≤ C₁ := this
      _ ≤ |C₁| + |C₂| := by have := le_abs_self C₁; have := abs_nonneg C₂; linarith
      _ ≤ (|C₁| + |C₂|) * (1 + |τ| ^ (-max σ 0)) := by nlinarith [abs_nonneg C₁, abs_nonneg C₂]
  · have := h₂ τ 1 isK_one hτ h.le
    rw [hval] at this
    have hmono : |τ| ^ (-σ) ≤ |τ| ^ (-max σ 0) :=
      Real.rpow_le_rpow_of_exponent_ge hτ' h.le (by simp)
    calc ‖D.W (diagOne τ)‖ ≤ C₂ * |τ| ^ (-σ) := this
      _ ≤ |C₂| * |τ| ^ (-max σ 0) := by
          have hnn : 0 ≤ |τ| ^ (-σ) := Real.rpow_nonneg hτ'.le _
          calc C₂ * |τ| ^ (-σ) ≤ |C₂| * |τ| ^ (-σ) := mul_le_mul_of_nonneg_right (le_abs_self C₂) hnn
            _ ≤ |C₂| * |τ| ^ (-max σ 0) := mul_le_mul_of_nonneg_left hmono (abs_nonneg C₂)
      _ ≤ (|C₁| + |C₂|) * (1 + |τ| ^ (-max σ 0)) := by nlinarith [abs_nonneg C₁, abs_nonneg C₂]

theorem continuousOn_quasiChar (u : ℂ) (b : ZMod 2) : ContinuousOn (fun r : ℝ => quasiChar u b r) {r | r ≠ 0} := by
  intro r hr
  refine ContinuousAt.continuousWithinAt ?_
  unfold quasiChar
  refine ContinuousAt.mul ?_ ?_
  · exact (Complex.continuousAt_ofReal_cpow_const |r| u (Or.inr (abs_ne_zero.2 hr))).comp continuous_abs.continuousAt
  · split_ifs
    · exact continuousAt_const
    · exact ((continuous_of_discreteTopology (f := fun s : SignType => ((s : ℝ) : ℂ))).continuousAt).comp
        (continuousAt_sign_of_ne_zero hr)

theorem norm_quasiChar {u : ℂ} {b : ZMod 2} {r : ℝ} (hr : r ≠ 0) : ‖quasiChar u b r‖ = |r| ^ u.re := by
  unfold quasiChar
  rw [norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos (abs_pos.2 hr)]
  split_ifs
  · simp
  · rcases lt_or_gt_of_ne hr with h | h
    · rw [sign_neg h]; simp
    · rw [sign_pos h]; simp

namespace KB

variable {b : ℝ} (hb : 0 < b)
include hb

noncomputable def kb (b N : ℝ) (w : ℝ) : ℝ := w ^ N * Real.exp (-(b * (w ^ 2 + (w ^ 2)⁻¹)))

theorem kb_pos (N : ℝ) {w : ℝ} (hw : 0 < w) : 0 < kb b N w :=
  mul_pos (Real.rpow_pos_of_pos hw N) (Real.exp_pos _)

theorem measurable_kb (N : ℝ) : Measurable (kb b N) := by
  unfold kb
  exact (measurable_id.pow_const N).mul (Real.measurable_exp.comp
    (((measurable_id.pow_const 2).add ((measurable_id.pow_const 2).inv)).const_mul b).neg)

theorem continuousOn_kb (N : ℝ) : ContinuousOn (kb b N) (Ioi 0) := by
  intro w hw
  have hw' : w ≠ 0 := ne_of_gt hw
  unfold kb
  refine ContinuousAt.continuousWithinAt ?_
  refine (Real.continuousAt_rpow_const w N (Or.inl hw')).mul ?_
  refine (Real.continuous_exp.continuousAt).comp ?_
  exact (((continuousAt_id.pow 2).add ((continuousAt_id.pow 2).inv₀ (pow_ne_zero 2 hw'))).const_mul _).neg

theorem exp_neg_inv_sq_le (n : ℕ) {w : ℝ} (hw : 0 < w) :
    Real.exp (-(b * (w ^ 2)⁻¹)) ≤ (n.factorial : ℝ) * b⁻¹ ^ n * w ^ (2 * n) := by
  have hu : 0 ≤ b * (w ^ 2)⁻¹ := by positivity
  have h := Real.pow_div_factorial_le_exp _ hu n
  have hpos : 0 < (b * (w ^ 2)⁻¹) ^ n / n.factorial := by positivity
  rw [Real.exp_neg]
  calc (Real.exp (b * (w ^ 2)⁻¹))⁻¹ ≤ ((b * (w ^ 2)⁻¹) ^ n / n.factorial)⁻¹ :=
        inv_anti₀ hpos h
    _ = (n.factorial : ℝ) * b⁻¹ ^ n * w ^ (2 * n) := by
        rw [inv_div, mul_pow, inv_pow, pow_mul]
        field_simp
        rw [one_div, inv_pow, mul_inv_cancel₀ (pow_ne_zero n hb.ne')]

theorem integrableOn_rpow_mul_kb (N σ : ℝ) : IntegrableOn (fun t : ℝ => t ^ (σ - 1) * kb b N t) (Ioi 0) := by
  have hcont : ContinuousOn (fun t : ℝ => t ^ (σ - 1) * kb b N t) (Ioi 0) := fun t ht =>
    ((Real.continuousAt_rpow_const t (σ - 1) (Or.inl (ne_of_gt ht))).continuousWithinAt).mul (continuousOn_kb hb N t ht)
  rw [← Ioc_union_Ioi_eq_Ioi zero_le_one]
  refine IntegrableOn.union ?_ ?_
  ·
    set p : ℝ := σ - 1 + N with hp
    obtain ⟨n, hn⟩ : ∃ n : ℕ, -p ≤ 2 * n := by
      obtain ⟨n, hn⟩ := exists_nat_ge (-p / 2)
      exact ⟨n, by linarith⟩
    set C : ℝ := (n.factorial : ℝ) * b⁻¹ ^ n with hC
    refine Measure.integrableOn_of_bounded (M := C) (by simp) ((measurable_id.pow_const (σ - 1)).mul (measurable_kb hb N)).aestronglyMeasurable ?_
    · refine (ae_restrict_iff' measurableSet_Ioc).2 (ae_of_all _ fun t ht => ?_)
      obtain ⟨ht0, ht1⟩ := ht
      have hkb := kb_pos hb N ht0
      rw [Real.norm_eq_abs, abs_of_pos (mul_pos (Real.rpow_pos_of_pos ht0 _) hkb)]

      have h1 : t ^ (σ - 1) * kb b N t = t ^ p * (Real.exp (-(b * t ^ 2)) * Real.exp (-(b * (t ^ 2)⁻¹))) := by
        rw [kb, hp, ← Real.exp_add, Real.rpow_add ht0]; ring_nf
      rw [h1]
      have h2 : Real.exp (-(b * t ^ 2)) ≤ 1 := by
        rw [Real.exp_le_one_iff]; nlinarith [hb, sq_nonneg t]
      have h3 := exp_neg_inv_sq_le hb n ht0
      have htp : 0 < t ^ p := Real.rpow_pos_of_pos ht0 _
      calc t ^ p * (Real.exp (-(b * t ^ 2)) * Real.exp (-(b * (t ^ 2)⁻¹)))
          ≤ t ^ p * (1 * (C * t ^ (2 * n))) := by
            refine mul_le_mul_of_nonneg_left (mul_le_mul h2 h3 (Real.exp_pos _).le zero_le_one) htp.le
        _ = C * (t ^ p * t ^ ((2 * n : ℕ) : ℝ)) := by rw [Real.rpow_natCast]; ring
        _ = C * t ^ (p + 2 * n) := by rw [← Real.rpow_add ht0]; push_cast; ring_nf
        _ ≤ C * 1 := by
            refine mul_le_mul_of_nonneg_left ?_ (by positivity)
            exact Real.rpow_le_one ht0.le ht1 (by linarith)
        _ = C := mul_one C
  ·
    set p : ℝ := σ - 1 + N with hp
    set p' : ℝ := max p 0 with hp'
    have hdom := (integrableOn_rpow_mul_exp_neg_mul_sq hb (s := p') (by rw [hp']; exact lt_of_lt_of_le neg_one_lt_zero (le_max_right _ _))).mono_set
      (Ioi_subset_Ioi zero_le_one)
    refine Integrable.mono' hdom ((hcont.mono (Ioi_subset_Ioi zero_le_one)).aestronglyMeasurable measurableSet_Ioi) ?_
    refine (ae_restrict_iff' measurableSet_Ioi).2 (ae_of_all _ fun t (ht : 1 < t) => ?_)
    have ht0 : 0 < t := one_pos.trans ht
    rw [Real.norm_eq_abs, abs_of_pos (mul_pos (Real.rpow_pos_of_pos ht0 _) (kb_pos hb N ht0))]
    have h1 : t ^ (σ - 1) * kb b N t = t ^ p * (Real.exp (-(b * t ^ 2)) * Real.exp (-(b * (t ^ 2)⁻¹))) := by
      rw [kb, hp, ← Real.exp_add, Real.rpow_add ht0]; ring_nf
    rw [h1]
    have h2 : Real.exp (-(b * (t ^ 2)⁻¹)) ≤ 1 := by
      rw [Real.exp_le_one_iff]
      have : 0 < (t ^ 2)⁻¹ := by positivity
      nlinarith [hb]
    have h3 : t ^ p ≤ t ^ p' := Real.rpow_le_rpow_of_exponent_le ht.le (le_max_left _ _)
    calc t ^ p * (Real.exp (-(b * t ^ 2)) * Real.exp (-(b * (t ^ 2)⁻¹)))
        ≤ t ^ p' * (Real.exp (-(b * t ^ 2)) * 1) :=
          mul_le_mul h3 (mul_le_mul_of_nonneg_left h2 (Real.exp_pos _).le) (by positivity) (by positivity)
      _ = t ^ p' * Real.exp (-b * t ^ 2) := by ring_nf

end KB

theorem continuousOn_torus {P : RealArchParam} (D : ArchDatumR P) :
    ContinuousOn (fun τ : ℝ => D.W (diagOne τ)) {τ | τ ≠ 0} := by
  have hc : Continuous fun τ : ℝ => (fun i j => (!![τ, 0; 0, 1] : Matrix (Fin 2) (Fin 2) ℝ) i j : Fin 2 → Fin 2 → ℝ) := by
    refine continuous_pi fun i => continuous_pi fun j => ?_
    fin_cases i <;> fin_cases j <;> simp <;> fun_prop
  have hmaps : Set.MapsTo (fun τ : ℝ => (fun i j => (!![τ, 0; 0, 1] : Matrix (Fin 2) (Fin 2) ℝ) i j : Fin 2 → Fin 2 → ℝ))
      {τ | τ ≠ 0} glSet := by
    intro τ hτ
    show (Matrix.of fun i j => (!![τ, 0; 0, 1] : Matrix (Fin 2) (Fin 2) ℝ) i j).det ≠ 0
    rw [Matrix.det_fin_two]
    simpa using hτ
  have h := D.smooth.continuousOn.comp hc.continuousOn hmaps
  refine h.congr fun τ _ => ?_
  show D.W (diagOne τ) = D.W (Matrix.of fun i j => (!![τ, 0; 0, 1] : Matrix (Fin 2) (Fin 2) ℝ) i j)
  rfl

end Ws23HCont

open Ws23HCont in
open LanglandsTunnell.Converse.ArchR Set in

theorem solution
    {P₂ : RealArchParam} (D : ArchDatumR P₂) (a : ℝ) (ha : a ≠ 0) (ν : ℂ)
    (H : ℝ → ℂ)
    (hH : H = fun σ' => (Real.exp (-(Real.pi * a ^ 2 * σ' ^ 2)) : ℂ) *
        ∫ w in Set.Ioi (0 : ℝ),
          D.W (ArchR.diagOne (a * (σ' / w))) *
            (ArchR.centralChar P₂ w * ((|w| : ℝ) : ℂ)) * ((w : ℝ) : ℂ) ^ ν *
            (Real.exp (-(Real.pi * ((w ^ 2)⁻¹ + a ^ 2 * w ^ 2))) : ℂ)) :
    ContinuousOn H (Set.Ioi 0) := by
  subst hH
  obtain ⟨C, σD, hC, hσD, hbd⟩ := exists_bound_torus D
  have hf := continuousOn_torus D
  have hmin : 0 < min 1 (a ^ 2) := lt_min one_pos (by positivity)
  set b : ℝ := Real.pi * min 1 (a ^ 2) with hb
  have hb0 : 0 < b := by positivity
  set N : ℝ := P₂.centralExponent.re + 1 + ν.re with hN
  set F : ℝ → ℝ → ℂ := fun σ' w => D.W (ArchR.diagOne (a * (σ' / w))) *
      (ArchR.centralChar P₂ w * ((|w| : ℝ) : ℂ)) * ((w : ℝ) : ℂ) ^ ν *
      (Real.exp (-(Real.pi * ((w ^ 2)⁻¹ + a ^ 2 * w ^ 2))) : ℂ) with hF

  have hcontw : ∀ σ' : ℝ, σ' ≠ 0 → ContinuousOn (F σ') (Ioi 0) := by
    intro σ' hσ'
    have h1 : ContinuousOn (fun w : ℝ => D.W (ArchR.diagOne (a * (σ' / w)))) (Ioi 0) := by
      refine hf.comp (continuousOn_const.mul (continuousOn_const.div continuousOn_id fun w hw => ne_of_gt hw)) ?_
      intro w hw; exact mul_ne_zero ha (div_ne_zero hσ' (ne_of_gt hw))
    have h2 : ContinuousOn (fun w : ℝ => ArchR.centralChar P₂ w) (Ioi 0) := by
      simp only [ArchR.centralChar]
      exact (continuousOn_quasiChar _ _).mono fun w hw => ne_of_gt hw
    have h3 : Continuous fun w : ℝ => (((|w| : ℝ)) : ℂ) := by fun_prop
    have h4 : ContinuousOn (fun w : ℝ => ((w : ℝ) : ℂ) ^ ν) (Ioi 0) := fun w hw =>
      (Complex.continuousAt_ofReal_cpow_const w ν (Or.inr (ne_of_gt hw))).continuousWithinAt
    have h5 : ContinuousOn (fun w : ℝ => (Real.exp (-(Real.pi * ((w ^ 2)⁻¹ + a ^ 2 * w ^ 2))) : ℂ)) (Ioi 0) := by
      refine Complex.continuous_ofReal.continuousOn.comp (Real.continuous_exp.continuousOn.comp ?_ (Set.mapsTo_univ _ _)) (Set.mapsTo_univ _ _)
      exact (continuousOn_const.mul (((continuous_id.pow 2).continuousOn.inv₀ fun w hw => pow_ne_zero 2 (ne_of_gt hw)).add
        (continuous_const.mul (continuous_id.pow 2)).continuousOn)).neg
    simp only [hF]
    exact ((h1.mul (h2.mul h3.continuousOn)).mul h4).mul h5

  refine ContinuousOn.mul (Complex.continuous_ofReal.comp (by fun_prop : Continuous fun σ' : ℝ =>
    Real.exp (-(Real.pi * a ^ 2 * σ' ^ 2)))).continuousOn ?_
  intro σ₀ hσ₀
  have hσ₀' : 0 < σ₀ := hσ₀
  apply ContinuousAt.continuousWithinAt
  change ContinuousAt (fun σ' : ℝ => ∫ w in Ioi (0 : ℝ), F σ' w) σ₀
  set K₀ : ℝ := (|a| * (σ₀ / 2)) ^ (-σD) with hK₀
  have hK₀0 : 0 ≤ K₀ := Real.rpow_nonneg (by positivity) _
  refine continuousAt_of_dominated (μ := volume.restrict (Ioi 0)) (F := F) (x₀ := σ₀)
    (bound := fun w => C * KB.kb b N w + (C * K₀) * KB.kb b (N + σD) w) ?_ ?_ ?_ ?_
  ·
    exact Filter.eventually_of_mem (Ioi_mem_nhds hσ₀') fun σ' hσ' =>
      (hcontw σ' (ne_of_gt hσ')).aestronglyMeasurable measurableSet_Ioi
  ·
    refine Filter.eventually_of_mem (Ioo_mem_nhds (by linarith : σ₀ / 2 < σ₀) (by linarith : σ₀ < 2 * σ₀)) fun σ' hσ' => ?_
    obtain ⟨hσ'1, hσ'2⟩ := hσ'
    have hσ'0 : 0 < σ' := by linarith
    refine (ae_restrict_iff' measurableSet_Ioi).2 (ae_of_all _ fun w (hw : 0 < w) => ?_)
    have hw' : w ≠ 0 := hw.ne'
    have hτ : a * (σ' / w) ≠ 0 := mul_ne_zero ha (div_ne_zero hσ'0.ne' hw')

    have hE : Real.exp (-(Real.pi * ((w ^ 2)⁻¹ + a ^ 2 * w ^ 2))) ≤ Real.exp (-(b * (w ^ 2 + (w ^ 2)⁻¹))) := by
      rw [Real.exp_le_exp, hb, neg_le_neg_iff]
      have h1 : min 1 (a ^ 2) * w ^ 2 ≤ a ^ 2 * w ^ 2 := mul_le_mul_of_nonneg_right (min_le_right _ _) (sq_nonneg w)
      have h2 : min 1 (a ^ 2) * (w ^ 2)⁻¹ ≤ (w ^ 2)⁻¹ := by
        have : 0 ≤ (w ^ 2)⁻¹ := by positivity
        nlinarith [min_le_left (1 : ℝ) (a ^ 2)]
      nlinarith [Real.pi_pos]
    have hnorm : ‖F σ' w‖ = ‖D.W (ArchR.diagOne (a * (σ' / w)))‖ *
        (w ^ N * Real.exp (-(Real.pi * ((w ^ 2)⁻¹ + a ^ 2 * w ^ 2)))) := by
      simp only [hF, norm_mul, ArchR.centralChar, norm_quasiChar hw', Complex.norm_real, Real.norm_eq_abs,
        abs_of_pos hw, Complex.norm_cpow_eq_rpow_re_of_pos hw, abs_of_pos (Real.exp_pos _), hN]
      rw [Real.rpow_add hw, Real.rpow_add hw, Real.rpow_one]; ring
    have hfb : ‖D.W (ArchR.diagOne (a * (σ' / w)))‖ ≤ C * (1 + K₀ * w ^ σD) := by
      refine (hbd _ hτ).trans (mul_le_mul_of_nonneg_left ?_ hC)
      refine add_le_add le_rfl ?_
      have habs : |a * (σ' / w)| = (|a| * σ') / w := by
        rw [abs_mul, abs_div, abs_of_pos hσ'0, abs_of_pos hw, mul_div_assoc]
      rw [habs, Real.div_rpow (by positivity) hw.le, Real.rpow_neg hw.le, div_inv_eq_mul]
      refine mul_le_mul_of_nonneg_right ?_ (Real.rpow_nonneg hw.le _)
      rw [hK₀]
      exact Real.rpow_le_rpow_of_nonpos (by positivity) (by nlinarith [abs_nonneg a, abs_pos.2 ha]) (by linarith)
    rw [hnorm]
    show _ ≤ C * KB.kb b N w + C * K₀ * KB.kb b (N + σD) w
    have hkb1 : KB.kb b N w = w ^ N * Real.exp (-(b * (w ^ 2 + (w ^ 2)⁻¹))) := rfl
    have hkb2 : KB.kb b (N + σD) w = w ^ σD * w ^ N * Real.exp (-(b * (w ^ 2 + (w ^ 2)⁻¹))) := by
      rw [KB.kb, Real.rpow_add hw]; ring
    rw [hkb1, hkb2]
    have hwN : 0 ≤ w ^ N := Real.rpow_nonneg hw.le _
    have hwD : 0 ≤ w ^ σD := Real.rpow_nonneg hw.le _
    have hE0 : 0 ≤ Real.exp (-(Real.pi * ((w ^ 2)⁻¹ + a ^ 2 * w ^ 2))) := (Real.exp_pos _).le
    calc ‖D.W (ArchR.diagOne (a * (σ' / w)))‖ * (w ^ N * Real.exp (-(Real.pi * ((w ^ 2)⁻¹ + a ^ 2 * w ^ 2))))
        ≤ (C * (1 + K₀ * w ^ σD)) * (w ^ N * Real.exp (-(b * (w ^ 2 + (w ^ 2)⁻¹)))) :=
          mul_le_mul hfb (mul_le_mul_of_nonneg_left hE hwN) (mul_nonneg hwN hE0) (by positivity)
      _ = C * (w ^ N * Real.exp (-(b * (w ^ 2 + (w ^ 2)⁻¹)))) +
            C * K₀ * (w ^ σD * w ^ N * Real.exp (-(b * (w ^ 2 + (w ^ 2)⁻¹)))) := by ring
  ·
    have hk : ∀ M : ℝ, IntegrableOn (KB.kb b M) (Ioi 0) := fun M =>
      (KB.integrableOn_rpow_mul_kb hb0 M 1).congr_fun (fun t ht => by beta_reduce; rw [sub_self, Real.rpow_zero, one_mul]) measurableSet_Ioi
    exact ((hk N).const_mul C).add ((hk (N + σD)).const_mul (C * K₀))
  ·
    refine (ae_restrict_iff' measurableSet_Ioi).2 (ae_of_all _ fun w (hw : 0 < w) => ?_)
    have hτ : a * (σ₀ / w) ≠ 0 := mul_ne_zero ha (div_ne_zero hσ₀'.ne' hw.ne')
    have h0 : ContinuousAt (fun σ' : ℝ => a * (σ' / w)) σ₀ := (continuous_const.mul (continuous_id.div_const w)).continuousAt
    have h1 : ContinuousAt (fun σ' : ℝ => D.W (ArchR.diagOne (a * (σ' / w)))) σ₀ :=
      ContinuousAt.comp (f := fun σ' : ℝ => a * (σ' / w)) (g := fun τ : ℝ => D.W (ArchR.diagOne τ)) (x := σ₀)
        (hf.continuousAt (isOpen_ne.mem_nhds hτ)) h0
    simp only [hF]
    exact ((h1.mul continuousAt_const).mul continuousAt_const).mul continuousAt_const

end S_LanglandsTunnell_Converse_ArchDatumR_continuousOn_gaussian_mul_integral_W_diagOne_torusKernel
end P2MW
export P2MW.S_LanglandsTunnell_Converse_ArchDatumR_continuousOn_gaussian_mul_integral_W_diagOne_torusKernel (solution)
