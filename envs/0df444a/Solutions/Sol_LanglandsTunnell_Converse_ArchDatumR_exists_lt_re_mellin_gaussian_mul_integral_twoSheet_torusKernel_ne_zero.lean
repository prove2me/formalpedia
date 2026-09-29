-- Prove2me | solution 1 for LanglandsTunnell.Converse.ArchDatumR.exists_lt_re_mellin_gaussian_mul_integral_twoSheet_torusKernel_ne_zero
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:08.353894+00:00
-- url     : https://prove2.me/submissions/bba91448-cc00-56c6-82b2-deea7c83a53e

import Definitions.Def_LanglandsTunnell_CubicInduction_JacquetVector3
import Definitions.Def_AutomorphicForm_ArchWeightChar
import Mathlib.Analysis.MellinTransform
import Mathlib.Analysis.MellinInversion
import Mathlib.Analysis.Analytic.IsolatedZeros
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import Mathlib.Topology.Instances.Sign
import Theorems.Thm_LanglandsTunnell_mellinConvergent_integral_mul_comp_mul_and_mellin_eq_mellin_mul_mellin
import Theorems.Thm_LanglandsTunnell_mellinConvergent_and_mellin_ofReal_pos_rpow_mul_exp_neg_mul_sq_add_inv_sq
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_LanglandsTunnell_Converse_ArchDatumR_exists_lt_re_mellin_gaussian_mul_integral_twoSheet_torusKernel_ne_zero

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

open NumberField AutomorphicForm LanglandsTunnell LanglandsTunnell.Converse MeasureTheory

namespace Ws23HMNZ2

open LanglandsTunnell.Converse.ArchR Set Filter Asymptotics Topology

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

theorem mellinConvergent_kb (N : ℝ) (s : ℂ) : MellinConvergent (fun w : ℝ => (kb b N w : ℂ)) s := by
  have hmeas : AEStronglyMeasurable (fun w : ℝ => (kb b N w : ℂ)) (volume.restrict (Ioi 0)) :=
    (Complex.continuous_ofReal.continuousOn.comp (continuousOn_kb hb N) (mapsTo_univ _ _)).aestronglyMeasurable measurableSet_Ioi
  rw [MellinConvergent, mellin_convergent_iff_norm (subset_refl _) measurableSet_Ioi hmeas]
  refine (integrableOn_rpow_mul_kb hb N s.re).congr_fun (fun t ht => ?_) measurableSet_Ioi
  rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos (kb_pos hb N ht)]

theorem mellin_kb_ofReal (N x : ℝ) :
    mellin (fun w : ℝ => (kb b N w : ℂ)) (x : ℂ) = ((∫ t in Ioi (0 : ℝ), t ^ (x - 1) * kb b N t : ℝ) : ℂ) := by
  rw [mellin]
  refine (setIntegral_congr_fun measurableSet_Ioi fun t (ht : 0 < t) => ?_).trans integral_ofReal
  show (t : ℂ) ^ ((x : ℂ) - 1) • ((kb b N t : ℝ) : ℂ) = ((t ^ (x - 1) * kb b N t : ℝ) : ℂ)
  rw [smul_eq_mul, Complex.ofReal_mul, Complex.ofReal_cpow ht.le]
  push_cast
  rfl

theorem mellin_kb_re_pos (N x : ℝ) : 0 < ∫ t in Ioi (0 : ℝ), t ^ (x - 1) * kb b N t := by
  rw [setIntegral_pos_iff_support_of_nonneg_ae ?_ (integrableOn_rpow_mul_kb hb N x)]
  · have : Function.support (fun t : ℝ => t ^ (x - 1) * kb b N t) ∩ Ioi 0 = Ioi 0 := by
      refine inter_eq_right.2 fun t ht => ?_
      exact (mul_pos (Real.rpow_pos_of_pos ht _) (kb_pos hb N ht)).ne'
    rw [this, Real.volume_Ioi]; simp
  · exact (ae_restrict_iff' measurableSet_Ioi).2 (ae_of_all _ fun t ht =>
      (mul_pos (Real.rpow_pos_of_pos ht _) (kb_pos hb N ht)).le)

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

section Profile

variable {P : RealArchParam} (D : ArchDatumR P) (a : ℝ) (ha : a ≠ 0) (ε : ℂ)

noncomputable def psiD (r : ℝ) : ℂ := D.W (diagOne (a * r)) + ε * D.W (diagOne (-(a * r)))

include ha in
theorem continuousOn_psiD : ContinuousOn (psiD D a ε) (Ioi 0) := by
  have h1 : ContinuousOn (fun r : ℝ => D.W (diagOne (a * r))) (Ioi 0) :=
    (continuousOn_torus D).comp (continuous_const.mul continuous_id).continuousOn fun r hr => mul_ne_zero ha (ne_of_gt hr)
  have h2 : ContinuousOn (fun r : ℝ => D.W (diagOne (-(a * r)))) (Ioi 0) :=
    (continuousOn_torus D).comp (continuous_const.mul continuous_id).neg.continuousOn fun r hr =>
      neg_ne_zero.2 (mul_ne_zero ha (ne_of_gt hr))
  exact h1.add (continuousOn_const.mul h2)

include ha in
theorem locallyIntegrableOn_psiD : LocallyIntegrableOn (psiD D a ε) (Ioi 0) :=
  (continuousOn_psiD D a ha ε).locallyIntegrableOn measurableSet_Ioi

theorem torus_bound_zero {P : RealArchParam} (D : ArchDatumR P) :
    ∃ C σ : ℝ, ∀ y : ℝ, y ≠ 0 → |y| ≤ 1 → ‖D.W (diagOne y)‖ ≤ C * |y| ^ (-σ) := by
  obtain ⟨C, σ, h⟩ := D.decay_zero 0
  refine ⟨C, σ, fun y hy hy1 => ?_⟩
  have := h y 1 isK_one hy hy1
  rw [norm_iteratedFDerivWithin_zero] at this
  simpa [asPi, diagOneMulCoords] using this

theorem torus_bound_top {P : RealArchParam} (D : ArchDatumR P) (N : ℕ) :
    ∃ C : ℝ, ∀ y : ℝ, 1 ≤ |y| → ‖D.W (diagOne y)‖ ≤ C * |y| ^ (-(N : ℝ)) := by
  obtain ⟨C, h⟩ := D.decay_top 0 N
  refine ⟨C, fun y hy1 => ?_⟩
  have := h y 1 isK_one hy1
  rw [norm_iteratedFDerivWithin_zero] at this
  simpa [asPi, diagOneMulCoords] using this

include ha in
theorem exists_isBigO_psiD_nhds_zero : ∃ σ₀ : ℝ, psiD D a ε =O[𝓝[>] 0] fun r : ℝ => r ^ (-σ₀) := by
  obtain ⟨C, σ, h⟩ := torus_bound_zero D
  refine ⟨σ, ?_⟩
  have ha' : 0 < |a| := abs_pos.2 ha
  refine IsBigO.of_bound ((|C| + ‖ε‖ * |C|) * |a| ^ (-σ)) ?_
  have hmem : Ioc (0 : ℝ) |a|⁻¹ ∈ 𝓝[>] (0 : ℝ) := Ioc_mem_nhdsGT (inv_pos.2 ha')
  filter_upwards [hmem] with r hr
  have hr0 : 0 < r := hr.1
  have har : |a * r| ≤ 1 := by rw [abs_mul, abs_of_pos hr0]; calc |a| * r ≤ |a| * |a|⁻¹ := by gcongr; exact hr.2
    _ = 1 := mul_inv_cancel₀ ha'.ne'
  have hne : a * r ≠ 0 := mul_ne_zero ha hr0.ne'
  have h1 := h (a * r) hne har
  have h2 := h (-(a * r)) (neg_ne_zero.2 hne) (by rwa [abs_neg])
  rw [abs_neg] at h2
  have hpow : |a * r| ^ (-σ) = |a| ^ (-σ) * r ^ (-σ) := by rw [abs_mul, abs_of_pos hr0, Real.mul_rpow ha'.le hr0.le]
  rw [hpow] at h1 h2
  have hp : 0 ≤ |a| ^ (-σ) * r ^ (-σ) := by positivity
  rw [psiD, Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg hr0.le _)]
  calc ‖D.W (diagOne (a * r)) + ε * D.W (diagOne (-(a * r)))‖
      ≤ ‖D.W (diagOne (a * r))‖ + ‖ε‖ * ‖D.W (diagOne (-(a * r)))‖ := by
        refine (norm_add_le _ _).trans ?_; rw [norm_mul]
    _ ≤ |C| * (|a| ^ (-σ) * r ^ (-σ)) + ‖ε‖ * (|C| * (|a| ^ (-σ) * r ^ (-σ))) := by
        gcongr
        · exact h1.trans (mul_le_mul_of_nonneg_right (le_abs_self C) hp)
        · exact h2.trans (mul_le_mul_of_nonneg_right (le_abs_self C) hp)
    _ = (|C| + ‖ε‖ * |C|) * |a| ^ (-σ) * r ^ (-σ) := by ring

include ha in
theorem isBigO_psiD_atTop (A : ℝ) : psiD D a ε =O[atTop] fun r : ℝ => r ^ (-A) := by
  obtain ⟨C, h⟩ := torus_bound_top D (Nat.ceil (max A 0))
  have ha' : 0 < |a| := abs_pos.2 ha
  set N : ℝ := (Nat.ceil (max A 0) : ℝ) with hN
  have hNA : A ≤ N := le_trans (le_max_left A 0) (Nat.le_ceil _)
  refine IsBigO.of_bound ((|C| + ‖ε‖ * |C|) * |a| ^ (-N)) ?_
  filter_upwards [eventually_ge_atTop (max 1 |a|⁻¹)] with r hr
  have hr1 : 1 ≤ r := le_trans (le_max_left _ _) hr
  have hr0 : 0 < r := one_pos.trans_le hr1
  have har : 1 ≤ |a * r| := by
    rw [abs_mul, abs_of_pos hr0]
    calc (1 : ℝ) = |a| * |a|⁻¹ := (mul_inv_cancel₀ ha'.ne').symm
      _ ≤ |a| * r := by gcongr; exact le_trans (le_max_right _ _) hr
  have h1 := h (a * r) har
  have h2 := h (-(a * r)) (by rwa [abs_neg])
  rw [abs_neg] at h2
  have hpow : |a * r| ^ (-N) = |a| ^ (-N) * r ^ (-N) := by rw [abs_mul, abs_of_pos hr0, Real.mul_rpow ha'.le hr0.le]
  rw [hpow] at h1 h2
  have hp : 0 ≤ |a| ^ (-N) * r ^ (-N) := by positivity
  rw [psiD, Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg hr0.le _)]
  have hrr : r ^ (-N) ≤ r ^ (-A) := Real.rpow_le_rpow_of_exponent_le hr1 (by linarith)
  calc ‖D.W (diagOne (a * r)) + ε * D.W (diagOne (-(a * r)))‖
      ≤ ‖D.W (diagOne (a * r))‖ + ‖ε‖ * ‖D.W (diagOne (-(a * r)))‖ := by
        refine (norm_add_le _ _).trans ?_; rw [norm_mul]
    _ ≤ |C| * (|a| ^ (-N) * r ^ (-N)) + ‖ε‖ * (|C| * (|a| ^ (-N) * r ^ (-N))) := by
        gcongr
        · exact h1.trans (mul_le_mul_of_nonneg_right (le_abs_self C) hp)
        · exact h2.trans (mul_le_mul_of_nonneg_right (le_abs_self C) hp)
    _ = (|C| + ‖ε‖ * |C|) * |a| ^ (-N) * r ^ (-N) := by ring
    _ ≤ (|C| + ‖ε‖ * |C|) * |a| ^ (-N) * r ^ (-A) := by gcongr

include ha in
theorem exists_abscissa_psiD : ∃ σ₀ : ℝ, (∀ s : ℂ, σ₀ < s.re → MellinConvergent (psiD D a ε) s) ∧
    DifferentiableOn ℂ (mellin (psiD D a ε)) {s : ℂ | σ₀ < s.re} := by
  obtain ⟨σ₀, hbot⟩ := exists_isBigO_psiD_nhds_zero D a ha ε
  refine ⟨σ₀, fun s hs => ?_, fun s hs => ?_⟩
  · exact mellinConvergent_of_isBigO_rpow (locallyIntegrableOn_psiD D a ha ε) (isBigO_psiD_atTop D a ha ε (s.re + 1))
      (by linarith) hbot hs
  · exact (mellin_differentiableAt_of_isBigO_rpow (locallyIntegrableOn_psiD D a ha ε) (isBigO_psiD_atTop D a ha ε (s.re + 1))
      (by linarith) hbot hs).differentiableWithinAt

end Profile

section Kernel

variable {P : RealArchParam} (a : ℝ) (ha : a ≠ 0) (ν : ℂ)

noncomputable def Efun (w : ℝ) : ℂ := (Real.exp (-(Real.pi * ((w ^ 2)⁻¹ + a ^ 2 * w ^ 2))) : ℂ)

noncomputable def kfun (P : RealArchParam) (w : ℝ) : ℂ :=
  (centralChar P w * ((|w| : ℝ) : ℂ)) * ((w : ℝ) : ℂ) ^ ν * Efun a w

noncomputable def Etil (u : ℝ) : ℂ := ((u ^ (0 : ℝ) * Real.exp (-(Real.pi * |a| * (u ^ 2 + (u ^ 2)⁻¹))) : ℝ) : ℂ)

include ha in
theorem Efun_eq (w : ℝ) (hw : 0 < w) : Efun a w = Etil a (Real.sqrt |a| * w) := by
  have ha' : 0 < |a| := abs_pos.2 ha
  have hs : Real.sqrt |a| ^ 2 = |a| := Real.sq_sqrt ha'.le
  have hsw : 0 < Real.sqrt |a| * w := mul_pos (Real.sqrt_pos.2 ha') hw
  rw [Efun, Etil, Real.rpow_zero, one_mul]
  congr 2
  rw [mul_pow, hs]
  have hw2 : w ^ 2 ≠ 0 := pow_ne_zero 2 hw.ne'
  have : a ^ 2 = |a| ^ 2 := (sq_abs a).symm
  rw [this]
  field_simp
  ring

noncomputable def β (P : RealArchParam) (ν : ℂ) : ℂ := P.centralExponent + 1 + ν

theorem kfun_eq_on {w : ℝ} (hw : 0 < w) : kfun a ν P w = ((w : ℝ) : ℂ) ^ β P ν • Efun a w := by
  have hw0 : ((w : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 hw.ne'
  rw [kfun, centralChar, quasiChar, abs_of_pos hw, β, smul_eq_mul, Complex.cpow_add _ _ hw0, Complex.cpow_add _ _ hw0,
    Complex.cpow_one]
  split_ifs
  · ring
  · rw [sign_pos hw]; simp

include ha in
theorem mellinConvergent_kfun (s : ℂ) : MellinConvergent (kfun a ν P) s := by
  have ha' : 0 < |a| := abs_pos.2 ha
  have hb : 0 < Real.pi * |a| := by positivity
  have hα : 0 < Real.sqrt |a| := Real.sqrt_pos.2 ha'
  have h1 : MellinConvergent (fun w : ℝ => ((w : ℝ) : ℂ) ^ β P ν • Efun a w) s := by
    rw [MellinConvergent.cpow_smul]
    have h2 : MellinConvergent (fun w : ℝ => Etil a (Real.sqrt |a| * w)) (s + β P ν) :=
      (MellinConvergent.comp_mul_left hα).2
        ((LanglandsTunnell.mellinConvergent_and_mellin_ofReal_pos_rpow_mul_exp_neg_mul_sq_add_inv_sq _ hb 0).1 _)
    exact (integrableOn_congr_fun (fun w hw => by rw [Efun_eq a ha w hw]) measurableSet_Ioi).2 h2
  exact (integrableOn_congr_fun (fun w hw => by rw [kfun_eq_on a ν hw]) measurableSet_Ioi).2 h1

include ha in

theorem mellin_kfun_ne_zero (s : ℂ) (hs : (s + β P ν).im = 0) : mellin (kfun a ν P) s ≠ 0 := by
  have ha' : 0 < |a| := abs_pos.2 ha
  have hb : 0 < Real.pi * |a| := by positivity
  have hα : 0 < Real.sqrt |a| := Real.sqrt_pos.2 ha'
  have h1 : mellin (kfun a ν P) s = mellin (fun w : ℝ => ((w : ℝ) : ℂ) ^ β P ν • Efun a w) s :=
    setIntegral_congr_fun measurableSet_Ioi fun w hw => by rw [kfun_eq_on a ν hw]
  have h2 : mellin (Efun a) (s + β P ν) = mellin (fun w : ℝ => Etil a (Real.sqrt |a| * w)) (s + β P ν) :=
    setIntegral_congr_fun measurableSet_Ioi fun w hw => by rw [Efun_eq a ha w hw]
  rw [h1, mellin_cpow_smul, h2, mellin_comp_mul_left _ _ hα]
  set x : ℝ := (s + β P ν).re with hx
  have hsx : s + β P ν = (x : ℂ) := by apply Complex.ext <;> simp [hx, hs]
  obtain ⟨r, hr, hmr⟩ := (LanglandsTunnell.mellinConvergent_and_mellin_ofReal_pos_rpow_mul_exp_neg_mul_sq_add_inv_sq _ hb 0).2 x
  rw [hsx, show (mellin (Etil a) (x : ℂ)) = (r : ℂ) from hmr, smul_eq_mul]
  refine mul_ne_zero ?_ (by exact_mod_cast hr.ne')
  rw [Ne, Complex.cpow_eq_zero_iff, not_and_or]; left; exact_mod_cast hα.ne'

include ha in
theorem continuousOn_kfun : ContinuousOn (kfun a ν P) (Ioi 0) := by
  have h4 : ContinuousOn (fun w : ℝ => centralChar P w) (Ioi 0) :=
    (continuousOn_quasiChar _ _).mono fun w hw => ne_of_gt hw
  have h5 : Continuous fun w : ℝ => (((|w| : ℝ)) : ℂ) := by fun_prop
  have h6 : ContinuousOn (fun w : ℝ => ((w : ℝ) : ℂ) ^ ν) (Ioi 0) := fun w hw =>
    (Complex.continuousAt_ofReal_cpow_const w ν (Or.inr (ne_of_gt hw))).continuousWithinAt
  have h7 : ContinuousOn (Efun a) (Ioi 0) := by
    refine Complex.continuous_ofReal.continuousOn.comp (Real.continuous_exp.continuousOn.comp ?_ (Set.mapsTo_univ _ _)) (Set.mapsTo_univ _ _)
    exact (continuousOn_const.mul (((continuous_id.pow 2).continuousOn.inv₀ fun w hw => pow_ne_zero 2 (ne_of_gt hw)).add
      (continuous_const.mul (continuous_id.pow 2)).continuousOn)).neg
  unfold kfun
  exact ((h4.mul h5.continuousOn).mul h6).mul h7

theorem norm_kfun {w : ℝ} (hw : 0 < w) :
    ‖kfun a ν P w‖ = w ^ P.centralExponent.re * w * w ^ ν.re * Real.exp (-(Real.pi * ((w ^ 2)⁻¹ + a ^ 2 * w ^ 2))) := by
  rw [kfun, Efun, norm_mul, norm_mul, norm_mul, centralChar, norm_quasiChar hw.ne', abs_of_pos hw, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos hw, Complex.norm_cpow_eq_rpow_re_of_pos hw, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]

include ha in

theorem integrableOn_rpow_mul_norm_kfun (p : ℝ) : IntegrableOn (fun w : ℝ => w ^ p * ‖kfun a ν P w‖) (Ioi 0) := by
  set b : ℝ := Real.pi * min 1 (a ^ 2) with hb
  have hbpos : 0 < b := by have : 0 < a ^ 2 := sq_pos_of_ne_zero ha; positivity
  have hdom : IntegrableOn (fun w : ℝ => KB.kb b (p + P.centralExponent.re + 1 + ν.re) w) (Ioi 0) := by
    have := KB.integrableOn_rpow_mul_kb hbpos (p + P.centralExponent.re + 1 + ν.re) 1
    simpa using this
  have hmeas : AEStronglyMeasurable (fun w : ℝ => w ^ p * ‖kfun a ν P w‖) (volume.restrict (Ioi 0)) := by
    refine (ContinuousOn.mul (fun w hw => ?_) (continuousOn_kfun a ha ν).norm).aestronglyMeasurable measurableSet_Ioi
    exact (Real.continuousAt_rpow_const _ _ (Or.inl (ne_of_gt hw))).continuousWithinAt
  refine Integrable.mono' hdom hmeas ((ae_restrict_iff' measurableSet_Ioi).2 (ae_of_all _ fun w (hw : 0 < w) => ?_))
  rw [Real.norm_eq_abs, abs_of_nonneg (by positivity), norm_kfun a ν hw, KB.kb]
  have hE : Real.exp (-(Real.pi * ((w ^ 2)⁻¹ + a ^ 2 * w ^ 2))) ≤ Real.exp (-(b * (w ^ 2 + (w ^ 2)⁻¹))) := by
    apply Real.exp_le_exp.2
    have hw2 : 0 < w ^ 2 := by positivity
    have hwi : 0 < (w ^ 2)⁻¹ := by positivity
    have hm1 : min 1 (a ^ 2) ≤ 1 := min_le_left _ _
    have hm2 : min 1 (a ^ 2) ≤ a ^ 2 := min_le_right _ _
    have hmin : 0 ≤ min 1 (a ^ 2) := le_min zero_le_one (sq_nonneg a)
    rw [hb]
    nlinarith [Real.pi_pos, mul_le_mul_of_nonneg_right hm1 hwi.le, mul_le_mul_of_nonneg_right hm2 hw2.le]
  have hpow : w ^ (p + P.centralExponent.re + 1 + ν.re) = w ^ p * (w ^ P.centralExponent.re * w * w ^ ν.re) := by
    rw [Real.rpow_add hw, Real.rpow_add hw, Real.rpow_add hw, Real.rpow_one]; ring
  rw [hpow]
  have : 0 ≤ w ^ p * (w ^ P.centralExponent.re * w * w ^ ν.re) := by positivity
  calc w ^ p * (w ^ P.centralExponent.re * w * w ^ ν.re * Real.exp (-(Real.pi * ((w ^ 2)⁻¹ + a ^ 2 * w ^ 2))))
      = w ^ p * (w ^ P.centralExponent.re * w * w ^ ν.re) * Real.exp (-(Real.pi * ((w ^ 2)⁻¹ + a ^ 2 * w ^ 2))) := by ring
    _ ≤ w ^ p * (w ^ P.centralExponent.re * w * w ^ ν.re) * Real.exp (-(b * (w ^ 2 + (w ^ 2)⁻¹))) := by gcongr

end Kernel

end Ws23HMNZ2

open Ws23HMNZ2 LanglandsTunnell.Converse.ArchR Set Filter Asymptotics Topology in

theorem solution
    {P₂ : RealArchParam} (D : ArchDatumR P₂) (a : ℝ) (ha : a ≠ 0) (ν : ℂ) (ε : ℂ) (hε : ε = 1 ∨ ε = -1)
    (hg : ∃ τ : ℝ, 0 < τ ∧ D.W (ArchR.diagOne τ) + ε * D.W (ArchR.diagOne (-τ)) ≠ 0)
    (H : ℝ → ℂ)
    (hH : H = fun σ' => (Real.exp (-(Real.pi * a ^ 2 * σ' ^ 2)) : ℂ) *
        ∫ w in Set.Ioi (0 : ℝ),
          (D.W (ArchR.diagOne (a * (σ' / w))) + ε * D.W (ArchR.diagOne (-(a * (σ' / w))))) *
            (ArchR.centralChar P₂ w * ((|w| : ℝ) : ℂ)) * ((w : ℝ) : ℂ) ^ ν *
            (Real.exp (-(Real.pi * ((w ^ 2)⁻¹ + a ^ 2 * w ^ 2))) : ℂ))
    (hHc : ContinuousOn H (Set.Ioi 0)) (x₀ : ℝ) :
    ∃ s : ℂ, x₀ < s.re ∧ mellin H (s - 1) ≠ 0 := by
  by_contra hcon
  push Not at hcon
  have h0 : ∀ z : ℂ, x₀ - 1 < z.re → mellin H z = 0 := fun z hz => by
    have := hcon (z + 1) (by simp; linarith)
    simpa using this
  have ha' : 0 < |a| := abs_pos.2 ha
  have hπa : 0 < Real.pi * a ^ 2 := by have := sq_pos_of_ne_zero ha; positivity

  obtain ⟨σψ, hψconv, hψdiff⟩ := exists_abscissa_psiD D a ha ε
  obtain ⟨C₀, σD, hC₀, hσD, hbd₀⟩ := exists_bound_torus D
  have hεn : ‖ε‖ = 1 := by rcases hε with h | h <;> simp [h]
  obtain ⟨C, hC, hbd⟩ : ∃ C : ℝ, 0 ≤ C ∧ ∀ τ : ℝ, τ ≠ 0 →
      ‖D.W (diagOne τ) + ε * D.W (diagOne (-τ))‖ ≤ C * (1 + |τ| ^ (-σD)) := by
    refine ⟨2 * C₀, by positivity, fun τ hτ => ?_⟩
    have h1 := hbd₀ τ hτ
    have h2 := hbd₀ (-τ) (neg_ne_zero.2 hτ)
    rw [abs_neg] at h2
    calc ‖D.W (diagOne τ) + ε * D.W (diagOne (-τ))‖ ≤ ‖D.W (diagOne τ)‖ + ‖ε‖ * ‖D.W (diagOne (-τ))‖ := by
          refine (norm_add_le _ _).trans ?_; rw [norm_mul]
      _ ≤ C₀ * (1 + |τ| ^ (-σD)) + 1 * (C₀ * (1 + |τ| ^ (-σD))) := by rw [hεn]; gcongr
      _ = 2 * C₀ * (1 + |τ| ^ (-σD)) := by ring

  set V : ℝ → ℂ := fun σ' => ∫ w in Ioi (0 : ℝ), psiD D a ε (σ' / w) * kfun a ν P₂ w with hV
  have hHV : ∀ σ' : ℝ, H σ' = (Real.exp (-(Real.pi * a ^ 2 * σ' ^ 2)) : ℂ) * V σ' := by
    intro σ'
    simp only [hH, hV]
    congr 1
    refine setIntegral_congr_fun measurableSet_Ioi fun w _ => ?_
    simp only [psiD, kfun, Efun]
    ring

  set K₀ : ℝ := ∫ w in Ioi (0 : ℝ), w ^ (0 : ℝ) * ‖kfun a ν P₂ w‖ with hK₀
  set K₁ : ℝ := ∫ w in Ioi (0 : ℝ), w ^ σD * ‖kfun a ν P₂ w‖ with hK₁
  have hK₀n : 0 ≤ K₀ := setIntegral_nonneg measurableSet_Ioi fun w (hw : 0 < w) => by positivity
  have hK₁n : 0 ≤ K₁ := setIntegral_nonneg measurableSet_Ioi fun w (hw : 0 < w) => by positivity
  have hI₀ := integrableOn_rpow_mul_norm_kfun a ha ν (P := P₂) 0
  have hI₁ := integrableOn_rpow_mul_norm_kfun a ha ν (P := P₂) σD
  have hVb : ∀ σ' : ℝ, 0 < σ' → ‖V σ'‖ ≤ C * K₀ + C * |a| ^ (-σD) * K₁ * σ' ^ (-σD) := by
    intro σ' hσ'
    have hbound : ∀ w ∈ Ioi (0 : ℝ), ‖psiD D a ε (σ' / w) * kfun a ν P₂ w‖ ≤
        C * (w ^ (0 : ℝ) * ‖kfun a ν P₂ w‖) + (C * |a| ^ (-σD) * σ' ^ (-σD)) * (w ^ σD * ‖kfun a ν P₂ w‖) := by
      intro w hw
      have hw : 0 < w := hw
      have hτ : a * (σ' / w) ≠ 0 := mul_ne_zero ha (div_ne_zero hσ'.ne' hw.ne')
      rw [norm_mul, psiD, Real.rpow_zero, one_mul]
      have h1 := hbd _ hτ
      have h2 : |a * (σ' / w)| ^ (-σD) = |a| ^ (-σD) * σ' ^ (-σD) * w ^ σD := by
        rw [abs_mul, abs_div, abs_of_pos hσ', abs_of_pos hw, Real.mul_rpow (abs_nonneg a) (by positivity),
          Real.div_rpow hσ'.le hw.le, Real.rpow_neg hw.le, div_inv_eq_mul]
        ring
      have hk : 0 ≤ ‖kfun a ν P₂ w‖ := norm_nonneg _
      calc ‖D.W (diagOne (a * (σ' / w))) + ε * D.W (diagOne (-(a * (σ' / w))))‖ * ‖kfun a ν P₂ w‖ ≤
          C * (1 + |a * (σ' / w)| ^ (-σD)) * ‖kfun a ν P₂ w‖ :=
            mul_le_mul_of_nonneg_right h1 hk
        _ = _ := by rw [h2]; ring
    have hint : IntegrableOn (fun w : ℝ => C * (w ^ (0 : ℝ) * ‖kfun a ν P₂ w‖) +
        (C * |a| ^ (-σD) * σ' ^ (-σD)) * (w ^ σD * ‖kfun a ν P₂ w‖)) (Ioi 0) :=
      (hI₀.const_mul C).add (hI₁.const_mul _)
    have hmeas : AEStronglyMeasurable (fun w : ℝ => psiD D a ε (σ' / w) * kfun a ν P₂ w) (volume.restrict (Ioi 0)) := by
      refine (ContinuousOn.mul ?_ (continuousOn_kfun a ha ν)).aestronglyMeasurable measurableSet_Ioi
      refine (continuousOn_psiD D a ha ε).comp (continuousOn_const.div continuous_id.continuousOn fun w hw => ne_of_gt hw) ?_
      intro w hw; exact div_pos hσ' hw
    have hI : IntegrableOn (fun w : ℝ => psiD D a ε (σ' / w) * kfun a ν P₂ w) (Ioi 0) :=
      Integrable.mono' hint hmeas ((ae_restrict_iff' measurableSet_Ioi).2 (ae_of_all _ hbound))
    calc ‖V σ'‖ ≤ ∫ w in Ioi (0 : ℝ), ‖psiD D a ε (σ' / w) * kfun a ν P₂ w‖ := norm_integral_le_integral_norm _
      _ ≤ ∫ w in Ioi (0 : ℝ), (C * (w ^ (0 : ℝ) * ‖kfun a ν P₂ w‖) +
            (C * |a| ^ (-σD) * σ' ^ (-σD)) * (w ^ σD * ‖kfun a ν P₂ w‖)) :=
          setIntegral_mono_on hI.norm hint measurableSet_Ioi hbound
      _ = C * K₀ + C * |a| ^ (-σD) * K₁ * σ' ^ (-σD) := by
          rw [integral_add (hI₀.const_mul C) (hI₁.const_mul _), integral_const_mul, integral_const_mul]; ring

  set M : ℝ := C * K₀ + C * |a| ^ (-σD) * K₁ with hM
  have hMn : 0 ≤ M := by positivity
  have hHbot : H =O[𝓝[>] 0] fun t : ℝ => t ^ (-σD) := by
    refine IsBigO.of_bound M ?_
    filter_upwards [Ioc_mem_nhdsGT (zero_lt_one' ℝ)] with t ht
    have ht0 : 0 < t := ht.1
    have hpow : 1 ≤ t ^ (-σD) := Real.one_le_rpow_of_pos_of_le_one_of_nonpos ht0 ht.2 (by linarith)
    rw [hHV t, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _),
      Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    have hexp : Real.exp (-(Real.pi * a ^ 2 * t ^ 2)) ≤ 1 := by rw [Real.exp_le_one_iff]; nlinarith [hπa, sq_nonneg t]
    have hVt := hVb t ht0
    calc Real.exp (-(Real.pi * a ^ 2 * t ^ 2)) * ‖V t‖ ≤ 1 * (C * K₀ + C * |a| ^ (-σD) * K₁ * t ^ (-σD)) := by
          gcongr
      _ ≤ M * t ^ (-σD) := by rw [hM]; nlinarith [mul_nonneg hC hK₀n]
  have hHtop : H =O[atTop] fun t : ℝ => Real.exp (-(Real.pi * a ^ 2) * t) := by
    refine IsBigO.of_bound M ?_
    filter_upwards [eventually_ge_atTop (1 : ℝ)] with t ht
    have ht0 : 0 < t := one_pos.trans_le ht
    have hpow : t ^ (-σD) ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos ht (by linarith)
    rw [hHV t, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _),
      Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    have hexp : Real.exp (-(Real.pi * a ^ 2 * t ^ 2)) ≤ Real.exp (-(Real.pi * a ^ 2) * t) := by
      apply Real.exp_le_exp.2
      have htt : t ≤ t ^ 2 := by nlinarith
      nlinarith [mul_le_mul_of_nonneg_left htt hπa.le]
    have hVt := hVb t ht0
    have : ‖V t‖ ≤ M := by
      calc ‖V t‖ ≤ C * K₀ + C * |a| ^ (-σD) * K₁ * t ^ (-σD) := hVt
        _ ≤ C * K₀ + C * |a| ^ (-σD) * K₁ * 1 := by gcongr
        _ = M := by rw [hM]; ring
    calc Real.exp (-(Real.pi * a ^ 2 * t ^ 2)) * ‖V t‖ ≤ Real.exp (-(Real.pi * a ^ 2) * t) * M := by gcongr
      _ = M * Real.exp (-(Real.pi * a ^ 2) * t) := mul_comm _ _
  have hHconv : ∀ s : ℂ, σD < s.re → MellinConvergent H s := fun s hs =>
    mellinConvergent_of_isBigO_rpow_exp hπa (hHc.locallyIntegrableOn measurableSet_Ioi) hHtop hHbot hs

  have hH0 : ∀ x : ℝ, 0 < x → H x = 0 := by
    intro x hx
    set σ₁ : ℝ := max (x₀ - 1) σD + 1 with hσ₁
    have h1 : x₀ - 1 < σ₁ := by have := le_max_left (x₀ - 1) σD; linarith
    have h2 : σD < σ₁ := by have := le_max_right (x₀ - 1) σD; linarith
    have hconvB : MellinConvergent H (σ₁ : ℂ) := hHconv _ (by simpa using h2)
    have hline : ∀ y : ℝ, mellin H ((σ₁ : ℂ) + (y : ℂ) * Complex.I) = 0 := fun y => h0 _ (by simpa using h1)
    have hvert : Complex.VerticalIntegrable (mellin H) σ₁ := by
      have : (fun y : ℝ => mellin H ((σ₁ : ℂ) + (y : ℂ) * Complex.I)) = 0 := funext hline
      rw [Complex.VerticalIntegrable, this]; exact integrable_zero _ _ _
    have hcx : ContinuousAt H x := (hHc x hx).continuousAt (Ioi_mem_nhds hx)
    have hinv := mellinInv_mellin_eq σ₁ H hx hconvB hvert hcx
    rw [← hinv, mellinInv]
    simp only [hline, smul_zero, integral_zero]
  have hV0 : ∀ x : ℝ, 0 < x → V x = 0 := by
    intro x hx
    have := hH0 x hx
    rw [hHV x] at this
    exact (mul_eq_zero.1 this).resolve_left (by exact_mod_cast (Real.exp_pos _).ne')

  set G : ℝ → ℂ := fun t => psiD D a ε t⁻¹ with hG
  set T : ℝ → ℂ := fun r => ∫ w in Ioi (0 : ℝ), kfun a ν P₂ w * G (r * w) with hT
  have hT0 : ∀ r : ℝ, 0 < r → T r = 0 := by
    intro r hr
    have := hV0 r⁻¹ (inv_pos.2 hr)
    simp only [hV] at this
    simp only [hT, hG]
    rw [← this]
    refine setIntegral_congr_fun measurableSet_Ioi fun w _ => ?_
    rw [div_eq_mul_inv, mul_comm, mul_inv]
  have hmT : ∀ z : ℂ, mellin T z = 0 := by
    intro z
    rw [mellin]
    refine (setIntegral_congr_fun measurableSet_Ioi fun r (hr : 0 < r) => ?_).trans (integral_zero _ _)
    rw [hT0 r hr, smul_zero]
  have hGm : AEStronglyMeasurable G (volume.restrict (Ioi (0 : ℝ))) :=
    ((continuousOn_psiD D a ha ε).comp (continuousOn_inv₀.mono fun t ht => ne_of_gt ht) fun t (ht : 0 < t) =>
      (inv_pos.2 ht : (0 : ℝ) < t⁻¹)).aestronglyMeasurable measurableSet_Ioi
  have hkm : AEStronglyMeasurable (kfun a ν P₂) (volume.restrict (Ioi (0 : ℝ))) :=
    (continuousOn_kfun a ha ν).aestronglyMeasurable measurableSet_Ioi
  have hprod : ∀ z : ℂ, σψ < z.re → mellin (kfun a ν P₂) (1 + z) * mellin (psiD D a ε) z = 0 := by
    intro z hz
    have hGc : MellinConvergent G (-z) := by
      have h := (MellinConvergent.comp_rpow (f := psiD D a ε) (s := -z) (a := (-1 : ℝ)) (by norm_num)).2
        (by rw [show -z / ((-1 : ℝ) : ℂ) = z by push_cast; field_simp]; exact hψconv z hz)
      refine (integrableOn_congr_fun (fun t (ht : 0 < t) => ?_) measurableSet_Ioi).1 h
      simp only [hG, Real.rpow_neg_one]
    have hK3 := LanglandsTunnell.mellinConvergent_integral_mul_comp_mul_and_mellin_eq_mellin_mul_mellin (kfun a ν P₂) G (-z)
      hkm hGm (by rw [sub_neg_eq_add]; exact mellinConvergent_kfun a ha ν _) hGc
    have h2 := hK3.2
    rw [sub_neg_eq_add] at h2
    have hGmel : mellin G (-z) = mellin (psiD D a ε) z := by
      simp only [hG]; rw [mellin_comp_inv, neg_neg]
    rw [← hGmel, ← h2]
    exact hmT (-z)

  set y₀ : ℝ := -(β P₂ ν).im with hy₀
  have hline : ∀ x : ℝ, σψ < x → mellin (psiD D a ε) ((x : ℂ) + (y₀ : ℂ) * Complex.I) = 0 := by
    intro x hx
    have hz : σψ < ((x : ℂ) + (y₀ : ℂ) * Complex.I).re := by simpa using hx
    have hne := mellin_kfun_ne_zero a ha ν (P := P₂) (1 + ((x : ℂ) + (y₀ : ℂ) * Complex.I)) (by simp [hy₀, β])
    exact (mul_eq_zero.1 (hprod _ hz)).resolve_left hne
  have hU : IsOpen {s : ℂ | σψ < s.re} := isOpen_lt continuous_const Complex.continuous_re
  have hF : AnalyticOnNhd ℂ (mellin (psiD D a ε)) {s : ℂ | σψ < s.re} := hψdiff.analyticOnNhd hU
  have hconn : IsPreconnected {s : ℂ | σψ < s.re} := (convex_halfSpace_re_gt σψ).isPreconnected
  set z₀ : ℂ := ((σψ + 1 : ℝ) : ℂ) + (y₀ : ℂ) * Complex.I with hz₀
  have hz₀mem : z₀ ∈ {s : ℂ | σψ < s.re} := by simp [hz₀]
  have hall : ∀ z ∈ {s : ℂ | σψ < s.re}, mellin (psiD D a ε) z = 0 := by
    rcases (hF _ hz₀mem).eventually_eq_zero_or_eventually_ne_zero with h | h
    · intro z hz
      exact hF.eqOn_zero_of_preconnected_of_eventuallyEq_zero hconn hz₀mem h hz
    · exfalso
      rw [eventually_nhdsWithin_iff, Metric.eventually_nhds_iff] at h
      obtain ⟨ε, hε, hball⟩ := h
      set z₁ : ℂ := ((σψ + 1 + ε / 2 : ℝ) : ℂ) + (y₀ : ℂ) * Complex.I with hz₁
      have hdist : dist z₁ z₀ < ε := by
        rw [Complex.dist_eq, hz₁, hz₀, show (((σψ + 1 + ε / 2 : ℝ) : ℂ) + (y₀ : ℂ) * Complex.I) -
          ((((σψ + 1 : ℝ) : ℂ) + (y₀ : ℂ) * Complex.I)) = ((ε / 2 : ℝ) : ℂ) by push_cast; ring,
          Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by linarith)]
        linarith
      have hne : z₁ ≠ z₀ := by
        intro h
        have := congrArg Complex.re h
        simp [hz₁, hz₀] at this
        linarith
      exact hball hdist hne (hline _ (by linarith))

  have hψ0 : ∀ t : ℝ, 0 < t → psiD D a ε t = 0 := by
    intro t ht
    set σ₁ : ℝ := σψ + 1 with hσ₁
    have hconvB : MellinConvergent (psiD D a ε) (σ₁ : ℂ) := hψconv _ (by simp [hσ₁])
    have hline' : ∀ y : ℝ, mellin (psiD D a ε) ((σ₁ : ℂ) + (y : ℂ) * Complex.I) = 0 := fun y =>
      hall _ (by simp [hσ₁])
    have hvert : Complex.VerticalIntegrable (mellin (psiD D a ε)) σ₁ := by
      have : (fun y : ℝ => mellin (psiD D a ε) ((σ₁ : ℂ) + (y : ℂ) * Complex.I)) = 0 := funext hline'
      rw [Complex.VerticalIntegrable, this]; exact integrable_zero _ _ _
    have hcx : ContinuousAt (psiD D a ε) t := (continuousOn_psiD D a ha ε t ht).continuousAt (Ioi_mem_nhds ht)
    have hinv := mellinInv_mellin_eq σ₁ (psiD D a ε) ht hconvB hvert hcx
    rw [← hinv, mellinInv]
    simp only [hline', smul_zero, integral_zero]
  obtain ⟨τ, hτ, hgτ⟩ := hg
  rcases lt_or_gt_of_ne ha with hneg | hpos
  ·
    have ht : 0 < τ / (-a) := div_pos hτ (by linarith)
    have h := hψ0 _ ht
    have harg : a * (τ / (-a)) = -τ := by field_simp
    simp only [psiD, harg, neg_neg] at h
    have hε2 : ε * ε = 1 := by rcases hε with h' | h' <;> simp [h']
    apply hgτ
    have : D.W (diagOne τ) + ε * D.W (diagOne (-τ)) = ε * (D.W (diagOne (-τ)) + ε * D.W (diagOne τ)) := by
      linear_combination (-(D.W (diagOne τ))) * hε2
    rw [this, h, mul_zero]
  · have ht : 0 < τ / a := div_pos hτ hpos
    have h := hψ0 _ ht
    have harg : a * (τ / a) = τ := by field_simp
    simp only [psiD, harg] at h
    exact hgτ h

#print axioms solution

end S_LanglandsTunnell_Converse_ArchDatumR_exists_lt_re_mellin_gaussian_mul_integral_twoSheet_torusKernel_ne_zero
end P2MW
export P2MW.S_LanglandsTunnell_Converse_ArchDatumR_exists_lt_re_mellin_gaussian_mul_integral_twoSheet_torusKernel_ne_zero (solution)
