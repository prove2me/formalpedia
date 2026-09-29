-- Prove2me | solution 1 for LanglandsTunnell.CubicInduction.integrable_and_setIntegral_torusMonomial_eq_mul_GammaR_mul_mellin_of_archDatumR
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:08.353894+00:00
-- url     : https://prove2.me/submissions/f24e6506-2f48-5895-8024-fedac55673a6

import Definitions.Def_LanglandsTunnell_CubicInduction_ArchZeta31
import Definitions.Def_M4aHerbrand_SIdeleClassGroup
import Definitions.Def_RatIdele_Normalizer
import Definitions.Def_LanglandsTunnell_CubicInduction_JacquetVector3
import Definitions.Def_AutomorphicForm_ArchWeightChar

import Mathlib.Analysis.MellinTransform
import Mathlib.Analysis.SpecialFunctions.Gamma.Deligne
import Mathlib.Topology.Instances.Sign
import Theorems.Thm_LanglandsTunnell_exists_forall_integrable_and_mellinConvergent_and_setIntegral_cpow_mul_torusKernel_eq_half_GammaR_mul_mellin
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_LanglandsTunnell_CubicInduction_integrable_and_setIntegral_torusMonomial_eq_mul_GammaR_mul_mellin_of_archDatumR

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

open NumberField AutomorphicForm LanglandsTunnell.Converse LanglandsTunnell LanglandsTunnell.CubicInduction MeasureTheory

namespace Ws23TermCore

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

section Main

variable (a : ℚ) (ha : a ≠ 0) {P₂ : RealArchParam} (D : ArchDatumR P₂) (u₃ : ℂ) (a₃ : ZMod 2) (m i j l : ℕ)

noncomputable def gD (t : ℝ) : ℂ := D.W (diagOne ((a : ℝ) * t))

noncomputable def KD (w : ℝ) : ℂ :=
  ((w : ℝ) : ℂ) ^ (-u₃ - 2) * (((w ^ (m + 2) : ℝ)) : ℂ) * centralChar P₂ w * ((((w⁻¹) ^ j : ℝ)) : ℂ) *
    (Real.exp (-(Real.pi * ((w ^ 2)⁻¹ + (a : ℝ) ^ 2 * w ^ 2))) : ℂ)

include ha in
theorem measurable_gD : Measurable (gD a D) := by
  refine measurable_of_continuousOn_compl_singleton 0 ?_
  refine (continuousOn_torus D).comp (continuous_const.mul continuous_id).continuousOn fun t ht => ?_
  have ha' : (a : ℝ) ≠ 0 := by exact_mod_cast ha
  exact mul_ne_zero ha' ht

include ha in
theorem bound_gD : ∃ C σ : ℝ, 0 ≤ σ ∧ ∀ t : ℝ, 0 < t → ‖gD a D t‖ ≤ C * (1 + t ^ (-σ)) := by
  obtain ⟨C, σD, hC, hσD, hb⟩ := exists_bound_torus D
  have ha0 : (a : ℝ) ≠ 0 := by exact_mod_cast ha
  have ha' : 0 < |(a : ℝ)| := abs_pos.2 ha0
  refine ⟨C * max 1 (|(a : ℝ)| ^ (-σD)), σD, hσD, fun t ht => ?_⟩
  have h := hb ((a : ℝ) * t) (mul_ne_zero ha0 ht.ne')
  rw [gD]
  rw [abs_mul, abs_of_pos ht, Real.mul_rpow (abs_nonneg _) ht.le] at h
  have hM1 : (1 : ℝ) ≤ max 1 (|(a : ℝ)| ^ (-σD)) := le_max_left _ _
  have hM2 : |(a : ℝ)| ^ (-σD) ≤ max 1 (|(a : ℝ)| ^ (-σD)) := le_max_right _ _
  have ht' : 0 ≤ t ^ (-σD) := Real.rpow_nonneg ht.le _
  calc ‖D.W (diagOne ((a : ℝ) * t))‖ ≤ C * (1 + |(a : ℝ)| ^ (-σD) * t ^ (-σD)) := h
    _ ≤ C * (max 1 (|(a : ℝ)| ^ (-σD)) * 1 + max 1 (|(a : ℝ)| ^ (-σD)) * t ^ (-σD)) := by gcongr; simp
    _ = C * max 1 (|(a : ℝ)| ^ (-σD)) * (1 + t ^ (-σD)) := by ring

theorem measurable_quasiChar (u : ℂ) (b : ZMod 2) : Measurable fun r : ℝ => quasiChar u b r := by
  have hsign : Measurable fun y : ℝ => (((SignType.sign y : SignType) : ℝ) : ℂ) := by
    have : (fun y : ℝ => (((SignType.sign y : SignType) : ℝ) : ℂ)) =
        fun y => if 0 < y then (1 : ℂ) else if y < 0 then -1 else 0 := by
      funext y; rw [sign_apply]; split_ifs <;> simp
    rw [this]
    exact Measurable.ite measurableSet_Ioi measurable_const
      (Measurable.ite measurableSet_Iio measurable_const measurable_const)
  unfold quasiChar
  refine ((Complex.measurable_ofReal.comp measurable_abs).pow_const u).mul ?_
  split_ifs
  · exact measurable_const
  · exact hsign

theorem measurable_KD : Measurable (KD a (P₂ := P₂) u₃ m j) := by
  unfold KD centralChar
  refine ((((Complex.measurable_ofReal.pow_const _).mul (by fun_prop)).mul (measurable_quasiChar _ _)).mul (by fun_prop)).mul
    (by fun_prop)

theorem norm_quasiChar_pos {u : ℂ} {b : ZMod 2} {r : ℝ} (hr : 0 < r) : ‖quasiChar u b r‖ = r ^ u.re := by
  unfold quasiChar
  rw [norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos (abs_pos.2 hr.ne'), abs_of_pos hr]
  split_ifs
  · simp
  · rw [sign_pos hr]; simp

theorem bound_KD : ∃ CK N : ℝ, ∀ w : ℝ, 0 < w →
    ‖KD a (P₂ := P₂) u₃ m j w‖ ≤ CK * (w ^ N + w ^ (-N)) * Real.exp (-(Real.pi * ((w ^ 2)⁻¹ + (a : ℝ) ^ 2 * w ^ 2))) := by
  set x : ℝ := (-u₃ - 2).re + ((m + 2 : ℕ) : ℝ) + P₂.centralExponent.re - (j : ℝ) with hx
  refine ⟨1, |x|, fun w hw => ?_⟩
  have hn : ‖KD a (P₂ := P₂) u₃ m j w‖ = w ^ x * Real.exp (-(Real.pi * ((w ^ 2)⁻¹ + (a : ℝ) ^ 2 * w ^ 2))) := by
    rw [KD, norm_mul, norm_mul, norm_mul, norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos hw, centralChar, norm_quasiChar_pos hw,
      Complex.norm_real, Complex.norm_real, Complex.norm_real, Real.norm_eq_abs, Real.norm_eq_abs, Real.norm_eq_abs,
      abs_of_pos (pow_pos hw _), abs_of_pos (pow_pos (inv_pos.2 hw) _), abs_of_pos (Real.exp_pos _)]
    have hpw : w ^ (-u₃ - 2).re * w ^ (m + 2) * w ^ P₂.centralExponent.re * w⁻¹ ^ j = w ^ x := by
      rw [hx, Real.rpow_sub hw, Real.rpow_add hw, Real.rpow_add hw, Real.rpow_natCast, Real.rpow_natCast, inv_pow]
      field_simp
    rw [← hpw]
  rw [hn, one_mul]
  have hE : 0 ≤ Real.exp (-(Real.pi * ((w ^ 2)⁻¹ + (a : ℝ) ^ 2 * w ^ 2))) := (Real.exp_pos _).le
  refine mul_le_mul_of_nonneg_right ?_ hE
  rcases le_or_gt 1 w with h1 | h1
  · calc w ^ x ≤ w ^ |x| := Real.rpow_le_rpow_of_exponent_le h1 (le_abs_self x)
      _ ≤ w ^ |x| + w ^ (-|x|) := le_add_of_nonneg_right (Real.rpow_nonneg hw.le _)
  · calc w ^ x ≤ w ^ (-|x|) := Real.rpow_le_rpow_of_exponent_ge hw h1.le (by have := neg_abs_le x; linarith)
      _ ≤ w ^ |x| + w ^ (-|x|) := le_add_of_nonneg_left (Real.rpow_nonneg hw.le _)

end Main

end Ws23TermCore

open Ws23TermCore LanglandsTunnell.Converse.ArchR Set in
theorem solution
    (a : ℚ) (ha : a ≠ 0)
    {P₂ : RealArchParam} (D : ArchDatumR P₂)
    (u₃ : ℂ) (a₃ : ZMod 2) (m i j l : ℕ)
    (H : ℝ → ℂ)
    (hH : H = fun σ' => (Real.exp (-(Real.pi * (a : ℝ) ^ 2 * σ' ^ 2)) : ℂ) *
        ∫ w in Set.Ioi (0 : ℝ),
          D.W (ArchR.diagOne ((a : ℝ) * (σ' / w))) *
            (ArchR.centralChar P₂ w * ((|w| : ℝ) : ℂ)) * ((w : ℝ) : ℂ) ^ ((m : ℂ) - u₃ - 1 - (j : ℂ)) *
            (Real.exp (-(Real.pi * ((w ^ 2)⁻¹ + (a : ℝ) ^ 2 * w ^ 2))) : ℂ)) :
    ∃ σ₀ : ℝ, ∀ s : ℂ, σ₀ < s.re →
      Integrable (fun q : ℝ × ℝ × ℝ =>
          ((q.1 : ℝ) : ℂ) ^ (s - 2) *
            (ArchR.quasiChar (u₃ + 2) a₃ (q.2.1 * q.2.2)⁻¹ * (((q.2.2 ^ (m + 2) : ℝ)) : ℂ) * ArchR.centralChar P₂ q.2.2 *
              (Real.exp (-(Real.pi * ((q.2.1 ^ 2)⁻¹ + (q.2.2 ^ 2)⁻¹ + (a : ℝ) ^ 2 * q.2.2 ^ 2 + (a : ℝ) ^ 2 * q.1 ^ 2 * q.2.1 ^ 2))) : ℂ) *
              D.W (ArchR.diagOne ((a : ℝ) * q.1 * q.2.1 / q.2.2)) *
              ((((q.2.1⁻¹) ^ i * (q.2.2⁻¹) ^ j * ((a : ℝ) * q.1 * q.2.1) ^ l : ℝ)) : ℂ)))
        ((volume.restrict (Set.Ioi (0 : ℝ))).prod ((volume.restrict (Set.Ioi (0 : ℝ))).prod (volume.restrict (Set.Ioi (0 : ℝ))))) ∧
      MellinConvergent H (s + (l : ℂ) - 1) ∧
      ∫ y in Set.Ioi (0 : ℝ), ((y : ℝ) : ℂ) ^ (s - 2) *
          ∫ y₁ in Set.Ioi (0 : ℝ), ∫ y₂ in Set.Ioi (0 : ℝ),
            ArchR.quasiChar (u₃ + 2) a₃ (y₁ * y₂)⁻¹ * (((y₂ ^ (m + 2) : ℝ)) : ℂ) * ArchR.centralChar P₂ y₂ *
              (Real.exp (-(Real.pi * ((y₁ ^ 2)⁻¹ + (y₂ ^ 2)⁻¹ + (a : ℝ) ^ 2 * y₂ ^ 2 + (a : ℝ) ^ 2 * y ^ 2 * y₁ ^ 2))) : ℂ) *
              D.W (ArchR.diagOne ((a : ℝ) * y * y₁ / y₂)) *
              ((((y₁⁻¹) ^ i * (y₂⁻¹) ^ j * ((a : ℝ) * y * y₁) ^ l : ℝ)) : ℂ) =
        (a : ℂ) ^ l * ((1 / 2 : ℂ) * Complex.Gammaℝ (s + u₃ + (i : ℂ)) * mellin H (s + (l : ℂ) - 1)) := by
  have ha' : (a : ℝ) ≠ 0 := by exact_mod_cast ha
  have hb : 0 < (a : ℝ) ^ 2 := by positivity
  obtain ⟨C, σ, hσ, hg⟩ := bound_gD a ha D
  obtain ⟨CK, N, hK⟩ := bound_KD a (P₂ := P₂) u₃ m j
  set p : ℂ := -u₃ - 2 - (i : ℂ) + (l : ℂ) with hp

  have hH' : H = fun σ' => (Real.exp (-(Real.pi * (a : ℝ) ^ 2 * σ' ^ 2)) : ℂ) *
      ∫ w in Ioi (0 : ℝ), gD a D (σ' / w) * KD a (P₂ := P₂) u₃ m j w := by
    rw [hH]
    funext σ'
    congr 1
    refine setIntegral_congr_fun measurableSet_Ioi fun w (hw : 0 < w) => ?_
    have hw0 : ((w : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 hw.ne'
    simp only [gD, KD]
    rw [abs_of_pos hw]
    have e1 : (((w ^ (m + 2) : ℝ)) : ℂ) = ((w : ℝ) : ℂ) ^ (((m + 2 : ℕ)) : ℂ) := by
      rw [Complex.cpow_natCast]; push_cast; ring
    have e2 : ((((w⁻¹) ^ j : ℝ)) : ℂ) = ((w : ℝ) : ℂ) ^ (-(j : ℂ)) := by
      rw [Complex.cpow_neg, Complex.cpow_natCast]; push_cast; rw [inv_pow]
    have e3 : ((w : ℝ) : ℂ) ^ ((m : ℂ) - u₃ - 1 - (j : ℂ)) =
        ((w : ℝ) : ℂ) ^ (-u₃ - 2) * ((w : ℝ) : ℂ) ^ (((m + 2 : ℕ)) : ℂ) * ((w : ℝ) : ℂ) ^ (-(j : ℂ)) * (((w : ℝ) : ℂ))⁻¹ := by
      rw [← Complex.cpow_add _ _ hw0, ← Complex.cpow_add _ _ hw0, ← Complex.cpow_neg_one, ← Complex.cpow_add _ _ hw0]
      congr 1; push_cast; ring
    rw [e1, e2, e3]
    field_simp
  obtain ⟨σ₀, hcore⟩ := LanglandsTunnell.exists_forall_integrable_and_mellinConvergent_and_setIntegral_cpow_mul_torusKernel_eq_half_GammaR_mul_mellin
    ((a : ℝ) ^ 2) hb p (gD a D) (measurable_gD a ha D) C σ hσ hg (KD a (P₂ := P₂) u₃ m j) (measurable_KD a u₃ m j) CK N hK H hH'
  refine ⟨σ₀, fun s hs => ?_⟩
  have hs' : σ₀ < (s + (l : ℂ)).re := by simp; linarith [(Nat.cast_nonneg l : (0:ℝ) ≤ l)]
  obtain ⟨hI, hM, hEq⟩ := hcore (s + (l : ℂ)) hs'

  have hpt : ∀ y y₁ y₂ : ℝ, 0 < y → 0 < y₁ → 0 < y₂ →
      ((y : ℝ) : ℂ) ^ (s - 2) *
        (quasiChar (u₃ + 2) a₃ (y₁ * y₂)⁻¹ * (((y₂ ^ (m + 2) : ℝ)) : ℂ) * centralChar P₂ y₂ *
          (Real.exp (-(Real.pi * ((y₁ ^ 2)⁻¹ + (y₂ ^ 2)⁻¹ + (a : ℝ) ^ 2 * y₂ ^ 2 + (a : ℝ) ^ 2 * y ^ 2 * y₁ ^ 2))) : ℂ) *
          D.W (diagOne ((a : ℝ) * y * y₁ / y₂)) *
          ((((y₁⁻¹) ^ i * (y₂⁻¹) ^ j * ((a : ℝ) * y * y₁) ^ l : ℝ)) : ℂ)) =
      (a : ℂ) ^ l * (((y : ℝ) : ℂ) ^ (s + (l : ℂ) - 2) *
        (((y₁ : ℝ) : ℂ) ^ p * KD a (P₂ := P₂) u₃ m j y₂ *
          (Real.exp (-(Real.pi * ((y₁ ^ 2)⁻¹ + (a : ℝ) ^ 2 * y ^ 2 * y₁ ^ 2))) : ℂ) * gD a D (y * y₁ / y₂))) := by
    intro y y₁ y₂ hy hy₁ hy₂
    have hy0 : ((y : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 hy.ne'
    have hy10 : ((y₁ : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 hy₁.ne'

    have hq : quasiChar (u₃ + 2) a₃ (y₁ * y₂)⁻¹ = ((y₁ : ℝ) : ℂ) ^ (-u₃ - 2) * ((y₂ : ℝ) : ℂ) ^ (-u₃ - 2) := by
      unfold quasiChar
      have hpos : 0 < (y₁ * y₂)⁻¹ := by positivity
      rw [abs_of_pos hpos]
      have : (if a₃ = 0 then (1 : ℂ) else (((SignType.sign (y₁ * y₂)⁻¹ : SignType) : ℝ) : ℂ)) = 1 := by
        split_ifs; rfl; rw [sign_pos hpos]; simp
      rw [this, mul_one, mul_inv, Complex.ofReal_mul, Complex.mul_cpow_ofReal_nonneg (inv_nonneg.2 hy₁.le) (inv_nonneg.2 hy₂.le),
        Complex.ofReal_inv, Complex.ofReal_inv,
        Complex.inv_cpow _ _ (by rw [Complex.arg_ofReal_of_nonneg hy₁.le]; exact Real.pi_ne_zero.symm),
        Complex.inv_cpow _ _ (by rw [Complex.arg_ofReal_of_nonneg hy₂.le]; exact Real.pi_ne_zero.symm),
        ← Complex.cpow_neg, ← Complex.cpow_neg]
      congr 2 <;> ring

    have hy1p : ((y₁ : ℝ) : ℂ) ^ (-u₃ - 2) * ((((y₁⁻¹) ^ i : ℝ)) : ℂ) * (((y₁ ^ l : ℝ)) : ℂ) = ((y₁ : ℝ) : ℂ) ^ p := by
      rw [hp, show -u₃ - 2 - (i : ℂ) + (l : ℂ) = (-u₃ - 2) + (-(i : ℂ)) + (l : ℂ) by ring,
        Complex.cpow_add _ _ hy10, Complex.cpow_add _ _ hy10, Complex.cpow_neg, Complex.cpow_natCast, Complex.cpow_natCast]
      push_cast
      rw [inv_pow]
    have hyp : ((y : ℝ) : ℂ) ^ (s - 2) * (((y ^ l : ℝ)) : ℂ) = ((y : ℝ) : ℂ) ^ (s + (l : ℂ) - 2) := by
      rw [show s + (l : ℂ) - 2 = (s - 2) + (l : ℂ) by ring, Complex.cpow_add _ _ hy0, Complex.cpow_natCast]; push_cast; ring
    have hexp : (Real.exp (-(Real.pi * ((y₁ ^ 2)⁻¹ + (y₂ ^ 2)⁻¹ + (a : ℝ) ^ 2 * y₂ ^ 2 + (a : ℝ) ^ 2 * y ^ 2 * y₁ ^ 2))) : ℂ) =
        (Real.exp (-(Real.pi * ((y₁ ^ 2)⁻¹ + (a : ℝ) ^ 2 * y ^ 2 * y₁ ^ 2))) : ℂ) *
          (Real.exp (-(Real.pi * ((y₂ ^ 2)⁻¹ + (a : ℝ) ^ 2 * y₂ ^ 2))) : ℂ) := by
      rw [← Complex.ofReal_mul, ← Real.exp_add]; congr 2; ring
    have hgarg : gD a D (y * y₁ / y₂) = D.W (diagOne ((a : ℝ) * y * y₁ / y₂)) := by
      simp only [gD]; congr 2; ring
    rw [hq, hexp, hgarg, KD]
    push_cast
    rw [← hy1p, ← hyp]
    push_cast
    ring
  refine ⟨?_, hM, ?_⟩
  ·
    have hI' := hI.const_mul ((a : ℂ) ^ l)
    refine hI'.congr ?_
    rw [Measure.prod_restrict, Measure.prod_restrict]
    refine (ae_restrict_iff' (measurableSet_Ioi.prod (measurableSet_Ioi.prod measurableSet_Ioi))).2 (ae_of_all _ fun q hq => ?_)
    obtain ⟨h1, h2, h3⟩ := hq
    exact (hpt q.1 q.2.1 q.2.2 h1 h2 h3).symm
  ·
    have hs2 : s + u₃ + (i : ℂ) = s + (l : ℂ) - p - 2 := by rw [hp]; ring
    have inner : ∀ y ∈ Ioi (0 : ℝ),
        ((y : ℝ) : ℂ) ^ (s - 2) *
          (∫ y₁ in Ioi (0 : ℝ), ∫ y₂ in Ioi (0 : ℝ),
            quasiChar (u₃ + 2) a₃ (y₁ * y₂)⁻¹ * (((y₂ ^ (m + 2) : ℝ)) : ℂ) * centralChar P₂ y₂ *
              (Real.exp (-(Real.pi * ((y₁ ^ 2)⁻¹ + (y₂ ^ 2)⁻¹ + (a : ℝ) ^ 2 * y₂ ^ 2 + (a : ℝ) ^ 2 * y ^ 2 * y₁ ^ 2))) : ℂ) *
              D.W (diagOne ((a : ℝ) * y * y₁ / y₂)) *
              ((((y₁⁻¹) ^ i * (y₂⁻¹) ^ j * ((a : ℝ) * y * y₁) ^ l : ℝ)) : ℂ)) =
        (a : ℂ) ^ l * (((y : ℝ) : ℂ) ^ (s + (l : ℂ) - 2) *
          ∫ y₁ in Ioi (0 : ℝ), ∫ y₂ in Ioi (0 : ℝ),
            ((y₁ : ℝ) : ℂ) ^ p * KD a (P₂ := P₂) u₃ m j y₂ *
              (Real.exp (-(Real.pi * ((y₁ ^ 2)⁻¹ + (a : ℝ) ^ 2 * y ^ 2 * y₁ ^ 2))) : ℂ) * gD a D (y * y₁ / y₂)) := by
      intro y hy
      have hy : 0 < y := hy
      rw [← integral_const_mul, ← mul_assoc, ← integral_const_mul]
      refine setIntegral_congr_fun measurableSet_Ioi fun y₁ (hy₁ : 0 < y₁) => ?_
      rw [← integral_const_mul, ← integral_const_mul]
      refine setIntegral_congr_fun measurableSet_Ioi fun y₂ (hy₂ : 0 < y₂) => ?_
      rw [hpt y y₁ y₂ hy hy₁ hy₂]
      ring
    rw [hs2, ← hEq, ← integral_const_mul]
    exact setIntegral_congr_fun measurableSet_Ioi inner

#print axioms solution

end S_LanglandsTunnell_CubicInduction_integrable_and_setIntegral_torusMonomial_eq_mul_GammaR_mul_mellin_of_archDatumR
end P2MW
export P2MW.S_LanglandsTunnell_CubicInduction_integrable_and_setIntegral_torusMonomial_eq_mul_GammaR_mul_mellin_of_archDatumR (solution)
