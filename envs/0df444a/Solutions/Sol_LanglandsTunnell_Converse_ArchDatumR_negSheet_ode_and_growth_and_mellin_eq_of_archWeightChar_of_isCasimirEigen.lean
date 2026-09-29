-- Prove2me | solution 1 for LanglandsTunnell.Converse.ArchDatumR.negSheet_ode_and_growth_and_mellin_eq_of_archWeightChar_of_isCasimirEigen
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:08.353894+00:00
-- url     : https://prove2.me/submissions/58a1c2ce-7161-538b-9458-c8c5b0bf4078

import Mathlib
import Definitions.Def_LanglandsTunnell_JLConverse
import Definitions.Def_LanglandsTunnell_ArchCasimirCompanion
import Definitions.Def_AutomorphicForm_ArchWeightChar
import Definitions.Def_AutomorphicForm_ArchDerivCasimir
import Theorems.Thm_LanglandsTunnell_whittaker_ode_splitTorus_of_casimir_of_archWeightChar_of_unipotent
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_LanglandsTunnell_Converse_ArchDatumR_negSheet_ode_and_growth_and_mellin_eq_of_archWeightChar_of_isCasimirEigen

set_option autoImplicit false

noncomputable section

open Real Complex MeasureTheory Set Filter
open NumberField AutomorphicForm
p2m_open "LanglandsTunnell P2MW.S_LanglandsTunnell_Converse_ArchDatumR_negSheet_ode_and_growth_and_mellin_eq_of_archWeightChar_of_isCasimirEigen.LanglandsTunnell LanglandsTunnell.RealArchParam LanglandsTunnell.Converse P2MW.S_LanglandsTunnell_Converse_ArchDatumR_negSheet_ode_and_growth_and_mellin_eq_of_archWeightChar_of_isCasimirEigen.LanglandsTunnell.Converse"

namespace LanglandsTunnell
p2m_export "LanglandsTunnell" "RealArchParam whittaker_ode_splitTorus_of_casimir_of_archWeightChar_of_unipotent"
namespace Converse
p2m_export "LanglandsTunnell.Converse" "ArchR.diagOne ArchR.unip ArchR.psi ArchR.glSet ArchR.asPi ArchR.diagOneMulCoords ArchR.quasiChar ArchR.centralChar ArchR.IsK ArchR.zetaIntegrand ArchDatumR ArchCasimir.matrixFlowDeriv ArchCasimir.matrixCasimir ArchCasimir.IsCasimirEigen"
namespace NegSheet
p2m_open "LanglandsTunnell.Converse LanglandsTunnell"

variable {P : RealArchParam}

theorem coe_J_mul_splitTorus {y : ℝ} (hy : 0 < y) :
    ((UpperHalfPlane.J * splitTorusGL2 (Real.log y / 2) : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) =
      !![-Real.sqrt y, 0; 0, (Real.sqrt y)⁻¹] := by
  have h1 : Real.exp (Real.log y / 2) = Real.sqrt y := by
    rw [Real.sqrt_eq_rpow, Real.rpow_def_of_pos hy]; ring_nf
  have h2 : Real.exp (-(Real.log y / 2)) = (Real.sqrt y)⁻¹ := by
    rw [Real.exp_neg, h1]
  rw [Units.val_mul]
  change (!![-1, 0; 0, 1] : Matrix (Fin 2) (Fin 2) ℝ) * !![Real.exp (Real.log y / 2), 0; 0, Real.exp (-(Real.log y / 2))] = _
  rw [h1, h2]
  ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]

def FGL (D : ArchDatumR P) (g : GL (Fin 2) ℝ) : ℂ := D.W (g : Matrix (Fin 2) (Fin 2) ℝ)

theorem FGL_contDiffOn (D : ArchDatumR P) :
    ContDiffOn ℝ 2
      (fun e : Fin 2 → Fin 2 → ℝ =>
        FGL D (if h : (Matrix.of e).det ≠ 0 then Matrix.GeneralLinearGroup.mkOfDetNeZero (Matrix.of e) h
          else 1))
      {e | (Matrix.of e).det ≠ 0} := by
  have h : ContDiffOn ℝ 2 (ArchR.asPi D.W) ArchR.glSet :=
    D.smooth.of_le (show (2 : WithTop ℕ∞) ≤ ((⊤ : ℕ∞) : WithTop ℕ∞) from WithTop.coe_le_coe.mpr le_top)
  refine h.congr ?_
  intro e he
  have he' : (Matrix.of e).det ≠ 0 := he
  simp only [FGL, dif_pos he', ArchR.asPi]
  rfl

theorem FGL_unip (D : ArchDatumR P) (x : ℝ) (m : GL (Fin 2) ℝ) :
    FGL D (unipotentGL2 x * m) = Complex.exp (2 * Real.pi * Complex.I * x) * FGL D m := by
  simp only [FGL, Units.val_mul, unipotentGL2_coe]
  have := D.unip_law x (m : Matrix (Fin 2) (Fin 2) ℝ)
  rw [ArchR.unip, ArchR.psi] at this
  rw [this]

theorem FGL_casimir (D : ArchDatumR P) (hDE : ArchCasimir.IsCasimirEigen D) (ν : ℂ)
    (hν : P.laplaceEigenvalue = 1 / 4 - ν ^ 2) (m : GL (Fin 2) ℝ) :
    -((1 / 4 : ℂ) * deriv (fun t : ℝ => deriv (fun s : ℝ =>
            FGL D (m * archFlowMatrix ArchDir.H t * archFlowMatrix ArchDir.H s)) 0) 0
          - (1 / 2 : ℂ) * deriv (fun t : ℝ => FGL D (m * archFlowMatrix ArchDir.H t)) 0
          + deriv (fun t : ℝ => deriv (fun s : ℝ =>
            FGL D (m * archFlowMatrix ArchDir.E t * archFlowMatrix ArchDir.Fm s)) 0) 0)
        = (1 / 4 - ν ^ 2) * FGL D m := by
  have h := hDE (m : Matrix (Fin 2) (Fin 2) ℝ) (Matrix.GeneralLinearGroup.det_ne_zero m)
  rw [hν] at h
  simpa only [ArchCasimir.matrixCasimir, ArchCasimir.matrixFlowDeriv, FGL, Units.val_mul, Pi.sub_apply,
    Pi.add_apply, Pi.neg_apply, Pi.smul_apply, smul_eq_mul, mul_assoc] using h

theorem negSheet_ode (D : ArchDatumR P) (k₀ : ℤ)
    (hDW : ∀ (r : rowIsometrySubgroup₀ ℝ) (x : GL (Fin 2) ℝ),
      D.W ((x * (r : GL (Fin 2) ℝ) : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) =
        (archWeightCharℝ k₀ r : ℂ) * D.W (x : Matrix (Fin 2) (Fin 2) ℝ))
    (hDE : ArchCasimir.IsCasimirEigen D) (ν : ℂ) (hν : P.laplaceEigenvalue = 1 / 4 - ν ^ 2) :
    let f : ℝ → ℂ := fun y => D.W !![-Real.sqrt y, 0; 0, (Real.sqrt y)⁻¹]
    DifferentiableOn ℝ f (Set.Ioi 0) ∧ DifferentiableOn ℝ (deriv f) (Set.Ioi 0) ∧
      ∀ y : ℝ, 0 < y →
        (y : ℂ) ^ 2 * deriv (deriv f) y
            + (1 / 4 - ν ^ 2 + 2 * (π : ℂ) * ((-(k₀ : ℝ) : ℝ) : ℂ) * (y : ℂ) - 4 * (π : ℂ) ^ 2 * (y : ℂ) ^ 2) * f y
          = 0 := by
  intro f
  obtain ⟨-, hJ⟩ := LanglandsTunnell.whittaker_ode_splitTorus_of_casimir_of_archWeightChar_of_unipotent
    (FGL D) k₀ ν (FGL_contDiffOn D) (FGL_unip D) (fun r x => hDW r x) (FGL_casimir D hDE ν hν)
  obtain ⟨hd, hd', heq⟩ := hJ

  set g : ℝ → ℂ := fun y => FGL D (UpperHalfPlane.J * splitTorusGL2 (Real.log y / 2)) with hg
  have hfg : Set.EqOn f g (Set.Ioi 0) := by
    intro y hy
    simp only [hg, FGL, coe_J_mul_splitTorus hy, f]
  have hfg' : ∀ y ∈ Set.Ioi (0 : ℝ), deriv f y = deriv g y := fun y hy =>
    Filter.EventuallyEq.deriv_eq (Filter.eventuallyEq_of_mem (Ioi_mem_nhds hy) hfg)
  have hfg'' : ∀ y ∈ Set.Ioi (0 : ℝ), deriv (deriv f) y = deriv (deriv g) y := fun y hy =>
    Filter.EventuallyEq.deriv_eq (Filter.eventuallyEq_of_mem (Ioi_mem_nhds hy) hfg')
  refine ⟨hd.congr hfg, (hd'.congr hfg'), fun y hy => ?_⟩
  rw [hfg'' y hy, hfg hy]
  have := heq y hy
  push_cast at this ⊢
  exact this

theorem sqrt_smul_ray {y : ℝ} (hy : 0 < y) :
    Real.sqrt y • (!![-Real.sqrt y, 0; 0, (Real.sqrt y)⁻¹] : Matrix (Fin 2) (Fin 2) ℝ) = ArchR.diagOne (-y) := by
  have hs : Real.sqrt y ≠ 0 := (Real.sqrt_pos.2 hy).ne'
  rw [ArchR.diagOne]
  ext i j; fin_cases i <;> fin_cases j <;>
    simp [Matrix.smul_apply, hs, Real.mul_self_sqrt hy.le]

theorem centralChar_of_pos (t : ℝ) (ht : 0 < t) : ArchR.centralChar P t = (t : ℂ) ^ P.centralExponent := by
  rw [ArchR.centralChar, ArchR.quasiChar, abs_of_pos ht]
  split_ifs
  · rw [mul_one]
  · rw [sign_pos ht]; simp

theorem W_diagOne_neg (D : ArchDatumR P) {y : ℝ} (hy : 0 < y) :
    D.W (ArchR.diagOne (-y)) =
      ((Real.sqrt y : ℝ) : ℂ) ^ P.centralExponent * ((Real.sqrt y : ℝ) : ℂ) *
        D.W !![-Real.sqrt y, 0; 0, (Real.sqrt y)⁻¹] := by
  have hs : 0 < Real.sqrt y := Real.sqrt_pos.2 hy
  rw [← sqrt_smul_ray hy, D.central_law _ _ hs.ne', centralChar_of_pos _ hs, abs_of_pos hs]

theorem sqrt_cpow_mul_sqrt_ne_zero {y : ℝ} (hy : 0 < y) :
    ((Real.sqrt y : ℝ) : ℂ) ^ P.centralExponent * ((Real.sqrt y : ℝ) : ℂ) ≠ 0 := by
  have hs : 0 < Real.sqrt y := Real.sqrt_pos.2 hy
  have h0 : ((Real.sqrt y : ℝ) : ℂ) ≠ 0 := ofReal_ne_zero.2 hs.ne'
  refine mul_ne_zero ?_ h0
  rw [Ne, cpow_eq_zero_iff]
  exact fun hh => h0 hh.1

theorem negSheet_growth (D : ArchDatumR P) :
    ∃ C N : ℝ, ∀ y : ℝ, 1 ≤ y → ‖D.W !![-Real.sqrt y, 0; 0, (Real.sqrt y)⁻¹]‖ ≤ C * y ^ N := by
  obtain ⟨C, hC⟩ := D.decay_top 0 0
  refine ⟨C, -((P.centralExponent.re + 1) / 2), fun y hy => ?_⟩
  have hy0 : 0 < y := lt_of_lt_of_le one_pos hy
  have hs : 0 < Real.sqrt y := Real.sqrt_pos.2 hy0

  have hK : ArchR.IsK (1 : Matrix (Fin 2) (Fin 2) ℝ) := Submonoid.one_mem _
  have h1 := hC (-y) 1 hK (by rw [abs_neg, abs_of_pos hy0]; exact hy)
  rw [norm_iteratedFDerivWithin_zero] at h1
  simp only [Nat.cast_zero, neg_zero, Real.rpow_zero, mul_one] at h1
  have h2 : ArchR.asPi D.W (ArchR.diagOneMulCoords (-y) 1) = D.W (ArchR.diagOne (-y)) := by
    simp [ArchR.asPi, ArchR.diagOneMulCoords]
  rw [h2, W_diagOne_neg D hy0, norm_mul, norm_mul] at h1

  have hn1 : ‖((Real.sqrt y : ℝ) : ℂ) ^ P.centralExponent‖ = Real.sqrt y ^ P.centralExponent.re :=
    Complex.norm_cpow_eq_rpow_re_of_pos hs _
  have hn2 : ‖((Real.sqrt y : ℝ) : ℂ)‖ = Real.sqrt y := by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos hs]
  rw [hn1, hn2] at h1
  have hpos : 0 < Real.sqrt y ^ P.centralExponent.re * Real.sqrt y := mul_pos (Real.rpow_pos_of_pos hs _) hs
  have h3 : ‖D.W !![-Real.sqrt y, 0; 0, (Real.sqrt y)⁻¹]‖ ≤ C / (Real.sqrt y ^ P.centralExponent.re * Real.sqrt y) := by
    rw [le_div_iff₀ hpos]
    calc ‖D.W !![-Real.sqrt y, 0; 0, (Real.sqrt y)⁻¹]‖ * (Real.sqrt y ^ P.centralExponent.re * Real.sqrt y)
        = Real.sqrt y ^ P.centralExponent.re * Real.sqrt y * ‖D.W !![-Real.sqrt y, 0; 0, (Real.sqrt y)⁻¹]‖ := by
          ring
      _ ≤ C := h1
  have h4 : Real.sqrt y ^ P.centralExponent.re * Real.sqrt y = y ^ ((P.centralExponent.re + 1) / 2) := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_mul hy0.le]
    conv_lhs => rw [show (y ^ (1 / 2 : ℝ) : ℝ) = y ^ (1 / 2 : ℝ) from rfl]
    rw [← Real.rpow_add hy0]
    congr 1; ring
  rw [h4] at h3
  rwa [Real.rpow_neg hy0.le, ← div_eq_mul_inv]

theorem sqrt_cpow_mul_sqrt {y : ℝ} (hy : 0 < y) (e : ℂ) :
    ((Real.sqrt y : ℝ) : ℂ) ^ e * ((Real.sqrt y : ℝ) : ℂ) = (y : ℂ) ^ ((e + 1) / 2) := by
  have hs : 0 < Real.sqrt y := Real.sqrt_pos.2 hy
  have hs0 : ((Real.sqrt y : ℝ) : ℂ) ≠ 0 := ofReal_ne_zero.2 hs.ne'
  have hy0 : (y : ℂ) ≠ 0 := ofReal_ne_zero.2 hy.ne'
  have hlog : Complex.log ((Real.sqrt y : ℝ) : ℂ) = ((Real.log y / 2 : ℝ) : ℂ) := by
    rw [← Complex.ofReal_log hs.le, Real.log_sqrt hy.le]
  have hlogy : Complex.log (y : ℂ) = ((Real.log y : ℝ) : ℂ) := by rw [← Complex.ofReal_log hy.le]
  rw [cpow_def_of_ne_zero hs0, cpow_def_of_ne_zero hy0]
  have h2 : Complex.exp (Complex.log ((Real.sqrt y : ℝ) : ℂ) * e) * ((Real.sqrt y : ℝ) : ℂ) =
      Complex.exp (Complex.log ((Real.sqrt y : ℝ) : ℂ) * e) * Complex.exp (Complex.log ((Real.sqrt y : ℝ) : ℂ)) := by
    rw [Complex.exp_log hs0]
  rw [h2, ← Complex.exp_add, hlog, hlogy]
  congr 1
  push_cast
  ring

theorem negSheet_eq_cpow_smul (D : ArchDatumR P) {y : ℝ} (hy : 0 < y) :
    D.W !![-Real.sqrt y, 0; 0, (Real.sqrt y)⁻¹] =
      (y : ℂ) ^ (-((P.centralExponent + 1) / 2)) • D.W (ArchR.diagOne (-y)) := by
  rw [W_diagOne_neg D hy, sqrt_cpow_mul_sqrt hy, smul_eq_mul, ← mul_assoc,
    ← cpow_add _ _ (ofReal_ne_zero.2 hy.ne'), neg_add_cancel, cpow_zero, one_mul]

def G0 (D : ArchDatumR P) (σ : ℂ) (y : ℝ) : ℂ :=
  D.W (ArchR.diagOne y) * ((|y| : ℝ) : ℂ) ^ (σ - 1) * (((|y| : ℝ) : ℂ))⁻¹

theorem zetaIntegrand_zero (D : ArchDatumR P) (σ : ℂ) (y : ℝ) :
    ArchR.zetaIntegrand D.W 1 0 0 σ y = G0 D σ y := by
  simp [ArchR.zetaIntegrand, ArchR.quasiChar, G0]

theorem zetaIntegrand_one (D : ArchDatumR P) (σ : ℂ) (y : ℝ) :
    ArchR.zetaIntegrand D.W 1 0 1 σ y = ((SignType.sign y : ℝ) : ℂ) * G0 D σ y := by
  simp [ArchR.zetaIntegrand, ArchR.quasiChar, G0]
  ring

theorem G0_neg {D : ArchDatumR P} {σ : ℂ} {y : ℝ} (hy : 0 < y) :
    G0 D σ (-y) = (y : ℂ) ^ (σ - 1 - 1) * D.W (ArchR.diagOne (-y)) := by
  have hy0 : (y : ℂ) ≠ 0 := ofReal_ne_zero.2 hy.ne'
  rw [G0, abs_neg, abs_of_pos hy, cpow_sub (σ - 1) 1 hy0, cpow_one]
  ring

theorem one_sub_sign_mul_eq_indicator (D : ArchDatumR P) (σ : ℂ) :
    (fun y : ℝ => (1 - ((SignType.sign y : ℝ) : ℂ)) * G0 D σ y) =ᵐ[volume]
      Set.indicator (Set.Iio 0) (fun y => (2 : ℂ) * G0 D σ y) := by
  have h0 : ({0}ᶜ : Set ℝ) ∈ ae (volume : Measure ℝ) := compl_mem_ae_iff.mpr Real.volume_singleton
  filter_upwards [h0] with y hy
  have hy' : y ≠ 0 := hy
  rcases lt_or_gt_of_ne hy' with h | h
  · rw [Set.indicator_of_mem (Set.mem_Iio.2 h), sign_neg h, SignType.coe_neg, SignType.coe_one]
    push_cast
    ring
  · rw [Set.indicator_of_notMem (by simpa using h.le), sign_pos h, SignType.coe_one]
    push_cast
    ring

theorem mellin_W_diagOne_neg (D : ArchDatumR P) (c₀ : ℂ)
    (hA : ∀ (a : ZMod 2) (s : ℂ), (P.twist 0 a).archFactor s = Complex.Gammaℂ (s + c₀))
    (σ : ℂ) (hσre : D.zeta_abscissa < σ.re) :
    MellinConvergent (fun y : ℝ => D.W (ArchR.diagOne (-y))) (σ - 1) ∧
      mellin (fun y : ℝ => D.W (ArchR.diagOne (-y))) (σ - 1) =
        Complex.Gammaℂ (σ + c₀) * ((D.zetaEntire 1 0 0 σ - D.zetaEntire 1 0 1 σ) / 2) := by
  have hσre' : D.zeta_abscissa < σ.re + (0 : ℂ).re := by simpa using hσre
  have hdet : (1 : Matrix (Fin 2) (Fin 2) ℝ).det ≠ 0 := by simp
  have hI0 := D.zeta_integrable 1 0 0 σ hdet hσre'
  have hI1 := D.zeta_integrable 1 0 1 σ hdet hσre'
  have hE0 := D.zeta_eq 1 0 0 σ hdet hσre'
  have hE1 := D.zeta_eq 1 0 1 σ hdet hσre'
  have hfun0 : ArchR.zetaIntegrand D.W 1 0 0 σ = G0 D σ := funext (zetaIntegrand_zero D σ)
  have hfun1 : ArchR.zetaIntegrand D.W 1 0 1 σ = fun y => ((SignType.sign y : ℝ) : ℂ) * G0 D σ y :=
    funext (zetaIntegrand_one D σ)
  rw [hfun0] at hI0 hE0
  rw [hfun1] at hI1 hE1
  rw [hA] at hE0 hE1

  have hdiff : ∫ y : ℝ, (1 - ((SignType.sign y : ℝ) : ℂ)) * G0 D σ y =
      Complex.Gammaℂ (σ + c₀) * (D.zetaEntire 1 0 0 σ - D.zetaEntire 1 0 1 σ) := by
    have : (fun y : ℝ => (1 - ((SignType.sign y : ℝ) : ℂ)) * G0 D σ y) =
        fun y => G0 D σ y - ((SignType.sign y : ℝ) : ℂ) * G0 D σ y := by
      funext y; ring
    rw [this, integral_sub hI0 hI1, hE0, hE1]
    ring
  have hIio : ∫ y in Set.Iio (0 : ℝ), G0 D σ y =
      Complex.Gammaℂ (σ + c₀) * (D.zetaEntire 1 0 0 σ - D.zetaEntire 1 0 1 σ) / 2 := by
    rw [← hdiff, integral_congr_ae (one_sub_sign_mul_eq_indicator D σ), integral_indicator measurableSet_Iio,
      integral_const_mul]
    ring

  have hIoi : ∫ y in Set.Ioi (0 : ℝ), G0 D σ (-y) = ∫ y in Set.Iio (0 : ℝ), G0 D σ y := by
    rw [integral_comp_neg_Ioi, neg_zero, integral_Iic_eq_integral_Iio]
  constructor
  · have h1 : Integrable (fun y : ℝ => G0 D σ (-y)) := hI0.comp_neg
    have h2 : IntegrableOn (fun y : ℝ => G0 D σ (-y)) (Set.Ioi 0) := h1.integrableOn
    rw [MellinConvergent]
    refine (integrableOn_congr_fun (fun y hy => ?_) measurableSet_Ioi).mp h2
    rw [smul_eq_mul]
    exact G0_neg hy
  · rw [mellin, ← mul_div_assoc, ← hIio, ← hIoi]
    refine setIntegral_congr_fun measurableSet_Ioi fun y hy => ?_
    rw [smul_eq_mul]
    exact (G0_neg hy).symm

theorem negSheet_mellin (D : ArchDatumR P) (c₀ : ℂ)
    (hA : ∀ (a : ZMod 2) (s : ℂ), (P.twist 0 a).archFactor s = Complex.Gammaℂ (s + c₀)) :
    ∃ (σ₀ : ℝ) (Ψ : ℂ → ℂ), Differentiable ℂ Ψ ∧
      ∀ s : ℂ, σ₀ < s.re →
        MellinConvergent (fun y : ℝ => D.W !![-Real.sqrt y, 0; 0, (Real.sqrt y)⁻¹]) s ∧
          mellin (fun y : ℝ => D.W !![-Real.sqrt y, 0; 0, (Real.sqrt y)⁻¹]) s =
            Complex.Gammaℂ (s + (c₀ - (P.centralExponent - 1) / 2)) * Ψ s := by

  refine ⟨D.zeta_abscissa - 1 + ((P.centralExponent + 1) / 2).re,
    fun s => (D.zetaEntire 1 0 0 (s + 1 - (P.centralExponent + 1) / 2)
      - D.zetaEntire 1 0 1 (s + 1 - (P.centralExponent + 1) / 2)) / 2, ?_, fun s hs => ?_⟩
  · have h0 := D.zetaEntire_differentiable 1 0 0
    have h1 := D.zetaEntire_differentiable 1 0 1
    have hsh : Differentiable ℂ (fun s : ℂ => s + 1 - (P.centralExponent + 1) / 2) :=
      (differentiable_id.add_const _).sub_const _
    exact ((h0.comp hsh).sub (h1.comp hsh)).div_const _
  have hσre : D.zeta_abscissa < (s + 1 - (P.centralExponent + 1) / 2).re := by
    simp only [sub_re, add_re, one_re]; linarith
  obtain ⟨hconv, hmel⟩ := mellin_W_diagOne_neg D c₀ hA (s + 1 - (P.centralExponent + 1) / 2) hσre
  have hsa : s + 1 - (P.centralExponent + 1) / 2 - 1 = s + -((P.centralExponent + 1) / 2) := by ring
  rw [hsa] at hconv hmel
  have hfun : Set.EqOn (fun y : ℝ => D.W !![-Real.sqrt y, 0; 0, (Real.sqrt y)⁻¹])
      (fun y : ℝ => (y : ℂ) ^ (-((P.centralExponent + 1) / 2)) • D.W (ArchR.diagOne (-y))) (Set.Ioi 0) :=
    fun y hy => negSheet_eq_cpow_smul D hy
  have hconv' : MellinConvergent
      (fun y : ℝ => (y : ℂ) ^ (-((P.centralExponent + 1) / 2)) • D.W (ArchR.diagOne (-y))) s :=
    MellinConvergent.cpow_smul.mpr hconv
  constructor
  · rw [MellinConvergent] at hconv' ⊢
    refine (integrableOn_congr_fun (fun y hy => ?_) measurableSet_Ioi).mpr hconv'
    simp only [hfun hy]
  · have hm : mellin (fun y : ℝ => D.W !![-Real.sqrt y, 0; 0, (Real.sqrt y)⁻¹]) s =
        mellin (fun y : ℝ => (y : ℂ) ^ (-((P.centralExponent + 1) / 2)) • D.W (ArchR.diagOne (-y))) s :=
      setIntegral_congr_fun measurableSet_Ioi fun y hy => by simp only [hfun hy]
    rw [hm, mellin_cpow_smul, hmel]
    congr 1
    ring_nf

end LanglandsTunnell.Converse.NegSheet

open LanglandsTunnell.Converse.NegSheet in
theorem solution
    (P : RealArchParam) (D : ArchDatumR P) (k₀ : ℤ)
    (hDW : ∀ (r : rowIsometrySubgroup₀ ℝ) (x : GL (Fin 2) ℝ),
      D.W ((x * (r : GL (Fin 2) ℝ) : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) =
        (archWeightCharℝ k₀ r : ℂ) * D.W (x : Matrix (Fin 2) (Fin 2) ℝ))
    (hDE : ArchCasimir.IsCasimirEigen D)
    (ν : ℂ) (hν : P.laplaceEigenvalue = 1 / 4 - ν ^ 2)
    (c₀ : ℂ) (hA : ∀ (a : ZMod 2) (s : ℂ), (P.twist 0 a).archFactor s = Complex.Gammaℂ (s + c₀)) :
    let f : ℝ → ℂ := fun y => D.W !![-Real.sqrt y, 0; 0, (Real.sqrt y)⁻¹]
    (DifferentiableOn ℝ f (Set.Ioi 0) ∧ DifferentiableOn ℝ (deriv f) (Set.Ioi 0) ∧
      ∀ y : ℝ, 0 < y →
        (y : ℂ) ^ 2 * deriv (deriv f) y
            + (1 / 4 - ν ^ 2 + 2 * (π : ℂ) * ((-(k₀ : ℝ) : ℝ) : ℂ) * (y : ℂ) - 4 * (π : ℂ) ^ 2 * (y : ℂ) ^ 2) * f y = 0) ∧
    (∃ C N : ℝ, ∀ y : ℝ, 1 ≤ y → ‖f y‖ ≤ C * y ^ N) ∧
    (∃ (σ₀ : ℝ) (Ψ : ℂ → ℂ), Differentiable ℂ Ψ ∧
      ∀ s : ℂ, σ₀ < s.re →
        MellinConvergent (fun y : ℝ => f y) s ∧
          mellin (fun y : ℝ => f y) s = Complex.Gammaℂ (s + (c₀ - (P.centralExponent - 1) / 2)) * Ψ s) :=
  ⟨negSheet_ode D k₀ hDW hDE ν hν, negSheet_growth D, negSheet_mellin D c₀ hA⟩

end

end S_LanglandsTunnell_Converse_ArchDatumR_negSheet_ode_and_growth_and_mellin_eq_of_archWeightChar_of_isCasimirEigen
end P2MW
export P2MW.S_LanglandsTunnell_Converse_ArchDatumR_negSheet_ode_and_growth_and_mellin_eq_of_archWeightChar_of_isCasimirEigen (solution)
