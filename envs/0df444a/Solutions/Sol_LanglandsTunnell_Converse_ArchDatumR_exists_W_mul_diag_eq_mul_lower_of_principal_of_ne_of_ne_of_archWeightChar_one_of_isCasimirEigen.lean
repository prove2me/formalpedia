-- Prove2me | solution 1 for LanglandsTunnell.Converse.ArchDatumR.exists_W_mul_diag_eq_mul_lower_of_principal_of_ne_of_ne_of_archWeightChar_one_of_isCasimirEigen
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:08.353894+00:00
-- url     : https://prove2.me/submissions/3d758bb0-4dae-5ce3-9f2f-b350e3e89867

import Definitions.Def_AutomorphicForm_TranslateSpanOccurrence
import Definitions.Def_AutomorphicForm_ArchDerivCasimir
import Definitions.Def_LanglandsTunnell_JLConverse
import Definitions.Def_LanglandsTunnell_ArchCasimirCompanion
import Definitions.Def_AutomorphicForm_ArchWeightChar
import Definitions.Def_NumberField_TateGlobalZeta
import Theorems.Thm_LanglandsTunnell_Converse_ArchDatumR_laws_and_torus_ode_of_archWeightChar_of_isCasimirEigen
import Theorems.Thm_LanglandsTunnell_Converse_ArchR_eq_mul_of_unip_law_of_central_law_of_archWeightChar_of_torus_eq_of_sign_det
import Theorems.Thm_LanglandsTunnell_linearDependent_of_whittaker_ode_of_moderateGrowth_complexParam
import Theorems.Thm_LanglandsTunnell_exists_mellin_whittakerProfile_eq_archFactor_of_whittaker_ode_weightOne
import Mathlib
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_LanglandsTunnell_Converse_ArchDatumR_exists_W_mul_diag_eq_mul_lower_of_principal_of_ne_of_ne_of_archWeightChar_one_of_isCasimirEigen

set_option autoImplicit false

open Real Complex MeasureTheory Set Filter
open NumberField AutomorphicForm
open LanglandsTunnell LanglandsTunnell.RealArchParam LanglandsTunnell.Converse

noncomputable section

namespace Ws47DZL

variable {P : RealArchParam}

def ray (ε y : ℝ) : Matrix (Fin 2) (Fin 2) ℝ := !![ε * Real.sqrt y, 0; 0, (Real.sqrt y)⁻¹]

theorem ray_one (y : ℝ) : ray 1 y = !![Real.sqrt y, 0; 0, (Real.sqrt y)⁻¹] := by
  simp [ray]

theorem ray_neg_one (y : ℝ) : ray (-1) y = !![-Real.sqrt y, 0; 0, (Real.sqrt y)⁻¹] := by
  simp [ray]

theorem ray_det (ε : ℝ) {y : ℝ} (hy : 0 < y) : (ray ε y).det = ε := by
  have hsq : Real.sqrt y ≠ 0 := (Real.sqrt_pos.mpr hy).ne'
  rw [ray, Matrix.det_fin_two_of, mul_zero, sub_zero, mul_assoc, mul_inv_cancel₀ hsq, mul_one]

theorem sqrt_smul_ray {ε y : ℝ} (hy : 0 < y) : Real.sqrt y • ray ε y = ArchR.diagOne (ε * y) := by
  have hs : Real.sqrt y ≠ 0 := (Real.sqrt_pos.2 hy).ne'
  rw [ArchR.diagOne, ray]
  ext i j; fin_cases i <;> fin_cases j <;>
    simp [Matrix.smul_apply, hs]
  rw [mul_left_comm, Real.mul_self_sqrt hy.le]

theorem centralChar_of_pos (t : ℝ) (ht : 0 < t) : ArchR.centralChar P t = (t : ℂ) ^ P.centralExponent := by
  rw [ArchR.centralChar, ArchR.quasiChar, abs_of_pos ht]
  split_ifs
  · rw [mul_one]
  · rw [sign_pos ht]; simp

theorem W_diagOne (D : ArchDatumR P) (ε : ℝ) {y : ℝ} (hy : 0 < y) :
    D.W (ArchR.diagOne (ε * y)) =
      ((Real.sqrt y : ℝ) : ℂ) ^ P.centralExponent * ((Real.sqrt y : ℝ) : ℂ) * D.W (ray ε y) := by
  have hs : 0 < Real.sqrt y := Real.sqrt_pos.2 hy
  rw [← sqrt_smul_ray hy, D.central_law _ _ hs.ne', centralChar_of_pos _ hs, abs_of_pos hs]

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

theorem G0_pos {D : ArchDatumR P} {σ : ℂ} {y : ℝ} (hy : 0 < y) :
    G0 D σ y = (y : ℂ) ^ (σ - 1 - 1) * D.W (ArchR.diagOne y) := by
  have hy0 : (y : ℂ) ≠ 0 := ofReal_ne_zero.2 hy.ne'
  rw [G0, abs_of_pos hy, cpow_sub (σ - 1) 1 hy0, cpow_one]
  ring

theorem zeta_split (D : ArchDatumR P) (b : ZMod 2) (σ : ℂ) (hσ : D.zeta_abscissa < σ.re) :
    ∫ y : ℝ, ArchR.zetaIntegrand D.W 1 0 b σ y =
      (∫ y in Set.Ioi (0 : ℝ), G0 D σ y) + (-1 : ℂ) ^ b.val * ∫ y in Set.Ioi (0 : ℝ), G0 D σ (-y) := by
  have hσre' : D.zeta_abscissa < σ.re + (0 : ℂ).re := by simpa using hσ
  have hdet : (1 : Matrix (Fin 2) (Fin 2) ℝ).det ≠ 0 := by simp
  have hI0 := D.zeta_integrable 1 0 0 σ hdet hσre'
  have hI1 := D.zeta_integrable 1 0 1 σ hdet hσre'
  have hfun0 : ArchR.zetaIntegrand D.W 1 0 0 σ = G0 D σ := funext (zetaIntegrand_zero D σ)
  have hfun1 : ArchR.zetaIntegrand D.W 1 0 1 σ = fun y => ((SignType.sign y : ℝ) : ℂ) * G0 D σ y :=
    funext (zetaIntegrand_one D σ)
  rw [hfun0] at hI0
  rw [hfun1] at hI1
  have hsplit0 : ∫ y : ℝ, G0 D σ y = (∫ y in Set.Iic (0 : ℝ), G0 D σ y) + ∫ y in Set.Ioi (0 : ℝ), G0 D σ y :=
    (intervalIntegral.integral_Iic_add_Ioi hI0.integrableOn hI0.integrableOn).symm
  have hsplit1 : ∫ y : ℝ, ((SignType.sign y : ℝ) : ℂ) * G0 D σ y =
      (∫ y in Set.Iic (0 : ℝ), ((SignType.sign y : ℝ) : ℂ) * G0 D σ y) +
        ∫ y in Set.Ioi (0 : ℝ), ((SignType.sign y : ℝ) : ℂ) * G0 D σ y :=
    (intervalIntegral.integral_Iic_add_Ioi hI1.integrableOn hI1.integrableOn).symm
  have hneg : ∫ y in Set.Iic (0 : ℝ), G0 D σ y = ∫ y in Set.Ioi (0 : ℝ), G0 D σ (-y) := by
    rw [integral_comp_neg_Ioi, neg_zero]
  have hIoi1 : ∫ y in Set.Ioi (0 : ℝ), ((SignType.sign y : ℝ) : ℂ) * G0 D σ y = ∫ y in Set.Ioi (0 : ℝ), G0 D σ y := by
    refine setIntegral_congr_fun measurableSet_Ioi fun y hy => ?_
    rw [sign_pos hy, SignType.coe_one]
    push_cast
    ring
  have hIic1 : ∫ y in Set.Iic (0 : ℝ), ((SignType.sign y : ℝ) : ℂ) * G0 D σ y = -∫ y in Set.Ioi (0 : ℝ), G0 D σ (-y) := by
    have hneg' : ∫ y in Set.Ioi (0 : ℝ), -G0 D σ (-y) = ∫ y in Set.Iic (0 : ℝ), -G0 D σ y := by
      have := integral_comp_neg_Ioi 0 (fun x => -G0 D σ x)
      simp only [neg_zero] at this
      exact this
    rw [← integral_neg, hneg', integral_Iic_eq_integral_Iio, integral_Iic_eq_integral_Iio]
    refine setIntegral_congr_fun measurableSet_Iio fun y hy => ?_
    rw [sign_neg hy, SignType.coe_neg, SignType.coe_one]
    push_cast
    ring
  have hb : b = 0 ∨ b = 1 := by fin_cases b <;> first | exact Or.inl rfl | exact Or.inr rfl
  rcases hb with rfl | rfl
  · rw [hfun0, hsplit0, hneg, ZMod.val_zero, pow_zero, one_mul]
    ring
  · rw [hfun1, hsplit1, hIoi1, hIic1, ZMod.val_one, pow_one]
    ring

theorem archFactor_principal_twist (u₁ u₂ : ℂ) (a₁ a₂ b : ZMod 2) (s : ℂ) :
    ((RealArchParam.principal u₁ a₁ u₂ a₂).twist 0 b).archFactor s =
      Gammaℝ (s + (u₁ + signShift (a₁ + b))) * Gammaℝ (s + (u₂ + signShift (a₂ + b))) := by
  simp [RealArchParam.twist, RealArchParam.archFactor, RealArchParam.gammaR, RealArchParam.gammaC]

def lowP (f : ℝ → ℂ) (y : ℝ) : ℂ := 2 * (y : ℂ) * deriv f y + (4 * (π : ℂ) * (y : ℂ) - 1) * f y

def lowM (g : ℝ → ℂ) (y : ℝ) : ℂ := 2 * (y : ℂ) * deriv g y - (4 * (π : ℂ) * (y : ℂ) + 1) * g y

theorem lowP_congr {f g : ℝ → ℂ} (h : Set.EqOn f g (Set.Ioi 0)) {y : ℝ} (hy : 0 < y) : lowP f y = lowP g y := by
  have hev : f =ᶠ[nhds y] g := Filter.eventuallyEq_of_mem (isOpen_Ioi.mem_nhds hy) h
  rw [lowP, lowP, hev.deriv_eq, h hy]

theorem lowM_congr {f g : ℝ → ℂ} (h : Set.EqOn f g (Set.Ioi 0)) {y : ℝ} (hy : 0 < y) : lowM f y = lowM g y := by
  have hev : f =ᶠ[nhds y] g := Filter.eventuallyEq_of_mem (isOpen_Ioi.mem_nhds hy) h
  rw [lowM, lowM, hev.deriv_eq, h hy]

theorem lowP_const_mul (c : ℂ) (f : ℝ → ℂ) (y : ℝ) : lowP (fun t => c * f t) y = c * lowP f y := by
  rw [lowP, lowP, deriv_const_mul_field']
  ring

theorem lowM_const_mul (c : ℂ) (f : ℝ → ℂ) (y : ℝ) : lowM (fun t => c * f t) y = c * lowM f y := by
  rw [lowM, lowM, deriv_const_mul_field']
  ring

theorem contDiffOn_top_iff_deriv {f : ℝ → ℂ} :
    ContDiffOn ℝ (⊤ : ℕ∞) f (Set.Ioi 0) ↔
      DifferentiableOn ℝ f (Set.Ioi 0) ∧ ContDiffOn ℝ (⊤ : ℕ∞) (deriv f) (Set.Ioi 0) := by
  have h := contDiffOn_succ_iff_deriv_of_isOpen (𝕜 := ℝ) (n := ((⊤ : ℕ∞) : WithTop ℕ∞)) (f := f)
    (s := Set.Ioi (0 : ℝ)) isOpen_Ioi
  rw [show ((⊤ : ℕ∞) : WithTop ℕ∞) + 1 = ((⊤ : ℕ∞) : WithTop ℕ∞) from rfl] at h
  rw [h]
  constructor
  · rintro ⟨h1, -, h3⟩; exact ⟨h1, h3⟩
  · rintro ⟨h1, h3⟩; exact ⟨h1, fun h => absurd h (by simp), h3⟩

theorem lowP_lowM_eq (ν : ℂ) (g : ℝ → ℂ)
    (hg : DifferentiableOn ℝ g (Set.Ioi 0)) (hg' : DifferentiableOn ℝ (deriv g) (Set.Ioi 0))
    (hgeq : ∀ y : ℝ, 0 < y →
      (y : ℂ) ^ 2 * deriv (deriv g) y
        + (1 / 4 - ν ^ 2 - 2 * (π : ℂ) * (y : ℂ) - 4 * (π : ℂ) ^ 2 * (y : ℂ) ^ 2) * g y = 0)
    (y : ℝ) (hy : 0 < y) :
    lowP (lowM g) y = 4 * ν ^ 2 * g y := by
  have h1 : HasDerivAt g (deriv g y) y := (hg.differentiableAt (isOpen_Ioi.mem_nhds hy)).hasDerivAt
  have h2 : HasDerivAt (deriv g) (deriv (deriv g) y) y := (hg'.differentiableAt (isOpen_Ioi.mem_nhds hy)).hasDerivAt
  have hc : HasDerivAt (fun t : ℝ => (t : ℂ)) 1 y := by
    simpa using (hasDerivAt_id y).ofReal_comp
  have hL : HasDerivAt (lowM g)
      (2 * 1 * deriv g y + 2 * (y : ℂ) * deriv (deriv g) y
        - ((4 * (π : ℂ) * 1 + 0) * g y + (4 * (π : ℂ) * (y : ℂ) + 1) * deriv g y)) y := by
    have hA : HasDerivAt (fun t : ℝ => 2 * (t : ℂ) * deriv g t)
        (2 * 1 * deriv g y + 2 * (y : ℂ) * deriv (deriv g) y) y := by
      have := ((hc.const_mul (2 : ℂ)).mul h2)
      convert this using 1 <;> first | rfl | ring1 | (funext _; simp only [Pi.mul_apply]; ring1)
    have hB : HasDerivAt (fun t : ℝ => (4 * (π : ℂ) * (t : ℂ) + 1) * g t)
        ((4 * (π : ℂ) * 1 + 0) * g y + (4 * (π : ℂ) * (y : ℂ) + 1) * deriv g y) y := by
      have hq : HasDerivAt (fun t : ℝ => 4 * (π : ℂ) * (t : ℂ) + 1) (4 * (π : ℂ) * 1 + 0) y :=
        ((hc.const_mul (4 * (π : ℂ))).add (hasDerivAt_const y (1 : ℂ)))
      exact hq.mul h1
    exact hA.sub hB
  rw [lowP, hL.deriv, lowM]
  have hode := hgeq y hy
  linear_combination (4 : ℂ) * hode

theorem lowM_ode (ν : ℂ) (g : ℝ → ℂ) (hg : ContDiffOn ℝ (⊤ : ℕ∞) g (Set.Ioi 0))
    (hgeq : ∀ y : ℝ, 0 < y →
      (y : ℂ) ^ 2 * deriv (deriv g) y
        + (1 / 4 - ν ^ 2 - 2 * (π : ℂ) * (y : ℂ) - 4 * (π : ℂ) ^ 2 * (y : ℂ) ^ 2) * g y = 0) :
    ContDiffOn ℝ (⊤ : ℕ∞) (lowM g) (Set.Ioi 0) ∧
      ∀ y : ℝ, 0 < y →
        (y : ℂ) ^ 2 * deriv (deriv (lowM g)) y
          + (1 / 4 - ν ^ 2 + 2 * (π : ℂ) * (y : ℂ) - 4 * (π : ℂ) ^ 2 * (y : ℂ) ^ 2) * lowM g y = 0 := by
  obtain ⟨hg0, hg1c⟩ := contDiffOn_top_iff_deriv.mp hg
  obtain ⟨hg1, hg2c⟩ := contDiffOn_top_iff_deriv.mp hg1c
  obtain ⟨hg2, hg3c⟩ := contDiffOn_top_iff_deriv.mp hg2c
  have hofr : ContDiff ℝ (⊤ : ℕ∞) (fun t : ℝ => (t : ℂ)) := Complex.ofRealCLM.contDiff
  have hc : ∀ t : ℝ, HasDerivAt (fun t : ℝ => (t : ℂ)) 1 t := fun t => by
    simpa using (hasDerivAt_id t).ofReal_comp
  refine ⟨?_, fun y hy => ?_⟩
  · have : lowM g = fun y : ℝ => 2 * (y : ℂ) * deriv g y - (4 * (π : ℂ) * (y : ℂ) + 1) * g y := rfl
    rw [this]
    exact ((contDiffOn_const.mul hofr.contDiffOn).mul hg1c).sub
      (((contDiffOn_const.mul hofr.contDiffOn).add contDiffOn_const).mul hg)
  · have hAt0 : ∀ t : ℝ, 0 < t → HasDerivAt g (deriv g t) t := fun t ht =>
      (hg0.differentiableAt (isOpen_Ioi.mem_nhds ht)).hasDerivAt
    have hAt1 : ∀ t : ℝ, 0 < t → HasDerivAt (deriv g) (deriv (deriv g) t) t := fun t ht =>
      (hg1.differentiableAt (isOpen_Ioi.mem_nhds ht)).hasDerivAt
    have hAt2 : ∀ t : ℝ, 0 < t → HasDerivAt (deriv (deriv g)) (deriv (deriv (deriv g)) t) t := fun t ht =>
      (hg2.differentiableAt (isOpen_Ioi.mem_nhds ht)).hasDerivAt

    have hL1 : ∀ t : ℝ, 0 < t → HasDerivAt (lowM g)
        (2 * 1 * deriv g t + 2 * (t : ℂ) * deriv (deriv g) t
          - ((4 * (π : ℂ) * 1 + 0) * g t + (4 * (π : ℂ) * (t : ℂ) + 1) * deriv g t)) t := by
      intro t ht
      have hA : HasDerivAt (fun s : ℝ => 2 * (s : ℂ) * deriv g s)
          (2 * 1 * deriv g t + 2 * (t : ℂ) * deriv (deriv g) t) t := by
        have := (((hc t).const_mul (2 : ℂ)).mul (hAt1 t ht))
        convert this using 1 <;> first | rfl | ring1 | (funext _; simp only [Pi.mul_apply]; ring1)
      have hB : HasDerivAt (fun s : ℝ => (4 * (π : ℂ) * (s : ℂ) + 1) * g s)
          ((4 * (π : ℂ) * 1 + 0) * g t + (4 * (π : ℂ) * (t : ℂ) + 1) * deriv g t) t :=
        (((hc t).const_mul (4 * (π : ℂ))).add (hasDerivAt_const t (1 : ℂ))).mul (hAt0 t ht)
      exact hA.sub hB
    set L1 : ℝ → ℂ := fun t => 2 * 1 * deriv g t + 2 * (t : ℂ) * deriv (deriv g) t
          - ((4 * (π : ℂ) * 1 + 0) * g t + (4 * (π : ℂ) * (t : ℂ) + 1) * deriv g t) with hL1def
    have hL1eq : Set.EqOn (deriv (lowM g)) L1 (Set.Ioi 0) := fun t ht => (hL1 t ht).deriv

    have hL2 : HasDerivAt L1
        (2 * 1 * deriv (deriv g) y + (2 * 1 * deriv (deriv g) y + 2 * (y : ℂ) * deriv (deriv (deriv g)) y)
          - ((4 * (π : ℂ) * 1 + 0) * deriv g y
            + ((4 * (π : ℂ) * 1 + 0) * deriv g y + (4 * (π : ℂ) * (y : ℂ) + 1) * deriv (deriv g) y))) y := by
      have hA : HasDerivAt (fun s : ℝ => 2 * (s : ℂ) * deriv (deriv g) s)
          (2 * 1 * deriv (deriv g) y + 2 * (y : ℂ) * deriv (deriv (deriv g)) y) y := by
        have := (((hc y).const_mul (2 : ℂ)).mul (hAt2 y hy))
        convert this using 1 <;> first | rfl | ring1 | (funext _; simp only [Pi.mul_apply]; ring1)
      have hB : HasDerivAt (fun s : ℝ => (4 * (π : ℂ) * (s : ℂ) + 1) * deriv g s)
          ((4 * (π : ℂ) * 1 + 0) * deriv g y + (4 * (π : ℂ) * (y : ℂ) + 1) * deriv (deriv g) y) y :=
        (((hc y).const_mul (4 * (π : ℂ))).add (hasDerivAt_const y (1 : ℂ))).mul (hAt1 y hy)
      have hA' : HasDerivAt (fun s : ℝ => 2 * 1 * deriv g s) (2 * 1 * deriv (deriv g) y) y :=
        (hAt1 y hy).const_mul _
      have hB' : HasDerivAt (fun s : ℝ => (4 * (π : ℂ) * 1 + 0) * g s) ((4 * (π : ℂ) * 1 + 0) * deriv g y) y :=
        (hAt0 y hy).const_mul _
      have := (hA'.add hA).sub (hB'.add hB)
      convert this using 1 <;> first | rfl | (funext _; simp only [Pi.add_apply, Pi.sub_apply])
    have hd2 : deriv (deriv (lowM g)) y =
        2 * 1 * deriv (deriv g) y + (2 * 1 * deriv (deriv g) y + 2 * (y : ℂ) * deriv (deriv (deriv g)) y)
          - ((4 * (π : ℂ) * 1 + 0) * deriv g y
            + ((4 * (π : ℂ) * 1 + 0) * deriv g y + (4 * (π : ℂ) * (y : ℂ) + 1) * deriv (deriv g) y)) := by
      have hev : deriv (lowM g) =ᶠ[nhds y] L1 := Filter.eventuallyEq_of_mem (isOpen_Ioi.mem_nhds hy) hL1eq
      rw [hev.deriv_eq]
      exact hL2.deriv

    set E : ℝ → ℂ := fun t => (t : ℂ) ^ 2 * deriv (deriv g) t
        + (1 / 4 - ν ^ 2 - 2 * (π : ℂ) * (t : ℂ) - 4 * (π : ℂ) ^ 2 * (t : ℂ) ^ 2) * g t with hEdef
    have hE : HasDerivAt E
        (2 * (y : ℂ) * 1 * deriv (deriv g) y + (y : ℂ) ^ 2 * deriv (deriv (deriv g)) y
          + ((0 - 2 * (π : ℂ) * 1 - 4 * (π : ℂ) ^ 2 * (2 * (y : ℂ) * 1)) * g y
            + (1 / 4 - ν ^ 2 - 2 * (π : ℂ) * (y : ℂ) - 4 * (π : ℂ) ^ 2 * (y : ℂ) ^ 2) * deriv g y)) y := by
      have hsq : HasDerivAt (fun t : ℝ => (t : ℂ) ^ 2) (2 * (y : ℂ) * 1) y := by
        have := (hc y).pow 2
        convert this using 1 <;> first | rfl | simp
      have hA : HasDerivAt (fun t : ℝ => (t : ℂ) ^ 2 * deriv (deriv g) t)
          (2 * (y : ℂ) * 1 * deriv (deriv g) y + (y : ℂ) ^ 2 * deriv (deriv (deriv g)) y) y := hsq.mul (hAt2 y hy)
      have hQ : HasDerivAt (fun t : ℝ => (1 / 4 - ν ^ 2 - 2 * (π : ℂ) * (t : ℂ) - 4 * (π : ℂ) ^ 2 * (t : ℂ) ^ 2))
          (0 - 2 * (π : ℂ) * 1 - 4 * (π : ℂ) ^ 2 * (2 * (y : ℂ) * 1)) y :=
        ((hasDerivAt_const y _).sub ((hc y).const_mul _)).sub (hsq.const_mul _)
      exact hA.add (hQ.mul (hAt0 y hy))
    have hE0 : deriv E y = 0 := by
      have hev : E =ᶠ[nhds y] fun _ => (0 : ℂ) :=
        Filter.eventuallyEq_of_mem (isOpen_Ioi.mem_nhds hy) fun t ht => hgeq t ht
      rw [hev.deriv_eq, deriv_const]
    have hdODE := hE.deriv
    rw [hE0] at hdODE
    have hode := hgeq y hy
    rw [hd2, lowM]
    linear_combination (2 * (y : ℂ)) * hdODE.symm + (-1 - 4 * (π : ℂ) * (y : ℂ)) * hode

theorem lowM_growth (ν : ℂ) (k : ℝ) (g : ℝ → ℂ)
    (hg : DifferentiableOn ℝ g (Set.Ioi 0)) (hg' : DifferentiableOn ℝ (deriv g) (Set.Ioi 0))
    (hgeq : ∀ y : ℝ, 0 < y →
      (y : ℂ) ^ 2 * deriv (deriv g) y
        + (1 / 4 - ν ^ 2 + 2 * (π : ℂ) * (k : ℂ) * (y : ℂ) - 4 * (π : ℂ) ^ 2 * (y : ℂ) ^ 2) * g y = 0)
    (hgr : ∃ C N : ℝ, ∀ y : ℝ, 1 ≤ y → ‖g y‖ ≤ C * y ^ N) :
    ∃ C N : ℝ, ∀ y : ℝ, 1 ≤ y → ‖lowM g y‖ ≤ C * y ^ N := by
  obtain ⟨C, N, hb⟩ := hgr

  set C' : ℝ := |C| with hC'
  set N' : ℝ := max N 0 with hN'
  have hN'0 : 0 ≤ N' := le_max_right _ _
  have hb' : ∀ y : ℝ, 1 ≤ y → ‖g y‖ ≤ C' * y ^ N' := by
    intro y hy
    have hy0 : 0 < y := lt_of_lt_of_le one_pos hy
    calc ‖g y‖ ≤ C * y ^ N := hb y hy
      _ ≤ |C| * y ^ N := by gcongr; exact le_abs_self C
      _ ≤ |C| * y ^ N' := by
        exact mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hy (le_max_left _ _)) (abs_nonneg C)

  set A : ℝ := ‖(1 / 4 : ℂ) - ν ^ 2‖ + 2 * π * |k| + 4 * π ^ 2 with hA
  have hA0 : 0 ≤ A := by positivity
  have hQ : ∀ t : ℝ, 1 ≤ t →
      ‖(1 / 4 - ν ^ 2 + 2 * (π : ℂ) * (k : ℂ) * (t : ℂ) - 4 * (π : ℂ) ^ 2 * (t : ℂ) ^ 2)‖ ≤ A * t ^ 2 := by
    intro t ht
    have ht0 : 0 ≤ t := le_trans zero_le_one ht
    have ht2 : t ≤ t ^ 2 := by nlinarith
    have h1 : ‖(1 / 4 : ℂ) - ν ^ 2‖ ≤ ‖(1 / 4 : ℂ) - ν ^ 2‖ * t ^ 2 := by
      have : (1 : ℝ) ≤ t ^ 2 := by nlinarith
      nlinarith [norm_nonneg ((1 / 4 : ℂ) - ν ^ 2)]
    have h2 : ‖2 * (π : ℂ) * (k : ℂ) * (t : ℂ)‖ ≤ 2 * π * |k| * t ^ 2 := by
      rw [norm_mul, norm_mul, norm_mul, Complex.norm_real, Complex.norm_real, Complex.norm_real, Complex.norm_ofNat,
        Real.norm_eq_abs, Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos Real.pi_pos, abs_of_nonneg ht0]
      have : 0 ≤ 2 * π * |k| := by positivity
      nlinarith
    have h3 : ‖4 * (π : ℂ) ^ 2 * (t : ℂ) ^ 2‖ ≤ 4 * π ^ 2 * t ^ 2 := by
      rw [norm_mul, norm_mul, norm_pow, norm_pow, Complex.norm_real, Complex.norm_real, Complex.norm_ofNat,
        Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos Real.pi_pos, abs_of_nonneg ht0]
    calc ‖(1 / 4 - ν ^ 2 + 2 * (π : ℂ) * (k : ℂ) * (t : ℂ) - 4 * (π : ℂ) ^ 2 * (t : ℂ) ^ 2)‖
        ≤ ‖(1 / 4 : ℂ) - ν ^ 2‖ + ‖2 * (π : ℂ) * (k : ℂ) * (t : ℂ)‖ + ‖4 * (π : ℂ) ^ 2 * (t : ℂ) ^ 2‖ :=
          norm_sub_le_of_le (norm_add_le _ _) le_rfl
      _ ≤ A * t ^ 2 := by rw [hA]; linarith

  have hg2 : ∀ t : ℝ, 1 ≤ t → ‖deriv (deriv g) t‖ ≤ A * C' * t ^ N' := by
    intro t ht
    have ht0 : 0 < t := lt_of_lt_of_le one_pos ht
    have heq := hgeq t ht0
    have hmul : ‖(t : ℂ) ^ 2 * deriv (deriv g) t‖ =
        ‖(1 / 4 - ν ^ 2 + 2 * (π : ℂ) * (k : ℂ) * (t : ℂ) - 4 * (π : ℂ) ^ 2 * (t : ℂ) ^ 2) * g t‖ := by
      rw [eq_neg_of_add_eq_zero_left heq, norm_neg]
    rw [norm_mul, norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs, abs_of_pos ht0] at hmul
    have hle : t ^ 2 * ‖deriv (deriv g) t‖ ≤ (A * t ^ 2) * (C' * t ^ N') := by
      rw [hmul]
      exact mul_le_mul (hQ t ht) (hb' t ht) (norm_nonneg _) (by positivity)
    have ht2 : 0 < t ^ 2 := by positivity
    have : t ^ 2 * ‖deriv (deriv g) t‖ ≤ t ^ 2 * (A * C' * t ^ N') := by nlinarith
    exact le_of_mul_le_mul_left this ht2

  have hg1 : ∀ y : ℝ, 1 ≤ y → ‖deriv g y‖ ≤ (‖deriv g 1‖ + A * C') * y ^ (N' + 1) := by
    intro y hy
    have hy0 : 0 < y := lt_of_lt_of_le one_pos hy
    have hmvt : ‖deriv g y - deriv g 1‖ ≤ (A * C' * y ^ N') * (y - 1) := by
      refine norm_image_sub_le_of_norm_deriv_le_segment' (f := deriv g) (f' := deriv (deriv g)) ?_ ?_ y
        (Set.right_mem_Icc.2 hy)
      · intro x hx
        have hx0 : 0 < x := lt_of_lt_of_le one_pos hx.1
        exact ((hg'.differentiableAt (isOpen_Ioi.mem_nhds hx0)).hasDerivAt).hasDerivWithinAt
      · intro x hx
        calc ‖deriv (deriv g) x‖ ≤ A * C' * x ^ N' := hg2 x hx.1
          _ ≤ A * C' * y ^ N' := by
            gcongr
            · exact le_trans zero_le_one hx.1
            · exact hx.2.le
    have hyN : (1 : ℝ) ≤ y ^ N' := Real.one_le_rpow hy hN'0
    have hyN1 : y ^ (N' + 1) = y ^ N' * y := by rw [Real.rpow_add hy0, Real.rpow_one]
    calc ‖deriv g y‖ ≤ ‖deriv g 1‖ + ‖deriv g y - deriv g 1‖ := by
          have := norm_add_le (deriv g 1) (deriv g y - deriv g 1)
          rwa [add_sub_cancel] at this
      _ ≤ ‖deriv g 1‖ + (A * C' * y ^ N') * (y - 1) := by gcongr
      _ ≤ (‖deriv g 1‖ + A * C') * y ^ (N' + 1) := by
          rw [hyN1]
          have h1 : 0 ≤ A * C' := by positivity
          have h2 : 0 ≤ ‖deriv g 1‖ := norm_nonneg _
          have hY : (1 : ℝ) ≤ y ^ N' * y := by nlinarith
          have e1 : ‖deriv g 1‖ ≤ ‖deriv g 1‖ * (y ^ N' * y) := le_mul_of_one_le_right h2 hY
          have e2 : A * C' * y ^ N' * (y - 1) ≤ A * C' * (y ^ N' * y) := by
            have : y ^ N' * (y - 1) ≤ y ^ N' * y := by nlinarith
            nlinarith
          linarith

  refine ⟨2 * (‖deriv g 1‖ + A * C') + (4 * π + 1) * C', N' + 2, fun y hy => ?_⟩
  have hy0 : 0 < y := lt_of_lt_of_le one_pos hy
  have hyN : (1 : ℝ) ≤ y ^ N' := Real.one_le_rpow hy hN'0
  have hyN2 : y ^ (N' + 2) = y ^ N' * y * y := by
    rw [show N' + 2 = N' + 1 + 1 by ring, Real.rpow_add hy0, Real.rpow_add hy0, Real.rpow_one]
  have hyN1 : y ^ (N' + 1) = y ^ N' * y := by rw [Real.rpow_add hy0, Real.rpow_one]
  have e1 : ‖2 * (y : ℂ) * deriv g y‖ ≤ 2 * y * ((‖deriv g 1‖ + A * C') * y ^ (N' + 1)) := by
    rw [norm_mul, norm_mul, Complex.norm_real, Complex.norm_ofNat, Real.norm_eq_abs, abs_of_pos hy0]
    gcongr
    exact hg1 y hy
  have e2 : ‖(4 * (π : ℂ) * (y : ℂ) + 1) * g y‖ ≤ (4 * π * y + 1) * (C' * y ^ N') := by
    rw [norm_mul]
    gcongr
    · calc ‖4 * (π : ℂ) * (y : ℂ) + 1‖ ≤ ‖4 * (π : ℂ) * (y : ℂ)‖ + ‖(1 : ℂ)‖ := norm_add_le _ _
        _ = 4 * π * y + 1 := by
          rw [norm_mul, norm_mul, Complex.norm_real, Complex.norm_real, Complex.norm_ofNat, norm_one,
            Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos Real.pi_pos, abs_of_pos hy0]
    · exact hb' y hy
  calc ‖lowM g y‖ ≤ ‖2 * (y : ℂ) * deriv g y‖ + ‖(4 * (π : ℂ) * (y : ℂ) + 1) * g y‖ := norm_sub_le _ _
    _ ≤ 2 * y * ((‖deriv g 1‖ + A * C') * y ^ (N' + 1)) + (4 * π * y + 1) * (C' * y ^ N') := add_le_add e1 e2
    _ ≤ (2 * (‖deriv g 1‖ + A * C') + (4 * π + 1) * C') * y ^ (N' + 2) := by
        rw [hyN2, hyN1]
        have h1 : 0 ≤ A * C' := by positivity
        have h2 : 0 ≤ ‖deriv g 1‖ := norm_nonneg _
        have h3 : 0 ≤ C' := abs_nonneg C
        have h4 : 0 ≤ y ^ N' := le_trans zero_le_one hyN
        set Y := y ^ N' with hY
        have hpi : 0 < π := Real.pi_pos

        have e1 : 2 * y * ((‖deriv g 1‖ + A * C') * (Y * y)) = 2 * (‖deriv g 1‖ + A * C') * (Y * y * y) := by ring
        have e2 : (4 * π * y + 1) * (C' * Y) ≤ (4 * π + 1) * C' * (Y * y * y) := by
          have hCY : 0 ≤ C' * Y := mul_nonneg h3 h4
          have f1 : 4 * π * y * (C' * Y) ≤ 4 * π * (C' * Y) * (y * y) := by
            have : y ≤ y * y := by nlinarith
            have h0 : 0 ≤ 4 * π * (C' * Y) := by positivity
            nlinarith
          have f2 : 1 * (C' * Y) ≤ C' * Y * (y * y) := by
            have : (1 : ℝ) ≤ y * y := by nlinarith
            nlinarith
          nlinarith
        nlinarith

def LW (W : Matrix (Fin 2) (Fin 2) ℝ → ℂ) (x : Matrix (Fin 2) (Fin 2) ℝ) : ℂ :=
  ArchCasimir.matrixFlowDeriv ArchDir.H W x -
    Complex.I * (ArchCasimir.matrixFlowDeriv ArchDir.E W x + ArchCasimir.matrixFlowDeriv ArchDir.Fm W x)

def kRot (t : ℝ) : GL (Fin 2) ℝ :=
  Matrix.GeneralLinearGroup.mkOfDetNeZero
    !![(Real.sqrt (1 + t ^ 2))⁻¹, -t * (Real.sqrt (1 + t ^ 2))⁻¹; t * (Real.sqrt (1 + t ^ 2))⁻¹, (Real.sqrt (1 + t ^ 2))⁻¹]
    (by
      have hp : 0 < Real.sqrt (1 + t ^ 2) := Real.sqrt_pos.2 (by positivity)
      rw [Matrix.det_fin_two_of]
      have : (Real.sqrt (1 + t ^ 2))⁻¹ * (Real.sqrt (1 + t ^ 2))⁻¹ * (1 + t ^ 2) = 1 := by
        rw [← mul_inv, Real.mul_self_sqrt (by positivity), inv_mul_cancel₀ (by positivity)]
      nlinarith [this])

theorem kRot_coe (t : ℝ) : ((kRot t : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) =
    !![(Real.sqrt (1 + t ^ 2))⁻¹, -t * (Real.sqrt (1 + t ^ 2))⁻¹; t * (Real.sqrt (1 + t ^ 2))⁻¹, (Real.sqrt (1 + t ^ 2))⁻¹] :=
  rfl

theorem kRot_mem (t : ℝ) : kRot t ∈ rowIsometrySubgroup₀ ℝ := by
  have hp0 : 0 < 1 + t ^ 2 := by positivity
  have hp : 0 < Real.sqrt (1 + t ^ 2) := Real.sqrt_pos.2 hp0
  have hpp : (Real.sqrt (1 + t ^ 2))⁻¹ * (Real.sqrt (1 + t ^ 2))⁻¹ * (1 + t ^ 2) = 1 := by
    rw [← mul_inv, Real.mul_self_sqrt hp0.le, inv_mul_cancel₀ hp0.ne']
  have hdet : ((kRot t : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ).det = 1 := by
    rw [kRot_coe, Matrix.det_fin_two_of]
    nlinarith [hpp]
  refine (mem_rowIsometrySubgroup₀_iff ℝ).2 ⟨hdet, ?_, ?_⟩
  · rw [hdet, norm_one]
  · intro x y
    simp only [kRot_coe, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.empty_val', Matrix.cons_val_fin_one, Real.norm_eq_abs, sq_abs]
    linear_combination (x ^ 2 + y ^ 2) * hpp

def rayGL (ε y : ℝ) (hε : ε ≠ 0) (hy : 0 < y) : GL (Fin 2) ℝ :=
  Matrix.GeneralLinearGroup.mkOfDetNeZero (ray ε y) (by rw [ray_det ε hy]; exact hε)

theorem rayGL_coe (ε y : ℝ) (hε : ε ≠ 0) (hy : 0 < y) :
    ((rayGL ε y hε hy : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) = ray ε y := rfl

theorem archWeightCharℝ_one_coe (r : rowIsometrySubgroup₀ ℝ) :
    ((archWeightCharℝ 1 r : ℂˣ) : ℂ) = firstRowℂ (r : GL (Fin 2) ℝ) := by
  show ((((archWeightOneℝ r) ^ (1 : ℤ) : ℂˣ)) : ℂ) = _
  rw [zpow_one]
  rfl

theorem archWeightCharℝ_neg_one_coe (r : rowIsometrySubgroup₀ ℝ) :
    ((archWeightCharℝ (-1) r : ℂˣ) : ℂ) = (firstRowℂ (r : GL (Fin 2) ℝ))⁻¹ := by
  show ((((archWeightOneℝ r) ^ (-1 : ℤ) : ℂˣ)) : ℂ) = _
  rw [zpow_neg, zpow_one, Units.val_inv_eq_inv_val]
  rfl

section TorusValues

variable (W : Matrix (Fin 2) (Fin 2) ℝ → ℂ)
  (hN : ∀ (t : ℝ) (g : Matrix (Fin 2) (Fin 2) ℝ), W (ArchR.unip t * g) = ArchR.psi t * W g)
  (hK : ∀ (r : rowIsometrySubgroup₀ ℝ) (x : GL (Fin 2) ℝ),
      W ((x * (r : GL (Fin 2) ℝ) : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) =
        (archWeightCharℝ 1 r : ℂ) * W (x : Matrix (Fin 2) (Fin 2) ℝ))

theorem flowH_ray (ε : ℝ) {y : ℝ} (hy : 0 < y) (hd : DifferentiableAt ℝ (fun t => W (ray ε t)) y) :
    ArchCasimir.matrixFlowDeriv ArchDir.H W (ray ε y) = 2 * (y : ℂ) * deriv (fun t => W (ray ε t)) y := by
  have hsq : Real.sqrt y ≠ 0 := (Real.sqrt_pos.mpr hy).ne'
  set f : ℝ → ℝ := fun s => y * Real.exp (2 * s) with hf
  have hfun : (fun s : ℝ => W (ray ε y * (archFlowMatrix ArchDir.H s : Matrix (Fin 2) (Fin 2) ℝ))) =
      fun s => W (ray ε (f s)) := by
    funext s
    congr 1
    have hsqrt : Real.sqrt (y * Real.exp (2 * s)) = Real.sqrt y * Real.exp s := by
      rw [Real.sqrt_mul hy.le, show (2 * s) = s + s from two_mul s, Real.exp_add,
        Real.sqrt_mul_self (Real.exp_pos s).le]
    rw [show (archFlowMatrix ArchDir.H s : Matrix (Fin 2) (Fin 2) ℝ) = !![Real.exp s, 0; 0, Real.exp (-s)] from rfl,
      ray, ray, hf]
    simp only [hsqrt]
    ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Real.exp_neg, mul_comm] <;> ring
  rw [ArchCasimir.matrixFlowDeriv, hfun]
  have hf0 : f 0 = y := by simp [hf]
  have hfd : HasDerivAt f (y * (Real.exp (2 * 0) * 2)) 0 := by
    have := ((hasDerivAt_id (0 : ℝ)).const_mul 2).exp.const_mul y
    first | simpa [Pi.div_def, Pi.mul_def, Pi.add_def, Pi.neg_def, Pi.inv_def, Pi.sub_def, Pi.pow_def, Function.comp_def] using this | (simp [Pi.div_def, Pi.mul_def, Pi.add_def, Pi.neg_def, Pi.inv_def, Pi.sub_def, Pi.pow_def, Function.comp_def] at this; exact this)
  have hg : HasDerivAt (fun t => W (ray ε t)) (deriv (fun t => W (ray ε t)) y) (f 0) := by
    rw [hf0]; exact hd.hasDerivAt
  have h2 : HasDerivAt (fun s => W (ray ε (f s))) ((y * (Real.exp (2 * 0) * 2)) • deriv (fun t => W (ray ε t)) y) 0 :=
    hg.scomp 0 hfd
  rw [h2.deriv, Complex.real_smul]
  simp only [mul_zero, Real.exp_zero, mul_one]
  push_cast
  ring

include hN in

theorem flowE_ray (ε : ℝ) {y : ℝ} (hy : 0 < y) :
    ArchCasimir.matrixFlowDeriv ArchDir.E W (ray ε y) = 2 * (π : ℂ) * Complex.I * (ε : ℂ) * (y : ℂ) * W (ray ε y) := by
  have hsq : Real.sqrt y ≠ 0 := (Real.sqrt_pos.mpr hy).ne'
  have hfun : (fun s : ℝ => W (ray ε y * (archFlowMatrix ArchDir.E s : Matrix (Fin 2) (Fin 2) ℝ))) =
      fun s => Complex.exp (2 * (π : ℂ) * Complex.I * (((ε * y) * s : ℝ) : ℂ)) * W (ray ε y) := by
    funext s
    have hm : ray ε y * (archFlowMatrix ArchDir.E s : Matrix (Fin 2) (Fin 2) ℝ) = ArchR.unip ((ε * y) * s) * ray ε y := by
      rw [show (archFlowMatrix ArchDir.E s : Matrix (Fin 2) (Fin 2) ℝ) = !![1, s; 0, 1] from rfl, ArchR.unip, ray]
      ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply]
      field_simp
      rw [Real.sq_sqrt hy.le]
      ring
    rw [hm, hN, ArchR.psi]
  rw [ArchCasimir.matrixFlowDeriv, hfun]
  apply HasDerivAt.deriv
  have h1 : HasDerivAt (fun s : ℝ => (((ε * y) * s : ℝ) : ℂ)) (((ε * y) : ℝ) : ℂ) 0 := by
    have := ((hasDerivAt_id (0 : ℝ)).const_mul (ε * y)).ofReal_comp
    first | simpa [Pi.div_def, Pi.mul_def, Pi.add_def, Pi.neg_def, Pi.inv_def, Pi.sub_def, Pi.pow_def, Function.comp_def] using this | (simp [Pi.div_def, Pi.mul_def, Pi.add_def, Pi.neg_def, Pi.inv_def, Pi.sub_def, Pi.pow_def, Function.comp_def] at this; exact this)
  have h2 := ((h1.const_mul (2 * (π : ℂ) * Complex.I)).cexp).mul_const (W (ray ε y))
  convert h2 using 1 <;> first | rfl | (push_cast; simp only [mul_zero, Complex.exp_zero]; ring) | (push_cast; ring)

include hN hK in

theorem flowF_ray (ε : ℝ) (hε : ε = 1 ∨ ε = -1) {y : ℝ} (hy : 0 < y)
    (hd : DifferentiableAt ℝ (fun t => W (ray ε t)) y) :
    ArchCasimir.matrixFlowDeriv ArchDir.Fm W (ray ε y) =
      (2 * (π : ℂ) * Complex.I * (ε : ℂ) * (y : ℂ) - Complex.I) * W (ray ε y) := by
  have hε0 : ε ≠ 0 := by rcases hε with rfl | rfl <;> norm_num
  have hq0 : ∀ t : ℝ, 0 < 1 + t ^ 2 := fun t => by positivity
  have hq : ∀ t : ℝ, 0 < Real.sqrt (1 + t ^ 2) := fun t => Real.sqrt_pos.2 (hq0 t)
  have hy' : ∀ t : ℝ, 0 < y / (1 + t ^ 2) := fun t => div_pos hy (hq0 t)
  have hs : 0 < Real.sqrt y := Real.sqrt_pos.2 hy

  have hdec : ∀ t : ℝ, ray ε y * (archFlowMatrix ArchDir.Fm t : Matrix (Fin 2) (Fin 2) ℝ) =
      ArchR.unip (ε * y * (t / (1 + t ^ 2))) *
        (ray ε (y / (1 + t ^ 2)) * ((kRot t : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ)) := by
    intro t
    have hsq : Real.sqrt (y / (1 + t ^ 2)) = Real.sqrt y / Real.sqrt (1 + t ^ 2) := Real.sqrt_div hy.le _
    have h1 : Real.sqrt y * Real.sqrt y = y := Real.mul_self_sqrt hy.le
    have h2 : Real.sqrt (1 + t ^ 2) * Real.sqrt (1 + t ^ 2) = 1 + t ^ 2 := Real.mul_self_sqrt (hq0 t).le
    have hsy : Real.sqrt y ≠ 0 := hs.ne'
    have hst : Real.sqrt (1 + t ^ 2) ≠ 0 := (hq t).ne'
    have h1t : (1 + t ^ 2) ≠ 0 := (hq0 t).ne'
    rw [show (archFlowMatrix ArchDir.Fm t : Matrix (Fin 2) (Fin 2) ℝ) = !![1, 0; t, 1] from rfl, ray, ray, ArchR.unip,
      kRot_coe, hsq]
    ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply] <;> field_simp <;>
      (simp only [Real.sq_sqrt hy.le, Real.sq_sqrt (hq0 t).le]; ring)

  set F : ℝ → ℂ := fun t =>
    Complex.exp (2 * (π : ℂ) * Complex.I * ((ε * y * (t / (1 + t ^ 2)) : ℝ) : ℂ)) *
      ((((Real.sqrt (1 + t ^ 2))⁻¹ : ℝ) : ℂ) + (((-t * (Real.sqrt (1 + t ^ 2))⁻¹) : ℝ) : ℂ) * Complex.I) *
        W (ray ε (y / (1 + t ^ 2))) with hF
  have hfun : (fun t : ℝ => W (ray ε y * (archFlowMatrix ArchDir.Fm t : Matrix (Fin 2) (Fin 2) ℝ))) = F := by
    funext t
    rw [hdec t, hN]
    have hw := hK ⟨kRot t, kRot_mem t⟩ (rayGL ε (y / (1 + t ^ 2)) hε0 (hy' t))
    rw [Units.val_mul] at hw
    change W (ray ε (y / (1 + t ^ 2)) * ((kRot t : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ)) = _ * W (ray ε (y / (1 + t ^ 2))) at hw
    rw [hw, archWeightCharℝ_one_coe, hF, ArchR.psi]
    have hfr : firstRowℂ (kRot t) =
        ((((Real.sqrt (1 + t ^ 2))⁻¹ : ℝ) : ℂ) + (((-t * (Real.sqrt (1 + t ^ 2))⁻¹) : ℝ) : ℂ) * Complex.I) := by
      apply Complex.ext <;> simp [firstRowℂ, kRot_coe]
    rw [hfr]
    simp only
    ring
  rw [ArchCasimir.matrixFlowDeriv, hfun]
  apply HasDerivAt.deriv

  have hA0 : HasDerivAt (fun t : ℝ => t / (1 + t ^ 2)) 1 0 := by
    have h1 : HasDerivAt (fun t : ℝ => 1 + t ^ 2) (0 : ℝ) 0 := by
      simpa using ((hasDerivAt_pow 2 (0 : ℝ)).const_add 1)
    have := (hasDerivAt_id (0 : ℝ)).div h1 (by norm_num)
    first | simpa [Pi.div_def, Pi.mul_def, Pi.add_def, Pi.neg_def, Pi.inv_def, Pi.sub_def, Pi.pow_def, Function.comp_def] using this | (simp [Pi.div_def, Pi.mul_def, Pi.add_def, Pi.neg_def, Pi.inv_def, Pi.sub_def, Pi.pow_def, Function.comp_def] at this; exact this)
  have hA : HasDerivAt (fun t : ℝ => Complex.exp (2 * (π : ℂ) * Complex.I * ((ε * y * (t / (1 + t ^ 2)) : ℝ) : ℂ)))
      (2 * (π : ℂ) * Complex.I * ((ε * y : ℝ) : ℂ)) 0 := by
    have h1 : HasDerivAt (fun t : ℝ => ((ε * y * (t / (1 + t ^ 2)) : ℝ) : ℂ)) ((ε * y * 1 : ℝ) : ℂ) 0 :=
      (hA0.const_mul (ε * y)).ofReal_comp
    have := (h1.const_mul (2 * (π : ℂ) * Complex.I)).cexp
    first | simpa [Pi.div_def, Pi.mul_def, Pi.add_def, Pi.neg_def, Pi.inv_def, Pi.sub_def, Pi.pow_def, Function.comp_def] using this | (simp [Pi.div_def, Pi.mul_def, Pi.add_def, Pi.neg_def, Pi.inv_def, Pi.sub_def, Pi.pow_def, Function.comp_def] at this; exact this)
  have hB : HasDerivAt (fun t : ℝ =>
      ((((Real.sqrt (1 + t ^ 2))⁻¹ : ℝ) : ℂ) + (((-t * (Real.sqrt (1 + t ^ 2))⁻¹) : ℝ) : ℂ) * Complex.I))
      (-Complex.I) 0 := by
    have h1 : HasDerivAt (fun t : ℝ => 1 + t ^ 2) (0 : ℝ) 0 := by
      simpa using ((hasDerivAt_pow 2 (0 : ℝ)).const_add 1)
    have h2 : HasDerivAt (fun t : ℝ => Real.sqrt (1 + t ^ 2)) 0 0 := by
      have := h1.sqrt (by norm_num)
      first | simpa [Pi.div_def, Pi.mul_def, Pi.add_def, Pi.neg_def, Pi.inv_def, Pi.sub_def, Pi.pow_def, Function.comp_def] using this | (simp [Pi.div_def, Pi.mul_def, Pi.add_def, Pi.neg_def, Pi.inv_def, Pi.sub_def, Pi.pow_def, Function.comp_def] at this; exact this)
    have h3 : HasDerivAt (fun t : ℝ => (Real.sqrt (1 + t ^ 2))⁻¹) 0 0 := by
      have := h2.inv (by norm_num)
      first | simpa [Pi.div_def, Pi.mul_def, Pi.add_def, Pi.neg_def, Pi.inv_def, Pi.sub_def, Pi.pow_def, Function.comp_def] using this | (simp [Pi.div_def, Pi.mul_def, Pi.add_def, Pi.neg_def, Pi.inv_def, Pi.sub_def, Pi.pow_def, Function.comp_def] at this; exact this)
    have h4 : HasDerivAt (fun t : ℝ => -t * (Real.sqrt (1 + t ^ 2))⁻¹) (-1) 0 := by
      have := ((hasDerivAt_id (0 : ℝ)).neg.mul h3)
      first | simpa [Pi.div_def, Pi.mul_def, Pi.add_def, Pi.neg_def, Pi.inv_def, Pi.sub_def, Pi.pow_def, Function.comp_def] using this | (simp [Pi.div_def, Pi.mul_def, Pi.add_def, Pi.neg_def, Pi.inv_def, Pi.sub_def, Pi.pow_def, Function.comp_def] at this; exact this)
    have := h3.ofReal_comp.add (h4.ofReal_comp.mul_const Complex.I)
    first | simpa [Pi.div_def, Pi.mul_def, Pi.add_def, Pi.neg_def, Pi.inv_def, Pi.sub_def, Pi.pow_def, Function.comp_def] using this | (simp [Pi.div_def, Pi.mul_def, Pi.add_def, Pi.neg_def, Pi.inv_def, Pi.sub_def, Pi.pow_def, Function.comp_def] at this; exact this)
  have hC : HasDerivAt (fun t : ℝ => W (ray ε (y / (1 + t ^ 2)))) 0 0 := by
    have h1 : HasDerivAt (fun t : ℝ => 1 + t ^ 2) (0 : ℝ) 0 := by
      simpa using ((hasDerivAt_pow 2 (0 : ℝ)).const_add 1)
    have h2 : HasDerivAt (fun t : ℝ => y / (1 + t ^ 2)) 0 0 := by
      have := (hasDerivAt_const (0 : ℝ) y).div h1 (by norm_num)
      first | simpa [Pi.div_def, Pi.mul_def, Pi.add_def, Pi.neg_def, Pi.inv_def, Pi.sub_def, Pi.pow_def, Function.comp_def] using this | (simp [Pi.div_def, Pi.mul_def, Pi.add_def, Pi.neg_def, Pi.inv_def, Pi.sub_def, Pi.pow_def, Function.comp_def] at this; exact this)
    have hpt : y / (1 + (0 : ℝ) ^ 2) = y := by norm_num
    have hg : HasDerivAt (fun t => W (ray ε t)) (deriv (fun t => W (ray ε t)) y) (y / (1 + (0 : ℝ) ^ 2)) := by
      rw [hpt]; exact hd.hasDerivAt
    have := hg.scomp 0 h2
    first | simpa [Pi.div_def, Pi.mul_def, Pi.add_def, Pi.neg_def, Pi.inv_def, Pi.sub_def, Pi.pow_def, Function.comp_def] using this | (simp [Pi.div_def, Pi.mul_def, Pi.add_def, Pi.neg_def, Pi.inv_def, Pi.sub_def, Pi.pow_def, Function.comp_def] at this; exact this)
  have := (hA.mul hB).mul hC
  convert this using 1 <;> try rfl
  simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, zero_div, add_zero, mul_zero, neg_zero,
    zero_mul, Real.sqrt_one, inv_one, Complex.ofReal_one, Complex.ofReal_zero, Complex.exp_zero, mul_one, one_mul,
    Pi.mul_apply, div_one]
  push_cast
  ring

include hN hK in

theorem LW_ray (ε : ℝ) (hε : ε = 1 ∨ ε = -1) {y : ℝ} (hy : 0 < y)
    (hd : DifferentiableAt ℝ (fun t => W (ray ε t)) y) :
    LW W (ray ε y) =
      2 * (y : ℂ) * deriv (fun t => W (ray ε t)) y + (4 * (π : ℂ) * (ε : ℂ) * (y : ℂ) - 1) * W (ray ε y) := by
  rw [LW, flowH_ray W ε hy hd, flowE_ray W hN ε hy, flowF_ray W hN hK ε hε hy hd]
  ring_nf
  rw [Complex.I_sq]
  ring

end TorusValues

section Frechet

def Xmat : ArchDir → Matrix (Fin 2) (Fin 2) ℝ
  | .H => !![1, 0; 0, -1]
  | .E => !![0, 1; 0, 0]
  | .Fm => !![0, 0; 1, 0]

theorem isOpen_glSet : IsOpen ArchR.glSet := by
  have hc : Continuous fun M : Fin 2 → Fin 2 → ℝ => (Matrix.of M).det :=
    (continuous_id : Continuous fun M : Matrix (Fin 2) (Fin 2) ℝ => M).matrix_det
  exact isOpen_ne_fun hc continuous_const

theorem hasDerivAt_archFlowMatrix (d : ArchDir) :
    HasDerivAt (fun t : ℝ => Matrix.of.symm ((archFlowMatrix d t : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ))
      (Matrix.of.symm (Xmat d)) 0 := by
  have he : HasDerivAt (fun t : ℝ => Real.exp t) 1 0 := by simpa using Real.hasDerivAt_exp 0
  have he' : HasDerivAt (fun t : ℝ => Real.exp (-t)) (-1) 0 := by
    simpa using ((hasDerivAt_neg (0 : ℝ)).exp)
  have hid : HasDerivAt (fun t : ℝ => t) 1 0 := hasDerivAt_id 0
  rw [hasDerivAt_pi]; intro i; rw [hasDerivAt_pi]; intro j
  cases d <;> fin_cases i <;> fin_cases j <;>
    simp [archFlowMatrix, splitTorusGL2_coe, lowerUnipotentGL2_coe, unipotentGL2, Xmat, hasDerivAt_const, he, he', hid]

def conjCLM (A B : Matrix (Fin 2) (Fin 2) ℝ) : (Fin 2 → Fin 2 → ℝ) →L[ℝ] (Fin 2 → Fin 2 → ℝ) :=
  LinearMap.toContinuousLinearMap
    { toFun := fun e => Matrix.of.symm (A * Matrix.of e * B)
      map_add' := fun e f => by
        change A * (Matrix.of e + Matrix.of f) * B = A * Matrix.of e * B + A * Matrix.of f * B
        rw [Matrix.mul_add, Matrix.add_mul]
      map_smul' := fun c e => by
        change A * (c • Matrix.of e) * B = c • (A * Matrix.of e * B)
        rw [Matrix.mul_smul, Matrix.smul_mul] }

theorem conjCLM_apply (A B : Matrix (Fin 2) (Fin 2) ℝ) (e : Fin 2 → Fin 2 → ℝ) :
    conjCLM A B e = Matrix.of.symm (A * Matrix.of e * B) := rfl

theorem hasDerivAt_W_conj_flow (W : Matrix (Fin 2) (Fin 2) ℝ → ℂ)
    (hsm : ContDiffOn ℝ (⊤ : ℕ∞) (ArchR.asPi W) ArchR.glSet) (d : ArchDir)
    (A B : Matrix (Fin 2) (Fin 2) ℝ) (hAB : (A * B).det ≠ 0) :
    HasDerivAt (fun t : ℝ => W (A * (archFlowMatrix d t : Matrix (Fin 2) (Fin 2) ℝ) * B))
      (fderiv ℝ (ArchR.asPi W) (Matrix.of.symm (A * B)) (Matrix.of.symm (A * Xmat d * B))) 0 := by
  have hmem : ArchR.glSet ∈ nhds (Matrix.of.symm (A * B)) := isOpen_glSet.mem_nhds hAB
  have hΦ : HasFDerivAt (ArchR.asPi W) (fderiv ℝ (ArchR.asPi W) (Matrix.of.symm (A * B))) (Matrix.of.symm (A * B)) :=
    ((hsm.contDiffAt hmem).differentiableAt (by simp)).hasFDerivAt
  have hγ : HasDerivAt (fun t : ℝ => Matrix.of.symm (A * (archFlowMatrix d t : Matrix (Fin 2) (Fin 2) ℝ) * B))
      (Matrix.of.symm (A * Xmat d * B)) 0 := by
    have := (conjCLM A B).hasFDerivAt.comp_hasDerivAt (0 : ℝ) (hasDerivAt_archFlowMatrix d)
    exact this
  have h0 : Matrix.of.symm (A * (archFlowMatrix d 0 : Matrix (Fin 2) (Fin 2) ℝ) * B) = Matrix.of.symm (A * B) := by
    rw [archFlowMatrix_zero, Units.val_one, Matrix.mul_one]
  have hΦ' : HasFDerivAt (ArchR.asPi W) (fderiv ℝ (ArchR.asPi W) (Matrix.of.symm (A * B)))
      (Matrix.of.symm (A * (archFlowMatrix d 0 : Matrix (Fin 2) (Fin 2) ℝ) * B)) := by
    rw [h0]; exact hΦ
  exact hΦ'.comp_hasDerivAt (0 : ℝ) hγ

theorem matrixFlowDeriv_eq_fderiv (W : Matrix (Fin 2) (Fin 2) ℝ → ℂ)
    (hsm : ContDiffOn ℝ (⊤ : ℕ∞) (ArchR.asPi W) ArchR.glSet) (d : ArchDir)
    (x : Matrix (Fin 2) (Fin 2) ℝ) (hx : x.det ≠ 0) :
    ArchCasimir.matrixFlowDeriv d W x = fderiv ℝ (ArchR.asPi W) (Matrix.of.symm x) (Matrix.of.symm (x * Xmat d)) := by
  have := hasDerivAt_W_conj_flow W hsm d x 1 (by rwa [Matrix.mul_one])
  simp only [Matrix.mul_one] at this
  exact this.deriv

end Frechet

section Laws

variable (W : Matrix (Fin 2) (Fin 2) ℝ → ℂ)

theorem matrixFlowDeriv_mul_left (d : ArchDir) (g x : Matrix (Fin 2) (Fin 2) ℝ) :
    ArchCasimir.matrixFlowDeriv d W (g * x) = ArchCasimir.matrixFlowDeriv d (fun z => W (g * z)) x := by
  simp only [ArchCasimir.matrixFlowDeriv, Matrix.mul_assoc]

theorem LW_unip (hN : ∀ (t : ℝ) (g : Matrix (Fin 2) (Fin 2) ℝ), W (ArchR.unip t * g) = ArchR.psi t * W g)
    (t : ℝ) (x : Matrix (Fin 2) (Fin 2) ℝ) : LW W (ArchR.unip t * x) = ArchR.psi t * LW W x := by
  have h : ∀ d : ArchDir, ArchCasimir.matrixFlowDeriv d W (ArchR.unip t * x) =
      ArchR.psi t * ArchCasimir.matrixFlowDeriv d W x := by
    intro d
    simp only [ArchCasimir.matrixFlowDeriv, Matrix.mul_assoc, hN]
    rw [deriv_const_mul_field']
  simp only [LW, h]
  ring

theorem LW_smul (c : ℝ → ℂ) (hZ : ∀ (t : ℝ) (g : Matrix (Fin 2) (Fin 2) ℝ), t ≠ 0 → W (t • g) = c t * W g)
    (t : ℝ) (ht : t ≠ 0) (x : Matrix (Fin 2) (Fin 2) ℝ) : LW W (t • x) = c t * LW W x := by
  have h : ∀ d : ArchDir, ArchCasimir.matrixFlowDeriv d W (t • x) =
      c t * ArchCasimir.matrixFlowDeriv d W x := by
    intro d
    simp only [ArchCasimir.matrixFlowDeriv, Matrix.smul_mul, hZ t _ ht]
    rw [deriv_const_mul_field']
  simp only [LW, h]
  ring

theorem LW_weight (hsm : ContDiffOn ℝ (⊤ : ℕ∞) (ArchR.asPi W) ArchR.glSet)
    (hK : ∀ (r : rowIsometrySubgroup₀ ℝ) (x : GL (Fin 2) ℝ),
      W ((x * (r : GL (Fin 2) ℝ) : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) =
        (archWeightCharℝ 1 r : ℂ) * W (x : Matrix (Fin 2) (Fin 2) ℝ))
    (r : rowIsometrySubgroup₀ ℝ) (x : GL (Fin 2) ℝ) :
    LW W ((x * (r : GL (Fin 2) ℝ) : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) =
      (archWeightCharℝ (-1) r : ℂ) * LW W (x : Matrix (Fin 2) (Fin 2) ℝ) := by
  obtain ⟨h10, h11, hab⟩ := entries_of_mem_rowIsometrySubgroup₀ r.2
  set a : ℝ := ((r : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) 0 0 with ha
  set b : ℝ := ((r : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) 0 1 with hb
  set R : Matrix (Fin 2) (Fin 2) ℝ := ((r : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) with hR
  set R' : Matrix (Fin 2) (Fin 2) ℝ := (((r : GL (Fin 2) ℝ)⁻¹ : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) with hR'
  have hRm : R = !![a, b; -b, a] := by
    ext i j; fin_cases i <;> fin_cases j
    · rfl
    · rfl
    · exact h10
    · exact h11
  have hRR' : R * R' = 1 := by
    rw [hR, hR', ← Units.val_mul, mul_inv_cancel, Units.val_one]
  have hR'm : R' = !![a, -b; b, a] := by
    have h1 : R * !![a, -b; b, a] = 1 := by
      rw [hRm]
      ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply] <;> nlinarith [hab]
    have hRu : IsUnit R.det := by
      rw [hR, ← Matrix.GeneralLinearGroup.val_det_apply]; exact Units.isUnit _
    calc R' = R⁻¹ * (R * R') := by rw [← Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hRu, Matrix.one_mul]
      _ = R⁻¹ * (R * !![a, -b; b, a]) := by rw [hRR', h1]
      _ = !![a, -b; b, a] := by rw [← Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hRu, Matrix.one_mul]
  set X : Matrix (Fin 2) (Fin 2) ℝ := ((x : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) with hX
  have hXdet : X.det ≠ 0 := by
    rw [hX, ← Matrix.GeneralLinearGroup.val_det_apply]; exact (Units.isUnit _).ne_zero
  set φ := fderiv ℝ (ArchR.asPi W) (Matrix.of.symm X) with hφ

  have hflow : ∀ d : ArchDir, ArchCasimir.matrixFlowDeriv d W (X * R) =
      (archWeightCharℝ 1 r : ℂ) * φ (Matrix.of.symm (X * R * Xmat d * R')) := by
    intro d
    have hfun : (fun t : ℝ => W (X * R * (archFlowMatrix d t : Matrix (Fin 2) (Fin 2) ℝ))) =
        fun t => (archWeightCharℝ 1 r : ℂ) * W (X * R * (archFlowMatrix d t : Matrix (Fin 2) (Fin 2) ℝ) * R') := by
      funext t
      have := hK r (x * ((r : GL (Fin 2) ℝ) * archFlowMatrix d t * (r : GL (Fin 2) ℝ)⁻¹))
      rw [show x * ((r : GL (Fin 2) ℝ) * archFlowMatrix d t * (r : GL (Fin 2) ℝ)⁻¹) * (r : GL (Fin 2) ℝ) =
          x * (r : GL (Fin 2) ℝ) * archFlowMatrix d t by group] at this
      simp only [Units.val_mul] at this
      rw [this]
      simp only [hX, hR, hR', Matrix.mul_assoc]
    rw [ArchCasimir.matrixFlowDeriv, hfun, deriv_const_mul_field']
    dsimp only
    congr 1
    have hAB : (X * R * R').det ≠ 0 := by rwa [Matrix.mul_assoc, hRR', Matrix.mul_one]
    have := (hasDerivAt_W_conj_flow W hsm d (X * R) R' hAB).deriv
    rw [this]
    simp only [Matrix.mul_assoc, hRR', Matrix.mul_one, hφ]
  have hflow0 : ∀ d : ArchDir, ArchCasimir.matrixFlowDeriv d W X = φ (Matrix.of.symm (X * Xmat d)) := fun d =>
    matrixFlowDeriv_eq_fderiv W hsm d X hXdet

  have hH : Matrix.of.symm (X * R * Xmat ArchDir.H * R') =
      (a ^ 2 - b ^ 2) • Matrix.of.symm (X * Xmat ArchDir.H) -
        (2 * a * b) • (Matrix.of.symm (X * Xmat ArchDir.E) + Matrix.of.symm (X * Xmat ArchDir.Fm)) := by
    rw [hRm, hR'm]
    ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two, Xmat] <;> ring
  have hE : Matrix.of.symm (X * R * Xmat ArchDir.E * R') =
      (a * b) • Matrix.of.symm (X * Xmat ArchDir.H) + (a ^ 2) • Matrix.of.symm (X * Xmat ArchDir.E) -
        (b ^ 2) • Matrix.of.symm (X * Xmat ArchDir.Fm) := by
    rw [hRm, hR'm]
    ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two, Xmat] <;> ring
  have hF : Matrix.of.symm (X * R * Xmat ArchDir.Fm * R') =
      (a * b) • Matrix.of.symm (X * Xmat ArchDir.H) - (b ^ 2) • Matrix.of.symm (X * Xmat ArchDir.E) +
        (a ^ 2) • Matrix.of.symm (X * Xmat ArchDir.Fm) := by
    rw [hRm, hR'm]
    ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two, Xmat] <;> ring

  have hab' : ((a : ℂ)) ^ 2 + (b : ℂ) ^ 2 = 1 := by exact_mod_cast hab
  have h1 : (firstRowℂ (r : GL (Fin 2) ℝ)) = (a : ℂ) + (b : ℂ) * Complex.I := by
    apply Complex.ext <;> simp [firstRowℂ, ha, hb, hR]
  have hχ1 : ((archWeightCharℝ 1 r : ℂˣ) : ℂ) = (a : ℂ) + (b : ℂ) * Complex.I := by
    rw [archWeightCharℝ_one_coe, h1]
  have hχm : ((archWeightCharℝ (-1) r : ℂˣ) : ℂ) = (a : ℂ) - (b : ℂ) * Complex.I := by
    rw [archWeightCharℝ_neg_one_coe, h1]
    apply inv_eq_of_mul_eq_one_right
    linear_combination hab' - ((b : ℂ)) ^ 2 * Complex.I_sq

  change LW W (X * R) = _ * LW W X
  simp only [LW, hflow, hflow0, hH, hE, hF, map_add, map_sub, map_smul, hχ1, hχm, Complex.real_smul]
  push_cast
  set H' := φ (Matrix.of.symm (X * Xmat ArchDir.H))
  set E' := φ (Matrix.of.symm (X * Xmat ArchDir.E))
  set F' := φ (Matrix.of.symm (X * Xmat ArchDir.Fm))
  linear_combination ((a : ℂ) - (b : ℂ) * Complex.I) * (H' - Complex.I * E' - Complex.I * F') * hab'
    - (2 * (a : ℂ) * (b : ℂ) ^ 2 * (H' - Complex.I * E' - Complex.I * F')
        + 2 * (a : ℂ) * (b : ℂ) * ((a : ℂ) + (b : ℂ) * Complex.I) * (E' + F')) * Complex.I_sq

end Laws

theorem contDiffOn_ray (D : ArchDatumR P) (ε : ℝ) (hε : ε ≠ 0) :
    ContDiffOn ℝ (⊤ : ℕ∞) (fun t : ℝ => D.W (ray ε t)) (Set.Ioi 0) := by
  set φ : ℝ → (Fin 2 → Fin 2 → ℝ) := fun t => Matrix.of.symm (ray ε t) with hφ
  have hsqrt : ContDiffOn ℝ (⊤ : ℕ∞) (fun t : ℝ => Real.sqrt t) (Set.Ioi 0) := fun t ht =>
    (Real.contDiffAt_sqrt (ne_of_gt ht)).contDiffWithinAt
  have hφd : ContDiffOn ℝ (⊤ : ℕ∞) φ (Set.Ioi 0) := by
    rw [contDiffOn_pi]
    intro i
    rw [contDiffOn_pi]
    intro j
    fin_cases i <;> fin_cases j
    · simpa [hφ, ray] using hsqrt.const_smul ε
    · simpa [hφ, ray] using contDiffOn_const
    · simpa [hφ, ray] using contDiffOn_const
    · simp only [hφ, ray]
      refine (hsqrt.inv fun t ht => (Real.sqrt_pos.2 ht).ne').congr fun t ht => ?_
      simp
  have hmaps : Set.MapsTo φ (Set.Ioi 0) ArchR.glSet := by
    intro t ht
    show (Matrix.of (Matrix.of.symm (ray ε t))).det ≠ 0
    rw [Equiv.apply_symm_apply, ray_det ε ht]
    exact hε
  have := D.smooth.comp hφd hmaps
  exact this

theorem coeff_eq_zero (u₁ u₂ : ℂ) (h2 : ∀ n : ℕ, u₁ - u₂ ≠ -(2 * (n : ℂ))) (p q : ℂ) (Φ : ℂ → ℂ)
    (hΦ : Differentiable ℂ Φ) (σ₀ : ℝ)
    (h : ∀ s : ℂ, σ₀ < s.re →
      p * (Gammaℝ (s + u₁ + 1) * Gammaℝ (s + u₂)) + q * (Gammaℝ (s + u₁) * Gammaℝ (s + u₂ + 1)) =
        Gammaℝ (s + u₁) * Gammaℝ (s + u₂ + 1) * Φ s) :
    p = 0 := by

  set I₀ : ℂ → ℂ := fun s => (Gammaℝ (s + u₁))⁻¹ * (Gammaℝ (s + u₂ + 1))⁻¹ with hI₀
  set I₁ : ℂ → ℂ := fun s => (Gammaℝ (s + u₁ + 1))⁻¹ * (Gammaℝ (s + u₂))⁻¹ with hI₁
  have hdI : ∀ c : ℂ, Differentiable ℂ fun s : ℂ => (Gammaℝ (s + c))⁻¹ := fun c =>
    differentiable_Gammaℝ_inv.comp (differentiable_id.add_const c)
  have hI₀d : Differentiable ℂ I₀ := by
    have h2' : Differentiable ℂ fun s : ℂ => (Gammaℝ (s + u₂ + 1))⁻¹ := by
      have := hdI (u₂ + 1); simpa [add_assoc] using this
    exact (hdI u₁).mul h2'
  have hI₁d : Differentiable ℂ I₁ := by
    have h1' : Differentiable ℂ fun s : ℂ => (Gammaℝ (s + u₁ + 1))⁻¹ := by
      have := hdI (u₁ + 1); simpa [add_assoc] using this
    exact h1'.mul (hdI u₂)
  set σ₁ : ℝ := max σ₀ (max (-u₁.re) (-u₂.re)) with hσ₁

  have hent : ∀ s : ℂ, σ₁ < s.re → p * I₀ s + q * I₁ s = I₁ s * Φ s := by
    intro s hs
    have hs0 : σ₀ < s.re := lt_of_le_of_lt (le_max_left _ _) hs
    have hs1 : -u₁.re < s.re := lt_of_le_of_lt ((le_max_left _ _).trans (le_max_right _ _)) hs
    have hs2 : -u₂.re < s.re := lt_of_le_of_lt ((le_max_right _ _).trans (le_max_right _ _)) hs
    have hne1 : Gammaℝ (s + u₁) ≠ 0 := Gammaℝ_ne_zero_of_re_pos (by rw [add_re]; linarith)
    have hne2 : Gammaℝ (s + u₂) ≠ 0 := Gammaℝ_ne_zero_of_re_pos (by rw [add_re]; linarith)
    have hne3 : Gammaℝ (s + u₁ + 1) ≠ 0 := Gammaℝ_ne_zero_of_re_pos (by rw [add_re, add_re, one_re]; linarith)
    have hne4 : Gammaℝ (s + u₂ + 1) ≠ 0 := Gammaℝ_ne_zero_of_re_pos (by rw [add_re, add_re, one_re]; linarith)
    have := h s hs0
    simp only [hI₀, hI₁]
    field_simp
    linear_combination this
  have heq : (fun s => p * I₀ s + q * I₁ s) = fun s => I₁ s * Φ s := by
    have hA : AnalyticOnNhd ℂ (fun s => p * I₀ s + q * I₁ s) Set.univ :=
      Complex.analyticOnNhd_univ_iff_differentiable.mpr
        (((differentiable_const p).mul hI₀d).add ((differentiable_const q).mul hI₁d))
    have hB : AnalyticOnNhd ℂ (fun s => I₁ s * Φ s) Set.univ :=
      Complex.analyticOnNhd_univ_iff_differentiable.mpr (hI₁d.mul hΦ)
    have hopen : IsOpen {s : ℂ | σ₁ < s.re} := isOpen_lt continuous_const Complex.continuous_re
    have hz₀ : ((σ₁ + 1 : ℝ) : ℂ) ∈ {s : ℂ | σ₁ < s.re} := by
      show σ₁ < ((σ₁ + 1 : ℝ) : ℂ).re
      rw [ofReal_re]; linarith
    have hev : (fun s => p * I₀ s + q * I₁ s) =ᶠ[nhds ((σ₁ + 1 : ℝ) : ℂ)] fun s => I₁ s * Φ s :=
      Filter.eventuallyEq_of_mem (hopen.mem_nhds hz₀) fun s hs => hent s hs
    have := AnalyticOnNhd.eqOn_of_preconnected_of_eventuallyEq hA hB isPreconnected_univ (Set.mem_univ _) hev
    funext s
    exact this (Set.mem_univ s)

  have hval := congrFun heq (-u₂)
  simp only [hI₀, hI₁] at hval
  have h0 : Gammaℝ (-u₂ + u₂) = 0 := by
    rw [neg_add_cancel, Gammaℝ_eq_zero_iff]; exact ⟨0, by simp⟩
  rw [h0, inv_zero, mul_zero, mul_zero, zero_mul, add_zero] at hval
  have h1 : Gammaℝ (-u₂ + u₂ + 1) ≠ 0 := by
    rw [neg_add_cancel, zero_add]; exact Gammaℝ_ne_zero_of_re_pos (by simp)
  have h3 : Gammaℝ (-u₂ + u₁) ≠ 0 := by
    rw [Ne, Gammaℝ_eq_zero_iff]
    rintro ⟨n, hn⟩
    apply h2 n
    linear_combination hn
  rcases mul_eq_zero.mp hval with hk | hk
  · exact hk
  · exfalso
    rcases mul_eq_zero.mp hk with hk | hk
    · exact h3 (inv_eq_zero.mp hk)
    · exact h1 (inv_eq_zero.mp hk)

theorem not_even_of_abs_re_lt_one {u₁ u₂ : ℂ} (hu : u₁ ≠ u₂) (htype : |(u₁ - u₂).re| < 1) (n : ℕ) :
    u₁ - u₂ ≠ -(2 * (n : ℂ)) := by
  intro h
  have hre : (u₁ - u₂).re = -(2 * (n : ℝ)) := by
    rw [h]; simp
  rw [hre, abs_neg, abs_of_nonneg (by positivity)] at htype
  have hn : n = 0 := by
    by_contra hn
    have : (1 : ℝ) ≤ n := Nat.one_le_cast.mpr (Nat.pos_of_ne_zero hn)
    linarith
  subst hn
  apply hu
  have : u₁ - u₂ = 0 := by rw [h]; simp
  exact sub_eq_zero.mp this

theorem ode_transfer {f g : ℝ → ℂ} (hfg : Set.EqOn f g (Set.Ioi 0)) (c : ℝ → ℂ)
    (h : DifferentiableOn ℝ g (Set.Ioi 0) ∧ DifferentiableOn ℝ (deriv g) (Set.Ioi 0) ∧
      ∀ y : ℝ, 0 < y → (y : ℂ) ^ 2 * deriv (deriv g) y + c y * g y = 0) :
    DifferentiableOn ℝ f (Set.Ioi 0) ∧ DifferentiableOn ℝ (deriv f) (Set.Ioi 0) ∧
      ∀ y : ℝ, 0 < y → (y : ℂ) ^ 2 * deriv (deriv f) y + c y * f y = 0 := by
  obtain ⟨h1, h2, h3⟩ := h
  have hev : ∀ y ∈ Set.Ioi (0 : ℝ), f =ᶠ[nhds y] g := fun y hy =>
    Filter.eventuallyEq_of_mem (isOpen_Ioi.mem_nhds hy) hfg
  have hd : Set.EqOn (deriv f) (deriv g) (Set.Ioi 0) := fun y hy => (hev y hy).deriv_eq
  have hev' : ∀ y ∈ Set.Ioi (0 : ℝ), deriv f =ᶠ[nhds y] deriv g := fun y hy =>
    Filter.eventuallyEq_of_mem (isOpen_Ioi.mem_nhds hy) hd
  refine ⟨h1.congr hfg, h2.congr hd, fun y hy => ?_⟩
  rw [(hev' y hy).deriv_eq, hfg hy]
  exact h3 y hy

theorem ray_package (D : ArchDatumR P) (ν : ℂ) (hν : ν ^ 2 = 1 / 4 - P.laplaceEigenvalue)
    (hDW : ∀ (r : rowIsometrySubgroup₀ ℝ) (x : GL (Fin 2) ℝ),
      D.W ((x * (r : GL (Fin 2) ℝ) : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) =
        (archWeightCharℝ 1 r : ℂ) * D.W (x : Matrix (Fin 2) (Fin 2) ℝ))
    (hDE : ArchCasimir.IsCasimirEigen D) (ε : ℝ) (hε : ε = 1 ∨ ε = -1) :
    DifferentiableOn ℝ (fun t : ℝ => D.W (ray ε t)) (Set.Ioi 0) ∧
      DifferentiableOn ℝ (deriv (fun t : ℝ => D.W (ray ε t))) (Set.Ioi 0) ∧
      (∀ t : ℝ, 0 < t → (t : ℂ) ^ 2 * deriv (deriv (fun t : ℝ => D.W (ray ε t))) t
        + (1 / 4 - ν ^ 2 + 2 * (π : ℂ) * (ε : ℂ) * (t : ℂ) - 4 * (π : ℂ) ^ 2 * (t : ℂ) ^ 2) * D.W (ray ε t) = 0) ∧
      ∃ C N : ℝ, ∀ t : ℝ, 1 ≤ t → ‖D.W (ray ε t)‖ ≤ C * t ^ N := by
  have hpk := (LanglandsTunnell.Converse.ArchDatumR.laws_and_torus_ode_of_archWeightChar_of_isCasimirEigen
    P D 1 ν hν hDW hDE).2.2.2 ε hε
  obtain ⟨h1, h2, h3, C, N, hb⟩ := hpk
  have hsheet : ∀ t : ℝ, 0 < t →
      (((|(!![ε * Real.sqrt t, 0; 0, (Real.sqrt t)⁻¹] : Matrix (Fin 2) (Fin 2) ℝ).det| ^ (-(1 / 2 : ℝ)) : ℝ)) : ℂ) *
          D.W !![ε * Real.sqrt t, 0; 0, (Real.sqrt t)⁻¹] = D.W (ray ε t) := by
    intro t ht
    rw [show (!![ε * Real.sqrt t, 0; 0, (Real.sqrt t)⁻¹] : Matrix (Fin 2) (Fin 2) ℝ) = ray ε t from rfl, ray_det ε ht]
    have : |ε| = 1 := by rcases hε with rfl | rfl <;> norm_num
    rw [this, Real.one_rpow]
    push_cast
    ring
  have heqOn : Set.EqOn (fun t : ℝ => D.W (ray ε t))
      (fun t : ℝ => (((|(!![ε * Real.sqrt t, 0; 0, (Real.sqrt t)⁻¹] : Matrix (Fin 2) (Fin 2) ℝ).det| ^ (-(1 / 2 : ℝ)) : ℝ)) : ℂ) *
        D.W !![ε * Real.sqrt t, 0; 0, (Real.sqrt t)⁻¹]) (Set.Ioi 0) := fun t ht => (hsheet t ht).symm
  have hode := ode_transfer heqOn _ ⟨h1, h2, h3⟩
  refine ⟨hode.1, hode.2.1, fun t ht => ?_, C, N, fun t ht => ?_⟩
  · have := hode.2.2 t ht
    convert this using 3
    push_cast
    ring
  · have := hb t ht
    dsimp only at this
    rw [hsheet t (lt_of_lt_of_le one_pos ht)] at this
    exact this

theorem coeff_eq_zero' (u₁ u₂ : ℂ) (h2 : ∀ n : ℕ, u₂ - u₁ ≠ -(2 * (n : ℂ))) (p q : ℂ) (Φ : ℂ → ℂ)
    (hΦ : Differentiable ℂ Φ) (σ₀ : ℝ)
    (h : ∀ s : ℂ, σ₀ < s.re →
      p * (Gammaℝ (s + u₁ + 1) * Gammaℝ (s + u₂)) + q * (Gammaℝ (s + u₁) * Gammaℝ (s + u₂ + 1)) =
        Gammaℝ (s + u₁ + 1) * Gammaℝ (s + u₂) * Φ s) :
    q = 0 := by
  refine coeff_eq_zero u₂ u₁ h2 q p Φ hΦ σ₀ fun s hs => ?_
  have := h s hs
  linear_combination this

theorem mellin_pin (u₁ u₂ : ℂ) (a₁ a₂ : ZMod 2) (ha : a₁ ≠ a₂) (hu : u₁ ≠ u₂)
    (htype : |(u₁ - u₂).re| < 1)
    (D : ArchDatumR (RealArchParam.principal u₁ a₁ u₂ a₂))
    (f : ℝ → ℂ) (hf : DifferentiableOn ℝ f (Set.Ioi 0)) (hf' : DifferentiableOn ℝ (deriv f) (Set.Ioi 0))
    (hode : ∀ y : ℝ, 0 < y →
      (y : ℂ) ^ 2 * deriv (deriv f) y
          + (1 / 4 - ((u₁ - u₂) / 2) ^ 2 + 2 * (π : ℂ) * (y : ℂ) - 4 * (π : ℂ) ^ 2 * (y : ℂ) ^ 2) * f y = 0)
    (hgr : ∃ C N : ℝ, ∀ y : ℝ, 1 ≤ y → ‖f y‖ ≤ C * y ^ N)
    (hne : ∃ y : ℝ, 0 < y ∧ f y ≠ 0) (α β : ℂ)
    (hα : ∀ t : ℝ, 0 < t → D.W (ray 1 t) = α * f t)
    (hβ : ∀ t : ℝ, 0 < t → D.W (ray (-1) t) = β * lowP f t) :
    α = β * (u₁ - u₂) ∨ α = -(β * (u₁ - u₂)) := by
  set c : ℂ := u₁ - u₂ with hcdef
  have hc0 : c ≠ 0 := sub_ne_zero.mpr hu
  set e : ℂ := u₁ + u₂ with hedef

  set W₀ : ℂ → ℂ := fun z => if 0 ≤ z.re then ((Real.sqrt z.re : ℝ) : ℂ) ^ (u₁ + u₂ + 1) * f z.re
    else c⁻¹ * (((Real.sqrt (-z.re) : ℝ) : ℂ) ^ (u₁ + u₂ + 1) * lowP f (-z.re)) with hW₀
  have hW0p : ∀ t : ℝ, 0 < t → W₀ t = ((Real.sqrt t : ℝ) : ℂ) ^ (u₁ + u₂ + 1) * f t := by
    intro t ht; simp only [hW₀, ofReal_re, if_pos ht.le]
  have hW0m : ∀ t : ℝ, 0 < t → W₀ (-t) = c⁻¹ * (((Real.sqrt t : ℝ) : ℂ) ^ (u₁ + u₂ + 1) * lowP f t) := by
    intro t ht
    have : ¬ (0 : ℝ) ≤ (-(t : ℂ)).re := by rw [neg_re, ofReal_re]; linarith
    simp only [hW₀, if_neg this, neg_re, ofReal_re, neg_neg]
  have hWm : ∀ t : ℝ, 0 < t → c * W₀ (-t) = ((Real.sqrt t : ℝ) : ℂ) ^ (u₁ + u₂ + 1)
      * (2 * (t : ℂ) * deriv f t + (4 * (π : ℂ) * (t : ℂ) - 1) * f t) := by
    intro t ht
    rw [hW0m t ht, ← mul_assoc, mul_inv_cancel₀ hc0, one_mul]
    rfl
  obtain ⟨P', hP', ρ, hρ, hmel⟩ :=
    LanglandsTunnell.exists_mellin_whittakerProfile_eq_archFactor_of_whittaker_ode_weightOne u₁ u₂ a₁ a₂ ha hu W₀ f c
      (Or.inl rfl) hf hf' hode hgr hne hW0p hWm

  set Mp : ℂ → ℂ := fun s => ∫ t in Set.Ioi (0 : ℝ), (t : ℂ) ^ (s - 1) • (W₀ t / (t : ℂ)) with hMp
  set Mm : ℂ → ℂ := fun s => ∫ t in Set.Ioi (0 : ℝ), (t : ℂ) ^ (s - 1) • (W₀ (-t) / (t : ℂ)) with hMm
  have hdict : ∀ (b : ZMod 2) (s : ℂ), max (-u₁.re) (-u₂.re) < s.re →
      ρ * Mp s + (-1 : ℂ) ^ b.val * (ρ * Mm s) = (P'.twist 0 b).archFactor s := by
    intro b s hs
    have hI0 := (hmel 0 s hs).1
    have hI1 := (hmel 1 s hs).1
    rw [MellinConvergent] at hI0 hI1
    simp only [ZMod.val_zero, pow_zero, one_mul] at hI0
    simp only [ZMod.val_one, pow_one, neg_one_mul] at hI1
    have hIp : IntegrableOn (fun t : ℝ => (t : ℂ) ^ (s - 1) • (W₀ t / (t : ℂ))) (Set.Ioi 0) := by
      have h' : IntegrableOn (fun t : ℝ => (ρ⁻¹ * 2⁻¹ : ℂ) •
          ((t : ℂ) ^ (s - 1) • ((ρ * W₀ t + ρ * W₀ (-t)) / (t : ℂ))
            + (t : ℂ) ^ (s - 1) • ((ρ * W₀ t + -(ρ * W₀ (-t))) / (t : ℂ)))) (Set.Ioi 0) :=
        (hI0.add hI1).smul (ρ⁻¹ * 2⁻¹ : ℂ)
      refine h'.congr_fun (fun t _ => ?_) measurableSet_Ioi
      simp only [smul_eq_mul]
      field_simp
      ring
    have hIm : IntegrableOn (fun t : ℝ => (t : ℂ) ^ (s - 1) • (W₀ (-t) / (t : ℂ))) (Set.Ioi 0) := by
      have h' : IntegrableOn (fun t : ℝ => (ρ⁻¹ * 2⁻¹ : ℂ) •
          ((t : ℂ) ^ (s - 1) • ((ρ * W₀ t + ρ * W₀ (-t)) / (t : ℂ))
            - (t : ℂ) ^ (s - 1) • ((ρ * W₀ t + -(ρ * W₀ (-t))) / (t : ℂ)))) (Set.Ioi 0) :=
        (hI0.sub hI1).smul (ρ⁻¹ * 2⁻¹ : ℂ)
      refine h'.congr_fun (fun t _ => ?_) measurableSet_Ioi
      simp only [smul_eq_mul]
      field_simp
      ring
    have key : ∀ b' : ZMod 2, mellin (fun t : ℝ => (ρ * W₀ t + (-1 : ℂ) ^ b'.val * (ρ * W₀ (-t))) / (t : ℂ)) s =
        ρ * Mp s + (-1 : ℂ) ^ b'.val * (ρ * Mm s) := by
      intro b'
      rw [mellin, hMp, hMm]
      simp only
      rw [← integral_const_mul, ← integral_const_mul, ← integral_const_mul, ← integral_add]
      · refine setIntegral_congr_fun measurableSet_Ioi fun t ht => ?_
        simp only [smul_eq_mul]
        ring
      · exact hIp.integrable.const_mul ρ
      · exact (hIm.integrable.const_mul ρ).const_mul _
    rw [← key b]
    exact (hmel b s hs).2

  have hsqrt : ∀ t : ℝ, 0 < t →
      ((Real.sqrt t : ℝ) : ℂ) ^ (RealArchParam.principal u₁ a₁ u₂ a₂).centralExponent * ((Real.sqrt t : ℝ) : ℂ) =
        ((Real.sqrt t : ℝ) : ℂ) ^ (u₁ + u₂ + 1) := by
    intro t ht
    have hs0 : ((Real.sqrt t : ℝ) : ℂ) ≠ 0 := ofReal_ne_zero.2 (Real.sqrt_pos.2 ht).ne'
    rw [show (RealArchParam.principal u₁ a₁ u₂ a₂).centralExponent = u₁ + u₂ from rfl, cpow_add (u₁ + u₂) 1 hs0,
      cpow_one]
  have hGp : ∀ σ : ℂ, ∀ t : ℝ, 0 < t → G0 D σ t = α * ((t : ℂ) ^ (σ - 1) • (W₀ t / (t : ℂ))) := by
    intro σ t ht
    have ht0 : (t : ℂ) ≠ 0 := ofReal_ne_zero.2 ht.ne'
    have h1 := W_diagOne D 1 ht
    rw [one_mul] at h1
    rw [G0_pos ht, h1, hW0p t ht, smul_eq_mul, hsqrt t ht, hα t ht, cpow_sub _ _ ht0, cpow_one]
    field_simp
  have hGm : ∀ σ : ℂ, ∀ t : ℝ, 0 < t → G0 D σ (-t) = (β * c) * ((t : ℂ) ^ (σ - 1) • (W₀ (-t) / (t : ℂ))) := by
    intro σ t ht
    have ht0 : (t : ℂ) ≠ 0 := ofReal_ne_zero.2 ht.ne'
    have h1 := W_diagOne D (-1) ht
    rw [neg_one_mul] at h1
    rw [G0_neg ht, h1, hW0m t ht, smul_eq_mul, hsqrt t ht, hβ t ht, cpow_sub _ _ ht0, cpow_one]
    field_simp
  set σ₀ : ℝ := max D.zeta_abscissa (max (-u₁.re) (-u₂.re)) with hσ₀
  have hzeta : ∀ (b : ZMod 2) (s : ℂ), σ₀ < s.re →
      (2 * ρ) * (((RealArchParam.principal u₁ a₁ u₂ a₂).twist 0 b).archFactor s * D.zetaEntire 1 0 b s) =
        (α + (-1 : ℂ) ^ b.val * (β * c)) * (P'.twist 0 0).archFactor s +
          (α - (-1 : ℂ) ^ b.val * (β * c)) * (P'.twist 0 1).archFactor s := by
    intro b s hs
    have hsa : D.zeta_abscissa < s.re := lt_of_le_of_lt (le_max_left _ _) hs
    have hsm : max (-u₁.re) (-u₂.re) < s.re := lt_of_le_of_lt (le_max_right _ _) hs
    have hsa' : D.zeta_abscissa < s.re + (0 : ℂ).re := by simpa using hsa
    have hdet : (1 : Matrix (Fin 2) (Fin 2) ℝ).det ≠ 0 := by simp
    have hZ := D.zeta_eq 1 0 b s hdet hsa'
    rw [zeta_split D b s hsa] at hZ
    have h1 : ∫ t in Set.Ioi (0 : ℝ), G0 D s t = α * Mp s := by
      rw [hMp]; simp only; rw [← integral_const_mul]
      exact setIntegral_congr_fun measurableSet_Ioi fun t ht => hGp s t ht
    have h2 : ∫ t in Set.Ioi (0 : ℝ), G0 D s (-t) = (β * c) * Mm s := by
      rw [hMm]; simp only; rw [← integral_const_mul]
      exact setIntegral_congr_fun measurableSet_Ioi fun t ht => hGm s t ht
    rw [h1, h2] at hZ
    have hd0 := hdict 0 s hsm
    have hd1 := hdict 1 s hsm
    simp only [ZMod.val_zero, pow_zero, one_mul] at hd0
    simp only [ZMod.val_one, pow_one, neg_one_mul] at hd1
    rw [← hZ, ← hd0, ← hd1]
    ring

  have hΦ := D.zetaEntire_differentiable 1 0 0
  have ha2 : a₂ = a₁ + 1 := by
    have h1 : a₁ = 0 ∨ a₁ = 1 := by fin_cases a₁ <;> first | exact Or.inl rfl | exact Or.inr rfl
    have h2 : a₂ = 0 ∨ a₂ = 1 := by fin_cases a₂ <;> first | exact Or.inl rfl | exact Or.inr rfl
    rcases h1 with rfl | rfl <;> rcases h2 with rfl | rfl <;> first | exact absurd rfl ha | decide
  subst ha2
  have hn12 : ∀ n : ℕ, u₁ - u₂ ≠ -(2 * (n : ℂ)) := not_even_of_abs_re_lt_one hu htype
  have hn21 : ∀ n : ℕ, u₂ - u₁ ≠ -(2 * (n : ℂ)) := by
    refine not_even_of_abs_re_lt_one (Ne.symm hu) ?_
    rwa [← neg_sub, neg_re, abs_neg]
  have hz0 := fun s hs => hzeta 0 s hs
  simp only [ZMod.val_zero, pow_zero, one_mul] at hz0
  have ha1 : a₁ = 0 ∨ a₁ = 1 := by fin_cases a₁ <;> first | exact Or.inl rfl | exact Or.inr rfl

  have hL0 : ∀ s : ℂ, ((RealArchParam.principal u₁ 0 u₂ (0 + 1)).twist 0 0).archFactor s =
      Gammaℝ (s + u₁) * Gammaℝ (s + u₂ + 1) := by
    intro s; rw [archFactor_principal_twist]; simp [signShift, add_assoc]
  have hL1 : ∀ s : ℂ, ((RealArchParam.principal u₁ 1 u₂ (1 + 1)).twist 0 0).archFactor s =
      Gammaℝ (s + u₁ + 1) * Gammaℝ (s + u₂) := by
    intro s; rw [archFactor_principal_twist]
    have : (1 : ZMod 2) + 1 = 0 := by decide
    simp [signShift, add_assoc, this]
  have hA00 : ∀ s : ℂ, ((RealArchParam.principal u₁ 0 u₂ (0 + 1)).twist 0 1).archFactor s =
      Gammaℝ (s + u₁ + 1) * Gammaℝ (s + u₂) := by
    intro s; rw [archFactor_principal_twist]
    have : (1 : ZMod 2) + 1 = 0 := by decide
    simp [signShift, add_assoc, this]
  have hA11 : ∀ s : ℂ, ((RealArchParam.principal u₁ 1 u₂ (1 + 1)).twist 0 1).archFactor s =
      Gammaℝ (s + u₁) * Gammaℝ (s + u₂ + 1) := by
    intro s; rw [archFactor_principal_twist]
    have : (1 : ZMod 2) + 1 = 0 := by decide
    simp [signShift, add_assoc, this]
  have hsw0 : ∀ s : ℂ, ((RealArchParam.principal u₁ (0 + 1) u₂ 0).twist 0 0).archFactor s =
      Gammaℝ (s + u₁ + 1) * Gammaℝ (s + u₂) := by
    intro s; rw [archFactor_principal_twist]; simp [signShift, add_assoc]
  have hsw0' : ∀ s : ℂ, ((RealArchParam.principal u₁ (0 + 1) u₂ 0).twist 0 1).archFactor s =
      Gammaℝ (s + u₁) * Gammaℝ (s + u₂ + 1) := by
    intro s; rw [archFactor_principal_twist]
    have : (1 : ZMod 2) + 1 = 0 := by decide
    simp [signShift, add_assoc, this]
  have hsw1 : ∀ s : ℂ, ((RealArchParam.principal u₁ (1 + 1) u₂ 1).twist 0 0).archFactor s =
      Gammaℝ (s + u₁) * Gammaℝ (s + u₂ + 1) := by
    intro s; rw [archFactor_principal_twist]
    have : (1 : ZMod 2) + 1 = 0 := by decide
    simp [signShift, add_assoc, this]
  have hsw1' : ∀ s : ℂ, ((RealArchParam.principal u₁ (1 + 1) u₂ 1).twist 0 1).archFactor s =
      Gammaℝ (s + u₁ + 1) * Gammaℝ (s + u₂) := by
    intro s; rw [archFactor_principal_twist]
    have : (1 : ZMod 2) + 1 = 0 := by decide
    simp [signShift, add_assoc, this]
  have h2ρ : (2 : ℂ) * ρ ≠ 0 := mul_ne_zero two_ne_zero hρ
  rcases ha1 with rfl | rfl
  ·
    rcases hP' with rfl | rfl
    ·
      left
      have := coeff_eq_zero u₁ u₂ hn12 (α - β * c) (α + β * c)
        (fun s => (2 * ρ) * D.zetaEntire 1 0 0 s) ((differentiable_const _).mul hΦ) σ₀ (fun s hs => by
          have h := hz0 s hs
          simp only [hL0, hA00] at h
          linear_combination -h)
      exact sub_eq_zero.mp this
    ·
      right
      have := coeff_eq_zero u₁ u₂ hn12 (α + β * c) (α - β * c)
        (fun s => (2 * ρ) * D.zetaEntire 1 0 0 s) ((differentiable_const _).mul hΦ) σ₀ (fun s hs => by
          have h := hz0 s hs
          simp only [hL0, hsw0, hsw0'] at h
          linear_combination -h)
      exact eq_neg_of_add_eq_zero_left this
  ·
    rcases hP' with rfl | rfl
    · left
      have := coeff_eq_zero' u₁ u₂ hn21 (α + β * c) (α - β * c)
        (fun s => (2 * ρ) * D.zetaEntire 1 0 0 s) ((differentiable_const _).mul hΦ) σ₀ (fun s hs => by
          have h := hz0 s hs
          simp only [hL1, hA11] at h
          linear_combination -h)
      exact sub_eq_zero.mp this
    · right
      have := coeff_eq_zero' u₁ u₂ hn21 (α - β * c) (α + β * c)
        (fun s => (2 * ρ) * D.zetaEntire 1 0 0 s) ((differentiable_const _).mul hΦ) σ₀ (fun s hs => by
          have h := hz0 s hs
          simp only [hL1, hsw1, hsw1'] at h
          linear_combination -h)
      exact eq_neg_of_add_eq_zero_left this

theorem torus_relation (u₁ u₂ : ℂ) (a₁ a₂ : ZMod 2) (ha : a₁ ≠ a₂) (hu : u₁ ≠ u₂)
    (htype : |(u₁ - u₂).re| < 1)
    (D : ArchDatumR (RealArchParam.principal u₁ a₁ u₂ a₂))
    (hDW : ∀ (r : rowIsometrySubgroup₀ ℝ) (x : GL (Fin 2) ℝ),
      D.W ((x * (r : GL (Fin 2) ℝ) : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) =
        (archWeightCharℝ 1 r : ℂ) * D.W (x : Matrix (Fin 2) (Fin 2) ℝ))
    (hDE : ArchCasimir.IsCasimirEigen D) :
    ∃ κ : ℂ, (∀ y : ℝ, 0 < y → D.W (ray (-1) y) = κ * lowP (fun t => D.W (ray 1 t)) y) ∧
      (∀ y : ℝ, 0 < y → D.W (ray 1 y) = κ * lowM (fun t => D.W (ray (-1) t)) y) := by

  have hc0 : u₁ - u₂ ≠ 0 := sub_ne_zero.mpr hu
  have hν : ((u₁ - u₂) / 2) ^ 2 = 1 / 4 - (RealArchParam.principal u₁ a₁ u₂ a₂).laplaceEigenvalue := by
    rw [laplaceEigenvalue_principal]; ring
  have h4 : (4 : ℂ) * ((u₁ - u₂) / 2) ^ 2 = (u₁ - u₂) ^ 2 := by ring
  have h40 : (4 : ℂ) * ((u₁ - u₂) / 2) ^ 2 ≠ 0 := by rw [h4]; exact pow_ne_zero 2 hc0

  set fp : ℝ → ℂ := fun t => D.W (ray 1 t) with hfp_def
  set fm : ℝ → ℂ := fun t => D.W (ray (-1) t) with hfm_def
  obtain ⟨hp1, hp2, hp3, hpgr⟩ := ray_package D ((u₁ - u₂) / 2) hν hDW hDE 1 (Or.inl rfl)
  obtain ⟨hm1, hm2, hm3, hmgr⟩ := ray_package D ((u₁ - u₂) / 2) hν hDW hDE (-1) (Or.inr rfl)

  have hp3' : ∀ y : ℝ, 0 < y → (y : ℂ) ^ 2 * deriv (deriv fp) y
      + (1 / 4 - ((u₁ - u₂) / 2) ^ 2 + 2 * (π : ℂ) * (y : ℂ) - 4 * (π : ℂ) ^ 2 * (y : ℂ) ^ 2) * fp y = 0 := by
    intro y hy
    have := hp3 y hy
    convert this using 3
    push_cast
    ring

  have hm3' : ∀ y : ℝ, 0 < y → (y : ℂ) ^ 2 * deriv (deriv fm) y
      + (1 / 4 - ((u₁ - u₂) / 2) ^ 2 - 2 * (π : ℂ) * (y : ℂ) - 4 * (π : ℂ) ^ 2 * (y : ℂ) ^ 2) * fm y = 0 := by
    intro y hy
    have := hm3 y hy
    convert this using 3
    push_cast
    ring

  set h : ℝ → ℂ := lowM fm with hh_def
  have hfmC : ContDiffOn ℝ (⊤ : ℕ∞) fm (Set.Ioi 0) := contDiffOn_ray D (-1) (by norm_num)
  obtain ⟨hhC, hh3⟩ := lowM_ode ((u₁ - u₂) / 2) fm hfmC hm3'
  obtain ⟨hh1, hhC'⟩ := contDiffOn_top_iff_deriv.mp hhC
  obtain ⟨hh2, -⟩ := contDiffOn_top_iff_deriv.mp hhC'
  have hhgr : ∃ C N : ℝ, ∀ y : ℝ, 1 ≤ y → ‖h y‖ ≤ C * y ^ N :=
    lowM_growth ((u₁ - u₂) / 2) (-1) fm hm1 hm2 hm3 hmgr

  have hh3k : ∀ y : ℝ, 0 < y → (y : ℂ) ^ 2 * deriv (deriv h) y
      + (1 / 4 - ((u₁ - u₂) / 2) ^ 2 + 2 * (π : ℂ) * ((1 : ℝ) : ℂ) * (y : ℂ) - 4 * (π : ℂ) ^ 2 * (y : ℂ) ^ 2) * h y
        = 0 := by
    intro y hy
    have := hh3 y hy
    convert this using 3
    push_cast
    ring

  have hI : ∀ y : ℝ, 0 < y → fm y = ((4 : ℂ) * ((u₁ - u₂) / 2) ^ 2)⁻¹ * lowP h y := by
    intro y hy
    rw [eq_inv_mul_iff_mul_eq₀ h40]
    exact (lowP_lowM_eq ((u₁ - u₂) / 2) fm hm1 hm2 hm3' y hy).symm
  by_cases hA : ∃ y : ℝ, 0 < y ∧ fp y ≠ 0
  ·
    obtain ⟨c₁, c₂, hne, hlin⟩ :=
      LanglandsTunnell.linearDependent_of_whittaker_ode_of_moderateGrowth_complexParam ((u₁ - u₂) / 2) 1 h fp
        hh1 hh2 hh3k hhgr hp1 hp2 hp3 hpgr
    have hc1 : c₁ ≠ 0 := by
      intro h0
      apply hne
      obtain ⟨t, ht, hft⟩ := hA
      have hl := hlin t ht
      rw [h0, zero_mul, zero_add] at hl
      have hc2 : c₂ = 0 := (mul_eq_zero.mp hl).resolve_right hft
      rw [h0, hc2]
      rfl
    have hheq : Set.EqOn h (fun t => (-c₂ / c₁) * fp t) (Set.Ioi 0) := by
      intro t ht
      have hl := hlin t ht
      show h t = -c₂ / c₁ * fp t
      field_simp
      linear_combination hl
    have hfm : ∀ y : ℝ, 0 < y → fm y = (-c₂ / c₁) / ((4 : ℂ) * ((u₁ - u₂) / 2) ^ 2) * lowP fp y := by
      intro y hy
      rw [hI y hy, lowP_congr hheq hy, lowP_const_mul]
      field_simp
    have hpin := mellin_pin u₁ u₂ a₁ a₂ ha hu htype D fp hp1 hp2 hp3' hpgr hA 1
      ((-c₂ / c₁) / ((4 : ℂ) * ((u₁ - u₂) / 2) ^ 2)) (fun t _ => (one_mul _).symm) hfm
    have hsq : (-c₂ / c₁) / ((4 : ℂ) * ((u₁ - u₂) / 2) ^ 2) * (-c₂ / c₁) = 1 := by
      have hb : (-c₂ / c₁) / ((4 : ℂ) * ((u₁ - u₂) / 2) ^ 2) * (u₁ - u₂) = 1 ∨
          (-c₂ / c₁) / ((4 : ℂ) * ((u₁ - u₂) / 2) ^ 2) * (u₁ - u₂) = -1 := by
        rcases hpin with h1 | h1
        · exact Or.inl h1.symm
        · exact Or.inr (by linear_combination h1)
      have hsq' : ((-c₂ / c₁) / ((4 : ℂ) * ((u₁ - u₂) / 2) ^ 2) * (u₁ - u₂)) ^ 2 = 1 := by
        rcases hb with h1 | h1 <;> rw [h1] <;> norm_num
      have key : (-c₂ / c₁) / ((4 : ℂ) * ((u₁ - u₂) / 2) ^ 2) * (-c₂ / c₁)
          = ((-c₂ / c₁) / ((4 : ℂ) * ((u₁ - u₂) / 2) ^ 2) * (u₁ - u₂)) ^ 2 := by
        field_simp
        ring
      rw [key, hsq']
    refine ⟨(-c₂ / c₁) / ((4 : ℂ) * ((u₁ - u₂) / 2) ^ 2), hfm, fun y hy => ?_⟩
    show fp y = _ * h y
    rw [hheq hy, ← mul_assoc, hsq, one_mul]
  ·
    push Not at hA
    by_cases hB : ∃ y : ℝ, 0 < y ∧ h y ≠ 0
    · exfalso
      have hpin := mellin_pin u₁ u₂ a₁ a₂ ha hu htype D h hh1 hh2 hh3 hhgr hB 0
        ((4 : ℂ) * ((u₁ - u₂) / 2) ^ 2)⁻¹ (fun t ht => by rw [zero_mul]; exact hA t ht) hI
      have hz : ((4 : ℂ) * ((u₁ - u₂) / 2) ^ 2)⁻¹ * (u₁ - u₂) = 0 := by
        rcases hpin with h1 | h1
        · exact h1.symm
        · linear_combination h1
      exact mul_ne_zero (inv_ne_zero h40) hc0 hz
    · push Not at hB
      refine ⟨0, fun y hy => ?_, fun y hy => ?_⟩
      · show fm y = 0 * _
        rw [zero_mul, hI y hy, lowP_congr (fun t ht => hB t ht : Set.EqOn h (fun _ => (0 : ℂ)) (Set.Ioi 0)) hy]
        simp [lowP]
      · show fp y = 0 * _
        rw [zero_mul]
        exact hA y hy

theorem det_diagonal_negOne_one : (Matrix.diagonal ![(-1 : ℝ), 1]).det = -1 := by
  simp [Matrix.det_diagonal, Fin.prod_univ_two]

theorem diagonal_mul_self : Matrix.diagonal ![(-1 : ℝ), 1] * Matrix.diagonal ![(-1 : ℝ), 1] = 1 := by
  rw [Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
  congr 1
  funext i; fin_cases i <;> simp

theorem ray_mul_diagonal (ε y : ℝ) : ray ε y * Matrix.diagonal ![(-1 : ℝ), 1] = ray (-ε) y := by
  rw [ray, ray]
  ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Matrix.diagonal]

theorem J_coe_eq_diagonal :
    ((UpperHalfPlane.J : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) = Matrix.diagonal ![(-1 : ℝ), 1] := by
  rw [UpperHalfPlane.val_J]
  ext i j; fin_cases i <;> fin_cases j <;> simp

theorem J_mul_mul_J (r : rowIsometrySubgroup₀ ℝ) :
    UpperHalfPlane.J * (r : GL (Fin 2) ℝ) * UpperHalfPlane.J = (r : GL (Fin 2) ℝ)⁻¹ := by
  obtain ⟨h10, h11, hab⟩ := entries_of_mem_rowIsometrySubgroup₀ r.2
  apply eq_inv_of_mul_eq_one_left
  apply Units.ext
  rw [Units.val_mul, Units.val_mul, Units.val_mul, J_coe_eq_diagonal, Units.val_one]
  ext i j; fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two, Matrix.diagonal, h10, h11] <;> nlinarith [hab]

theorem main (u₁ u₂ : ℂ) (a₁ a₂ : ZMod 2) (ha : a₁ ≠ a₂) (hu : u₁ ≠ u₂)
    (htype : |(u₁ - u₂).re| < 1)
    (D : ArchDatumR (RealArchParam.principal u₁ a₁ u₂ a₂))
    (hDW : ∀ (r : rowIsometrySubgroup₀ ℝ) (x : GL (Fin 2) ℝ),
      D.W ((x * (r : GL (Fin 2) ℝ) : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) =
        (archWeightCharℝ 1 r : ℂ) * D.W (x : Matrix (Fin 2) (Fin 2) ℝ))
    (hDE : ArchCasimir.IsCasimirEigen D) :
    ∃ κ : ℂ, ∀ x : Matrix (Fin 2) (Fin 2) ℝ, x.det ≠ 0 →
      D.W (x * Matrix.diagonal ![(-1 : ℝ), 1]) = κ * LW D.W x := by
  classical
  set ν : ℂ := (u₁ - u₂) / 2 with hνdef
  have hν : ν ^ 2 = 1 / 4 - (RealArchParam.principal u₁ a₁ u₂ a₂).laplaceEigenvalue := by
    rw [laplaceEigenvalue_principal]; ring

  obtain ⟨hB0N, hB0Z, hB0K, -⟩ :=
    LanglandsTunnell.Converse.ArchDatumR.laws_and_torus_ode_of_archWeightChar_of_isCasimirEigen _ D 1 ν hν hDW hDE

  obtain ⟨κ, hκP, hκM⟩ := torus_relation u₁ u₂ a₁ a₂ ha hu htype D hDW hDE
  set Jm : Matrix (Fin 2) (Fin 2) ℝ := Matrix.diagonal ![(-1 : ℝ), 1] with hJm

  have hJJ : (UpperHalfPlane.J : GL (Fin 2) ℝ) * UpperHalfPlane.J = 1 := by
    apply Units.ext
    rw [Units.val_mul, J_coe_eq_diagonal, Units.val_one, diagonal_mul_self]
  have hdet_unip : ∀ t : ℝ, (ArchR.unip t).det = 1 := fun t => by
    simp [ArchR.unip, Matrix.det_fin_two_of]
  have hdet_r : ∀ r : rowIsometrySubgroup₀ ℝ, ((r : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ).det = 1 := fun r =>
    ((mem_rowIsometrySubgroup₀_iff _).1 r.2).1
  have hrpow_sq : ∀ (t : ℝ), 0 < t → ∀ (X : ℝ), 0 ≤ X → (t ^ 2 * X) ^ (-(1 / 2 : ℝ)) = t⁻¹ * X ^ (-(1 / 2 : ℝ)) := by
    intro t ht X hX
    rw [Real.mul_rpow (sq_nonneg t) hX]
    congr 1
    rw [show t ^ 2 = t ^ (2 : ℝ) by rw [Real.rpow_two], ← Real.rpow_mul ht.le,
      show (2 : ℝ) * -(1 / 2 : ℝ) = -1 by norm_num, Real.rpow_neg_one]

  have hBN : ∀ (t : ℝ) (x : Matrix (Fin 2) (Fin 2) ℝ), x.det ≠ 0 →
      (fun x : Matrix (Fin 2) (Fin 2) ℝ => (((|x.det| ^ (-(1 / 2 : ℝ)) : ℝ)) : ℂ) * LW D.W x) (ArchR.unip t * x) =
        ArchR.psi t * (fun x : Matrix (Fin 2) (Fin 2) ℝ => (((|x.det| ^ (-(1 / 2 : ℝ)) : ℝ)) : ℂ) * LW D.W x) x := by
    intro t x hx
    simp only
    rw [Matrix.det_mul, hdet_unip, one_mul, LW_unip D.W D.unip_law]
    ring
  have hBZ : ∀ (t : ℝ) (x : Matrix (Fin 2) (Fin 2) ℝ), 0 < t → x.det ≠ 0 →
      (fun x : Matrix (Fin 2) (Fin 2) ℝ => (((|x.det| ^ (-(1 / 2 : ℝ)) : ℝ)) : ℂ) * LW D.W x) (t • x) =
        ((t : ℂ) ^ (RealArchParam.principal u₁ a₁ u₂ a₂).centralExponent) *
          (fun x : Matrix (Fin 2) (Fin 2) ℝ => (((|x.det| ^ (-(1 / 2 : ℝ)) : ℝ)) : ℂ) * LW D.W x) x := by
    intro t x ht hx
    simp only
    rw [Matrix.det_smul, Fintype.card_fin, LW_smul D.W (fun s => ArchR.centralChar (RealArchParam.principal u₁ a₁ u₂ a₂) s * ((|s| : ℝ) : ℂ))
      (fun s g hs => D.central_law s g hs) t ht.ne' x, centralChar_of_pos t ht, abs_of_pos ht, abs_mul,
      abs_of_pos (pow_pos ht 2), hrpow_sq t ht _ (abs_nonneg _)]
    have ht' : (t : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 ht.ne'
    push_cast
    field_simp
  have hBK : ∀ (r : rowIsometrySubgroup₀ ℝ) (x : GL (Fin 2) ℝ),
      (fun x : Matrix (Fin 2) (Fin 2) ℝ => (((|x.det| ^ (-(1 / 2 : ℝ)) : ℝ)) : ℂ) * LW D.W x)
          ((x * (r : GL (Fin 2) ℝ) : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) =
        (archWeightCharℝ (-1) r : ℂ) *
          (fun x : Matrix (Fin 2) (Fin 2) ℝ => (((|x.det| ^ (-(1 / 2 : ℝ)) : ℝ)) : ℂ) * LW D.W x)
            (x : Matrix (Fin 2) (Fin 2) ℝ) := by
    intro r x
    simp only
    rw [LW_weight D.W D.smooth hDW r x, Units.val_mul, Matrix.det_mul, hdet_r r, mul_one]
    ring

  have hAN : ∀ (t : ℝ) (x : Matrix (Fin 2) (Fin 2) ℝ), x.det ≠ 0 →
      (fun x : Matrix (Fin 2) (Fin 2) ℝ => (((|(x * Jm).det| ^ (-(1 / 2 : ℝ)) : ℝ)) : ℂ) * D.W (x * Jm)) (ArchR.unip t * x) =
        ArchR.psi t * (fun x : Matrix (Fin 2) (Fin 2) ℝ => (((|(x * Jm).det| ^ (-(1 / 2 : ℝ)) : ℝ)) : ℂ) * D.W (x * Jm)) x := by
    intro t x hx
    have hxJ : (x * Jm).det ≠ 0 := by
      rw [Matrix.det_mul, det_diagonal_negOne_one]; simpa using hx
    have := hB0N t (x * Jm) hxJ
    simp only [Matrix.mul_assoc] at this ⊢
    exact this
  have hAZ : ∀ (t : ℝ) (x : Matrix (Fin 2) (Fin 2) ℝ), 0 < t → x.det ≠ 0 →
      (fun x : Matrix (Fin 2) (Fin 2) ℝ => (((|(x * Jm).det| ^ (-(1 / 2 : ℝ)) : ℝ)) : ℂ) * D.W (x * Jm)) (t • x) =
        ((t : ℂ) ^ (RealArchParam.principal u₁ a₁ u₂ a₂).centralExponent) *
          (fun x : Matrix (Fin 2) (Fin 2) ℝ => (((|(x * Jm).det| ^ (-(1 / 2 : ℝ)) : ℝ)) : ℂ) * D.W (x * Jm)) x := by
    intro t x ht hx
    have hxJ : (x * Jm).det ≠ 0 := by
      rw [Matrix.det_mul, det_diagonal_negOne_one]; simpa using hx
    have := hB0Z t (x * Jm) ht hxJ
    simp only [Matrix.smul_mul] at this ⊢
    exact this
  have hAK : ∀ (r : rowIsometrySubgroup₀ ℝ) (x : GL (Fin 2) ℝ),
      (fun x : Matrix (Fin 2) (Fin 2) ℝ => (((|(x * Jm).det| ^ (-(1 / 2 : ℝ)) : ℝ)) : ℂ) * D.W (x * Jm))
          ((x * (r : GL (Fin 2) ℝ) : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) =
        (archWeightCharℝ (-1) r : ℂ) *
          (fun x : Matrix (Fin 2) (Fin 2) ℝ => (((|(x * Jm).det| ^ (-(1 / 2 : ℝ)) : ℝ)) : ℂ) * D.W (x * Jm))
            (x : Matrix (Fin 2) (Fin 2) ℝ) := by
    intro r x
    simp only
    have h1 := hB0K r⁻¹ (x * UpperHalfPlane.J)

    have hGL : x * (r : GL (Fin 2) ℝ) * UpperHalfPlane.J = x * UpperHalfPlane.J * ((r⁻¹ : rowIsometrySubgroup₀ ℝ) : GL (Fin 2) ℝ) := by
      rw [Subgroup.coe_inv, ← J_mul_mul_J r, ← mul_assoc, ← mul_assoc,
        mul_assoc x UpperHalfPlane.J UpperHalfPlane.J, hJJ, mul_one]
    have hmat : (((x * (r : GL (Fin 2) ℝ) : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ)) * Jm =
        (((x * UpperHalfPlane.J * ((r⁻¹ : rowIsometrySubgroup₀ ℝ) : GL (Fin 2) ℝ) : GL (Fin 2) ℝ)) :
          Matrix (Fin 2) (Fin 2) ℝ) := by
      rw [← hGL, Units.val_mul (x * (r : GL (Fin 2) ℝ)), J_coe_eq_diagonal]
    have hmat2 : ((x : Matrix (Fin 2) (Fin 2) ℝ)) * Jm =
        (((x * UpperHalfPlane.J : GL (Fin 2) ℝ)) : Matrix (Fin 2) (Fin 2) ℝ) := by
      rw [Units.val_mul, J_coe_eq_diagonal]
    have hchar : ((archWeightCharℝ 1 r⁻¹ : ℂˣ) : ℂ) = ((archWeightCharℝ (-1) r : ℂˣ) : ℂ) := by
      rw [map_inv, Units.val_inv_eq_inv_val, archWeightCharℝ_neg_one_coe, archWeightCharℝ_one_coe]
    rw [hmat, hmat2, ← hchar]
    exact h1

  have htor : ∀ (ε : ℝ), (ε = 1 ∨ ε = -1) → ∀ y : ℝ, 0 < y →
      (fun x : Matrix (Fin 2) (Fin 2) ℝ => (((|(x * Jm).det| ^ (-(1 / 2 : ℝ)) : ℝ)) : ℂ) * D.W (x * Jm))
          !![ε * Real.sqrt y, 0; 0, (Real.sqrt y)⁻¹] =
        κ * (fun x : Matrix (Fin 2) (Fin 2) ℝ => (((|x.det| ^ (-(1 / 2 : ℝ)) : ℝ)) : ℂ) * LW D.W x)
          !![ε * Real.sqrt y, 0; 0, (Real.sqrt y)⁻¹] := by
    intro ε hε y hy
    have hd : DifferentiableAt ℝ (fun t => D.W (ray ε t)) y :=
      (ray_package D ν hν hDW hDE ε hε).1.differentiableAt (Ioi_mem_nhds hy)
    have habs : |ε| = 1 := by rcases hε with rfl | rfl <;> norm_num
    have habs' : |-ε| = 1 := by rw [abs_neg, habs]
    show (((|(ray ε y * Jm).det| ^ (-(1 / 2 : ℝ)) : ℝ)) : ℂ) * D.W (ray ε y * Jm) =
      κ * ((((|(ray ε y).det| ^ (-(1 / 2 : ℝ)) : ℝ)) : ℂ) * LW D.W (ray ε y))
    rw [ray_mul_diagonal, ray_det _ hy, ray_det _ hy, habs, habs', Real.one_rpow, Complex.ofReal_one, one_mul, one_mul,
      LW_ray D.W D.unip_law hDW ε hε hy hd]
    rcases hε with rfl | rfl
    · rw [hκP y hy, lowP]
      push_cast
      ring
    · rw [neg_neg, hκM y hy, lowM]
      push_cast
      ring

  have key : ∀ (ε : ℝ), (ε = 1 ∨ ε = -1) → ∀ (x : Matrix (Fin 2) (Fin 2) ℝ), 0 < ε * x.det →
      (fun x : Matrix (Fin 2) (Fin 2) ℝ => (((|(x * Jm).det| ^ (-(1 / 2 : ℝ)) : ℝ)) : ℂ) * D.W (x * Jm)) x =
        κ * (fun x : Matrix (Fin 2) (Fin 2) ℝ => (((|x.det| ^ (-(1 / 2 : ℝ)) : ℝ)) : ℂ) * LW D.W x) x :=
    fun ε hε => LanglandsTunnell.Converse.ArchR.eq_mul_of_unip_law_of_central_law_of_archWeightChar_of_torus_eq_of_sign_det
      (fun x : Matrix (Fin 2) (Fin 2) ℝ => (((|(x * Jm).det| ^ (-(1 / 2 : ℝ)) : ℝ)) : ℂ) * D.W (x * Jm))
      (fun x : Matrix (Fin 2) (Fin 2) ℝ => (((|x.det| ^ (-(1 / 2 : ℝ)) : ℝ)) : ℂ) * LW D.W x)
      (-1) (RealArchParam.principal u₁ a₁ u₂ a₂).centralExponent κ hAN hBN hAZ hBZ hAK hBK ε hε (htor ε hε)
  refine ⟨κ, fun x hx => ?_⟩
  have hres : (((|(x * Jm).det| ^ (-(1 / 2 : ℝ)) : ℝ)) : ℂ) * D.W (x * Jm) =
      κ * ((((|x.det| ^ (-(1 / 2 : ℝ)) : ℝ)) : ℂ) * LW D.W x) := by
    by_cases hpos : 0 < x.det
    · exact key 1 (Or.inl rfl) x (by simpa using hpos)
    · have hneg : 0 < (-1) * x.det := by
        have : x.det < 0 := lt_of_le_of_ne (not_lt.mp hpos) hx
        linarith
      exact key (-1) (Or.inr rfl) x hneg
  have hdet : |(x * Jm).det| = |x.det| := by
    rw [Matrix.det_mul, det_diagonal_negOne_one, abs_mul]; norm_num
  rw [hdet] at hres
  have hc : ((((|x.det| ^ (-(1 / 2 : ℝ)) : ℝ)) : ℂ)) ≠ 0 := by
    exact_mod_cast (Real.rpow_pos_of_pos (abs_pos.mpr hx) _).ne'
  have h2 : ((((|x.det| ^ (-(1 / 2 : ℝ)) : ℝ)) : ℂ)) * D.W (x * Jm) =
      ((((|x.det| ^ (-(1 / 2 : ℝ)) : ℝ)) : ℂ)) * (κ * LW D.W x) := by
    rw [hres]; ring
  exact mul_left_cancel₀ hc h2

end Ws47DZL

end

open Ws47DZL in
theorem solution
    (u₁ u₂ : ℂ) (a₁ a₂ : ZMod 2) (ha : a₁ ≠ a₂) (hu : u₁ ≠ u₂)
    (hgen : ∀ p : ℤ, p ≠ 0 → u₁ - u₂ = (p : ℂ) → a₁ - a₂ ≠ ((p + 1 : ℤ) : ZMod 2))
    (htype : |(u₁ - u₂).re| < 1)
    (D : ArchDatumR (RealArchParam.principal u₁ a₁ u₂ a₂))
    (hDW : ∀ (r : rowIsometrySubgroup₀ ℝ) (x : GL (Fin 2) ℝ),
      D.W ((x * (r : GL (Fin 2) ℝ) : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) =
        (archWeightCharℝ 1 r : ℂ) * D.W (x : Matrix (Fin 2) (Fin 2) ℝ))
    (hDE : ArchCasimir.IsCasimirEigen D) :
    ∃ κ : ℂ, ∀ x : Matrix (Fin 2) (Fin 2) ℝ, x.det ≠ 0 →
      D.W (x * Matrix.diagonal ![(-1 : ℝ), 1]) =
        κ * (ArchCasimir.matrixFlowDeriv ArchDir.H D.W x -
              Complex.I * (ArchCasimir.matrixFlowDeriv ArchDir.E D.W x + ArchCasimir.matrixFlowDeriv ArchDir.Fm D.W x)) :=
  Ws47DZL.main u₁ u₂ a₁ a₂ ha hu htype D hDW hDE

end S_LanglandsTunnell_Converse_ArchDatumR_exists_W_mul_diag_eq_mul_lower_of_principal_of_ne_of_ne_of_archWeightChar_one_of_isCasimirEigen
end P2MW
export P2MW.S_LanglandsTunnell_Converse_ArchDatumR_exists_W_mul_diag_eq_mul_lower_of_principal_of_ne_of_ne_of_archWeightChar_one_of_isCasimirEigen (solution)
