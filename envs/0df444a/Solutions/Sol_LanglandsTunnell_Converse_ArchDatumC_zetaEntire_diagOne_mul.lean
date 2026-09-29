-- Prove2me | solution 1 for LanglandsTunnell.Converse.ArchDatumC.zetaEntire_diagOne_mul
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:08.353894+00:00
-- url     : https://prove2.me/submissions/3535dd4a-8025-524c-bec5-d99c61a7cc19

import Definitions.Def_LanglandsTunnell_JLConverse
import Mathlib.MeasureTheory.Measure.Haar.NormedSpace
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Analysis.Analytic.Uniqueness
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.MeasureTheory.Measure.Lebesgue.Complex
import Mathlib.Analysis.Complex.Isometry
import Mathlib.LinearAlgebra.Complex.FiniteDimensional
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_LanglandsTunnell_Converse_ArchDatumC_zetaEntire_diagOne_mul

set_option autoImplicit false

noncomputable section

namespace ArchDiagScalingComplex

p2m_open "Complex MeasureTheory Filter Topology LanglandsTunnell LanglandsTunnell.Converse LanglandsTunnell.Converse.ArchC"

private theorem diagOne_mul_diagOne (y A : ℂ) : diagOne y * diagOne A = diagOne (y * A) := by
  simp [diagOne]

private theorem det_diagOne_mul (A : ℂ) (g : Matrix (Fin 2) (Fin 2) ℂ) : (diagOne A * g).det = A * g.det := by
  rw [Matrix.det_mul]
  simp [diagOne, Matrix.det_fin_two_of]

private theorem quasiChar_mul (u : ℂ) (k : ℤ) (A z : ℂ) :
    quasiChar u k (A * z) = quasiChar u k A * quasiChar u k z := by
  unfold quasiChar
  rw [norm_mul, Complex.ofReal_mul, Complex.mul_cpow_ofReal_nonneg (norm_nonneg A) (norm_nonneg z), mul_div_mul_comm,
    mul_zpow]
  ring

private theorem quasiChar_ne_zero (u : ℂ) (k : ℤ) {A : ℂ} (hA : A ≠ 0) : quasiChar u k A ≠ 0 := by
  unfold quasiChar
  have hn : ((‖A‖ : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 (norm_ne_zero_iff.2 hA)
  exact mul_ne_zero (Complex.cpow_ne_zero_iff.2 (Or.inl hn)) (zpow_ne_zero k (div_ne_zero hA hn))

private theorem zetaIntegrand_mul_left (W : Matrix (Fin 2) (Fin 2) ℂ → ℂ) (g : Matrix (Fin 2) (Fin 2) ℂ) (u : ℂ)
    (k : ℤ) (s : ℂ) (A z : ℂ) :
    zetaIntegrand W g u k s (A * z)
      = (quasiChar u k A * (((‖A‖ ^ 2 : ℝ)) : ℂ) ^ (s - 1) * ((((‖A‖ ^ 2 : ℝ)) : ℂ))⁻¹)
          * zetaIntegrand W (diagOne A * g) u k s z := by
  unfold zetaIntegrand
  rw [quasiChar_mul, norm_mul, mul_pow, Complex.ofReal_mul,
    Complex.mul_cpow_ofReal_nonneg (sq_nonneg ‖A‖) (sq_nonneg ‖z‖), mul_inv, ← Matrix.mul_assoc, diagOne_mul_diagOne,
    mul_comm z A]
  ring

private theorem integral_comp_mul_left (f : ℂ → ℂ) {A : ℂ} (hA : A ≠ 0) :
    ∫ z : ℂ, f (A * z) = ((((‖A‖ ^ 2 : ℝ)) : ℂ))⁻¹ * ∫ z : ℂ, f z := by
  have hr : (‖A‖ : ℝ) ≠ 0 := norm_ne_zero_iff.2 hA
  have hr' : ((‖A‖ : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 hr
  let w : Circle := ⟨A / ((‖A‖ : ℝ) : ℂ), mem_sphere_zero_iff_norm.2 (by
    rw [norm_div, Complex.norm_of_nonneg (norm_nonneg A), div_self hr])⟩
  have hw : ∀ z : ℂ, (‖A‖ : ℝ) • (rotation w z) = A * z := fun z => by
    rw [rotation_apply, Complex.real_smul, ← mul_assoc]
    show ((‖A‖ : ℝ) : ℂ) * (A / ((‖A‖ : ℝ) : ℂ)) * z = A * z
    rw [mul_div_cancel₀ A hr']
  calc ∫ z : ℂ, f (A * z)
      = ∫ z : ℂ, (fun y : ℂ => f ((‖A‖ : ℝ) • y)) (rotation w z) := by simp only [hw]
    _ = ∫ y : ℂ, f ((‖A‖ : ℝ) • y) :=
        (rotation w).measurePreserving.integral_comp (rotation w).toHomeomorph.measurableEmbedding
          (fun y : ℂ => f ((‖A‖ : ℝ) • y))
    _ = |((‖A‖ ^ Module.finrank ℝ ℂ)⁻¹ : ℝ)| • ∫ y : ℂ, f y := MeasureTheory.Measure.integral_comp_smul volume f ‖A‖
    _ = ((((‖A‖ ^ 2 : ℝ)) : ℂ))⁻¹ * ∫ z : ℂ, f z := by
        rw [Complex.finrank_real_complex, abs_of_nonneg (inv_nonneg.2 (sq_nonneg ‖A‖)), Complex.real_smul,
          Complex.ofReal_inv]

private theorem integral_zetaIntegrand_diagOne_mul (W : Matrix (Fin 2) (Fin 2) ℂ → ℂ)
    (g : Matrix (Fin 2) (Fin 2) ℂ) (u : ℂ) (k : ℤ) (s : ℂ) {A : ℂ} (hA : A ≠ 0) :
    ∫ z : ℂ, zetaIntegrand W (diagOne A * g) u k s z
      = (quasiChar u k A)⁻¹ * (((‖A‖ ^ 2 : ℝ)) : ℂ) ^ (1 - s) * ∫ z : ℂ, zetaIntegrand W g u k s z := by
  have hn : ((((‖A‖ ^ 2 : ℝ)) : ℂ)) ≠ 0 := Complex.ofReal_ne_zero.2 (pow_ne_zero 2 (norm_ne_zero_iff.2 hA))
  have hχ : quasiChar u k A ≠ 0 := quasiChar_ne_zero u k hA
  have hP : (((‖A‖ ^ 2 : ℝ)) : ℂ) ^ (s - 1) ≠ 0 := Complex.cpow_ne_zero_iff.2 (Or.inl hn)
  set C : ℂ := quasiChar u k A * (((‖A‖ ^ 2 : ℝ)) : ℂ) ^ (s - 1) * ((((‖A‖ ^ 2 : ℝ)) : ℂ))⁻¹ with hC
  have hC0 : C ≠ 0 := mul_ne_zero (mul_ne_zero hχ hP) (inv_ne_zero hn)
  have h1 : ∫ z : ℂ, zetaIntegrand W g u k s (A * z) = C * ∫ z : ℂ, zetaIntegrand W (diagOne A * g) u k s z := by
    rw [← MeasureTheory.integral_const_mul]
    exact MeasureTheory.integral_congr_ae (Eventually.of_forall fun z => zetaIntegrand_mul_left W g u k s A z)
  have h2 : ∫ z : ℂ, zetaIntegrand W g u k s (A * z)
      = ((((‖A‖ ^ 2 : ℝ)) : ℂ))⁻¹ * ∫ z : ℂ, zetaIntegrand W g u k s z :=
    integral_comp_mul_left _ hA
  have h3 : C * ∫ z : ℂ, zetaIntegrand W (diagOne A * g) u k s z
      = ((((‖A‖ ^ 2 : ℝ)) : ℂ))⁻¹ * ∫ z : ℂ, zetaIntegrand W g u k s z := by
    rw [← h1, h2]
  rw [← inv_mul_cancel_left₀ hC0 (∫ z : ℂ, zetaIntegrand W (diagOne A * g) u k s z), h3, hC,
    show (1 : ℂ) - s = -(s - 1) by ring, Complex.cpow_neg, mul_inv, mul_inv, inv_inv, mul_assoc,
    mul_inv_cancel_left₀ hn]

private theorem Gammaℂ_ne_zero_of_re_pos {w : ℂ} (hw : 0 < w.re) : Complex.Gammaℂ w ≠ 0 := by
  rw [Complex.Gammaℂ_def]
  refine mul_ne_zero (mul_ne_zero two_ne_zero ?_) (Complex.Gamma_ne_zero_of_re_pos hw)
  exact Complex.cpow_ne_zero_iff.2 (Or.inl (mul_ne_zero two_ne_zero (Complex.ofReal_ne_zero.2 Real.pi_ne_zero)))

private theorem exists_prod_Gammaℂ_ne_zero (m : Multiset ℂ) :
    ∃ R : ℝ, ∀ s : ℂ, R < s.re → (m.map fun ν => Complex.Gammaℂ (s + ν)).prod ≠ 0 := by
  induction m using Multiset.induction_on with
  | empty => exact ⟨0, fun s _ => by simp⟩
  | cons ν m ih =>
    obtain ⟨R, hR⟩ := ih
    refine ⟨max R (-ν.re), fun s hs => ?_⟩
    rw [Multiset.map_cons, Multiset.prod_cons]
    refine mul_ne_zero (Gammaℂ_ne_zero_of_re_pos ?_) (hR s ((le_max_left _ _).trans_lt hs))
    have h := (le_max_right R (-ν.re)).trans_lt hs
    rw [Complex.add_re]
    linarith

private theorem exists_archFactor_ne_zero (Q : ComplexArchParam) :
    ∃ R : ℝ, ∀ s : ℂ, R < s.re → Q.archFactor s ≠ 0 := by
  obtain ⟨R, h⟩ := exists_prod_Gammaℂ_ne_zero Q.gammaC
  refine ⟨R, fun s hs => ?_⟩
  unfold ComplexArchParam.archFactor
  exact h s hs

end ArchDiagScalingComplex

end

open Filter Topology
open LanglandsTunnell LanglandsTunnell.Converse

theorem solution {P : ComplexArchParam} (D : ArchDatumC P)
    (g : Matrix (Fin 2) (Fin 2) ℂ) (A : ℂ) (u : ℂ) (k : ℤ) (s : ℂ) (hA : A ≠ 0) (hg : g.det ≠ 0) :
    D.zetaEntire (ArchC.diagOne A * g) u k s =
      (ArchC.quasiChar u k A)⁻¹ * ((‖A‖ ^ 2 : ℝ) : ℂ) ^ (1 - s) * D.zetaEntire g u k s := by
  obtain ⟨R, hR⟩ := ArchDiagScalingComplex.exists_archFactor_ne_zero (P.twist u k)
  have hn : (((‖A‖ ^ 2 : ℝ)) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 (pow_ne_zero 2 (norm_ne_zero_iff.2 hA))
  have hF : AnalyticOnNhd ℂ (fun t => D.zetaEntire (ArchC.diagOne A * g) u k t) Set.univ :=
    (D.zetaEntire_differentiable _ u k).differentiableOn.analyticOnNhd isOpen_univ
  have hpow : Differentiable ℂ (fun t : ℂ => (((‖A‖ ^ 2 : ℝ)) : ℂ) ^ (1 - t)) :=
    ((differentiable_const (1 : ℂ)).sub differentiable_id).const_cpow (Or.inl hn)
  have hG : AnalyticOnNhd ℂ
      (fun t => (ArchC.quasiChar u k A)⁻¹ * (((‖A‖ ^ 2 : ℝ)) : ℂ) ^ (1 - t) * D.zetaEntire g u k t) Set.univ :=
    (((differentiable_const _).mul hpow).mul (D.zetaEntire_differentiable g u k)).differentiableOn.analyticOnNhd
      isOpen_univ
  have hloc : ∀ t : ℂ, max R (D.zeta_abscissa - u.re) < t.re →
      D.zetaEntire (ArchC.diagOne A * g) u k t
        = (ArchC.quasiChar u k A)⁻¹ * (((‖A‖ ^ 2 : ℝ)) : ℂ) ^ (1 - t) * D.zetaEntire g u k t := by
    intro t ht
    have h₁ := (le_max_left R (D.zeta_abscissa - u.re)).trans_lt ht
    have h₂ := (le_max_right R (D.zeta_abscissa - u.re)).trans_lt ht
    have habsc : D.zeta_abscissa < t.re + u.re := by linarith
    have hdet : (ArchC.diagOne A * g).det ≠ 0 := by
      rw [ArchDiagScalingComplex.det_diagOne_mul]
      exact mul_ne_zero hA hg
    have e₁ := D.zeta_eq (ArchC.diagOne A * g) u k t hdet habsc
    have e₂ := D.zeta_eq g u k t hg habsc
    have e₃ := ArchDiagScalingComplex.integral_zetaIntegrand_diagOne_mul D.W g u k t hA
    have hL : (P.twist u k).archFactor t ≠ 0 := hR t h₁
    refine mul_left_cancel₀ hL ?_
    rw [← e₁, e₃, e₂]
    ring
  have hev : (fun t => D.zetaEntire (ArchC.diagOne A * g) u k t)
      =ᶠ[𝓝 (((max R (D.zeta_abscissa - u.re) + 1 : ℝ)) : ℂ)]
        (fun t => (ArchC.quasiChar u k A)⁻¹ * (((‖A‖ ^ 2 : ℝ)) : ℂ) ^ (1 - t) * D.zetaEntire g u k t) := by
    have hopen : IsOpen {t : ℂ | max R (D.zeta_abscissa - u.re) < t.re} :=
      isOpen_lt continuous_const Complex.continuous_re
    have hmem : (((max R (D.zeta_abscissa - u.re) + 1 : ℝ)) : ℂ)
        ∈ {t : ℂ | max R (D.zeta_abscissa - u.re) < t.re} := by
      rw [Set.mem_setOf_eq, Complex.ofReal_re]
      linarith
    filter_upwards [hopen.mem_nhds hmem] with t ht using hloc t ht
  exact congrFun (AnalyticOnNhd.eq_of_eventuallyEq hF hG hev) s

#print axioms solution

end S_LanglandsTunnell_Converse_ArchDatumC_zetaEntire_diagOne_mul
end P2MW
export P2MW.S_LanglandsTunnell_Converse_ArchDatumC_zetaEntire_diagOne_mul (solution)
