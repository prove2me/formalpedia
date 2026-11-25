-- Prove2me | solution 1 for GlobalTheory.HCXi.ConePolar.plane
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T03:44:25.987906+00:00
-- url     : https://prove2.me/submissions/967045ad-7424-42ba-88d9-3a2ddd73ca5e

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ThetaMetrics_IsKMeas
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_LintegralHyperboloidFibration
import Theorems.Thm_GlobalTheory_HCXi_ConePolar_angle_shift
import Theorems.Thm_GlobalTheory_HCXi_ConePolar_radial

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix MeasureTheory Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.B2 GlobalTheory.HCXi
open scoped ENNReal ComplexOrder
open GlobalTheory GlobalTheory.HCXi GlobalTheory.HCXi.ConePolar
namespace GlobalTheory.HCXi.ConePolar
theorem _root_.solution (a : ℝ) (ha : 0 ≤ a) (F : ℝ → ℝ≥0∞) (g : ℂ → ℝ≥0∞) (hF : Measurable F) (hg : Measurable g) :
    ∫⁻ z : ℂ, Set.indicator {z : ℂ | a < Complex.normSq z} (fun z => F (Complex.normSq z - a) * g z) z
      = (1 / 2 : ℝ≥0∞) * ∫⁻ τ in Set.Ioi (0 : ℝ), F τ * ∫⁻ θ in Set.Ioc 0 (2 * Real.pi),
          g (((Real.sqrt (a + τ) : ℝ) : ℂ) * Complex.exp (Complex.I * (θ : ℝ))) := by
  rw [← radial a ha F (fun ρ => ∫⁻ θ in Set.Ioc 0 (2 * Real.pi),
          g (((ρ : ℝ) : ℂ) * Complex.exp (Complex.I * (θ : ℝ)))),
    ← Complex.lintegral_comp_polarCoord_symm, polarCoord_target]
  have hsymm : ∀ p : ℝ × ℝ, Complex.polarCoord.symm p = (p.1 : ℂ) * Complex.exp (Complex.I * p.2) := by
    intro p
    rw [Complex.polarCoord_symm_apply, mul_comm Complex.I, Complex.exp_mul_I]
    simp
  have hn : ∀ ρ θ : ℝ, Complex.normSq ((ρ : ℂ) * Complex.exp (Complex.I * θ)) = ρ ^ 2 := by
    intro ρ θ
    rw [Complex.normSq_eq_norm_sq, norm_mul, Complex.norm_exp_I_mul_ofReal, mul_one,
      Complex.norm_real, Real.norm_eq_abs, sq_abs]
  have hm : Measurable (Set.indicator {z : ℂ | a < Complex.normSq z}
      (fun z => F (Complex.normSq z - a) * g z)) := by
    refine Measurable.indicator ?_ (measurableSet_lt measurable_const Complex.continuous_normSq.measurable)
    exact (hF.comp (Complex.continuous_normSq.measurable.sub_const a)).mul hg
  simp only [hsymm, smul_eq_mul]
  rw [Measure.volume_eq_prod, ← Measure.prod_restrict, lintegral_prod]
  swap
  · refine Measurable.aemeasurable ?_
    refine (measurable_fst.ennreal_ofReal).mul (hm.comp ?_)
    fun_prop
  have hsub : Set.Ioi (Real.sqrt a) = Set.Ioi (Real.sqrt a) ∩ Set.Ioi (0 : ℝ) := by
    rw [Set.Ioi_inter_Ioi, max_eq_left (Real.sqrt_nonneg a)]
  rw [hsub, ← Measure.restrict_restrict measurableSet_Ioi,
    ← lintegral_indicator (s := Set.Ioi (Real.sqrt a)) measurableSet_Ioi]
  refine setLIntegral_congr_fun measurableSet_Ioi fun ρ hρ => ?_
  have hρ0 : 0 < ρ := hρ
  simp only [Set.indicator, Set.mem_setOf_eq, hn, Set.mem_Ioi, Real.sqrt_lt' hρ0]
  split_ifs with h
  · have hmg : Measurable fun θ : ℝ => g ((ρ : ℂ) * Complex.exp (Complex.I * θ)) :=
      hg.comp (by fun_prop)
    rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top, lintegral_const_mul _ hmg, angle_shift]
    intro θ
    simp only
    congr 2
    push_cast
    rw [mul_add, Complex.exp_add, mul_comm Complex.I (2 * _), Complex.exp_two_pi_mul_I, mul_one]
  · simp
end GlobalTheory.HCXi.ConePolar
