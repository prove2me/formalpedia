-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.SiegelND.Integ.Weyl.enorm_sq_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T14:04:04.221501+00:00
-- url     : https://prove2.me/submissions/8aac5b3c-c906-42ee-8f1b-51121a84566e

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_SecondCountableHermC
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_ContinuousSeminormDiffSLe
import Theorems.Thm_GlobalTheory_CompanionTheory_SiegelND_Integ_Weyl_diffS_apply
import Theorems.Thm_GlobalTheory_CompanionTheory_SiegelND_Integ_Weyl_ee_add
import Theorems.Thm_GlobalTheory_CompanionTheory_SiegelND_Integ_Weyl_norm_ee
import Theorems.Thm_GlobalTheory_CompanionTheory_SiegelND_Integ_Weyl_conj_ee
import Theorems.Thm_GlobalTheory_CompanionTheory_SiegelND_Integ_Weyl_continuous_ee

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.SiegelND GlobalTheory.CompanionTheory.SiegelND.Integ GlobalTheory.CompanionTheory.SiegelND.Integ.Weyl
open MeasureTheory
open scoped ComplexConjugate FourierTransform
variable {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  [MeasurableSpace V] [BorelSpace V]
namespace GlobalTheory.CompanionTheory.SiegelND.Integ.Weyl
theorem _root_.solution (f : SchwartzMap V ℂ) (q : V → ℝ) (T : V →ₗ[ℝ] V) (hq : Continuous q)
    (hT : ∀ x y, q (x + y) = q x + q y + inner ℝ x (T y)) :
    ENNReal.ofReal (‖∫ x, f x * ee (q x)‖ ^ 2) ≤ ∫⁻ y, ‖𝓕 (diffS f y) (-(T y))‖ₑ := by
  set v : V → ℂ := fun x => f x * ee (q x) with hv
  set u : V → ℂ := fun x => conj (v x) with hu
  have hvc : Continuous v := f.continuous.mul (continuous_ee.comp hq)
  have hvi : Integrable v := by
    refine f.integrable.mono hvc.aestronglyMeasurable (ae_of_all _ fun x => ?_)
    simp [hv, norm_ee]
  have hui : Integrable u := by
    refine hvi.mono (Complex.continuous_conj.comp hvc).aestronglyMeasurable (ae_of_all _ fun x => ?_)
    simp [hu]
  have hh : Integrable (fun z : V × V => u z.1 * v z.2) (volume.prod volume) := hui.mul_prod hvi
  have mp := measurePreserving_prod_add (volume : Measure V) (volume : Measure V)
  set F : V × V → ℂ := fun z => u z.1 * v (z.1 + z.2) with hF
  have hFi : Integrable F (volume.prod volume) := mp.integrable_comp_of_integrable hh
  have e1 : ∫ z : V × V, u z.1 * v z.2 ∂(volume.prod volume) =
      ∫ z : V × V, F z ∂(volume.prod volume) := by
    conv_lhs => rw [← mp.map_eq]
    exact integral_map mp.measurable.aemeasurable (by rw [mp.map_eq]; exact hh.aestronglyMeasurable)
  have e2 : ∀ y : V, ∫ x, F (x, y) = ee (q y) * 𝓕 (diffS f y) (-(T y)) := by
    intro y
    rw [SchwartzMap.fourier_coe, Real.fourier_eq', ← integral_const_mul]
    refine integral_congr_ae (ae_of_all _ fun x => ?_)
    have hx : Complex.exp (((-2 * Real.pi * inner ℝ x (-(T y)) : ℝ) : ℂ) * Complex.I) =
        ee (inner ℝ x (T y)) := by
      rw [ee]
      congr 1
      rw [inner_neg_right]
      push_cast
      ring
    simp only [hF, hu, hv, hx, diffS_apply, smul_eq_mul, map_mul, conj_ee, hT x y, ee_add]
    have h1 : ee (-q x) * ee (q x) = 1 := by
      rw [← ee_add]; simp [ee]
    linear_combination (conj (f x) * f (x + y) * ee (q y) * ee (inner ℝ x (T y))) * h1
  have e3 : conj (∫ x, v x) * ∫ x, v x = ∫ y, ee (q y) * 𝓕 (diffS f y) (-(T y)) := by
    rw [← integral_conj, ← integral_prod_mul u v, e1, integral_prod_symm F hFi]
    exact integral_congr_ae (ae_of_all _ e2)
  have e4 : ENNReal.ofReal (‖∫ x, v x‖ ^ 2) = ‖conj (∫ x, v x) * ∫ x, v x‖ₑ := by
    rw [← ofReal_norm, norm_mul, Complex.norm_conj, sq]
  rw [e4, e3]
  refine (enorm_integral_le_lintegral_enorm _).trans (le_of_eq ?_)
  refine lintegral_congr fun y => ?_
  rw [enorm_mul, ← ofReal_norm (ee _), norm_ee]
  simp
end GlobalTheory.CompanionTheory.SiegelND.Integ.Weyl
