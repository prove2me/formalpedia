-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.Kloc.Fresnel.integral_gauss_kerOp
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T12:56:29.68712+00:00
-- url     : https://prove2.me/submissions/02573a7d-ee79-453c-98d9-4df3f3e2fb1c

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_FourierTransformMatrixSpaceInvolution
import Theorems.Thm_GlobalTheory_CompanionTheory_Kloc_Fresnel_inner_gaussian

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Complex
open scoped FourierTransform RealInnerProductSpace SchwartzMap Matrix
noncomputable section
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.Kloc GlobalTheory.CompanionTheory.Kloc.Fresnel
variable {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  [MeasurableSpace V] [BorelSpace V]
namespace GlobalTheory.CompanionTheory.Kloc.Fresnel
theorem _root_.solution (C : ℂ) (a : ℝ) (ha : a ≠ 0) (R : V ≃ₗᵢ[ℝ] V) {b : ℂ} (hb : 0 < b.re)
    (f : 𝓢(V, ℂ)) :
    ∫ t : V, cexp (-b * ((‖t‖ ^ 2 : ℝ) : ℂ)) * kerOp C a R f t =
      C * (Real.pi / b) ^ (Module.finrank ℝ V / 2 : ℂ) *
        ∫ v : V, f v * cexp (-((Real.pi : ℂ) ^ 2 * (a : ℂ) ^ 2 * ((‖v‖ ^ 2 : ℝ) : ℂ) / b)) := by
  have hG : Integrable (fun t : V => cexp (-b * ((‖t‖ ^ 2 : ℝ) : ℂ))) := by
    have := GaussianFourier.integrable_cexp_neg_mul_sq_norm_add (V := V) hb 0 0
    simpa using this
  have hf : Integrable (f : V → ℂ) := f.integrable
  have hF : Integrable (Function.uncurry fun (t v : V) => cexp (-b * ((‖t‖ ^ 2 : ℝ) : ℂ)) *
      (cexp (2 * Real.pi * I * ((a * ⟪t, R v⟫ : ℝ) : ℂ)) * f v)) (volume.prod volume) := by
    have base := Integrable.mul_prod hG hf
    refine base.mono ?_ (Filter.Eventually.of_forall fun p => ?_)
    · apply Continuous.aestronglyMeasurable
      have := f.continuous
      have hR := R.continuous
      simp only [Function.uncurry_def]
      fun_prop
    · have hK : ‖cexp (2 * Real.pi * I * ((a * ⟪p.1, R p.2⟫ : ℝ) : ℂ))‖ = 1 := by
        have : (2 * Real.pi * I * ((a * ⟪p.1, R p.2⟫ : ℝ) : ℂ)) =
            ((2 * Real.pi * (a * ⟪p.1, R p.2⟫) : ℝ) : ℂ) * I := by push_cast; ring
        rw [this, Complex.norm_exp_ofReal_mul_I]
      simp only [Function.uncurry_def, norm_mul, hK, one_mul, le_refl]
  calc ∫ t : V, cexp (-b * ((‖t‖ ^ 2 : ℝ) : ℂ)) * kerOp C a R f t
      = C * ∫ t : V, ∫ v : V, cexp (-b * ((‖t‖ ^ 2 : ℝ) : ℂ)) *
          (cexp (2 * Real.pi * I * ((a * ⟪t, R v⟫ : ℝ) : ℂ)) * f v) := by
        rw [← integral_const_mul]
        refine integral_congr_ae (Filter.Eventually.of_forall fun t => ?_)
        simp only [kerOp]
        rw [integral_const_mul]
        ring
    _ = C * ∫ v : V, ∫ t : V, cexp (-b * ((‖t‖ ^ 2 : ℝ) : ℂ)) *
          (cexp (2 * Real.pi * I * ((a * ⟪t, R v⟫ : ℝ) : ℂ)) * f v) := by
        rw [integral_integral_swap hF]
    _ = C * ∫ v : V, (Real.pi / b) ^ (Module.finrank ℝ V / 2 : ℂ) *
          (f v * cexp (-((Real.pi : ℂ) ^ 2 * (a : ℂ) ^ 2 * ((‖v‖ ^ 2 : ℝ) : ℂ) / b))) := by
        congr 1
        refine integral_congr_ae (Filter.Eventually.of_forall fun v => ?_)
        have e : ∀ t : V, cexp (-b * ((‖t‖ ^ 2 : ℝ) : ℂ)) *
            (cexp (2 * Real.pi * I * ((a * ⟪t, R v⟫ : ℝ) : ℂ)) * f v) =
            (cexp (-b * ((‖t‖ ^ 2 : ℝ) : ℂ)) *
              cexp (2 * Real.pi * I * ((a * ⟪t, R v⟫ : ℝ) : ℂ))) * f v := fun t => by ring
        simp only [e]
        rw [integral_mul_const, inner_gaussian a R hb v]
        ring
    _ = _ := by
        rw [integral_const_mul]
        ring
end GlobalTheory.CompanionTheory.Kloc.Fresnel
