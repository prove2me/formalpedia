-- Prove2me | solution 2 for MTT.Cohomology.integration_map_exists
-- status  : ACCEPTED   (prove)
-- author  : @allychan327
-- created : 2026-09-07T04:34:03.989784+00:00
-- url     : https://prove2.me/submissions/d39269ba-615a-47f9-af7d-269d0d4da6e3

import Definitions.Def_MTT_Cohomology
import Mathlib.RingTheory.Flat.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Theorems.Thm_MTT_modularIntegral_integrable
import Theorems.Thm_MTT_Cohomology_integral_class_exists
import Theorems.Thm_MTT_Cohomology_integral_class_hecke
import Theorems.Thm_MTT_Cohomology_integral_class_unique

set_option autoImplicit false
set_option maxHeartbeats 800000
noncomputable section
open scoped BigOperators TensorProduct
open MTT.Cohomology

namespace P2MIE

variable {N k : ℕ}

/-- The modular integral is additive in the cusp form, because the integrand is. -/
theorem mi_add (hN : 0 < N) (hk : 2 ≤ k) (f g : CuspForm (MTT.GammaOne N) (k : ℤ))
    (P : Polynomial ℂ) (r : ℚ) :
    MTT.modularIntegral ((f + g : CuspForm (MTT.GammaOne N) (k : ℤ)) : UpperHalfPlane → ℂ) P r
      = MTT.modularIntegral f P r + MTT.modularIntegral g P r := by
  have hf := MTT.modularIntegral_integrable hN hk f P r
  have hg := MTT.modularIntegral_integrable hN hk g P r
  have hpt : ∀ t : ℝ,
      (f + g) (UpperHalfPlane.ofComplex ((r : ℂ) + Complex.I * t)) *
          P.eval ((r : ℂ) + Complex.I * t)
        = f (UpperHalfPlane.ofComplex ((r : ℂ) + Complex.I * t)) *
            P.eval ((r : ℂ) + Complex.I * t)
          + g (UpperHalfPlane.ofComplex ((r : ℂ) + Complex.I * t)) *
            P.eval ((r : ℂ) + Complex.I * t) := by
    intro t
    show (f _ + g _) * _ = _
    ring
  unfold MTT.modularIntegral
  rw [← mul_add, ← MeasureTheory.integral_add hf hg]
  congr 1
  exact MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall hpt)

/-- The modular integral is homogeneous in the cusp form. -/
theorem mi_smul (c : ℂ) (f : CuspForm (MTT.GammaOne N) (k : ℤ))
    (P : Polynomial ℂ) (r : ℚ) :
    MTT.modularIntegral ((c • f : CuspForm (MTT.GammaOne N) (k : ℤ)) : UpperHalfPlane → ℂ) P r
      = c * MTT.modularIntegral f P r := by
  have hpt : ∀ t : ℝ,
      (c • f) (UpperHalfPlane.ofComplex ((r : ℂ) + Complex.I * t)) *
          P.eval ((r : ℂ) + Complex.I * t)
        = c * (f (UpperHalfPlane.ofComplex ((r : ℂ) + Complex.I * t)) *
            P.eval ((r : ℂ) + Complex.I * t)) := by
    intro t
    show (c * f _) * _ = _
    ring
  unfold MTT.modularIntegral
  rw [MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall hpt),
    MeasureTheory.integral_const_mul]
  ring

end P2MIE

open P2MIE in
theorem solution {N k : ℕ} (hN : 0 < N) (hk : 2 ≤ k) :
    ∃ I : CuspForm (MTT.GammaOne N) (k : ℤ) →ₗ[ℂ] Hc N (k - 2) ℂ,
      HeckeEquivariant I ∧ ∀ f, IntegralClass f (I f) := by
  choose Φ hΦ using fun f : CuspForm (MTT.GammaOne N) (k : ℤ) =>
    MTT.Cohomology.integral_class_exists hN hk f
  have hadd : ∀ f g, Φ (f + g) = Φ f + Φ g := by
    intro f g
    refine MTT.Cohomology.integral_class_unique (f + g) _ _ (hΦ (f + g)) ?_
    intro j r hj
    rw [map_add, hΦ f j r hj, hΦ g j r hj, mi_add hN hk f g, mul_add]
  have hsmul : ∀ (c : ℂ) f, Φ (c • f) = c • Φ f := by
    intro c f
    refine MTT.Cohomology.integral_class_unique (c • f) _ _ (hΦ (c • f)) ?_
    intro j r hj
    rw [map_smul, hΦ f j r hj, mi_smul c f, smul_eq_mul]
    ring
  refine ⟨{ toFun := Φ, map_add' := hadd, map_smul' := fun c f => hsmul c f }, ?_, hΦ⟩
  intro e l hl f g hg
  exact MTT.Cohomology.integral_class_hecke hN hk e l hl f g hg (Φ f) (Φ g) (hΦ f) (hΦ g)
