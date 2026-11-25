-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.SW.selfDual_real_coord
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T17:34:52.640149+00:00
-- url     : https://prove2.me/submissions/d1bb5ef7-d35f-4b63-8b05-388da553cbc9

import Mathlib
import Definitions.Def_CompanionTheory_SpectralGeometry_CountingDefinitions_AdelicEulerProducts_IsEulerProd
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_LebesgueSelfdualForDotCharacter
import Theorems.Thm_GlobalTheory_CompanionTheory_SW_RealFourier_inversion_neg

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.SW
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix
namespace GlobalTheory.CompanionTheory.SW
theorem _root_.solution : ∀ (ι : Type) [Fintype ι] (ε : ℝ), ε = 1 ∨ ε = -1 →
    SelfDual (volume : Measure (ι → ℝ))
      (fun x y => Complex.exp (2 * Real.pi * Complex.I * (ε * (x ⬝ᵥ y) : ℝ))) := by
  intro ι _ ε hε
  refine ⟨inferInstance, fun Φ hc hs hi z => ?_⟩
  rcases hε with rfl | rfl
  ·
    have hG : ∀ y : ι → ℝ, (∫ x : ι → ℝ,
        Φ x * Complex.exp (2 * Real.pi * Complex.I * (((1 : ℝ) * (x ⬝ᵥ y) : ℝ) : ℝ))) =
        ∫ x : ι → ℝ, (fun u => Φ (-u)) x *
          Complex.exp (2 * Real.pi * Complex.I * (((-1 : ℝ) * (x ⬝ᵥ y) : ℝ) : ℝ)) := by
      intro y
      rw [← integral_neg_eq_self (fun x : ι → ℝ =>
        Φ x * Complex.exp (2 * Real.pi * Complex.I * (((1 : ℝ) * (x ⬝ᵥ y) : ℝ) : ℝ))) volume]
      refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
      simp
    have hc' : Continuous fun u : ι → ℝ => Φ (-u) := hc.comp continuous_neg
    have hs' : HasCompactSupport fun u : ι → ℝ => Φ (-u) :=
      hs.comp_homeomorph (Homeomorph.neg (ι → ℝ))
    have hi' : Integrable (fun y : ι → ℝ => ∫ x : ι → ℝ, (fun u => Φ (-u)) x *
        Complex.exp (2 * Real.pi * Complex.I * (((-1 : ℝ) * (x ⬝ᵥ y) : ℝ) : ℝ))) volume :=
      hi.congr (Filter.Eventually.of_forall hG)
    have key := RealFourier.inversion_neg ι (fun u => Φ (-u)) hc' hs' hi' (-z)
    simp only [neg_neg] at key
    rw [← key]
    refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
    simp only [hG y]
    simp
  · exact RealFourier.inversion_neg ι Φ hc hs hi z
end GlobalTheory.CompanionTheory.SW
