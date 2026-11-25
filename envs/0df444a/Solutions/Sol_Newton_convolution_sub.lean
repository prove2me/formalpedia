-- Prove2me | solution 1 for Newton.convolution_sub
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T01:11:49.857435+00:00
-- url     : https://prove2.me/submissions/eaea08b1-9813-4967-a979-aa5a3310ae64

import Mathlib.Analysis.Convolution
import Mathlib.MeasureTheory.Function.LpSeminorm.Basic
import Mathlib.MeasureTheory.Group.Measure
import Mathlib.MeasureTheory.Measure.Haar.Basic
import Definitions.Def_Newton_Analysis_Convolution_Basic
import Definitions.Def_Newton_Analysis_Convolution_Minkowski
import Definitions.Def_Newton_Analysis_Convolution_Bounds

set_option autoImplicit false
open MeasureTheory Complex NNReal
open scoped ENNReal ContDiff Pointwise
open Newton
variable {n : ℕ}
namespace Newton
theorem _root_.solution
    (f₁ f₂ g : (Fin n → ℝ) → ℂ)
    (hconv₁ : ∀ᵐ x ∂volume, Integrable (fun y => f₁ (x - y) * g y) volume)
    (hconv₂ : ∀ᵐ x ∂volume, Integrable (fun y => f₂ (x - y) * g y) volume) :
    (fun x => ∫ a, (f₁ (x - a) - f₂ (x - a)) * g a) =ᶠ[ae volume]
    (fun x => (∫ a, f₁ (x - a) * g a) - ∫ a, f₂ (x - a) * g a) := by
  have h_ae_both : ∀ᵐ x ∂volume, Integrable (fun a => f₁ (x - a) * g a) volume ∧
                                    Integrable (fun a => f₂ (x - a) * g a) volume := by
    filter_upwards [hconv₁, hconv₂] with x h₁ h₂
    exact ⟨h₁, h₂⟩
  filter_upwards [h_ae_both] with x ⟨hint₁, hint₂⟩
  have h₁ :
      ∫ a, (f₁ (x - a) - f₂ (x - a)) * g a =
        ∫ a, f₁ (x - a) * g a - f₂ (x - a) * g a := by
    simp [sub_mul]
  have h₂ :
      ∫ a, f₁ (x - a) * g a - f₂ (x - a) * g a =
        (∫ a, f₁ (x - a) * g a) - ∫ a, f₂ (x - a) * g a := by
    simpa using integral_sub hint₁ hint₂
  exact h₁.trans h₂
end Newton
