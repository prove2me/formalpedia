-- Prove2me | solution 1 for ModularCurve.periodAlongOf_apply_eq_sub_of_hasDerivAt
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.280726+00:00
-- url     : https://prove2.me/submissions/5d47339f-2910-59c2-b81f-bfcf74614847

import Mathlib
import Definitions.Def_ModularCurve_PeriodOf
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_periodAlongOf_apply_eq_sub_of_hasDerivAt

set_option autoImplicit false

open UpperHalfPlane
open scoped MatrixGroups

namespace ModularCurve
p2m_export "ModularCurve" "periodAlongOf periodAlongOf_apply clamp01 segmentPoint segmentPoint_im_pos continuous_segmentPoint segmentPath periodAlong period"
namespace Ws49
namespace PeriodPathOf
p2m_open "ModularCurve"

p2m_open "ModularCurve P2MW.S_ModularCurve_periodAlongOf_apply_eq_sub_of_hasDerivAt.ModularCurve"

theorem continuous_segmentPoint (τ₀ τ₁ : ℍ) : Continuous fun t : ℝ => segmentPoint τ₀ τ₁ t := by
  unfold segmentPoint clamp01
  fun_prop

theorem continuous_comp_segmentPoint (τ₀ τ₁ : ℍ) {H : ℂ → ℂ}
    (hH : ∀ τ : ℍ, ContinuousAt H (τ : ℂ)) :
    Continuous fun t : ℝ => H (segmentPoint τ₀ τ₁ t) :=
  continuous_iff_continuousAt.2 fun t =>
    ContinuousAt.comp (f := fun s : ℝ => segmentPoint τ₀ τ₁ s) (x := t)
      (hH ⟨segmentPoint τ₀ τ₁ t, segmentPoint_im_pos τ₀ τ₁ t⟩)
      (continuous_segmentPoint τ₀ τ₁).continuousAt

theorem hasDerivAt_segmentPoint (τ₀ τ₁ : ℍ) {t : ℝ} (ht : t ∈ Set.Ioo (0 : ℝ) 1) :
    HasDerivAt (fun s : ℝ => segmentPoint τ₀ τ₁ s) ((τ₁ : ℂ) - τ₀) t := by
  have haff : HasDerivAt (fun s : ℝ => (τ₀ : ℂ) + (s : ℂ) * ((τ₁ : ℂ) - τ₀)) ((τ₁ : ℂ) - τ₀) t := by
    have h1 : HasDerivAt (fun s : ℝ => (s : ℂ)) 1 t := (hasDerivAt_id t).ofReal_comp
    simpa using (h1.mul_const ((τ₁ : ℂ) - τ₀)).const_add (τ₀ : ℂ)
  refine haff.congr_of_eventuallyEq ?_
  filter_upwards [Ioo_mem_nhds ht.1 ht.2] with s hs
  have hc : clamp01 s = s := by
    unfold clamp01
    rw [min_eq_left hs.2.le, max_eq_right hs.1.le]
  simp only [segmentPoint, hc, Complex.real_smul]
  push_cast
  ring

theorem segmentPoint_zero (τ₀ τ₁ : ℍ) : segmentPoint τ₀ τ₁ 0 = (τ₀ : ℂ) := by
  simp [segmentPoint, clamp01]

theorem segmentPoint_one (τ₀ τ₁ : ℍ) : segmentPoint τ₀ τ₁ 1 = (τ₁ : ℂ) := by
  simp [segmentPoint, clamp01]

theorem periodAlongOf_apply_eq_sub_of_hasDerivAt (Γ : Subgroup SL(2, ℤ))
    (f : CuspForm Γ 2) {F : ℍ → ℂ}
    (hF : ∀ τ : ℍ, HasDerivAt (F ∘ ofComplex) (f τ) (τ : ℂ)) (τ₀ τ₁ : ℍ) :
    periodAlongOf Γ τ₀ τ₁ f = F τ₁ - F τ₀ := by
  rw [periodAlongOf_apply]

  set g : ℝ → ℂ := (F ∘ ofComplex) ∘ fun s : ℝ => segmentPoint τ₀ τ₁ s with hg
  have hderiv : ∀ t ∈ Set.Ioo (0 : ℝ) 1,
      HasDerivAt g (f (segmentPath τ₀ τ₁ t) * ((τ₁ : ℂ) - τ₀)) t := fun t ht =>
    HasDerivAt.comp t (hF (segmentPath τ₀ τ₁ t)) (hasDerivAt_segmentPoint τ₀ τ₁ ht)
  have hcont : Continuous g :=
    continuous_comp_segmentPoint τ₀ τ₁ fun τ => (hF τ).continuousAt

  have hfcont : ∀ τ : ℍ, ContinuousAt (⇑f ∘ ofComplex) (τ : ℂ) := fun τ =>
    (UpperHalfPlane.mdifferentiableAt_iff.mp (CuspFormClass.holo f τ)).continuousAt
  have hint : IntervalIntegrable (fun t : ℝ => f (segmentPath τ₀ τ₁ t) * ((τ₁ : ℂ) - τ₀))
      MeasureTheory.volume 0 1 := by
    refine (Continuous.mul ?_ continuous_const).intervalIntegrable 0 1
    have heq : (fun t : ℝ => f (segmentPath τ₀ τ₁ t)) =
        fun t : ℝ => (⇑f ∘ ofComplex) (segmentPoint τ₀ τ₁ t) := by
      funext t
      simp only [Function.comp_apply, ofComplex_apply_of_im_pos (segmentPoint_im_pos τ₀ τ₁ t)]
      rfl
    rw [heq]
    exact continuous_comp_segmentPoint τ₀ τ₁ hfcont
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le zero_le_one hcont.continuousOn hderiv hint,
    hg]
  simp only [Function.comp_apply, segmentPoint_zero, segmentPoint_one, ofComplex_apply]

end ModularCurve.Ws49.PeriodPathOf

theorem solution (Γ : Subgroup SL(2, ℤ))
    (f : CuspForm Γ 2) {F : UpperHalfPlane → ℂ}
    (hF : ∀ τ : UpperHalfPlane, HasDerivAt (F ∘ ofComplex) (f τ) (τ : ℂ)) (τ₀ τ₁ : UpperHalfPlane) :
    ModularCurve.periodAlongOf Γ τ₀ τ₁ f = F τ₁ - F τ₀ :=
  ModularCurve.Ws49.PeriodPathOf.periodAlongOf_apply_eq_sub_of_hasDerivAt Γ f hF τ₀ τ₁

end S_ModularCurve_periodAlongOf_apply_eq_sub_of_hasDerivAt
end P2MW
export P2MW.S_ModularCurve_periodAlongOf_apply_eq_sub_of_hasDerivAt (solution)
