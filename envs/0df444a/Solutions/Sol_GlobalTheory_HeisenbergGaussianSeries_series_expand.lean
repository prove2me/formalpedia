-- Prove2me | solution 1 for GlobalTheory.HeisenbergGaussianSeries.series_expand
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T17:26:14.453642+00:00
-- url     : https://prove2.me/submissions/ea6c7009-c189-46e2-b9b0-e7215680be7d

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_ExpSeriesContDiffAndHasDerivAt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_CharSeriesExistsNeZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_SummableGaussianCoset
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_ExistsPosMulNormSqLe
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_ContinuousBicharacterWeilSetup

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped ContDiff
open GlobalTheory GlobalTheory.HeisenbergGaussianSeries
variable {G V : Type} [AddCommGroup G] [AddCommGroup V] [Module ℝ V]
    {p : G →+ V} {ι : V →+ G} {β : G → G → ℂ} {om : V →ₗ[ℝ] V →ₗ[ℝ] ℝ} {J : V →ₗ[ℝ] V}
    {Γ : AddSubgroup G} {χ : G → ℂ}
namespace GlobalTheory.HeisenbergGaussianSeries
theorem _root_.solution (hp : ∀ v, p (ι v) = v)
    (hl : ∀ x y z, β (x + y) z = β x z * β y z) (hr : ∀ x y z, β x (y + z) = β x y * β x z)
    (hβ : ∀ x v, β x (ι v) = Complex.exp (-(Real.pi * Complex.I) * (om (p x) v : ℝ)))
    (hsym : ∀ x y, om x (J y) = om y (J x)) (hχ : ∀ x v, χ (x + ι v) = χ x)
    (M : V → V → ℂ)
    (hM : ∀ y v, M y v = -(Real.pi : ℂ) * (Complex.I * (om y v : ℝ) + (om y (J v) : ℝ)))
    (a : V) (w : G) (v : V) :
    β w (ι v) * series p ι β om J Γ χ a (w + ι v) =
      Complex.exp (-(Real.pi / 2 : ℂ) * (om v (J v) : ℝ)) *
      ∑' g : Γ, (β g w * β (ι a) (g + w) * χ (g + w) *
        Complex.exp (-(Real.pi / 2 : ℂ) * (om (p g + (a + p w)) (J (p g + (a + p w))) : ℝ))) *
        Complex.exp (M (p g + (a + p w)) v) := by
  unfold series
  rw [← tsum_mul_left, ← tsum_mul_left]
  refine tsum_congr fun g => ?_
  have e1 : p g + (a + p (w + ι v)) = (p g + (a + p w)) + v := by rw [map_add, hp]; abel
  have e2 : β w (ι v) * β g (ι v) * β (ι a) (ι v) =
      Complex.exp (-(Real.pi * Complex.I) * (om (p g + (a + p w)) v : ℝ)) := by
    rw [← hl, ← hl, hβ, map_add p, map_add p, hp]
    congr 5; abel
  rw [e1, ← add_assoc (g : G) w, hχ, hr (ι a) (g + w), hr g w, hM]
  set y := p g + (a + p w)
  have e3 : Complex.exp (-(Real.pi * Complex.I) * (om y v : ℝ)) *
      Complex.exp (-(Real.pi / 2 : ℂ) * (om (y + v) (J (y + v)) : ℝ)) =
      Complex.exp (-(Real.pi / 2 : ℂ) * (om v (J v) : ℝ)) *
      Complex.exp (-(Real.pi / 2 : ℂ) * (om y (J y) : ℝ)) *
      Complex.exp (-(Real.pi : ℂ) * (Complex.I * (om y v : ℝ) + (om y (J v) : ℝ))) := by
    rw [← Complex.exp_add, ← Complex.exp_add, ← Complex.exp_add]
    congr 1
    simp only [map_add, LinearMap.add_apply, hsym v y]
    push_cast; ring
  linear_combination (β g w * β (ι a) (g + w) * χ (g + w) *
      Complex.exp (-(Real.pi / 2 : ℂ) * (om (y + v) (J (y + v)) : ℝ))) * e2 +
    (β g w * β (ι a) (g + w) * χ (g + w)) * e3
end GlobalTheory.HeisenbergGaussianSeries
