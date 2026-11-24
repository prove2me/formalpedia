-- Prove2me | solution 1 for GlobalTheory.HeisenbergGaussianSeries.series_inv
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T17:26:15.522009+00:00
-- url     : https://prove2.me/submissions/b76b7a22-4c59-49bc-b2a0-5420dcbfe114

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_ExpSeriesContDiffAndHasDerivAt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_CharSeriesExistsNeZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_SummableGaussianCoset
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_ExistsPosMulNormSqLe
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_ContinuousBicharacterWeilSetup
import Theorems.Thm_GlobalTheory_HeisenbergGaussianSeries_swap_mul

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
theorem _root_.solution
    (hl : ∀ x y z, β (x + y) z = β x z * β y z) (hr : ∀ x y z, β x (y + z) = β x y * β x z)
    (hd : ∀ x, β x x = 1)
    (hβ : ∀ x v, β x (ι v) = Complex.exp (-(Real.pi * Complex.I) * (om (p x) v : ℝ)))
    (a : V) (u : G) (hu : p u = 0) (hχ : ∀ x, β x u * χ (x + u) = χ x) (w : G) :
    β w u * series p ι β om J Γ χ a (w + u) = series p ι β om J Γ χ a w := by
  unfold series
  rw [← tsum_mul_left]
  refine tsum_congr fun g => ?_
  have h1 : β (ι a) u = 1 := by
    have := swap_mul β hl hr hd (ι a) u
    rw [hβ u a, hu] at this
    simpa using this
  rw [← hχ (g + w), ← add_assoc (g : G) w u, hr (ι a) (g + w) u, h1, hr g w u, hl g w u,
    map_add p w u, hu,
    add_zero]
  ring
end GlobalTheory.HeisenbergGaussianSeries
