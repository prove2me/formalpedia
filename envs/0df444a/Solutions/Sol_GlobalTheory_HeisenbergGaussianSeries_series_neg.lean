-- Prove2me | solution 1 for GlobalTheory.HeisenbergGaussianSeries.series_neg
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T17:26:16.415028+00:00
-- url     : https://prove2.me/submissions/ab39aa36-02aa-4dab-b90e-d8ada18dd19d

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
theorem _root_.solution (hp : ∀ v, p (ι v) = v)
    (hl : ∀ x y z, β (x + y) z = β x z * β y z) (hr : ∀ x y z, β x (y + z) = β x y * β x z)
    (hd : ∀ x, β x x = 1)
    (hβ : ∀ x v, β x (ι v) = Complex.exp (-(Real.pi * Complex.I) * (om (p x) v : ℝ)))
    (halt : ∀ v, om v v = 0) (hχ : ∀ x v, χ (x + ι v) = χ x) (a : V) :
    series p ι β om J Γ χ a (ι (-a)) =
      ∑' g : Γ, (χ g * Complex.exp (-(Real.pi / 2 : ℂ) * (om (p g) (J (p g)) : ℝ))) *
        Complex.exp (2 * Real.pi * Complex.I * (om (p g) a : ℝ)) := by
  unfold series
  refine tsum_congr fun g => ?_
  have h1 : β (ι a) g = Complex.exp (Real.pi * Complex.I * (om (p g) a : ℝ)) := by
    have := swap_mul β hl hr hd (ι a) g
    rw [hβ g a] at this
    rw [eq_inv_of_mul_eq_one_left this, ← Complex.exp_neg]
    congr 1; ring
  have h2 : Complex.exp (2 * Real.pi * Complex.I * (om (p g) a : ℝ)) =
      Complex.exp (Real.pi * Complex.I * (om (p g) a : ℝ)) *
      Complex.exp (Real.pi * Complex.I * (om (p g) a : ℝ)) := by
    rw [← Complex.exp_add]; congr 1; ring
  rw [hχ, hr, h1, h2, hβ, hβ, hp, hp, add_neg_cancel, add_zero]
  simp [halt]
  ring
end GlobalTheory.HeisenbergGaussianSeries
