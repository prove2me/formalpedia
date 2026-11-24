-- Prove2me | solution 1 for GlobalTheory.HeisenbergGaussianSeries.series_quasi
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T17:26:17.448994+00:00
-- url     : https://prove2.me/submissions/eb8f6066-d110-4d7a-af50-2353e7ce2d0e

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
theorem _root_.solution
    (hl : ∀ x y z, β (x + y) z = β x z * β y z) (hr : ∀ x y z, β x (y + z) = β x y * β x z)
    (hΓ : ∀ g ∈ Γ, ∀ g' ∈ Γ, β g g' = 1) (a : V) (g₀ : G) (hg₀ : g₀ ∈ Γ) (w : G) :
    β g₀ w * series p ι β om J Γ χ a (g₀ + w) = series p ι β om J Γ χ a w := by
  unfold series
  rw [← tsum_mul_left]
  refine Eq.trans ?_ ((Equiv.addRight (⟨g₀, hg₀⟩ : Γ)).tsum_eq _)
  refine tsum_congr fun g => ?_
  have e1 : p g + (a + p (g₀ + w)) = p (g + g₀) + (a + p w) := by simp only [map_add]; abel
  simp only [Equiv.coe_addRight, AddSubgroup.coe_add]
  rw [e1, hr g g₀ w, hΓ g g.2 g₀ hg₀, hl g g₀ w, add_assoc (g : G) g₀ w]
  ring
end GlobalTheory.HeisenbergGaussianSeries
