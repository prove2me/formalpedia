-- Prove2me | solution 1 for GlobalTheory.T.differentiableAt_limit_of_directional_derivs_converge
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T23:49:48.087104+00:00
-- url     : https://prove2.me/submissions/ae35cc6c-35ed-4e03-aff3-2b7a773e6548

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_DifferentiableAtLimitOfDirectionalDerivsConverge
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_DifferentiableAtLimitOfDirectionalDerivsConvergeStatement
import Theorems.Thm_GlobalTheory_differentiableAt_of_tendstoLocallyUniformly_directional


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped ContDiff Topology
set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] {A : Type} [Fintype A] (v : A → E) (c : A → E →L[ℝ] ℝ), (∀ x, ∑ a, c a x • v a = x) → ∀ (φ : E → ℂ) (g : ℕ → E → ℂ) (ψ : A → E → ℂ), (∀ j, Differentiable ℝ (g j)) → TendstoLocallyUniformly g φ Filter.atTop → (∀ a, TendstoLocallyUniformly (fun j y => fderiv ℝ (g j) y (v a)) (ψ a) Filter.atTop) → ∀ y, DifferentiableAt ℝ φ y ∧ ∀ a, fderiv ℝ φ y (v a) = ψ a y := by
  first | exact @GlobalTheory.differentiableAt_of_tendstoLocallyUniformly_directional | exact GlobalTheory.differentiableAt_of_tendstoLocallyUniformly_directional | (intros; apply GlobalTheory.differentiableAt_of_tendstoLocallyUniformly_directional <;> assumption)
end _root_.GlobalTheory.T
