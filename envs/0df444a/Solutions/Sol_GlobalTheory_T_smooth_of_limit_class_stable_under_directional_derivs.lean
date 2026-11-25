-- Prove2me | solution 1 for GlobalTheory.T.smooth_of_limit_class_stable_under_directional_derivs
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T18:26:34.207289+00:00
-- url     : https://prove2.me/submissions/68f2dabf-1d29-426f-9b9f-0381ef8073f5

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_SmoothOfLimitClassStableUnderDirectionalDerivs
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_DifferentiableAtLimitOfDirectionalDerivsConvergeStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_SmoothOfLimitClassStableUnderDirectionalDerivsStatement
import Theorems.Thm_GlobalTheory_contDiff_of_class_tendstoLocallyUniformly


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
theorem _root_.solution : ∀ {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] {A : Type} [Fintype A] (v : A → E) (c : A → E →L[ℝ] ℝ), (∀ x, ∑ a, c a x • v a = x) → ∀ P : (E → ℂ) → Prop, (∀ φ, P φ → ∃ g : ℕ → E → ℂ, (∀ j, Differentiable ℝ (g j)) ∧ TendstoLocallyUniformly g φ Filter.atTop ∧ ∀ a, ∃ α : E → ℂ, ContDiff ℝ ∞ α ∧ ∃ χ, P χ ∧ TendstoLocallyUniformly (fun j y => fderiv ℝ (g j) y (v a)) (fun y => α y * φ y + χ y) Filter.atTop) → ∀ φ, P φ → ContDiff ℝ ∞ φ := by
  first | exact @GlobalTheory.contDiff_of_class_tendstoLocallyUniformly | exact GlobalTheory.contDiff_of_class_tendstoLocallyUniformly | (intros; apply GlobalTheory.contDiff_of_class_tendstoLocallyUniformly <;> assumption)
end _root_.GlobalTheory.T
