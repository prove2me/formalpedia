-- Prove2me | solution 1 for GlobalTheory.LatticeIndicator.exists_matrix_of_span_eq_top_field
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T18:53:16.241222+00:00
-- url     : https://prove2.me/submissions/06f6f2d8-3aed-4022-aedd-7fb9c81b5d6a

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_ExistsEqSumIndicatorOfRightInvariant
import Theorems.Thm_GlobalTheory_LatticeIndicator_exists_injective_comp_eq_of_surjective

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix
open GlobalTheory
open GlobalTheory.LatticeIndicator
namespace GlobalTheory.LatticeIndicator
theorem _root_.solution {k W n : Type*} [Field k] [AddCommGroup W] [Module k W]
    [Fintype n] [DecidableEq n] (a b : n → W) (ha : Submodule.span k (Set.range a) = ⊤)
    (hb : Submodule.span k (Set.range b) = ⊤) :
    ∃ g : Matrix n n k, g.det ≠ 0 ∧ ∀ j, a j = ∑ i, g i j • b i := by
  obtain ⟨e, he, hge⟩ := exists_injective_comp_eq_of_surjective
    (Fintype.linearCombination k a) (Fintype.linearCombination k b)
    (by rw [← LinearMap.range_eq_top, Fintype.range_linearCombination, ha])
    (by rw [← LinearMap.range_eq_top, Fintype.range_linearCombination, hb])
  refine ⟨LinearMap.toMatrix' e, ?_, fun j => ?_⟩
  · rw [LinearMap.det_toMatrix']
    exact ((LinearMap.isUnit_iff_isUnit_det e).1
      ((LinearMap.isUnit_iff_ker_eq_bot e).2 (LinearMap.ker_eq_bot.2 he))).ne_zero
  · have := LinearMap.congr_fun hge (Pi.single j 1)
    rw [Fintype.linearCombination_apply_single, one_smul] at this
    rw [← this]
    simp [Fintype.linearCombination_apply, LinearMap.toMatrix'_apply]
end GlobalTheory.LatticeIndicator
