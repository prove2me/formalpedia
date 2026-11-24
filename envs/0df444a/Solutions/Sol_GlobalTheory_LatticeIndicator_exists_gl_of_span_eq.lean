-- Prove2me | solution 1 for GlobalTheory.LatticeIndicator.exists_gl_of_span_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T19:26:00.44956+00:00
-- url     : https://prove2.me/submissions/40c8ab47-c52f-4a6f-9067-6b40bb350cdb

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_ExistsEqSumIndicatorOfRightInvariant
import Theorems.Thm_GlobalTheory_LatticeIndicator_exists_gl_of_span_eq_top

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
theorem _root_.solution {O Q n : Type*} [CommRing O] [IsLocalRing O] [AddCommGroup Q]
    [Module O Q] [Fintype n] [DecidableEq n] (a b : n → Q)
    (hab : Submodule.span O (Set.range a) = Submodule.span O (Set.range b)) :
    ∃ g : GL n O, ∀ j, a j = ∑ i, (g : Matrix n n O) i j • b i := by
  set S := Submodule.span O (Set.range b) with hS
  have hspan : ∀ (c : n → Q) (hc : Submodule.span O (Set.range c) = S),
      Submodule.span O (Set.range fun i =>
        (⟨c i, hc ▸ Submodule.subset_span ⟨i, rfl⟩⟩ : S)) = ⊤ := by
    intro c hc
    apply Submodule.map_injective_of_injective S.injective_subtype
    rw [Submodule.map_span, ← Set.range_comp, Submodule.map_top, Submodule.range_subtype]
    exact hc
  obtain ⟨g, hg⟩ := exists_gl_of_span_eq_top _ _ (hspan a hab) (hspan b rfl)
  exact ⟨g, fun j => by simpa using congrArg Subtype.val (hg j)⟩
end GlobalTheory.LatticeIndicator
