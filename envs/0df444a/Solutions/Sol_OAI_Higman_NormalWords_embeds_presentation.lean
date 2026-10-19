-- Prove2me | solution 1 for OAI.Higman.NormalWords.embeds_presentation
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-18T19:47:18.546421+00:00
-- url     : https://prove2.me/submissions/dd7ccc64-99ba-4faa-930b-b6967575bc91

import Mathlib
import Definitions.Def_OAIQWUFI000
import Theorems.Thm_OAI_Higman_NormalWords_benign_normalClosure
import Theorems.Thm_OAI_Higman_embeds_of_benign_kernel

section
-- module Solutions.OAIQW_UniversalFInfinity.HigmanEmbedding
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe u v w x

noncomputable section

namespace Higman.NormalWords

theorem embeds_presentation_oai (r : ℕ → Raw) (hr : Computable r) :
    ∃ (K : Type) (_ : Group K) (_ : Group.IsFinitelyPresented K)
      (i : PresentedGroup (Set.range (fun n ↦ FreeGroup.mk (r n))) →* K),
      Function.Injective i := by
  apply embeds_of_benign_kernel (PresentedGroup.mk _) (PresentedGroup.mk_surjective _)
  have he : (PresentedGroup.mk (Set.range (fun n ↦ FreeGroup.mk (r n)))).ker =
      Subgroup.normalClosure (Set.range (fun n ↦ FreeGroup.mk (r n))) := by
    ext g
    exact PresentedGroup.mk_eq_one_iff
  rw [he]
  exact benign_normalClosure r hr

end Higman.NormalWords

end

end OAI
end

theorem solution : type_of% @OAI.Higman.NormalWords.embeds_presentation_oai := @OAI.Higman.NormalWords.embeds_presentation_oai
