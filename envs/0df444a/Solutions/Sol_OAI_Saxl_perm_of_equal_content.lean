-- Prove2me | solution 1 for OAI.Saxl.perm_of_equal_content
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-13T04:10:12.613665+00:00
-- url     : https://prove2.me/submissions/7f495140-1f09-4a5d-a301-dd6493e215c2

import Mathlib

section
-- module Solutions.OAIQ259_US.Saxl_YoungRule
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open scoped TensorProduct

namespace Saxl

/- Horizontal-strip chains recording the exact ordered strip sizes. -/

lemma perm_of_equal_content_oai {n d : ℕ} (a b : Fin n → Fin d)
    (h : ∀ j, (Finset.univ.filter (fun i => a i = j)).card =
      (Finset.univ.filter (fun i => b i = j)).card) :
    ∃ g : Equiv.Perm (Fin n), b ∘ g = a := by
  classical
  let e (j) : {i // a i = j} ≃ {i // b i = j} :=
    Fintype.equivOfCardEq (by simpa only [Fintype.card_subtype] using h j)
  let g := (Equiv.sigmaFiberEquiv a).symm.trans
    ((Equiv.sigmaCongrRight e).trans (Equiv.sigmaFiberEquiv b))
  refine ⟨g, ?_⟩
  funext i
  exact (e (a i) ⟨i,rfl⟩).property

end Saxl

end

end OAI
end

theorem solution : type_of% @OAI.Saxl.perm_of_equal_content_oai := @OAI.Saxl.perm_of_equal_content_oai
