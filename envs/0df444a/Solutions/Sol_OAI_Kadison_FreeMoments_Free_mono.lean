-- Prove2me | solution 1 for OAI.Kadison.FreeMoments.Free.mono
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-28T07:14:41.013265+00:00
-- url     : https://prove2.me/submissions/a7e1455a-dc8f-42fb-b93b-bbef4eae0b2f

import Mathlib
import Definitions.Def_OAIQ039C010

section
-- module Solutions.OAIQ039_CM.Commutator_FreeMomentsMonotone
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

section

noncomputable section

namespace Kadison.FreeMoments

variable {A ι : Type*} [Ring A] [Algebra ℂ A] [StarRing A] [StarModule ℂ A]

variable {S T : ι → StarSubalgebra ℂ A} {τ : A →ₗ[ℂ] ℂ}

lemma Free.mono_oai (hfree : Free T τ) (hle : ∀ i,S i≤T i) : Free S τ := by
  let f : Letter S τ → Letter T τ := fun a => ⟨a.color,a.val,hle _ a.mem,a.centered⟩
  intro w hw hne
  have hr : Reduced (w.map f) := (List.isChain_map _).mpr hw
  have hn : w.map f≠[] := by
    cases w with
    | nil => exact (hne rfl).elim
    | cons a w => intro h; cases h
  have h := hfree (w.map f) hr hn
  simpa only [word,List.map_map,Function.comp_def] using h

end Kadison.FreeMoments

end

end
end

end OAI
end

theorem solution.{u_1, u_2} : type_of% @OAI.Kadison.FreeMoments.Free.mono_oai.{u_1, u_2} := @OAI.Kadison.FreeMoments.Free.mono_oai.{u_1, u_2}
