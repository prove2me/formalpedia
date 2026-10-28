-- Prove2me | solution 2 for OAI.FiniteAlgebraicEnvelopes.embedsInFinitelyPresentedSimpleGroup_of_hasDecidableWordProblem
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-24T20:40:25.225473+00:00
-- url     : https://prove2.me/submissions/49a2f101-429f-47c4-ab5d-ef46f7b1d52d

import Mathlib
import Definitions.Def_BooneHigman
import Definitions.Def_OAIFAE003
import Theorems.Thm_OAI_FiniteAlgebraicEnvelopes_TwistedBrinThompson_finitelyPresented
import Theorems.Thm_OAI_FiniteAlgebraicEnvelopes_envelope
import Theorems.Thm_OAI_FiniteAlgebraicEnvelopes_TwistedBrinThompson_isSimpleGroup_group

section
-- module Solutions.OAIFAE.CantorBricks
attribute [-instance] _root_.OAI.FiniteAlgebraicEnvelopes.AffinePermutation.action _root_.OAI.FiniteAlgebraicEnvelopes.LiftedAction.faithful _root_.OAI.FiniteAlgebraicEnvelopes.MachineRealization.FoldLiteral.instFintypeK'_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

/-!
Cantor prefixes, bricks, charts, finite-table group, localization, and displacement.
-/

namespace FiniteAlgebraicEnvelopes.TwistedBrinThompson

section
universe u v
attribute [local instance] Classical.propDecidable

variable {Γ : Type u} {X : Type v} [Group Γ] [MulAction Γ X]

theorem embedding_injective [FaithfulSMul Γ X] :
    Function.Injective (embedding (Γ:=Γ) (X:=X)) := by
  intro g h he
  exact twist_injective (congrArg Subtype.val he)

end

universe u v
attribute [local instance] Classical.propDecidable

end FiniteAlgebraicEnvelopes.TwistedBrinThompson

end

end OAI
end

section
-- module Solutions.OAIFAE.Forward
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace FiniteAlgebraicEnvelopes
universe u

/-- Forward direction of the Boone–Higman equivalence, from the envelope, finite presentation
and simplicity of the twisted Brin–Thompson group (OpenAI's `main_forward`, with the simplicity
step named). -/
theorem embedsInFinitelyPresentedSimpleGroup_of_hasDecidableWordProblem_oai
    (GroupType : Type u) [Group GroupType] [Group.FG GroupType]
    (h : HasDecidableWordProblem GroupType) :
    EmbedsInFinitelyPresentedSimpleGroup GroupType := by
  obtain ⟨Γ,hΓ,X,hX,hfp,hcount,hinf,hfaith,htwo,hstab,f,hf⟩ := envelope GroupType h
  let := hfp
  let := hinf
  let := hfaith
  exact ⟨TwistedBrinThompson.group (Γ:=Γ) (X:=X),inferInstance,
    TwistedBrinThompson.finitelyPresented htwo hstab,
    TwistedBrinThompson.isSimpleGroup_group,
    (TwistedBrinThompson.embedding (X:=X)).comp f,
    TwistedBrinThompson.embedding_injective.comp hf⟩

end FiniteAlgebraicEnvelopes

end

end OAI
end

theorem solution.{u} : type_of% @OAI.FiniteAlgebraicEnvelopes.embedsInFinitelyPresentedSimpleGroup_of_hasDecidableWordProblem_oai.{u} := @OAI.FiniteAlgebraicEnvelopes.embedsInFinitelyPresentedSimpleGroup_of_hasDecidableWordProblem_oai.{u}
