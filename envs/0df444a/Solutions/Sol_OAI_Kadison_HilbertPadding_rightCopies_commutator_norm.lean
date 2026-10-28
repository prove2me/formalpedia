-- Prove2me | solution 1 for OAI.Kadison.HilbertPadding.rightCopies_commutator_norm
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-28T07:26:23.316788+00:00
-- url     : https://prove2.me/submissions/185ef45f-ddcb-4f46-a84e-9c017cafdb70

import Mathlib
import Definitions.Def_OAIQ039C027
import Theorems.Thm_OAI_Kadison_HilbertPadding_norm_extend_commutator
import Theorems.Thm_OAI_Kadison_HilbertPadding_rightCopies_diagonal

section
-- module Solutions.OAIQ039_CM.Commutator_RightCopies
attribute [-instance] _root_.OAI.Kadison.VonNeumannCStar.isClosed _root_.OAI.Kadison.VonNeumannCStar.smulMemClass _root_.OAI.Kadison.VonNeumannCStar.starOrderedRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

section

noncomputable section

open scoped BigOperators InnerProductSpace

open ContinuousLinearMap

namespace Kadison.HilbertPadding

open OperatorAmplification

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

variable (ι κ : Type*) [Fintype ι] [Fintype κ]

local instance rightCopiesSourceDecidableEq_r3e211a_1 : DecidableEq ι := Classical.decEq ι
local instance rightCopiesPaddingDecidableEq_r3e211a_1 : DecidableEq κ := Classical.decEq κ
lemma rightCopies_adjoint_diagonal (a : H →L[ℂ] H) :
    (rightCopies (H:=H) ι κ).toContinuousLinearMap.adjoint.comp (diagonal (H:=H) (κ⊕ι) a)=
      (diagonal (H:=H) ι a).comp (rightCopies (H:=H) ι κ).toContinuousLinearMap.adjoint := by
  have h := congrArg (fun T => T.adjoint) (rightCopies_diagonal ι κ (star a))
  simpa only [adjoint_comp,←star_eq_adjoint,←map_star,star_star] using h

lemma rightCopies_commutator_norm_oai
    (Y : SumSpace (H:=H) ι →L[ℂ] SumSpace (H:=H) ι) (a : H →L[ℂ] H) :
    ‖extend (rightCopies ι κ) Y*diagonal (H:=H) (κ⊕ι) a-
      diagonal (H:=H) (κ⊕ι) a*extend (rightCopies ι κ) Y‖=
        ‖Y*diagonal (H:=H) ι a-diagonal (H:=H) ι a*Y‖ :=
  norm_extend_commutator _ _ _ _ (rightCopies_diagonal ι κ a) (rightCopies_adjoint_diagonal ι κ a)

end Kadison.HilbertPadding

end

end
end

end OAI
end

theorem solution.{u_1, u_2, u_3} : type_of% @OAI.Kadison.HilbertPadding.rightCopies_commutator_norm_oai.{u_1, u_2, u_3} := @OAI.Kadison.HilbertPadding.rightCopies_commutator_norm_oai.{u_1, u_2, u_3}
