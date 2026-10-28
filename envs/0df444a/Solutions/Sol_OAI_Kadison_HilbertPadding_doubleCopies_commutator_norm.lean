-- Prove2me | solution 1 for OAI.Kadison.HilbertPadding.doubleCopies_commutator_norm
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-28T07:24:52.209996+00:00
-- url     : https://prove2.me/submissions/1e86ec1f-2913-4777-923f-a0277c7f34ac

import Mathlib
import Definitions.Def_OAIQ039C027
import Theorems.Thm_OAI_Kadison_HilbertPadding_doubleCopies_diagonal
import Theorems.Thm_OAI_Kadison_HilbertPadding_norm_extend_commutator

section
-- module Solutions.OAIQ039_CM.Commutator_DoubleCopies
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

variable (ι : Type*) [Fintype ι]

local instance doubleCopiesIndexDecidableEq_rb2290a_1 : DecidableEq ι := Classical.decEq ι
lemma doubleCopies_adjoint_diagonal (a : H →L[ℂ] H) :
    (doubleCopies (H:=H) ι).toContinuousLinearMap.adjoint.comp (diagonal (H:=H) ((Fin 2)×ι) a)=
      (diagonal (H:=H) ι a).comp (doubleCopies (H:=H) ι).toContinuousLinearMap.adjoint := by
  have h := congrArg (fun T => T.adjoint) (doubleCopies_diagonal ι (star a))
  simpa only [adjoint_comp,←star_eq_adjoint,←map_star,star_star] using h

theorem doubleCopies_commutator_norm_oai
    (Y : SumSpace (H:=H) ι →L[ℂ] SumSpace (H:=H) ι) (a : H →L[ℂ] H) :
    ‖extend (doubleCopies ι) Y*diagonal (H:=H) ((Fin 2)×ι) a-
      diagonal (H:=H) ((Fin 2)×ι) a*extend (doubleCopies ι) Y‖=
        ‖Y*diagonal (H:=H) ι a-diagonal (H:=H) ι a*Y‖ :=
  norm_extend_commutator _ _ _ _ (doubleCopies_diagonal ι a) (doubleCopies_adjoint_diagonal ι a)

end Kadison.HilbertPadding

end

end
end

end OAI
end

theorem solution.{u_1, u_2} : type_of% @OAI.Kadison.HilbertPadding.doubleCopies_commutator_norm_oai.{u_1, u_2} := @OAI.Kadison.HilbertPadding.doubleCopies_commutator_norm_oai.{u_1, u_2}
