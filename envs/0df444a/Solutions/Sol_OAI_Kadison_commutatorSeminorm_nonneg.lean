-- Prove2me | solution 1 for OAI.Kadison.commutatorSeminorm_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-28T10:05:15.237693+00:00
-- url     : https://prove2.me/submissions/23d62fd0-67e5-49dd-9b0c-fdd34cb6d6c4

import Mathlib
import Definitions.Def_UniformCommutator
import Definitions.Def_OAIQ039C018

section
-- module Solutions.OAIQ039_CM.Commutator_MainMatrix
attribute [-instance] _root_.OAI.Kadison.UnitaryDualAction.action
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

section

noncomputable section

universe u

open scoped InnerProductSpace BigOperators ComplexOrder

namespace Kadison

variable {K : Type u} [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]

lemma commutatorSeminorm_nonneg_oai (P : VonNeumannAlgebra K) (Y : K →L[ℂ] K) :
    0 ≤ commutatorSeminorm P Y :=
  le_csSup (commutator_ball_bdd P Y) ⟨0,zero_mem P,by simp,by simp⟩

end Kadison

end

end
end

end OAI
end

theorem solution.{u} : type_of% @OAI.Kadison.commutatorSeminorm_nonneg_oai.{u} := @OAI.Kadison.commutatorSeminorm_nonneg_oai.{u}
