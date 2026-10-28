-- Prove2me | solution 1 for OAI.Kadison.FreeBlocks.gns_vectorState
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-28T07:41:59.481814+00:00
-- url     : https://prove2.me/submissions/8a43ce22-a0a5-4a7d-b590-343967e275ba

import Mathlib
import Definitions.Def_OAIQ039C047

section
-- module Solutions.OAIQ039_CM.Commutator_NormalFreeCorner
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

section

noncomputable section

open scoped ComplexOrder InnerProductSpace Matrix.Norms.L2Operator

open UniformSpace

namespace Kadison.FreeBlocks

open FreeMoments FreeWordTensor FreeWordAction

variable {A : Type} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

lemma gns_vectorState_oai (τ : A →ₚ[ℂ] ℂ) (a : A) :
    CornerSymmetrization.vectorState (TracialGNS.vacuum τ) (τ.gnsStarAlgHom a)=τ a := by
  change inner ℂ (TracialGNS.vacuum τ) (τ.gnsStarAlgHom a (TracialGNS.vacuum τ))=τ a
  rw [TracialGNS.left_vacuum]
  exact TracialGNS.inner_vacuum_algebraVector τ a

end Kadison.FreeBlocks

end

end
end

end OAI
end

theorem solution : type_of% @OAI.Kadison.FreeBlocks.gns_vectorState_oai := @OAI.Kadison.FreeBlocks.gns_vectorState_oai
