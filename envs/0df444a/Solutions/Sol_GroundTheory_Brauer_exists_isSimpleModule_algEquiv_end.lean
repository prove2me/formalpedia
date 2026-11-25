-- Prove2me | solution 1 for GroundTheory.Brauer.exists_isSimpleModule_algEquiv_end
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T00:10:41.84207+00:00
-- url     : https://prove2.me/submissions/b4e651e9-c7cf-44ba-b5fe-8996415dfa6d

import Mathlib
import Definitions.Def_GroundTheory_Brauer_TensorSimple
import Definitions.Def_GroundTheory_Brauer_IsBrauerEquivalentIffNonemptyAlgEquiv
import Theorems.Thm_GroundTheory_Brauer_isSimpleModule_columnIdeal

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Brauer
open TensorProduct
universe u v w
variable {K : Type u} [Field K]
namespace GroundTheory.Brauer
theorem _root_.solution {R : Type v} [Ring R] [Algebra K R] {D : Type w}
    [DivisionRing D] [Algebra K D] {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]
    (e : R ≃ₐ[K] Matrix ι ι D) :
    ∃ I : Ideal R, IsSimpleModule R I ∧ Nonempty (Module.End R I ≃ₐ[K] Dᵐᵒᵖ) :=
  ⟨_, isSimpleModule_columnIdeal e (Classical.arbitrary ι),
    ⟨endColumnIdealAlgEquiv e (Classical.arbitrary ι)⟩⟩
end GroundTheory.Brauer
