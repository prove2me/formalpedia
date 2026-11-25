-- Prove2me | solution 1 for GlobalTheory.InnerAutomorphism.sigmaSplit_self
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T17:58:46.167614+00:00
-- url     : https://prove2.me/submissions/990658ab-6095-415c-b0d6-8bc97abc36df

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_SigmaSplitSymmInl

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.InnerAutomorphism
variable {ι : Type*} [DecidableEq ι] (F : ι → Type*)
namespace GlobalTheory.InnerAutomorphism
theorem _root_.solution (j : ι) (x : F j) : sigmaSplit F j ⟨j, x⟩ = Sum.inl x :=
  (Equiv.apply_eq_iff_eq_symm_apply _).2 rfl
end GlobalTheory.InnerAutomorphism
