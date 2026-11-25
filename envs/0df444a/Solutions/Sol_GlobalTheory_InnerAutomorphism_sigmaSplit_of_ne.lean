-- Prove2me | solution 1 for GlobalTheory.InnerAutomorphism.sigmaSplit_of_ne
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T17:58:44.416265+00:00
-- url     : https://prove2.me/submissions/92101e76-248e-4d5c-b4fc-c2056462ae8a

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
theorem _root_.solution {i j : ι} (h : i ≠ j) (x : F i) :
    sigmaSplit F j ⟨i, x⟩ = Sum.inr ⟨⟨i, h⟩, x⟩ :=
  (Equiv.apply_eq_iff_eq_symm_apply _).2 rfl
end GlobalTheory.InnerAutomorphism
