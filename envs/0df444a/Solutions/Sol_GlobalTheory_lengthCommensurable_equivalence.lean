-- Prove2me | solution 1 for GlobalTheory.lengthCommensurable_equivalence
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T00:00:45.237683+00:00
-- url     : https://prove2.me/submissions/4f39e7c4-7521-42e2-9df2-5a9cca154b5b

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_QuasicoherentCohomology_LengthCommensurableMapIffOfInjective
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_LengthCommensurableIffOfLeOfLe

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory
variable {R V : Type*} [Ring R] [AddCommGroup V] [Module R V]
variable {A A' B B' C : Submodule R V}
namespace GlobalTheory
theorem _root_.solution :
    Equivalence (LengthCommensurable : Submodule R V → Submodule R V → Prop) :=
  ⟨LengthCommensurable.refl, LengthCommensurable.symm, LengthCommensurable.trans⟩
end GlobalTheory
