-- Prove2me | solution 1 for GlobalTheory.LengthCommensurable.signedLength_eq_toNat_sub_of_ge
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T18:00:21.32511+00:00
-- url     : https://prove2.me/submissions/e2a9126d-24f0-4440-ac35-53a29d800681

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_QuasicoherentCohomology_LengthCommensurableMapIffOfInjective
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_LengthCommensurableIffOfLeOfLe
import Theorems.Thm_GlobalTheory_LengthCommensurable_signedLength_eq_sub_left

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
open GlobalTheory.LengthCommensurable
namespace GlobalTheory.LengthCommensurable
theorem _root_.solution {D : Submodule R V} (h : LengthCommensurable A B)
    (hDA : LengthCommensurable D A) (hAD : A ≤ D) (hBD : B ≤ D) :
    signedLength A B = ((relLength D B).toNat : ℤ) - ((relLength D A).toNat : ℤ) := by
  rw [hDA.signedLength_eq_sub_left (hDA.trans h), hDA.signedLength_of_ge hAD,
    (hDA.trans h).signedLength_of_ge hBD]
end GlobalTheory.LengthCommensurable
