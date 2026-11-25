-- Prove2me | solution 1 for GlobalTheory.LengthCommensurable.signedLength_smul_smul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T18:03:47.482779+00:00
-- url     : https://prove2.me/submissions/5bca057c-f595-49ff-a340-49052f336cfd

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_QuasicoherentCohomology_LengthCommensurableMapIffOfInjective
import Theorems.Thm_GlobalTheory_LengthCommensurable_signedLength_map_of_injective

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
open Pointwise
namespace GlobalTheory
namespace LengthCommensurable
theorem _root_.solution {G : Type*} [Monoid G] [DistribMulAction G V]
    [SMulCommClass G R V] {a : G} {A B : Submodule R V} (h : LengthCommensurable A B)
    (ha : IsSMulRegular V a) : signedLength (a • A) (a • B) = signedLength A B :=
  h.signedLength_map_of_injective (DistribSMul.toLinearMap R V a) ha
end LengthCommensurable
end GlobalTheory
