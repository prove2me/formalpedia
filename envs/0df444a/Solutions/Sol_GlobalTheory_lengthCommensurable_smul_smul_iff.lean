-- Prove2me | solution 1 for GlobalTheory.lengthCommensurable_smul_smul_iff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-27T04:38:59.420857+00:00
-- url     : https://prove2.me/submissions/591b9cb7-c15e-4af7-94f5-f2eadf6be8f3

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_QuasicoherentCohomology_LengthCommensurableMapIffOfInjective
import Theorems.Thm_GlobalTheory_lengthCommensurable_map_iff_of_injective

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
theorem _root_.solution {G : Type*} [Monoid G] [DistribMulAction G V]
    [SMulCommClass G R V] {a : G} (ha : IsSMulRegular V a) {A B : Submodule R V} :
    LengthCommensurable (a • A) (a • B) ↔ LengthCommensurable A B :=
  lengthCommensurable_map_iff_of_injective (DistribSMul.toLinearMap R V a) ha
end GlobalTheory
