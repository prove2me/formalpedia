-- Prove2me | solution 1 for GlobalTheory.signedLength_smul_self
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-27T04:41:23.248804+00:00
-- url     : https://prove2.me/submissions/464737ff-4ee5-4c25-aa07-5c5b0ed069a8

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_QuasicoherentCohomology_LengthCommensurableMapIffOfInjective
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_LengthQuotientMaximalIdealPowSmulTop
import Theorems.Thm_GlobalTheory_signedLength_smul_self_of_addVal_eq

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Pointwise
open GlobalTheory
open IsDiscreteValuationRing
variable {R : Type*} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
variable {V : Type*} [AddCommGroup V] [Module R V] [Module.IsTorsionFree R V]
  {A : Submodule R V}
namespace GlobalTheory
theorem _root_.solution (hA : A.FG) {a : R} (ha : a ≠ 0) :
    signedLength A (a • A) = ((addVal R a).toNat : ℤ) * (Module.finrank R A : ℤ) :=
  signedLength_smul_self_of_addVal_eq hA (ENat.coe_toNat (addVal_eq_top_iff.not.mpr ha)).symm
end GlobalTheory
