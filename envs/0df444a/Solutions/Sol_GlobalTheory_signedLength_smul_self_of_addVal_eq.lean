-- Prove2me | solution 1 for GlobalTheory.signedLength_smul_self_of_addVal_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T23:44:30.196862+00:00
-- url     : https://prove2.me/submissions/bbda60d6-7a56-4e33-bd0a-7d55392d2291

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_QuasicoherentCohomology_LengthCommensurableMapIffOfInjective
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_LengthQuotientMaximalIdealPowSmulTop
import Theorems.Thm_GlobalTheory_lengthCommensurable_smul_self
import Theorems.Thm_GlobalTheory_LengthCommensurable_signedLength_eq_natCast_iff_of_ge


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
theorem _root_.solution (hA : A.FG) {a : R} {n : ℕ} (hn : addVal R a = n) :
    signedLength A (a • A) = (n : ℤ) * (Module.finrank R A : ℤ) := by
  have ha : a ≠ 0 := addVal_eq_top_iff.not.mp (hn ▸ ENat.coe_ne_top n)
  rw [← Nat.cast_mul, (lengthCommensurable_smul_self hA ha).signedLength_eq_natCast_iff_of_ge
    (Submodule.smul_le_self_of_tower a A), relLength_smul_self_of_addVal_eq hA hn]
end GlobalTheory
