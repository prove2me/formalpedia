-- Prove2me | solution 1 for GlobalTheory.LatPair.Model.phiOne_one_dia
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T18:00:23.965856+00:00
-- url     : https://prove2.me/submissions/2a564f8d-7dc8-4b05-a5d4-9d5a8189c1a7

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_TwistedInnerProducts_HasConductorMulShift
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_SecondCountableAndT2LocalField
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_TwistedInnerProducts_ExistsFFNeZeroThree

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ValuativeRel Matrix IsLocalRing
open scoped Pointwise
noncomputable section
open GlobalTheory GlobalTheory.LatPair GlobalTheory.LatPair.Model
variable {k : Type*} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {n n' : Type*}
variable {M : Type*} [AddCommGroup M] [Module ℂ M]
namespace GlobalTheory.LatPair.Model
theorem _root_.solution [Fintype n] [DecidableEq n] (P : Pair k n) {c : 𝓀[k]ˣ} (hc : c ≠ 1) :
    phiOne P (c • P) 1 = 0 :=
  if_neg fun h => hc (by
    have h1 := maps_iff_hasVal.1 h _ _ P.hasVal_vec
    rw [one_mulVec, Pair.dia_hasVal] at h1
    simpa using h1.unique P.hasVal_vec)
end GlobalTheory.LatPair.Model
