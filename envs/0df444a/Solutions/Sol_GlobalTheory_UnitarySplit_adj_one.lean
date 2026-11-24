-- Prove2me | solution 1 for GlobalTheory.UnitarySplit.adj_one
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T22:05:20.135462+00:00
-- url     : https://prove2.me/submissions/47a96f8d-bde8-4b6c-936a-ca1d3dd2142b

import Mathlib
import Definitions.Def_Formalism_SatakeDualWeyl_KpqSubgroupCompact
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SatakeParameters_UnitarySupportedEquiv
import Theorems.Thm_Formalism_UG_Final_KpqSubgroupCompact


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.UG
open GlobalTheory GlobalTheory.UnitarySplit
variable {A : Type} [CommRing A] {n : ℕ}
namespace GlobalTheory.UnitarySplit
theorem _root_.solution (c : A →+* A) {J : Matrix (Fin n) (Fin n) A} (hJ : IsUnit J.det) :
    adj c J 1 = 1 := by
  rw [adj, cT_one, Matrix.mul_one, Matrix.nonsing_inv_mul _ hJ]
end GlobalTheory.UnitarySplit
