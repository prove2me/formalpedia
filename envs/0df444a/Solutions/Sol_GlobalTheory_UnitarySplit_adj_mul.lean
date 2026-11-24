-- Prove2me | solution 1 for GlobalTheory.UnitarySplit.adj_mul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T22:05:19.369984+00:00
-- url     : https://prove2.me/submissions/6cb3fd02-a7c4-4b9d-8bed-d23462c816e4

import Mathlib
import Definitions.Def_Formalism_SatakeDualWeyl_KpqSubgroupCompact
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SatakeParameters_UnitarySupportedEquiv
import Theorems.Thm_Formalism_GradedWeylDivisibility_rowDivL_apply
import Theorems.Thm_Formalism_UG_Final_KpqSubgroupCompact
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.GradedWeylDivisibility.rowDivL_apply



set_option autoImplicit false
open Formalism.UG
open GlobalTheory GlobalTheory.UnitarySplit
variable {A : Type} [CommRing A] {n : ℕ}
namespace GlobalTheory.UnitarySplit
theorem _root_.solution (c : A →+* A) {J : Matrix (Fin n) (Fin n) A} (hJ : IsUnit J.det)
    (M N : Matrix (Fin n) (Fin n) A) : adj c J (M * N) = adj c J N * adj c J M := by
  simp only [adj, cT_mul, Matrix.mul_assoc, Matrix.mul_nonsing_inv_cancel_left _ _ hJ]
end GlobalTheory.UnitarySplit
