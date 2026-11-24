-- Prove2me | solution 1 for GlobalTheory.UnitarySplit.mem_iff_adj
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T22:05:21.36909+00:00
-- url     : https://prove2.me/submissions/70526996-9fd7-4fe0-b96a-758a76f64257

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
    (G : GL (Fin n) A) :
    G ∈ UJ c J ↔ adj c J (G : Matrix (Fin n) (Fin n) A) * (G : Matrix (Fin n) (Fin n) A) = 1 := by
  change cT c (G : Matrix (Fin n) (Fin n) A) * J * (G : Matrix (Fin n) (Fin n) A) = J ↔ _
  constructor
  · intro h
    rw [adj, Matrix.mul_assoc J⁻¹, Matrix.mul_assoc J⁻¹, h, Matrix.nonsing_inv_mul _ hJ]
  · intro h
    have := congrArg (fun M => J * M) h
    simpa only [adj, Matrix.mul_assoc, Matrix.mul_nonsing_inv_cancel_left _ _ hJ,
      Matrix.mul_one] using this
end GlobalTheory.UnitarySplit
