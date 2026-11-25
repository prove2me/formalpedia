-- Prove2me | solution 1 for GlobalTheory.UnitarySplit.adj_adj
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T04:17:25.143994+00:00
-- url     : https://prove2.me/submissions/a3d658d7-1ca7-4bf0-84e5-a9208275d557

import Mathlib
import Definitions.Def_Formalism_SatakeDualWeyl_KpqSubgroupCompact
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SatakeParameters_UnitarySupportedEquiv
import Theorems.Thm_P2M_GlobalTheory_UnitarySplit_cT_cT__65cdfa7a426c
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
theorem _root_.solution (c : A →+* A) (hc : ∀ x, c (c x) = x) {J : Matrix (Fin n) (Fin n) A}
    (hJ : IsUnit J.det) (hh : cT c J = J) (M : Matrix (Fin n) (Fin n) A) :
    adj c J (adj c J M) = M := by
  have h1 : J * cT c J⁻¹ = 1 := by
    have := cT_mul c J⁻¹ J
    rw [Matrix.nonsing_inv_mul _ hJ, cT_one, hh] at this
    exact this.symm
  have h2 : cT c J⁻¹ * J = 1 := mul_eq_one_comm.mp h1
  simp only [adj, cT_mul, hh, cT_cT' c hc, Matrix.mul_assoc, h2, Matrix.mul_one,
    Matrix.nonsing_inv_mul_cancel_left _ _ hJ]
end GlobalTheory.UnitarySplit
