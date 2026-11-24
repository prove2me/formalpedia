-- Prove2me | solution 1 for GlobalTheory.UnitarySwap.form_herm
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T16:11:29.209798+00:00
-- url     : https://prove2.me/submissions/309fe121-4107-4023-9b76-0334c5e8df3d

import Mathlib
import Definitions.Def_Formalism_SatakeDualWeyl_KpqSubgroupCompact
import Definitions.Def_Formalism_SatakeDualWeyl_StatementF
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SatakeParameters_ImportsTail
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SatakeParameters_InvMemDoubleCosetAndComm
import Theorems.Thm_GlobalTheory_UnitarySwap_form_apply
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
open Formalism.UG Matrix
noncomputable section
open GlobalTheory GlobalTheory.UnitarySwap
variable {L : Type} [Field L] [Valued L (WithZero (Multiplicative ℤ))]
variable {n : ℕ} {σ : L →+* L}
omit [Valued L (WithZero (Multiplicative ℤ))]
namespace GlobalTheory.UnitarySwap
theorem _root_.solution (hσσ : ∀ x, σ (σ x) = x) {J : Matrix (Fin n) (Fin n) L}
    (hJ : ∀ i j, σ (J i j) = J j i) (u v : Fin n → L) : σ (form σ J u v) = form σ J v u := by
  simp only [form_apply, Matrix.mulVec, dotProduct, map_sum, map_mul, Function.comp_apply, hσσ, hJ,
    Finset.mul_sum]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring
end GlobalTheory.UnitarySwap
