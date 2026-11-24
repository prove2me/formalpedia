-- Prove2me | solution 1 for GlobalTheory.Reg.Transfer.chval_fin_pow
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T20:45:40.688281+00:00
-- url     : https://prove2.me/submissions/319b2d2a-86e7-4155-883b-d6897ba5b15e

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_RegularCharts_SCharts
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_RegModelC
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GenericRegularity_RegularAtCentre
import Theorems.Thm_GlobalTheory_Reg_Transfer_chval_fin_mul
import Theorems.Thm_GlobalTheory_Reg_Transfer_chval_fin_one
import Theorems.Thm_Formalism_L2_Pj_IsEval_zero


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.Reg GlobalTheory.Reg.Transfer
open IsLocalRing Formalism.L2.Pj GlobalTheory.Reg
variable {V : Type} [CommRing V] [IsDomain V] [IsDiscreteValuationRing V]
variable {A : Type} [CommRing A] [IsDomain A]
namespace GlobalTheory.Reg.Transfer
theorem _root_.solution (φ : A →+* V) (e : ℕ) {f : FractionRing A} {u : ℝ} (h : ChV φ e f (u : EReal))
    (N : ℕ) : ChV φ e (f ^ N) (((N : ℝ) * u : ℝ) : EReal) := by
  induction N with
  | zero => simpa using chval_fin_one φ e
  | succ N ih =>
    have := chval_fin_mul φ e ih h
    rw [pow_succ]
    convert this using 2
    push_cast
    ring
end GlobalTheory.Reg.Transfer
