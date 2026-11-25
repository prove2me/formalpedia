-- Prove2me | solution 1 for GlobalTheory.JR.normalForm_invariants
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T02:39:38.198282+00:00
-- url     : https://prove2.me/submissions/b85b7036-fbf5-49bf-86a3-e9d125b44635

import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_FourierMatch
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_JacquetRallisBorderedMatrixNormalFormInvariants
import Theorems.Thm_P2M_GlobalTheory_JR_NormalFormL_inv_act__a1785aba4025
import Theorems.Thm_P2M_GlobalTheory_JR_NormalFormL_act_mul__049dd60a3f1d
import Theorems.Thm_P2M_GlobalTheory_JR_NormalFormL_inv_sec__4f2b1984a7c3
import Theorems.Thm_GlobalTheory_JR_NormalFormL_hankel_eq
import Theorems.Thm_GlobalTheory_JR_NormalFormL_unique_conj

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.JR Matrix MeasureTheory Filter Topology
namespace GlobalTheory.JR
theorem _root_.solution : ∀ (k : Type) [Field k] (r : ℕ), (∀ (g : GL (Fin r) k) (Y : Gl r k), inv (act g Y) = inv Y) ∧ (∀ a : Inv r k, inv (sec a) = a) ∧ (∀ Y : Gl r k, Cm Y * Bm Y = hankel (inv Y)) ∧ (∀ (g h : GL (Fin r) k) (Y : Gl r k), act (g * h) Y = act g (act h Y)) ∧ ∀ Y Y₁ : Gl r k, Delta (inv Y) ≠ 0 → inv Y₁ = inv Y → ∃! g : GL (Fin r) k, act g Y = Y₁ ∧ (g : Matrix (Fin r) (Fin r) k) * Bm Y = Bm Y₁ := by
  intro k _ r
  exact ⟨GlobalTheory.JR.NormalFormL.inv_act', GlobalTheory.JR.NormalFormL.inv_sec', GlobalTheory.JR.NormalFormL.hankel_eq,
    GlobalTheory.JR.NormalFormL.act_mul', GlobalTheory.JR.NormalFormL.unique_conj⟩
end GlobalTheory.JR
