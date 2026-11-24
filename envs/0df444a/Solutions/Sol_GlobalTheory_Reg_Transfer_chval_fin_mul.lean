-- Prove2me | solution 1 for GlobalTheory.Reg.Transfer.chval_fin_mul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T20:28:24.507531+00:00
-- url     : https://prove2.me/submissions/eafa991d-b904-495d-b0bd-72f8bb6014b3

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_RegularCharts_SCharts
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_RegModelC
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GenericRegularity_RegularAtCentre
import Theorems.Thm_GlobalTheory_Reg_Transfer_vr_mul
import Theorems.Thm_GlobalTheory_Reg_Transfer_chval_fin_iff

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
theorem _root_.solution (φ : A →+* V) (e : ℕ) {f1 f2 : FractionRing A} {u1 u2 : ℝ}
    (h1 : ChV φ e f1 (u1 : EReal)) (h2 : ChV φ e f2 (u2 : EReal)) :
    ChV φ e (f1 * f2) ((u1 + u2 : ℝ) : EReal) := by
  obtain ⟨x1, s1, hs1, hx1, hf1, hu1⟩ := (chval_fin_iff φ e f1 u1).1 h1
  obtain ⟨x2, s2, hs2, hx2, hf2, hu2⟩ := (chval_fin_iff φ e f2 u2).1 h2
  refine (chval_fin_iff φ e _ _).2 ⟨x1 * x2, s1 * s2, ?_, ?_, ?_, ?_⟩
  · rw [map_mul]; exact mul_ne_zero hs1 hs2
  · rw [map_mul]; exact mul_ne_zero hx1 hx2
  · rw [map_mul, map_mul, ← hf1, ← hf2]; ring
  · rw [map_mul, map_mul, vr_mul e hx1 hx2, vr_mul e hs1 hs2, hu1, hu2]; ring
end GlobalTheory.Reg.Transfer
