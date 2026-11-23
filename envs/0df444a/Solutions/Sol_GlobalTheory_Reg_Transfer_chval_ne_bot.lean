-- Prove2me | solution 1 for GlobalTheory.Reg.Transfer.chval_ne_bot
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T13:08:47.669826+00:00
-- url     : https://prove2.me/submissions/9f5d8f9a-8355-4a7a-bf62-3ef5927a4d57

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_RegularCharts_SCharts
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_RegModelC
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GenericRegularity_RegularAtCentre
import Theorems.Thm_GlobalTheory_Reg_Transfer_nval_eq_vr
import Theorems.Thm_Formalism_L2_Pj_nval_zero


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
theorem _root_.solution {φ : A →+* V} {e : ℕ} {f : FractionRing A} {r : EReal} (h : ChV φ e f r) : r ≠ ⊥ := by
  obtain ⟨x, s, hs, -, rfl⟩ := h
  rw [nval_eq_vr e hs]
  by_cases hx : φ x = 0
  · rw [hx, map_zero, nval_zero, EReal.top_sub_coe]; exact top_ne_bot
  · rw [nval_eq_vr e hx, ← EReal.coe_sub]; exact EReal.coe_ne_bot _
end GlobalTheory.Reg.Transfer
