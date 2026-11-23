-- Prove2me | solution 1 for GlobalTheory.Reg.Transfer.chval_zero
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T13:08:48.083989+00:00
-- url     : https://prove2.me/submissions/a35fe007-2dd8-42f5-9efb-41873842ddbe

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
theorem _root_.solution {φ : A →+* V} {e : ℕ} {r : EReal} (h : ChV φ e (0 : FractionRing A) r) : r = ⊤ := by
  obtain ⟨x, s, hs, hfs, rfl⟩ := h
  have hx : x = 0 := by
    rw [zero_mul] at hfs
    exact IsFractionRing.injective A (FractionRing A) (by rw [← hfs, map_zero])
  rw [hx, map_zero, map_zero, nval_zero, nval_eq_vr e hs, EReal.top_sub_coe]
end GlobalTheory.Reg.Transfer
