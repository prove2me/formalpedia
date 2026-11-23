-- Prove2me | solution 1 for GlobalTheory.Reg.Transfer.w_fin
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T13:03:47.607796+00:00
-- url     : https://prove2.me/submissions/6b09e50e-7e96-4f1c-8c6c-192b83335473

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_RegularCharts_SCharts
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_RegModelC
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GenericRegularity_RegularAtCentre
import Theorems.Thm_GlobalTheory_Reg_Transfer_nval_eq_vr

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
theorem _root_.solution {φ : A →+* V} {e : ℕ} {fw : FractionRing A} {W : EReal} (hW : ChV φ e fw W) (P yw : A)
    (hrel : fw⁻¹ * algebraMap A (FractionRing A) P = algebraMap A (FractionRing A) yw) (hfw0 : fw ≠ 0)
    (hP : φ P ≠ 0) : ∃ w : ℝ, W = (w : EReal) := by
  obtain ⟨xw, sw, hsw, hfws, hWv⟩ := hW
  have hrel' : fw * algebraMap A (FractionRing A) yw = algebraMap A (FractionRing A) P := by
    rw [← hrel]; field_simp
  have hxy : xw * yw = sw * P := by
    apply IsFractionRing.injective A (FractionRing A)
    rw [map_mul, map_mul, ← hfws, ← hrel']; ring
  have hxw : φ xw ≠ 0 := by
    intro h0
    have := congrArg φ hxy
    rw [map_mul, map_mul, h0, zero_mul] at this
    exact mul_ne_zero hsw hP this.symm
  exact ⟨vr e (φ xw) - vr e (φ sw), by rw [hWv, nval_eq_vr e hxw, nval_eq_vr e hsw, EReal.coe_sub]⟩
end GlobalTheory.Reg.Transfer
