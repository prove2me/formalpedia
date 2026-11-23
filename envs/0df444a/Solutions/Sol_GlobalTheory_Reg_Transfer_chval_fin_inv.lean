-- Prove2me | solution 1 for GlobalTheory.Reg.Transfer.chval_fin_inv
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T13:09:51.835006+00:00
-- url     : https://prove2.me/submissions/d656b326-4cd4-453d-9f38-05bc02dedeab

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_RegularCharts_SCharts
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_RegModelC
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GenericRegularity_RegularAtCentre
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
theorem _root_.solution (φ : A →+* V) (e : ℕ) {f : FractionRing A} {u : ℝ} (h : ChV φ e f (u : EReal)) :
    ChV φ e f⁻¹ ((-u : ℝ) : EReal) := by
  obtain ⟨x, s, hs, hx, hfs, hu⟩ := (chval_fin_iff φ e f u).1 h
  have hx0 : x ≠ 0 := fun h0 => hx (by rw [h0, map_zero])
  have hxK : algebraMap A (FractionRing A) x ≠ 0 := fun h0 => hx0 (IsFractionRing.injective A _ (by rw [h0, map_zero]))
  have hf0 : f ≠ 0 := by
    intro h0
    rw [h0, zero_mul] at hfs
    exact hxK hfs.symm
  refine (chval_fin_iff φ e _ _).2 ⟨s, x, hx, hs, ?_, ?_⟩
  · rw [← hfs]
    field_simp
  · rw [hu]; ring
end GlobalTheory.Reg.Transfer
