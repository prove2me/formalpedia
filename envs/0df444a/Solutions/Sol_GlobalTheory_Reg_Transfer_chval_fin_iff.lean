-- Prove2me | solution 1 for GlobalTheory.Reg.Transfer.chval_fin_iff
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T13:03:37.310585+00:00
-- url     : https://prove2.me/submissions/4439d603-f069-4915-89c2-aad1a7551b27

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_RegularCharts_SCharts
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_RegModelC
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GenericRegularity_RegularAtCentre
import Theorems.Thm_GlobalTheory_Reg_Transfer_ne_zero_map
import Theorems.Thm_GlobalTheory_Reg_Transfer_nval_eq_vr
import Theorems.Thm_Formalism_L2_Pj_nval_of_ne
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
theorem _root_.solution (φ : A →+* V) (e : ℕ) (f : FractionRing A) (u : ℝ) :
    ChV φ e f (u : EReal) ↔ ∃ x s : A, φ s ≠ 0 ∧ φ x ≠ 0 ∧
      f * algebraMap A (FractionRing A) s = algebraMap A (FractionRing A) x ∧ u = vr e (φ x) - vr e (φ s) := by
  constructor
  · rintro ⟨x, s, hs, hfs, hu⟩
    have hx : φ x ≠ 0 := by
      intro hx
      rw [hx, map_zero, nval_zero, nval_of_ne (ne_zero_map hs), EReal.top_sub_coe] at hu
      exact EReal.coe_ne_top u hu
    refine ⟨x, s, hs, hx, hfs, ?_⟩
    rw [nval_eq_vr e hx, nval_eq_vr e hs, ← EReal.coe_sub] at hu
    exact EReal.coe_injective hu
  · rintro ⟨x, s, hs, hx, hfs, hu⟩
    refine ⟨x, s, hs, hfs, ?_⟩
    rw [nval_eq_vr e hx, nval_eq_vr e hs, ← EReal.coe_sub, hu]
end GlobalTheory.Reg.Transfer
