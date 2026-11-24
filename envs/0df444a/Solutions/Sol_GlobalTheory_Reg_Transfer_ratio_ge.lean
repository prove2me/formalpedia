-- Prove2me | solution 1 for GlobalTheory.Reg.Transfer.ratio_ge
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T20:31:11.173639+00:00
-- url     : https://prove2.me/submissions/34720851-b142-4a36-b1ed-24e267b60096

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_RegularCharts_SCharts
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_RegModelC
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GenericRegularity_RegularAtCentre
import Theorems.Thm_GlobalTheory_Reg_Transfer_nval_nonneg
import Theorems.Thm_GlobalTheory_Reg_Transfer_chval_eq
import Theorems.Thm_GlobalTheory_Reg_Transfer_nval_eq_vr
import Theorems.Thm_GlobalTheory_Reg_Transfer_fin_of_ne_top
import Theorems.Thm_Formalism_L2_Pj_nval_mul
import Theorems.Thm_Formalism_L2_Pj_nval_ne_bot
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
theorem _root_.solution {φ : A →+* V} {e : ℕ} {f1 : FractionRing A} {r1 r2 : EReal} {xk : A}
    (h1 : ChV φ e f1 r1) (h2 : ChV φ e (algebraMap A (FractionRing A) xk * f1) r2) : r1 ≤ r2 := by
  obtain ⟨x1, s1, hs1, hf1, rfl⟩ := h1
  have hrel : algebraMap A (FractionRing A) xk * f1 * algebraMap A (FractionRing A) s1 =
      algebraMap A (FractionRing A) (xk * x1) := by rw [mul_assoc, hf1, map_mul]
  rw [chval_eq φ e _ r2 h2 (xk * x1) s1 hrel hs1, map_mul, map_mul, nval_mul, nval_eq_vr e hs1]
  have h0 := nval_nonneg e (φ xk)
  by_cases hx : φ x1 = 0
  · have hX := nval_ne_bot (V := V) e (algebraMap V (FractionRing V) (φ xk))
    rw [hx, map_zero, nval_zero]
    exact EReal.sub_le_sub (le_of_eq (EReal.add_top_of_ne_bot hX).symm) le_rfl
  · rw [nval_eq_vr e hx]
    rcases eq_or_ne (nval V e (algebraMap V (FractionRing V) (φ xk))) ⊤ with ht | ht
    · rw [ht, EReal.top_add_of_ne_bot (EReal.coe_ne_bot _), EReal.top_sub_coe]; exact le_top
    · obtain ⟨u, hu⟩ := fin_of_ne_top ht (nval_ne_bot (V := V) e _)
      rw [hu, ← EReal.coe_add, ← EReal.coe_sub, ← EReal.coe_sub, EReal.coe_le_coe_iff]
      rw [hu] at h0
      have := EReal.coe_nonneg.1 h0
      linarith
end GlobalTheory.Reg.Transfer
