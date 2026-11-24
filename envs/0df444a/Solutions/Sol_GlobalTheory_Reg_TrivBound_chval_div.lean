-- Prove2me | solution 1 for GlobalTheory.Reg.TrivBound.chval_div
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T20:15:38.307791+00:00
-- url     : https://prove2.me/submissions/8cd292d7-fa05-4eab-b47b-351ebee52f3b

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_RegModelC
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_RegularCharts_SCharts
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_FrameCharts
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_SecBaseChangeAnySt
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_RegQFree
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_FnTrdegOf
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_RealPtGeo
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_IntAllProofFree
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GenericRegularity_CombinedBoundAtTrivialValuationsOfCharts
import Theorems.Thm_GlobalTheory_Reg_TrivBound_mem_of_vV_nonneg
import Theorems.Thm_GlobalTheory_Reg_TrivBound_ne_zero_map
import Theorems.Thm_GlobalTheory_Reg_TrivBound_chval_eq
import Theorems.Thm_Formalism_L2_Pj_nval_of_ne
import Theorems.Thm_Formalism_L2_Pj_vV_mul


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.Reg GlobalTheory.Reg.TrivBound
open IsLocalRing Formalism.L2.Pj GlobalTheory.Reg
variable {V : Type} [CommRing V] [IsDomain V] [IsDiscreteValuationRing V]
variable {A : Type} [CommRing A] [IsDomain A]
namespace GlobalTheory.Reg.TrivBound
theorem _root_.solution (φ : A →+* V) (e : ℕ) (he : 0 < e) (f : FractionRing A) (r : EReal) (h : ChV φ e f r)
    (hr : 0 ≤ r) (a b : A) (hab : f * algebraMap A (FractionRing A) b = algebraMap A (FractionRing A) a)
    (hb : φ b ≠ 0) : ∃ w : V, φ a = w * φ b := by
  by_cases ha : φ a = 0
  · exact ⟨0, by rw [ha, zero_mul]⟩
  rw [chval_eq φ e f r h a b hab hb, nval_of_ne (ne_zero_map ha), nval_of_ne (ne_zero_map hb),
    ← EReal.coe_sub, EReal.coe_nonneg, div_sub_div_same] at hr
  have he' : (0 : ℝ) < e := by exact_mod_cast he
  have hle : (vV V (algebraMap V (FractionRing V) (φ b)) : ℝ) ≤ vV V (algebraMap V (FractionRing V) (φ a)) := by
    have := (div_nonneg_iff.1 hr)
    rcases this with ⟨h1, -⟩ | ⟨-, h2⟩
    · linarith
    · linarith
  have hle' : vV V (algebraMap V (FractionRing V) (φ b)) ≤ vV V (algebraMap V (FractionRing V) (φ a)) := by
    exact_mod_cast hle
  set y := algebraMap V (FractionRing V) (φ a) / algebraMap V (FractionRing V) (φ b)
  have hy0 : y ≠ 0 := div_ne_zero (ne_zero_map ha) (ne_zero_map hb)
  have hyv : vV V y + vV V (algebraMap V (FractionRing V) (φ b)) = vV V (algebraMap V (FractionRing V) (φ a)) := by
    rw [← vV_mul hy0 (ne_zero_map hb), div_mul_cancel₀ _ (ne_zero_map hb)]
  obtain ⟨w, hw⟩ := mem_of_vV_nonneg y hy0 (by omega)
  refine ⟨w, IsFractionRing.injective V (FractionRing V) ?_⟩
  rw [map_mul, hw, div_mul_cancel₀ _ (ne_zero_map hb)]
end GlobalTheory.Reg.TrivBound
