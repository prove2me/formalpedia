-- Prove2me | solution 1 for GlobalTheory.Published.GaussBonnet.IsOrthFrame.exists_inv
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T18:08:25.880549+00:00
-- url     : https://prove2.me/submissions/b46a9471-7718-4ea6-8ff0-540e37d3195e

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_Signature
import Definitions.Def_Formalism_LocalRingCardinality_DataCD
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TorusHaarMeasure_ExistsStabiliserImageSubgroup
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_Divisors__OfPositiveTrivial_b4304d4fbed4f169
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_HermitianTraceFormVanishing_cc_add
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_HermitianTraceFormVanishing_cc_cc
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_HermitianTraceFormVanishing_cc_eq_zero
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_HermitianTraceFormVanishing_cc_intCast
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_HermitianTraceFormVanishing_cc_inv
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_HermitianTraceFormVanishing_cc_mul
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_HermitianTraceFormVanishing_cc_natCast
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_HermitianTraceFormVanishing_cc_neg
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_HermitianTraceFormVanishing_cc_one
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_HermitianTraceFormVanishing_cc_sub
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_HermitianTraceFormVanishing_cc_zero
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] ReciprocityTheory.ChartRestriction.G.FD.HermitianTraceFormVanishing.cc_add
attribute [local simp] ReciprocityTheory.ChartRestriction.G.FD.HermitianTraceFormVanishing.cc_cc
attribute [local simp] ReciprocityTheory.ChartRestriction.G.FD.HermitianTraceFormVanishing.cc_eq_zero
attribute [local simp] ReciprocityTheory.ChartRestriction.G.FD.HermitianTraceFormVanishing.cc_intCast
attribute [local simp] ReciprocityTheory.ChartRestriction.G.FD.HermitianTraceFormVanishing.cc_inv
attribute [local simp] ReciprocityTheory.ChartRestriction.G.FD.HermitianTraceFormVanishing.cc_mul
attribute [local simp] ReciprocityTheory.ChartRestriction.G.FD.HermitianTraceFormVanishing.cc_natCast
attribute [local simp] ReciprocityTheory.ChartRestriction.G.FD.HermitianTraceFormVanishing.cc_neg
attribute [local simp] ReciprocityTheory.ChartRestriction.G.FD.HermitianTraceFormVanishing.cc_one
attribute [local simp] ReciprocityTheory.ChartRestriction.G.FD.HermitianTraceFormVanishing.cc_sub
attribute [local simp] ReciprocityTheory.ChartRestriction.G.FD.HermitianTraceFormVanishing.cc_zero



set_option autoImplicit false
noncomputable section
open NumberField MeasureTheory ReciprocityTheory.ChartRestriction.G.FD Formalism.BasicNotions
open scoped Matrix ENNReal
open GlobalTheory GlobalTheory.Published
open GlobalTheory.Published.GaussBonnet
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}
namespace GlobalTheory.Published.GaussBonnet
namespace IsOrthFrame
theorem _root_.solution {τ : E →+* ℂ} {G : Matrix (Fin r) (Fin r) E} {P Q : ℕ}
    {B : Matrix (Fin r) (Fin P ⊕ Fin Q) ℂ} (hB : IsOrthFrame τ G B) (hr : P + Q = r) :
    Bᴴ * ((G.map τ).map (starRingEnd ℂ) * B) = Formalism.UG.Jpq P Q ∧
      ∃ C : Matrix (Fin P ⊕ Fin Q) (Fin r) ℂ, C * B = 1 ∧ B * C = 1 := by
  have hJ : Formalism.UG.Jpq P Q * Formalism.UG.Jpq P Q = 1 := by
    simp [Formalism.UG.Jpq, Matrix.fromBlocks_multiply]
  have h1 : Bᴴ * ((G.map τ).map (starRingEnd ℂ) * B) = Formalism.UG.Jpq P Q := by
    ext a b
    have h := congrArg (starRingEnd ℂ) (hB a b)
    have h' : starRingEnd ℂ (Formalism.UG.Jpq P Q a b) = Formalism.UG.Jpq P Q a b := by
      rcases a with a | a <;> rcases b with b | b <;> simp [Formalism.UG.Jpq, Matrix.one_apply, apply_ite]
    rw [h'] at h
    rw [← h]
    simp [hermC, Matrix.mul_apply, Finset.mul_sum, mul_assoc]
  have h2 : (Formalism.UG.Jpq P Q * (Bᴴ * (G.map τ).map (starRingEnd ℂ))) * B = 1 := by
    rw [Matrix.mul_assoc, Matrix.mul_assoc, h1, hJ]
  refine ⟨h1, _, h2, ?_⟩
  exact (Matrix.mul_eq_one_comm_of_card_eq _ _ _ (by simp [hr])).1 h2
end IsOrthFrame
end GlobalTheory.Published.GaussBonnet
