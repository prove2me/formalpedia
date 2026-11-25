-- Prove2me | solution 1 for GlobalTheory.LogLinear.formalGroup_log_endomorphism_linear
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T04:51:29.090645+00:00
-- url     : https://prove2.me/submissions/f9d70582-fe64-49ab-8498-4b8204a3c908

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_TwoChartAtlas_AdditionLawSecondIdentity
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FormalGroupCharts_EqZeroOfAdditiveOfPderiv
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_RingsOfIntegers_CoeffSingleLawAdd
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FormalGroupCharts_FormalGroupLogEndomorphismLinear
import Theorems.Thm_GlobalTheory_LogLinear_eq_zero_of_additive
import Theorems.Thm_GlobalTheory_LogLinear_ev_sum_C_mul
import Theorems.Thm_GlobalTheory_LogLinear_dLin_comp1
import Theorems.Thm_GlobalTheory_LogLinear_germ_comp_additive_at_points
import Theorems.Thm_GlobalTheory_FormalCalc_formalExp_zero
import Theorems.Thm_GlobalTheory_FormalCalc_formalLog_one
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_WickVanishing_gp_addOf
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_WickVanishing_gp_comp1
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_WickVanishing_gp_pt
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_WickVanishing_gt_comp1_comp1
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_WickVanishing_gt_ev_sub
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_WickVanishing_single_point_zero_constant
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.FormalCalc.formalExp_zero
attribute [local simp] GlobalTheory.FormalCalc.formalLog_one



set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open MvPowerSeries ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.TB ReciprocityTheory.ChartRestriction.G.TB.WickVanishing
open GlobalTheory GlobalTheory.LogLinear
variable {k : Type} [CommRing k] {d : ℕ}
namespace GlobalTheory.LogLinear
theorem _root_.solution :
    ∀ (k : Type) [CommRing k] [Algebra ℚ k] (d : ℕ) (G : FGLaw k d) (ℓ α : Pt k 1 d),
      (∀ i, MvPowerSeries.constantCoeff (ℓ i) = 0) → dLin ℓ = 1 →
      comp1 ℓ (G.add (pt k (n := 2) d 0) (pt k (n := 2) d 1)) =
        comp1 ℓ (pt k (n := 2) d 0) + comp1 ℓ (pt k (n := 2) d 1) →
      (∀ i, MvPowerSeries.constantCoeff (α i) = 0) →
      comp1 α (G.add (pt k (n := 2) d 0) (pt k (n := 2) d 1)) =
        G.add (comp1 α (pt k (n := 2) d 0)) (comp1 α (pt k (n := 2) d 1)) →
      ∀ i, comp1 ℓ α i = ∑ j, MvPowerSeries.C (dLin α i j) * ℓ j := by
  intro k _ _ d G ℓ α _ h1 hadd hα hhom i
  have hS : GP (G.add (pt k (n := 2) d 0) (pt k (n := 2) d 1)) :=
    gp_addOf _ G.const _ _ (gp_pt _) (gp_pt _)
  have hev (a : Pt k 2 d) (ha : GP a) :
      ev ![a] (comp1 ℓ α i - ∑ j, C (dLin α i j) * ℓ j) =
        comp1 ℓ (comp1 α a) i - ∑ j, C (dLin α i j) * comp1 ℓ a j := by
    rw [gt_ev_sub _ (single_point_zero_constant ha), ev_sum_C_mul _ (single_point_zero_constant ha), ← gt_comp1_comp1 ℓ α hα a ha]
    rfl
  rw [← sub_eq_zero]
  refine eq_zero_of_additive G _ ?_ fun l => ?_
  · rw [hev _ hS, hev _ (gp_pt _), hev _ (gp_pt _), hhom, hadd,
      germ_comp_additive_at_points G ℓ hadd _ _ (gp_comp1 α _ hα (gp_pt _)) (gp_comp1 α _ hα (gp_pt _))]
    simp only [Pi.add_apply, mul_add, Finset.sum_add_distrib]
    ring
  · have h2 : dLin (comp1 ℓ α) i l = (dLin α * dLin ℓ) i l := by
      rw [dLin_comp1 ℓ α hα, h1, one_mul, mul_one]
    rw [map_sub, map_sum, sub_eq_zero]
    simp only [coeff_C_mul]
    exact h2
end GlobalTheory.LogLinear
