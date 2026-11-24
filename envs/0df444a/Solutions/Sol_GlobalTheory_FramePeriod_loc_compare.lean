-- Prove2me | solution 1 for GlobalTheory.FramePeriod.loc_compare
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T16:07:13.574656+00:00
-- url     : https://prove2.me/submissions/6de4a8b7-7118-402b-9d0a-322e83c3470c

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_Signature
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_HermFormConjDiag
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_FrameOfPeriodLinear
import Theorems.Thm_GlobalTheory_FramePeriod_eq_of_hermC_eq
import Theorems.Thm_GlobalTheory_CMLattice_embAll_apply
import Theorems.Thm_GlobalTheory_FramePeriod_locPer_apply
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_Data_mulVec_eq_sum_col
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_hermC_smul_left
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_hermC_sum_left
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.CMLattice.embAll_apply



set_option autoImplicit false
open NumberField Matrix
open scoped nonZeroDivisors ComplexConjugate
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.FramePeriod
noncomputable section
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}
namespace GlobalTheory.FramePeriod
theorem _root_.solution (τ : E →+* ℂ) (Gm : Matrix (Fin r) (Fin r) E) (hG : Gm.det ≠ 0) (q : ℕ)
    (M M' K : Matrix (Fin r) (Fin r) ℂ) (hM : M.det ≠ 0) (hM' : M'.det ≠ 0)
    (hK : ∀ a c : Fin r, ¬ ((a : ℕ) < q ↔ (c : ℕ) < q) → K a c = 0)
    (h : ∀ u, locPer τ Gm q M' u = K *ᵥ locPer τ Gm q M u) :
    (∀ a c : Fin r, (a : ℕ) < q → K a c = (M⁻¹ * M') c a) ∧
      ∀ a c : Fin r, q ≤ (a : ℕ) → K a c = (M⁻¹ * M')⁻¹ a c := by
  classical
  have hMu : IsUnit M.det := isUnit_iff_ne_zero.2 hM
  constructor
  · intro a c ha
    have h1 : FD.col M' a = ∑ e, K a e • FD.col M e := by
      apply eq_of_hermC_eq τ Gm hG
      intro u
      have := congrFun (h u) a
      rw [locPer_apply, if_pos ha] at this
      rw [this, FD.hermC_sum_left, mulVec, dotProduct]
      refine Finset.sum_congr rfl fun e _ => ?_
      rw [FD.hermC_smul_left, locPer_apply]
      by_cases he : (e : ℕ) < q
      · rw [if_pos he]
      · rw [hK a e (by simp [ha, he])]; simp
    rw [← FD.Data.mulVec_eq_sum_col] at h1
    have h2 : M⁻¹ *ᵥ FD.col M' a = K a := by
      rw [h1, mulVec_mulVec, Matrix.nonsing_inv_mul _ hMu, one_mulVec]
    rw [← h2]
    rfl
  · intro a c ha
    have ha' : ¬ (a : ℕ) < q := not_lt.2 ha
    rw [Matrix.mul_inv_rev, Matrix.nonsing_inv_nonsing_inv _ hMu]
    have h1 := congrFun (h (M *ᵥ Pi.single c 1)) a
    rw [locPer_apply, if_neg ha', mulVec_mulVec] at h1
    have h2 : (K *ᵥ locPer τ Gm q M (M *ᵥ Pi.single c 1)) a = (K *ᵥ Pi.single c 1) a := by
      rw [mulVec, mulVec, dotProduct, dotProduct]
      refine Finset.sum_congr rfl fun e _ => ?_
      by_cases he : (e : ℕ) < q
      · rw [hK a e (by simp [ha', he])]; simp
      · rw [locPer_apply, if_neg he, mulVec_mulVec, Matrix.nonsing_inv_mul _ hMu, one_mulVec]
    rw [h2] at h1
    simpa using h1.symm
end GlobalTheory.FramePeriod
