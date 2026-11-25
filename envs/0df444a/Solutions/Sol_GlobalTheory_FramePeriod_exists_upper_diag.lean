-- Prove2me | solution 1 for GlobalTheory.FramePeriod.exists_upper_diag
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T13:30:04.858111+00:00
-- url     : https://prove2.me/submissions/85197124-ce02-4209-a839-5da7cf6b8e68

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_Signature
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_ProdCastLESucc
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TorusSplitting_EqTopOfForallEmbAllMem
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_HermFormConjDiag
import Theorems.Thm_GlobalTheory_CMLattice_embAll_apply
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_FrameDegreeData_lminor_conj
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_FrameDegreeData_lminor_diagonal
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_FrameDegreeData_prod_castLE_succ
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_FrameDegreeData_psgn_succ
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_FrameDegreeData_uGu_lower
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_FrameDegreeData_uMat_diag
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_FrameDegreeData_uMat_upper
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
namespace GlobalTheory.FramePeriod
theorem _root_.solution {n : ℕ} (q : ℕ) (A : Matrix (Fin n) (Fin n) ℂ) (hA : A.IsHermitian)
    (hm : ∀ i : Fin (n + 1), 0 < FD.psgn q i * (FD.lminor A i).re) :
    ∃ (U : Matrix (Fin n) (Fin n) ℂ) (d : Fin n → ℝ), U.BlockTriangular id ∧ U.det = 1 ∧
      Uᵀ * A * U.map (starRingEnd ℂ) = Matrix.diagonal (fun a => (d a : ℂ)) ∧
      ∀ a : Fin n, 0 < FD.sgn q a * d a := by
  have hdet : ∀ c : Fin n, (FD.FrameDegreeData.blk A c).det ≠ 0 := by
    intro c h0
    have h := hm ⟨c, Nat.lt_succ_of_lt c.isLt⟩
    have : FD.lminor A ⟨c, Nat.lt_succ_of_lt c.isLt⟩ = 0 := h0
    rw [this] at h
    simp at h
  set U := FD.FrameDegreeData.uMat A with hU
  set B := Uᵀ * A * U.map (starRingEnd ℂ) with hB
  have hH : B.IsHermitian := by
    have := Matrix.isHermitian_mul_mul_conjTranspose Uᵀ hA
    exact this
  have hre : ∀ k, B k k = (((B k k).re : ℝ) : ℂ) := by
    intro k
    have h1 := congrFun (congrFun hH k) k
    rw [Matrix.conjTranspose_apply] at h1
    exact (Complex.conj_eq_iff_re.1 h1).symm
  have hBd : B = Matrix.diagonal (fun a => (((B a a).re : ℝ) : ℂ)) := by
    ext a c
    rcases lt_trichotomy a c with hac | hac | hac
    · rw [Matrix.diagonal_apply_ne _ (ne_of_lt hac)]
      have h1 := congrFun (congrFun hH a) c
      rw [Matrix.conjTranspose_apply] at h1
      rw [← h1, hB, hU, FD.FrameDegreeData.uGu_lower _ hdet hac, star_zero]
    · subst hac
      rw [Matrix.diagonal_apply_eq]; exact hre a
    · rw [Matrix.diagonal_apply_ne _ (ne_of_gt hac), hB, hU, FD.FrameDegreeData.uGu_lower _ hdet hac]
  have hprod : ∀ i : Fin (n + 1), FD.lminor A i =
      ∏ j : Fin i, (((B (Fin.castLE (Nat.le_of_lt_succ i.isLt) j)
        (Fin.castLE (Nat.le_of_lt_succ i.isLt) j)).re : ℝ) : ℂ) := by
    intro i
    have h1 : FD.lminor B i = FD.lminor A i := by
      rw [hB, hU, FD.FrameDegreeData.lminor_conj (FD.FrameDegreeData.uMat_upper _) i]
      simp only [FD.FrameDegreeData.uMat_diag, Finset.prod_const_one, one_mul, map_one, mul_one]
    rw [← h1]
    conv_lhs => rw [hBd]
    rw [FD.FrameDegreeData.lminor_diagonal]
  refine ⟨U, fun a => (B a a).re, FD.FrameDegreeData.uMat_upper _, ?_, hBd, fun k => ?_⟩
  · rw [hU, Matrix.det_of_isUpperTriangular (FD.FrameDegreeData.uMat_upper _)]
    simp only [FD.FrameDegreeData.uMat_diag, Finset.prod_const_one]
  · have hs : FD.lminor A k.succ = FD.lminor A k.castSucc * (((B k k).re : ℝ) : ℂ) := by
      rw [hprod k.succ, hprod k.castSucc]
      exact FD.FrameDegreeData.prod_castLE_succ (f := fun a => (((B a a).re : ℝ) : ℂ)) k.isLt
    have h1 := hm k.succ
    have h0 := hm k.castSucc
    rw [hs, Complex.re_mul_ofReal, Fin.val_succ, FD.FrameDegreeData.psgn_succ] at h1
    rw [Fin.val_castSucc] at h0
    refine (mul_pos_iff_of_pos_left h0).1 ?_
    simpa only [mul_assoc, mul_left_comm] using h1
end GlobalTheory.FramePeriod
