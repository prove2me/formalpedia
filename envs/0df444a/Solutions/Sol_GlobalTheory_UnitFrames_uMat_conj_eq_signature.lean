-- Prove2me | solution 1 for GlobalTheory.UnitFrames.uMat_conj_eq_signature
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T13:43:22.194472+00:00
-- url     : https://prove2.me/submissions/721fbae4-699a-45bb-a320-3e2e3bcf3137

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_ProdCastLESucc
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ExistenceOfLattices_UnivFrame
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ExistenceOfLattices_NormConst
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_CuspFree
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_RdOrbIntOfLatZ
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_AllTest
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_FundamentalDomainPointBound
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_SecBaseChangeAnySt
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_Landherr__ExistsNormTensor_9eff20d6b37353d0
import Definitions.Def_Development_AbelianVarietyTheory_Statements_HyperbolicHypotheses_HypothesesInhabitedHyperbolic
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_UnitFrameEqOrthonormalMulTriangular
import Theorems.Thm_GlobalTheory_UnitFrames_psgn_sq
import Theorems.Thm_GlobalTheory_HostModel_host_d
import Theorems.Thm_GlobalTheory_HostModel_host_rt
import Theorems.Thm_GlobalTheory_HostModel_host_rt0_eq_I_mul_sqrt_seven
import Theorems.Thm_GlobalTheory_HostModel_host_w0_eq_halfSqrtNegSeven
import Theorems.Thm_GlobalTheory_HostModel_hypDatum_p
import Theorems.Thm_GlobalTheory_HostModel_hypDatum_q
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
attribute [local simp] GlobalTheory.HostModel.host_d
attribute [local simp] GlobalTheory.HostModel.host_rt
attribute [local simp] GlobalTheory.HostModel.host_rt0_eq_I_mul_sqrt_seven
attribute [local simp] GlobalTheory.HostModel.host_w0_eq_halfSqrtNegSeven
attribute [local simp] GlobalTheory.HostModel.hypDatum_p
attribute [local simp] GlobalTheory.HostModel.hypDatum_q



set_option autoImplicit false
open NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj Formalism.L2.PjFree
open AlgebraicGeometry CategoryTheory Limits ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Frames GlobalTheory.FrameUnif
open scoped Matrix nonZeroDivisors
open GlobalTheory GlobalTheory.UnitFrames
open ReciprocityTheory.ChartRestriction.G.FD.FrameDegreeData
variable {n : ℕ}
namespace GlobalTheory.UnitFrames
theorem _root_.solution (p0 : ℕ) (A : Matrix (Fin n) (Fin n) ℂ) (hA : A.IsHermitian)
    (hs : ∀ i : Fin (n + 1), 0 < psgn p0 i * (lminor A i).re)
    (h1 : ∀ i : Fin (n + 1), ‖lminor A i‖ = 1) :
    (uMat A)ᵀ * A * (uMat A).map (starRingEnd ℂ)
      = Matrix.diagonal fun a : Fin n => ((sgn p0 (a : ℕ) : ℝ) : ℂ) := by
  have hdet : ∀ c : Fin n, (blk A c).det ≠ 0 := by
    intro c h0
    have h := h1 ⟨c, Nat.lt_succ_of_lt c.isLt⟩
    have : lminor A ⟨c, Nat.lt_succ_of_lt c.isLt⟩ = 0 := h0
    rw [this] at h
    simp at h
  set B := (uMat A)ᵀ * A * (uMat A).map (starRingEnd ℂ) with hB
  have hH : B.IsHermitian := by
    have e : (uMat A).map (starRingEnd ℂ) = ((uMat A)ᵀ)ᴴ := by
      ext a c; simp [Matrix.conjTranspose_apply]
    rw [hB, e]
    exact Matrix.isHermitian_mul_mul_conjTranspose _ hA
  have hdiag : B = Matrix.diagonal fun k => B k k := by
    ext a c
    rcases lt_trichotomy a c with hac | hac | hac
    · rw [Matrix.diagonal_apply_ne _ (ne_of_lt hac), ← hH.apply a c, hB,
        uGu_lower _ hdet hac, star_zero]
    · subst hac
      rw [Matrix.diagonal_apply_eq]
    · rw [Matrix.diagonal_apply_ne _ (ne_of_gt hac), hB, uGu_lower _ hdet hac]
  have hprod : ∀ i : Fin (n + 1), lminor A i
      = ∏ j : Fin i, (fun k => B k k) (Fin.castLE (Nat.le_of_lt_succ i.isLt) j) := by
    intro i
    have e : lminor B i = lminor A i := by
      rw [hB, lminor_conj (uMat_upper _) i]
      simp only [uMat_diag, Finset.prod_const_one, one_mul, map_one, mul_one]
    rw [← e]
    exact (congrArg (fun M => lminor M i) hdiag).trans (lminor_diagonal _ i)
  have hre : ∀ k, (B k k).im = 0 := fun k => Complex.conj_eq_iff_im.1 (hH.apply k k)
  have hval : ∀ i : Fin (n + 1), lminor A i = ((psgn p0 i : ℝ) : ℂ) := by
    intro i
    have him : (lminor A i).im = 0 := by
      rw [hprod i]
      refine Complex.conj_eq_iff_im.1 ?_
      rw [map_prod]
      exact Finset.prod_congr rfl fun j _ => Complex.conj_eq_iff_im.2 (hre _)
    have hd : lminor A i = (((lminor A i).re : ℝ) : ℂ) := by apply Complex.ext <;> simp [him]
    have hn := h1 i
    have hp := hs i
    rw [hd, Complex.norm_real, Real.norm_eq_abs] at hn
    rw [hd, Complex.ofReal_inj]
    rcases psgn_sq p0 i with h | h <;> rw [h] at hp ⊢
    · rw [abs_of_pos (by linarith)] at hn; exact hn
    · rw [abs_of_neg (by linarith)] at hn; linarith
  rw [hdiag]
  congr 1
  funext k
  have hsucc : lminor A k.succ = lminor A k.castSucc * B k k := by
    rw [hprod k.succ, hprod k.castSucc]
    exact prod_castLE_succ (f := fun k => B k k) k.isLt
  rw [hval, hval, Fin.val_succ, Fin.val_castSucc, psgn_succ, Complex.ofReal_mul] at hsucc
  have hne : ((psgn p0 k : ℝ) : ℂ) ≠ 0 := by
    rcases psgn_sq p0 k with h | h <;> simp [h]
  exact (mul_left_cancel₀ hne hsucc).symm
end GlobalTheory.UnitFrames
