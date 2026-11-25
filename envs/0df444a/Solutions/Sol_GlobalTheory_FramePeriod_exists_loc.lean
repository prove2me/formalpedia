-- Prove2me | solution 1 for GlobalTheory.FramePeriod.exists_loc
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T13:50:32.651699+00:00
-- url     : https://prove2.me/submissions/52690bec-117a-4744-a9b3-cd7bafc575a0

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_Signature
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_ProdCastLESucc
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TorusSplitting_EqTopOfForallEmbAllMem
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_HermFormConjDiag
import Theorems.Thm_GlobalTheory_FramePeriod_exists_upper_diag
import Theorems.Thm_GlobalTheory_FramePeriod_locPer_apply
import Theorems.Thm_GlobalTheory_FramePeriod_hermForm_conj_diag
import Theorems.Thm_GlobalTheory_CMLattice_embAll_apply
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_Data_mulVec_eq_sum_col
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_FrameDegreeData_gram_mul
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_gram_isHermitian
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_hermC_smul_left
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_hermC_smul_right
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_hermC_sum_left
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_hermC_sum_right
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
theorem _root_.solution (τ : E →+* ℂ) (Gm : Matrix (Fin r) (Fin r) E) (hG : ∀ a b, FD.cc (Gm a b) = Gm b a)
    (q : ℕ) (M : Matrix (Fin r) (Fin r) ℂ) (hM : M.det ≠ 0)
    (hm : ∀ i : Fin (r + 1), 0 < FD.psgn q i * (FD.lminor (FD.gram τ Gm M) i).re) :
    Function.Bijective (locPer τ Gm q M) ∧ ∃ Hl : Matrix (Fin r) (Fin r) ℂ, Hl.IsHermitian ∧
      (∀ z, z ≠ 0 → 0 < (hermForm Hl z z).re) ∧
      ∀ u w, (hermForm Hl (locPer τ Gm q M u) (locPer τ Gm q M w)).im = -(FD.hermC τ Gm u w).im := by
  obtain ⟨U, d, hU, hUd, hdiag, hd⟩ := exists_upper_diag q _ (FD.gram_isHermitian τ hG M) hm
  rw [← FD.FrameDegreeData.gram_mul] at hdiag
  have hUu : IsUnit U.det := by rw [hUd]; exact isUnit_one
  have hMu : IsUnit M.det := isUnit_iff_ne_zero.2 hM
  have hV : (U⁻¹).BlockTriangular id := by
    have := Matrix.invertibleOfIsUnitDet _ hUu
    exact Matrix.blockTriangular_inv_of_blockTriangular hU
  have hd0 : ∀ a, (d a : ℂ) ≠ 0 := fun a h => by
    have h1 := hd a
    rw [Complex.ofReal_eq_zero.1 h] at h1; simp at h1
  let c : (Fin r → ℂ) → Fin r → ℂ := fun u => U⁻¹ *ᵥ (M⁻¹ *ᵥ u)
  have hc : ∀ u, ∑ a, c u a • FD.col (M * U) a = u := by
    intro u
    rw [← FD.Data.mulVec_eq_sum_col]
    simp only [c, mulVec_mulVec]
    rw [Matrix.mul_assoc, Matrix.mul_nonsing_inv_cancel_left _ _ hUu, Matrix.mul_nonsing_inv _ hMu,
      one_mulVec]
  have hy : ∀ a b, FD.hermC τ Gm (FD.col (M * U) a) (FD.col (M * U) b) =
      if a = b then (d a : ℂ) else 0 := by
    intro a b
    have := congrFun (congrFun hdiag a) b
    simpa [FD.gram, diagonal_apply] using this
  have hyu : ∀ a u, FD.hermC τ Gm (FD.col (M * U) a) u = d a * conj (c u a) := by
    intro a u
    conv_lhs => rw [← hc u]
    rw [FD.hermC_sum_right]
    simp only [FD.hermC_smul_right, hy]
    simp [mul_comm]
  have huw : ∀ u w, FD.hermC τ Gm u w = ∑ a, (d a : ℂ) * (c u a * conj (c w a)) := by
    intro u w
    conv_lhs => rw [← hc u]
    rw [FD.hermC_sum_left]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [FD.hermC_smul_left, hyu]; ring
  let S : Matrix (Fin r) (Fin r) ℂ := Matrix.of fun a b => if (a : ℕ) < q then U b a / d a else U⁻¹ a b
  have hS : ∀ u a, (S *ᵥ locPer τ Gm q M u) a = if (a : ℕ) < q then conj (c u a) else c u a := by
    intro u a
    split_ifs with ha
    · have h1 : FD.col (M * U) a = ∑ b, U b a • FD.col M b := by
        funext k; simp [FD.col, Matrix.mul_apply, Finset.sum_apply, mul_comm]
      have h2 := hyu a u
      rw [h1, FD.hermC_sum_left] at h2
      rw [← mul_right_inj' (hd0 a), ← h2]
      simp only [mulVec, dotProduct, S, of_apply, if_pos ha, Finset.mul_sum]
      refine Finset.sum_congr rfl fun b _ => ?_
      rw [FD.hermC_smul_left, locPer_apply]
      by_cases hb : (b : ℕ) < q
      · rw [if_pos hb]; field_simp [hd0 a]
      · have : U b a = 0 := hU (show a < b by rw [Fin.lt_def]; omega)
        simp [this]
    · simp only [c]
      rw [mulVec, mulVec, dotProduct, dotProduct]
      refine Finset.sum_congr rfl fun b _ => ?_
      simp only [S, of_apply, if_neg ha, locPer_apply]
      by_cases hb : (b : ℕ) < q
      · have : U⁻¹ a b = 0 := hV (show b < a by rw [Fin.lt_def]; omega)
        simp [this]
      · rw [if_neg hb]
  have hS0 : ∀ u, S *ᵥ locPer τ Gm q M u = 0 → u = 0 := by
    intro u hu
    have : c u = 0 := by
      funext a
      have := hS u a
      rw [hu] at this
      split_ifs at this
      · simpa using this.symm
      · exact this.symm
    rw [← hc u, this]; simp
  have hinj : Function.Injective (locPer τ Gm q M) := by
    rw [injective_iff_map_eq_zero]
    intro u hu
    apply hS0; rw [hu, mulVec_zero]
  have hsurj := LinearMap.injective_iff_surjective.1 hinj
  refine ⟨⟨hinj, hsurj⟩, Sᵀ * Matrix.diagonal (fun a : Fin r => ((FD.sgn q a * d a : ℝ) : ℂ)) *
    S.map (starRingEnd ℂ), ?_, ?_, ?_⟩
  · have h1 : (Matrix.diagonal (fun a : Fin r => ((FD.sgn q a * d a : ℝ) : ℂ))).IsHermitian := by
      rw [Matrix.isHermitian_diagonal_iff]
      intro a; exact Complex.conj_ofReal _
    have := Matrix.isHermitian_mul_mul_conjTranspose Sᵀ h1
    exact this
  · intro z hz
    obtain ⟨u, rfl⟩ := hsurj z
    have h1 : S *ᵥ locPer τ Gm q M u ≠ 0 := fun h => hz (by rw [hS0 u h, map_zero])
    obtain ⟨i, hi⟩ := Function.ne_iff.1 h1
    rw [hermForm_conj_diag S (fun a : Fin r => FD.sgn q a * d a), Complex.re_sum]
    simp only [Complex.mul_conj, ← Complex.ofReal_mul, Complex.ofReal_re]
    exact Finset.sum_pos' (fun j _ => mul_nonneg (hd j).le (Complex.normSq_nonneg _))
      ⟨i, Finset.mem_univ _, mul_pos (hd i) (Complex.normSq_pos.2 hi)⟩
  · intro u w
    rw [hermForm_conj_diag S (fun a : Fin r => FD.sgn q a * d a), huw, Complex.im_sum, Complex.im_sum,
      ← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [hS, hS, Complex.im_ofReal_mul, Complex.im_ofReal_mul, FD.sgn]
    split_ifs
    · simp; ring
    · ring
end GlobalTheory.FramePeriod
