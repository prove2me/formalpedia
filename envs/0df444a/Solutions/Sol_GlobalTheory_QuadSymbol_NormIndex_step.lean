-- Prove2me | solution 1 for GlobalTheory.QuadSymbol.NormIndex.step
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T19:58:57.876842+00:00
-- url     : https://prove2.me/submissions/2e95ef4d-8d6a-4886-9574-e9755b0a11d9

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_PublishedTheorems_TwistedTraceFormula_QuadraticClassFieldTheory
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HeightProofs_QuadraticExtNormFormOverAlgebra
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HeightProofs_UnitNormFormAtOddPlace
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_ExistsUnitMulSqQuadraticDefectStep
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_ExistsGlobalUniformizerResidueRepresentatives
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_ExistsSubSqLtOneOfTwoLtOne
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_IsSquareMulOfNonsquareUnits
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_IsSquareOfValuedSubOneLt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_IsSquareMulInfinite
import Theorems.Thm_GlobalTheory_QuadSymbol_NormIndex_Nm_sq
import Theorems.Thm_GlobalTheory_QuadSymbol_NormIndex_even_or_odd
import Theorems.Thm_GlobalTheory_QuadSymbol_NormIndex_ne_zero_of_exp
import Theorems.Thm_GlobalTheory_QuadSymbol_NormIndex_val_mul_zpow_sq
import Theorems.Thm_GlobalTheory_QuadSymbol_NormIndex_map_two_le
import Theorems.Thm_GlobalTheory_QuadSymbol_NormIndex_map_four
import Theorems.Thm_GlobalTheory_Idele_adelicMulEquiv_mk
import Theorems.Thm_GlobalTheory_LocalLattice_hermPairing_apply
import Theorems.Thm_GlobalTheory_QNorm_exists_unit_mul_sq_sub_one_lt
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
attribute [local simp] GlobalTheory.Idele.adelicMulEquiv_mk
attribute [local simp] GlobalTheory.LocalLattice.hermPairing_apply
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
open NumberField IsDedekindDomain IsLocalRing
open scoped WithZero
open GlobalTheory GlobalTheory.QuadSymbol
open GlobalTheory.QuadSymbol.NormIndex
variable {K : Type} [Field K]
variable (w : Valuation K ℤᵐ⁰)
namespace GlobalTheory.QuadSymbol.NormIndex
theorem _root_.solution {π : K} (hπ : w π = WithZero.exp (-1))
    (hres : w 2 < 1 → ∀ x : K, w x ≤ 1 → ∃ y : K, w y ≤ 1 ∧ w (x - y ^ 2) < 1)
    {z : K} {j : ℤ} (hz : w z = WithZero.exp (2 * j + 1)) {u : K} (hu : w u = 1)
    (h4 : w 4 < w (u - 1)) : ∃ m : K, w m = 1 ∧ Nm z m ∧ w (u * m - 1) < w (u - 1) := by
  have hle : w (u - 1) ≤ 1 := w.map_sub_le hu.le (by simp)
  have hw2 : w 2 < 1 := by
    refine lt_of_le_of_ne (map_two_le w) fun h1 => ?_
    rw [map_four, h1, one_mul] at h4
    exact absurd hle (not_le.2 h4)
  have hne : u - 1 ≠ 0 := by
    intro h0; rw [h0] at h4; simp at h4
  rcases even_or_odd w hne with ⟨k, hk⟩ | ⟨k, hk⟩
  · have hk0 : 2 * k ≤ 0 := by
      rw [hk, ← WithZero.exp_zero, WithZero.exp_le_exp] at hle; exact hle
    obtain ⟨c, hc, hlt⟩ := GlobalTheory.QNorm.exists_unit_mul_sq_sub_one_lt K w u π (-k).toNat hπ
      (hres hw2) hu h4 (by rw [hk]; congr 1; omega)
    exact ⟨c ^ 2, by rw [map_pow, hc, one_pow], Nm.sq _ _, hlt⟩
  · have hk0 : 2 * k + 1 ≤ 0 := by
      rw [hk, ← WithZero.exp_zero, WithZero.exp_le_exp] at hle; exact hle
    have hlt1 : w (u - 1) < 1 := by
      rw [hk, ← WithZero.exp_zero, WithZero.exp_lt_exp]; omega
    have hs : w (z * (π ^ (j - k)) ^ 2) = w (u - 1) := by
      rw [val_mul_zpow_sq w hπ hz, hk]; congr 1; ring
    set s := π ^ (j - k)
    have hpos : 0 < w (u - 1) := by rw [hk]; exact WithZero.exp_pos
    have hs0 : z * s ^ 2 ≠ 0 := ne_zero_of_exp w (hs.trans hk)
    obtain ⟨y, hy, hy'⟩ := hres hw2 ((u - 1) / (z * s ^ 2)) (by
      rw [map_div₀, hs, div_self hpos.ne'])
    have h1 : w (z * s ^ 2 * y ^ 2) < 1 := by
      rw [map_mul, hs, map_pow]
      exact lt_of_le_of_lt (mul_le_of_le_one_right' (pow_le_one₀ zero_le hy)) hlt1
    refine ⟨1 - z * s ^ 2 * y ^ 2, w.map_one_sub_of_lt h1, ⟨1, s * y, by ring⟩, ?_⟩
    have e : u * (1 - z * s ^ 2 * y ^ 2) - 1 = z * s ^ 2 * ((u - 1) / (z * s ^ 2) - y ^ 2) -
        (u - 1) * (z * s ^ 2 * y ^ 2) := by
      rw [mul_sub (z * s ^ 2), mul_div_cancel₀ _ hs0]; ring
    rw [e]
    refine w.map_sub_lt ?_ ?_
    · rw [map_mul, hs]; exact mul_lt_of_lt_one_right hpos hy'
    · rw [map_mul]; exact mul_lt_of_lt_one_right hpos h1
end GlobalTheory.QuadSymbol.NormIndex
