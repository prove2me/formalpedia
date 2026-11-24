-- Prove2me | solution 1 for GlobalTheory.QuadSymbol.NormIndex.exists_mul_near
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T20:20:37.193681+00:00
-- url     : https://prove2.me/submissions/43cadb3a-2bca-47d6-a83e-a1c0397610c2

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
import Theorems.Thm_GlobalTheory_QuadSymbol_NormIndex_Nm_mul
import Theorems.Thm_GlobalTheory_QuadSymbol_NormIndex_Nm_sq
import Theorems.Thm_GlobalTheory_QuadSymbol_NormIndex_Nm_symm
import Theorems.Thm_GlobalTheory_QuadSymbol_NormIndex_even_or_odd
import Theorems.Thm_GlobalTheory_QuadSymbol_NormIndex_val_mul_zpow_sq
import Theorems.Thm_GlobalTheory_QuadSymbol_NormIndex_step
import Theorems.Thm_GlobalTheory_Idele_adelicMulEquiv_mk
import Theorems.Thm_GlobalTheory_LocalLattice_hermPairing_apply
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
theorem _root_.solution (h2 : (2 : K) ≠ 0) {π : K} (hπ : w π = WithZero.exp (-1))
    (hres : w 2 < 1 → ∀ x : K, w x ≤ 1 → ∃ y : K, w y ≤ 1 ∧ w (x - y ^ 2) < 1)
    {z : K} {j : ℤ} (hz : w z = WithZero.exp (2 * j + 1)) {d : K} (hd : d ≠ 0) :
    ∃ m : K, Nm z m ∧ w (d * m) = 1 ∧ w (d * m - 1) ≤ w 4 := by
  have h4 : (4 : K) ≠ 0 := by
    rw [show (4 : K) = 2 * 2 by norm_num]; exact mul_ne_zero h2 h2
  have he := (WithZero.exp_log ((Valuation.ne_zero_iff w).2 h4)).symm
  set e := WithZero.log (w 4)
  have H : ∀ (N : ℕ) (u : K), w u = 1 → w (u - 1) ≤ WithZero.exp (e + N) →
      ∃ m : K, Nm z m ∧ w (u * m) = 1 ∧ w (u * m - 1) ≤ w 4 := by
    intro N
    induction N with
    | zero =>
      intro u hu h
      exact ⟨1, ⟨1, 0, by ring⟩, by rwa [mul_one], by simpa [he] using h⟩
    | succ N ih =>
      intro u hu h
      by_cases h5 : w (u - 1) ≤ w 4
      · exact ⟨1, ⟨1, 0, by ring⟩, by rwa [mul_one], by rwa [mul_one]⟩
      obtain ⟨m, hm1, hm, hlt⟩ := step w hπ hres hz hu (not_le.1 h5)
      obtain ⟨m', hm', H⟩ := ih (u * m) (by rw [map_mul, hu, hm1, one_mul]) (by
        by_cases h0 : u * m - 1 = 0
        · rw [h0]; simp
        have hf := (WithZero.exp_log ((Valuation.ne_zero_iff w).2 h0)).symm
        have := hlt.trans_le h
        rw [hf, WithZero.exp_lt_exp] at this
        rw [hf, WithZero.exp_le_exp]
        push_cast at this
        omega)
      exact ⟨m * m', hm.mul hm', by rwa [← mul_assoc]⟩
  obtain ⟨m, hm, hu⟩ : ∃ m : K, Nm z m ∧ w (d * m) = 1 := by
    rcases even_or_odd w hd with ⟨k, hk⟩ | ⟨k, hk⟩
    · exact ⟨_, Nm.sq z (π ^ k), by rw [val_mul_zpow_sq w hπ hk]; simp⟩
    · have h1 : w (d * -z) = WithZero.exp (2 * (k + j + 1)) := by
        rw [map_mul, Valuation.map_neg, hk, hz, ← WithZero.exp_add]; congr 1; ring
      exact ⟨_, Nm.mul (x := -z) ⟨0, 1, by ring⟩ (Nm.sq z (π ^ (k + j + 1))), by
        rw [← mul_assoc, val_mul_zpow_sq w hπ h1]; simp⟩
  obtain ⟨m', hm', H'⟩ := H (-e).toNat _ hu (by
    refine (w.map_sub_le hu.le (by simp)).trans ?_
    rw [← WithZero.exp_zero, WithZero.exp_le_exp]
    omega)
  exact ⟨m * m', hm.mul hm', by rwa [← mul_assoc]⟩
end GlobalTheory.QuadSymbol.NormIndex
