-- Prove2me | solution 1 for GlobalTheory.QuadSymbol.NormIndex.nm_mul_adicCompletion
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T20:37:28.979981+00:00
-- url     : https://prove2.me/submissions/b9694f79-0f15-416c-893b-35b1d30ac5ea

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
import Theorems.Thm_GlobalTheory_QuadSymbol_NormIndex_Nm_of_isSquare
import Theorems.Thm_GlobalTheory_QuadSymbol_NormIndex_Nm_of_mul
import Theorems.Thm_GlobalTheory_QuadSymbol_NormIndex_ne_zero_of_exp
import Theorems.Thm_GlobalTheory_QuadSymbol_NormIndex_ne_zero_of_one
import Theorems.Thm_GlobalTheory_QuadSymbol_NormIndex_val_mul_zpow_sq
import Theorems.Thm_GlobalTheory_QuadSymbol_NormIndex_core
import Theorems.Thm_GlobalTheory_QuadSymbol_NormIndex_map_two_le
import Theorems.Thm_GlobalTheory_QuadSymbol_NormIndex_exists_mul_near
import Theorems.Thm_GlobalTheory_QuadSymbol_NormIndex_nm_unit_of_two_lt
import Theorems.Thm_GlobalTheory_QuadSymbol_NormIndex_isSquare_mul_of_near
import Theorems.Thm_GlobalTheory_Idele_adelicMulEquiv_mk
import Theorems.Thm_GlobalTheory_LocalLattice_hermPairing_apply
import Theorems.Thm_GlobalTheory_LocalQuad_isSquare_of_valued_sub_one_lt
import Theorems.Thm_GlobalTheory_Published_HasseNormSt_of_isSquare
import Theorems.Thm_GlobalTheory_QNorm_exists_integral_sq_sub_mul_sq_of_unit
import Theorems.Thm_GlobalTheory_QNorm_exists_sub_sq_lt_one_of_two_lt_one
import Theorems.Thm_GlobalTheory_QNorm_exists_uniformizer_and_residue_representatives
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
variable (F : Type) [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F))
namespace GlobalTheory.QuadSymbol.NormIndex
theorem _root_.solution {d x y : v.adicCompletion F} (hd : d ≠ 0) (hx0 : x ≠ 0) (hy0 : y ≠ 0)
    (hx : ¬ Nm d x) (hy : ¬ Nm d y) : Nm d (x * y) := by
  haveI : CharZero (v.adicCompletion F) :=
    charZero_of_injective_algebraMap (algebraMap F (v.adicCompletion F)).injective
  obtain ⟨⟨π, -, hπ⟩, -⟩ := GlobalTheory.QNorm.exists_uniformizer_and_residue_representatives F v
  have hres := GlobalTheory.QNorm.exists_sub_sq_lt_one_of_two_lt_one F v
  obtain ⟨Δ, hΔ1, hΔ4, hΔ⟩ : ∃ Δ : v.adicCompletion F, Valued.v Δ = 1 ∧
      Valued.v (Δ - 1) ≤ Valued.v (4 : v.adicCompletion F) ∧ ∀ u : v.adicCompletion F,
        Valued.v u = 1 → Valued.v (u - 1) ≤ Valued.v (4 : v.adicCompletion F) →
          IsSquare u ∨ IsSquare (u * Δ) := by
    by_cases h : ∃ Δ : v.adicCompletion F, Valued.v Δ = 1 ∧
      Valued.v (Δ - 1) ≤ Valued.v (4 : v.adicCompletion F) ∧ ¬ IsSquare Δ
    · obtain ⟨Δ, h1, h2, h3⟩ := h
      exact ⟨Δ, h1, h2, fun u hu hu4 => or_iff_not_imp_left.2 fun hu' =>
        isSquare_mul_of_near F v hu h1 hu4 h2 hu' h3⟩
    · push Not at h
      exact ⟨1, by simp, by simp, fun u hu hu4 => Or.inl (h u hu hu4)⟩
  refine core Valued.v two_ne_zero hπ (ne_zero_of_one _ hΔ1) hd (fun z n hz => ?_)
    (fun z n hz => ?_) hx0 hy0 hx hy
  · have hu := val_mul_zpow_sq Valued.v hπ hz n
    rw [sub_self, WithZero.exp_zero] at hu
    refine Nm.of_mul (pow_ne_zero 2 (zpow_ne_zero n (ne_zero_of_exp _ hπ))) (Nm.sq _ _) ?_
    rcases (map_two_le (Valued.v : Valuation (v.adicCompletion F) ℤᵐ⁰)).eq_or_lt with h2 | h2
    · obtain ⟨a, -, b, -, h⟩ := GlobalTheory.QNorm.exists_integral_sq_sub_mul_sq_of_unit F v Δ _ h2 hΔ1 hu
      exact ⟨a, b, h⟩
    · exact nm_unit_of_two_lt Valued.v two_ne_zero
        (GlobalTheory.LocalQuad.isSquare_of_valued_sub_one_lt F v) (hres h2) hΔ4 hu
  · obtain ⟨m, hm, h1, h4⟩ := exists_mul_near Valued.v two_ne_zero hπ hres hz hd
    have hm0 : m ≠ 0 := right_ne_zero_of_mul (ne_zero_of_one _ h1)
    refine (hΔ _ h1 h4).imp (fun h => Nm.of_mul hm0 hm (Nm.of_isSquare _ h))
      fun h => Nm.of_mul hm0 hm (Nm.of_isSquare _ ?_)
    rwa [mul_right_comm]
end GlobalTheory.QuadSymbol.NormIndex
