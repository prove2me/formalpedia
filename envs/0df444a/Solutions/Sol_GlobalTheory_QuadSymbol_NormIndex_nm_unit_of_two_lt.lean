-- Prove2me | solution 1 for GlobalTheory.QuadSymbol.NormIndex.nm_unit_of_two_lt
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T19:45:02.720095+00:00
-- url     : https://prove2.me/submissions/dc1775e3-c4a3-4197-a4ff-854f39997cd6

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
import Theorems.Thm_GlobalTheory_QuadSymbol_NormIndex_Nm_of_mul
import Theorems.Thm_GlobalTheory_QuadSymbol_NormIndex_Nm_of_isSquare_left
import Theorems.Thm_GlobalTheory_QuadSymbol_NormIndex_Nm_symm
import Theorems.Thm_GlobalTheory_QuadSymbol_NormIndex_isSquare_of_near

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain IsLocalRing
open scoped WithZero
open GlobalTheory GlobalTheory.QuadSymbol
open GlobalTheory.QuadSymbol.NormIndex
variable {K : Type} [Field K]
variable (w : Valuation K ℤᵐ⁰)
namespace GlobalTheory.QuadSymbol.NormIndex
theorem _root_.solution (h2 : (2 : K) ≠ 0) (hsq : ∀ x : K, w (x - 1) < w 4 → IsSquare x)
    (hres : ∀ x : K, w x ≤ 1 → ∃ y : K, w y ≤ 1 ∧ w (x - y ^ 2) < 1) {Δ u : K}
    (hΔ : w (Δ - 1) ≤ w 4) (hu : w u = 1) : Nm Δ u := by
  by_cases h1 : Δ = 1
  · exact Nm.of_isSquare_left h2 (h1 ▸ one_ne_zero) (h1 ▸ IsSquare.one) u
  obtain ⟨a, -, ha⟩ := hres u hu.le
  have ha2 : w (a ^ 2) = 1 := by
    rw [show a ^ 2 = u - (u - a ^ 2) by ring,
      Valuation.map_sub_eq_of_lt_left w (by rw [hu]; exact ha), hu]
  rw [map_pow] at ha2
  have ha1 : w a = 1 := (pow_eq_one_iff_of_nonneg zero_le two_ne_zero).1 ha2
  have hpos : 0 < w (Δ - 1) := zero_lt_iff.2 ((Valuation.ne_zero_iff w).2 (sub_ne_zero.2 h1))
  obtain ⟨c, hc⟩ := isSquare_of_near w hsq (u := a ^ 2 - (Δ - 1) * (u - a ^ 2)) ha1 (by
    rw [sub_sub_cancel_left, Valuation.map_neg, map_mul]
    exact (mul_lt_of_lt_one_right hpos ha).trans_le hΔ)
  exact Nm.of_mul (sub_ne_zero.2 (Ne.symm h1)) ⟨1, 1, by ring⟩ ⟨c, a, by linear_combination hc⟩
end GlobalTheory.QuadSymbol.NormIndex
