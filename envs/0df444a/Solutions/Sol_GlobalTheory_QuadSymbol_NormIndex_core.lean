-- Prove2me | solution 1 for GlobalTheory.QuadSymbol.NormIndex.core
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T15:13:38.928808+00:00
-- url     : https://prove2.me/submissions/f51e32ab-9b7c-4522-b19d-4b2f18d5506e

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
import Theorems.Thm_GlobalTheory_QuadSymbol_NormIndex_Nm_of_mul
import Theorems.Thm_GlobalTheory_QuadSymbol_NormIndex_Nm_symm
import Theorems.Thm_GlobalTheory_QuadSymbol_NormIndex_even_or_odd
import Theorems.Thm_GlobalTheory_QuadSymbol_NormIndex_ne_zero_of_exp

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
theorem _root_.solution (h2 : (2 : K) ≠ 0) {π Δ d : K} (hπ : w π = WithZero.exp (-1)) (hΔ : Δ ≠ 0)
    (hd : d ≠ 0) (hA : ∀ (x : K) (n : ℤ), w x = WithZero.exp (2 * n) → Nm Δ x)
    (hB : ∀ (z : K) (n : ℤ), w z = WithZero.exp (2 * n + 1) → Nm z d ∨ Nm z (d * Δ))
    {x y : K} (hx0 : x ≠ 0) (hy0 : y ≠ 0) (hx : ¬ Nm d x) (hy : ¬ Nm d y) : Nm d (x * y) := by
  have K1 : ∀ (z : K) (n : ℤ), w z = WithZero.exp (2 * n + 1) → ¬ Nm d z → Nm (d * Δ) z :=
    fun z n hz hn => ((hB z n hz).resolve_left fun h => hn (h.symm h2 hd)).symm h2
      (mul_ne_zero hd hΔ)
  have K2 : ∀ (z z' : K) (n n' : ℤ), w z = WithZero.exp (2 * n + 1) →
      w z' = WithZero.exp (2 * n' + 1) → ¬ Nm d z → ¬ Nm d z' → Nm d (z * z') := by
    intro z z' n n' hz hz' h h'
    have hzz : w (z * z') = WithZero.exp (2 * (n + n' + 1)) := by
      rw [map_mul, hz, hz', ← WithZero.exp_add]; congr 1; ring
    have h0 := ne_zero_of_exp w hzz
    have h1 := ((K1 z n hz h).mul (K1 z' n' hz' h')).symm h2 h0
    exact (Nm.of_mul hΔ ((hA _ _ hzz).symm h2 h0) h1).symm h2 hd
  by_cases ht : ∃ (t : K) (j : ℤ), w t = WithZero.exp (2 * j + 1) ∧ Nm d t
  · obtain ⟨t, j, ht, htn⟩ := ht
    have H : ∀ z : K, z ≠ 0 → ∃ (m : K) (n : ℤ), m ≠ 0 ∧ Nm d m ∧
        w (z * m) = WithZero.exp (2 * n + 1) := by
      intro z hz
      rcases even_or_odd w hz with ⟨n, hn⟩ | ⟨n, hn⟩
      · refine ⟨t, n + j, ne_zero_of_exp w ht, htn, ?_⟩
        rw [map_mul, hn, ht, ← WithZero.exp_add]; congr 1; ring
      · exact ⟨1, n, one_ne_zero, ⟨1, 0, by ring⟩, by rw [mul_one, hn]⟩
    obtain ⟨m, n, hm0, hm, hn⟩ := H x hx0
    obtain ⟨m', n', hm0', hm', hn'⟩ := H y hy0
    have := K2 _ _ n n' hn hn' (fun h => hx (Nm.of_mul hm0 hm h)) (fun h => hy (Nm.of_mul hm0' hm' h))
    refine Nm.of_mul (mul_ne_zero hm0 hm0') (hm.mul hm') ?_
    rwa [show x * y * (m * m') = x * m * (y * m') by ring]
  · push Not at ht
    have hπ' : w π = WithZero.exp (2 * (-1) + 1) := by rw [hπ]; norm_num
    have H : ∀ z : K, z ≠ 0 → ¬ Nm d z → ∃ n : ℤ, w z = WithZero.exp (2 * n + 1) := by
      intro z hz hzn
      rcases even_or_odd w hz with ⟨n, hn⟩ | h
      · have h1 : w (z * π) = WithZero.exp (2 * (n - 1) + 1) := by
          rw [map_mul, hn, hπ, ← WithZero.exp_add]; congr 1; ring
        have := K2 _ _ _ _ h1 hπ' (ht _ _ h1) (ht _ _ hπ')
        refine absurd (Nm.of_mul (pow_ne_zero 2 (ne_zero_of_exp w hπ)) (Nm.sq d π) ?_) hzn
        rwa [show z * π ^ 2 = z * π * π by ring]
      · exact h
    obtain ⟨n, hn⟩ := H x hx0 hx
    obtain ⟨n', hn'⟩ := H y hy0 hy
    exact K2 _ _ n n' hn hn' hx hy
end GlobalTheory.QuadSymbol.NormIndex
