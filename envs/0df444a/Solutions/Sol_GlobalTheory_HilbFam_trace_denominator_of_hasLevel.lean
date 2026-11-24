-- Prove2me | solution 1 for GlobalTheory.HilbFam.trace_denominator_of_hasLevel
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T17:49:48.313906+00:00
-- url     : https://prove2.me/submissions/f47355af-a15f-40d3-86ec-c656f663cabd

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_HasLevelStd
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_HasQIff
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_SplitLatticeLevelTraceDenominator
import Theorems.Thm_GlobalTheory_HilbFam_exists_int_mul_trace_of_hasLevel
import Theorems.Thm_GlobalTheory_CMVal_coe_latticeSub
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.CMVal.coe_latticeSub



set_option autoImplicit false
open NumberField UpperHalfPlane GlobalTheory.HilbFam GlobalTheory.QFam
open GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization (Emb Frac latM qPow upperHalf cK omegaFactor IsPartialZeta HasExpansion)
open GlobalTheory.IndefiniteRowSideFullHecke.DefiningCoordinates (iterD partialD)
open scoped Classical MatrixGroups nonZeroDivisors
open GlobalTheory GlobalTheory.HilbFam
namespace GlobalTheory.HilbFam
theorem _root_.solution : ∀ (F : Type) [Field F] [NumberField F] [IsTotallyReal F] (N : ℕ) (𝔞 𝔟 : Frac F) (x ξ : F), HasLevel N (split 𝔞 𝔟 x) → ξ ∈ ((𝔞 * 𝔟 : Frac F) : FractionalIdeal (𝓞 F)⁰ F) → (∃ n : ℤ, (N : ℚ) * Algebra.trace ℚ F ξ = n) ∧ ∃ n : ℤ, (N : ℚ) * Algebra.trace ℚ F (ξ * x) = n := by
  intro F _ _ _ N 𝔞 𝔟 x ξ h hξ
  rw [Units.val_mul] at hξ
  refine FractionalIdeal.mul_induction_on hξ (C := fun ξ ↦ (∃ n : ℤ, (N : ℚ) * Algebra.trace ℚ F ξ = n) ∧
    ∃ n : ℤ, (N : ℚ) * Algebra.trace ℚ F (ξ * x) = n) ?_ ?_
  · intro ν hν β hβ
    have h1 : (![β, β * x] : Fin 2 → F) ∈ split 𝔞 𝔟 x := by
      refine ⟨hβ, ?_⟩
      have : (![β, β * x] : Fin 2 → F) 1 - (![β, β * x] : Fin 2 → F) 0 * x = 0 := by simp
      rw [this]
      exact Submodule.zero_mem (latM 𝔞 : Submodule (𝓞 F) F)
    have h2 := h.2 h1
    refine ⟨exists_int_mul_trace_of_hasLevel h hν (h2 0 trivial), ?_⟩
    rw [mul_assoc]
    exact exists_int_mul_trace_of_hasLevel h hν (h2 1 trivial)
  · rintro a b ⟨⟨m, hm⟩, m', hm'⟩ ⟨⟨n, hn⟩, n', hn'⟩
    refine ⟨⟨m + n, ?_⟩, m' + n', ?_⟩
    · rw [map_add, mul_add, hm, hn]; push_cast; ring
    · rw [add_mul, map_add, mul_add, hm', hn']; push_cast; ring
end GlobalTheory.HilbFam
