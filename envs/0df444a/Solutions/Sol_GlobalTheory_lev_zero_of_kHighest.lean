-- Prove2me | solution 1 for GlobalTheory.lev_zero_of_kHighest
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T05:15:08.350602+00:00
-- url     : https://prove2.me/submissions/b318711c-eca1-45ee-b34d-0a3be96a6653

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Jets_SumIoPr
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_CompactCasimirHighestWeight
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_JetHarmonics_LevZeroOfKHighest
import Theorems.Thm_Formalism_REAL_compact_casimir_span_holds
import Theorems.Thm_Formalism_REAL_compact_span_stable
import Theorems.Thm_Formalism_REAL_glRel_kRel
import Theorems.Thm_Formalism_REAL_mem_compact_span_self


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset BranchingSupport Formalism.REAL Formalism.QuantumDeterminants
open scoped InnerProductSpace
open GlobalTheory
namespace GlobalTheory
theorem _root_.solution : ∀ (M : Type) [NormedAddCommGroup M] [InnerProductSpace ℂ M] (n : ℕ) (ε : Fin n → Bool) (E : Fin n → Fin n → Module.End ℂ M) (μ : Fin n → ℝ) (w : M), GlRel E → IsUnitary ε E → KHighest ε E (lowK ε μ) w → FiniteDimensional ℂ (kSpan ε E w) → Lev ε E μ 0 w := by
  intro M _ _ n ε E μ w hrel _ hhi hfin
  have hk : KRel ε E := glRel_kRel ε E hrel
  have hsq : ckv ε (lowK ε μ) ≤ (Real.sqrt (ckv ε (lowK ε μ)) + 4 * (n : ℝ) * ((0 : ℕ) : ℝ)) ^ 2 := by
    rcases le_total 0 (ckv ε (lowK ε μ)) with h | h
    · simp [Real.sq_sqrt h]
    · simp [Real.sqrt_eq_zero'.mpr h, h]
  refine ⟨⟨kSpan ε E w, hfin, ?_, mem_compact_span_self w, ?_⟩, ?_⟩
  · intro a b hab x hx
    exact compact_span_stable w a b hab x hx
  · intro x hx
    rw [compact_casimir_span_holds M n ε E (lowK ε μ) w hk hhi x hx, inner_smul_right,
      inner_self_eq_norm_sq_to_K]
    have hx2 : (0 : ℝ) ≤ ‖x‖ ^ 2 := by positivity
    refine le_trans (le_of_eq ?_) (mul_le_mul_of_nonneg_right hsq hx2)
    simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
    congr 1
    norm_cast
  · apply Submodule.subset_span
    exact ⟨lowK ε μ, by simp, hhi.1⟩
end GlobalTheory
