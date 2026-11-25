-- Prove2me | solution 1 for GlobalTheory.lev_io_pr_single
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T08:56:00.035659+00:00
-- url     : https://prove2.me/submissions/75908f38-1867-42e7-9178-2174136b418d

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Jets_SumIoPr
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_JetHarmonics_CompactCasimirBoundProjectionDualTensorStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_JetHarmonics_CompactCasimirBoundEmbeddedComponentStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_JetHarmonics_AlgTensWtNear
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_JetHarmonics_UnitaryGlModuleProjComponentsLevelAddTwo
import Theorems.Thm_GlobalTheory_T_compactCasimirBound_embedded_component
import Theorems.Thm_GlobalTheory_T_compactCasimirBound_projection_dualTensor
import Theorems.Thm_GlobalTheory_algTens_wtNear


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
theorem _root_.solution : ∀ (M : Type) [NormedAddCommGroup M] [InnerProductSpace ℂ M] (n : ℕ) (ε : Fin n → Bool) (E : Fin n → Fin n → Module.End ℂ M) (N : Fin n → Type) [∀ s, NormedAddCommGroup (N s)] [∀ s, InnerProductSpace ℂ (N s)] (F : ∀ s, Fin n → Fin n → Module.End ℂ (N s)) (io : ∀ s, N s →ₗ[ℂ] (Fin n → M)) (pr : ∀ s, (Fin n → M) →ₗ[ℂ] N s) (μ : Fin n → ℝ) (j : ℕ) (w : M), IsUnitary ε E → (∀ s, IsUnitary ε (F s)) → AlgTens ε E N F io pr → Lev ε E μ j w → ∀ s c d, Lev ε E μ (j + 2) (io s (pr s (Pi.single c w)) d) := by
  intro M _ _ n ε E N _ _ F io pr μ j w hE hF hT hw s c d
  obtain ⟨hc, hwt⟩ := hw
  have hn : (1 : ℝ) ≤ n := by
    have : 0 < n := Fin.pos s
    exact_mod_cast this
  have hsq : Real.sqrt n ≤ n := by
    rw [Real.sqrt_le_left (by linarith)]
    nlinarith
  have hs0 : 0 ≤ Real.sqrt (n : ℝ) := Real.sqrt_nonneg _
  have h0 : 0 ≤ Real.sqrt (ckv ε (lowK ε μ)) + 4 * (n : ℝ) * (j : ℝ) := by positivity
  refine ⟨?_, ?_⟩
  · have h1 := GlobalTheory.T.compactCasimirBound_projection_dualTensor M n ε E N F io pr _ w hE hF hT h0 hc s c
    have h2 := GlobalTheory.T.compactCasimirBound_embedded_component M n ε E N F io pr _ s _ hE hF hT (by linarith) h1 d
    obtain ⟨S, hS1, hS2, hS3, hS4⟩ := h2
    refine ⟨S, hS1, hS2, hS3, fun x hx => (hS4 x hx).trans ?_⟩
    apply mul_le_mul_of_nonneg_right _ (by positivity)
    apply pow_le_pow_left₀ (by linarith)
    push_cast
    nlinarith
  · have h1 := (GlobalTheory.algTens_wtNear M n ε E N F io pr (lowK ε μ) j hT).1 w hwt s c
    have h2 := (GlobalTheory.algTens_wtNear M n ε E N F io pr (lowK ε μ) (j + 1) hT).2 s _ h1 d
    have e : ((j + 2 : ℕ) : ℝ) = (j : ℝ) + 1 + 1 := by push_cast; ring
    rw [e]
    exact h2
end GlobalTheory
