-- Prove2me | solution 1 for GlobalTheory.T.compactCasimirBound_projection_dualTensor
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T08:27:58.839494+00:00
-- url     : https://prove2.me/submissions/171af58c-2154-4362-8341-c56fde66f59c

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_JetHarmonics_CompactCasimirBoundProjectionDualTensor
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Jets_SumIoPr
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_JetHarmonics_CompactCasimirBoundProjectionDualTensorStatement
import Theorems.Thm_GlobalTheory_casKLe_proj_single


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
set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ (M : Type) [NormedAddCommGroup M] [InnerProductSpace ℂ M] (n : ℕ) (ε : Fin n → Bool) (E : Fin n → Fin n → Module.End ℂ M) (N : Fin n → Type) [∀ s, NormedAddCommGroup (N s)] [∀ s, InnerProductSpace ℂ (N s)] (F : ∀ s, Fin n → Fin n → Module.End ℂ (N s)) (io : ∀ s, N s →ₗ[ℂ] (Fin n → M)) (pr : ∀ s, (Fin n → M) →ₗ[ℂ] N s) (c : ℝ) (w : M), IsUnitary ε E → (∀ s, IsUnitary ε (F s)) → AlgTens ε E N F io pr → 0 ≤ c → CasKLe ε E c w → ∀ s d, CasKLe ε (F s) (c + Real.sqrt n) (pr s (Pi.single d w)) := by
  first | exact @GlobalTheory.casKLe_proj_single | exact GlobalTheory.casKLe_proj_single | (intros; apply GlobalTheory.casKLe_proj_single <;> assumption)
end _root_.GlobalTheory.T
