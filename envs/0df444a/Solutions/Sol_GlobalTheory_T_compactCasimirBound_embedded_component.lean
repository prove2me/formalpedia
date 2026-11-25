-- Prove2me | solution 1 for GlobalTheory.T.compactCasimirBound_embedded_component
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T08:28:29.270366+00:00
-- url     : https://prove2.me/submissions/6c87fae5-16f3-4d27-9359-1b238595ee1b

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_JetHarmonics_CompactCasimirBoundEmbeddedComponent
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Jets_SumIoPr
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_JetHarmonics_CompactCasimirBoundEmbeddedComponentStatement
import Theorems.Thm_GlobalTheory_casKLe_io_component


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
theorem _root_.solution : ∀ (M : Type) [NormedAddCommGroup M] [InnerProductSpace ℂ M] (n : ℕ) (ε : Fin n → Bool) (E : Fin n → Fin n → Module.End ℂ M) (N : Fin n → Type) [∀ s, NormedAddCommGroup (N s)] [∀ s, InnerProductSpace ℂ (N s)] (F : ∀ s, Fin n → Fin n → Module.End ℂ (N s)) (io : ∀ s, N s →ₗ[ℂ] (Fin n → M)) (pr : ∀ s, (Fin n → M) →ₗ[ℂ] N s) (c : ℝ) (s : Fin n) (y : N s), IsUnitary ε E → (∀ s, IsUnitary ε (F s)) → AlgTens ε E N F io pr → 0 ≤ c → CasKLe ε (F s) c y → ∀ d, CasKLe ε E (c + Real.sqrt n) (io s y d) := by
  first | exact @GlobalTheory.casKLe_io_component | exact GlobalTheory.casKLe_io_component | (intros; apply GlobalTheory.casKLe_io_component <;> assumption)
end _root_.GlobalTheory.T
