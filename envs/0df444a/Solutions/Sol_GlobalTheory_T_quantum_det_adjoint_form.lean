-- Prove2me | solution 1 for GlobalTheory.T.quantum_det_adjoint_form
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T18:24:39.352849+00:00
-- url     : https://prove2.me/submissions/b4356a85-0f2b-46ca-abeb-4d24e5907187

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_QuantumDetAdjointForm
import Definitions.Def_Formalism_RealPlaceAnalysis_ThirdArithmeticHolds
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_QuantumDetAdjointFormStatement
import Theorems.Thm_GlobalTheory_CompanionTheory_CapelliAdj_adj_qdet


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.REAL
set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ (V : Type) [AddCommGroup V] [Module ℂ V] (B : V →ₗ[ℂ] V →ₗ⋆[ℂ] ℂ) (n : ℕ) (X Y : Fin n → Fin n → Module.End ℂ V), Formalism.REAL.GlRel Y → (∀ (i j : Fin n) (φ ψ : V), B (X i j φ) ψ = -B φ (Y i j ψ)) → ∀ (v : ℂ) (φ ψ : V), B (Formalism.REAL.qdet X v φ) ψ = B φ ((((-1 : ℂ) ^ n) • Formalism.REAL.qdet Y ((n : ℂ) - 1 - (starRingEnd ℂ) v)) ψ) := by
  first | exact @GlobalTheory.CompanionTheory.CapelliAdj.adj_qdet | exact GlobalTheory.CompanionTheory.CapelliAdj.adj_qdet | (intros; apply GlobalTheory.CompanionTheory.CapelliAdj.adj_qdet <;> assumption)
end _root_.GlobalTheory.T
