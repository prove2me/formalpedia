-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.CapelliAdj.adj_qdet
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T21:34:06.25415+00:00
-- url     : https://prove2.me/submissions/09397093-71e8-4127-8c65-d4f36d72f0aa

import Mathlib
import Definitions.Def_Formalism_RealPlaceAnalysis_ThirdArithmeticHolds
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_QuantumDetOppositeNegStatement
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_QuantumDetAdjointForm
import Theorems.Thm_GlobalTheory_CompanionTheory_CapelliAdj_hasAdj_qdet
import Theorems.Thm_GlobalTheory_T_quantum_det_opposite_neg


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.REAL
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.CapelliAdj
variable {V : Type} [AddCommGroup V] [Module ℂ V]
namespace GlobalTheory.CompanionTheory.CapelliAdj
theorem _root_.solution (V : Type) [AddCommGroup V] [Module ℂ V] (B : V →ₗ[ℂ] V →ₗ⋆[ℂ] ℂ) (n : ℕ)
    (X Y : Fin n → Fin n → Module.End ℂ V) (hY : GlRel Y)
    (h : ∀ (i j : Fin n) (φ ψ : V), B (X i j φ) ψ = -B φ (Y i j ψ)) (v : ℂ) (φ ψ : V) :
    B (qdet X v φ) ψ =
      B φ ((((-1 : ℂ) ^ n) • qdet Y ((n : ℂ) - 1 - (starRingEnd ℂ) v)) ψ) := by
  rw [hasAdj_qdet h v φ ψ, GlobalTheory.T.quantum_det_opposite_neg (Module.End ℂ V) n Y hY ((starRingEnd ℂ) v)]
end GlobalTheory.CompanionTheory.CapelliAdj
