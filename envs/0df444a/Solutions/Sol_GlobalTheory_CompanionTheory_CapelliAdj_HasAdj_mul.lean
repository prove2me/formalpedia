-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.CapelliAdj.HasAdj.mul
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T20:23:57.050508+00:00
-- url     : https://prove2.me/submissions/7ce9f52d-779a-44d7-92e7-cf1623a5fdd4

import Mathlib
import Definitions.Def_Formalism_RealPlaceAnalysis_ThirdArithmeticHolds
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_QuantumDetOppositeNegStatement
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_QuantumDetAdjointForm

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
namespace HasAdj
theorem _root_.solution {B : V →ₗ[ℂ] V →ₗ⋆[ℂ] ℂ} {T T' S S' : Module.End ℂ V}
    (h : HasAdj B T S) (h' : HasAdj B T' S') : HasAdj B (T * T') (S' * S) := by
  intro φ ψ
  show B (T (T' φ)) ψ = B φ (S' (S ψ))
  rw [h (T' φ) ψ, h' φ (S ψ)]
end HasAdj
end GlobalTheory.CompanionTheory.CapelliAdj
