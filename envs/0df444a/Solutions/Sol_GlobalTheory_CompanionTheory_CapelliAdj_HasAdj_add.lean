-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.CapelliAdj.HasAdj.add
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T20:23:07.341018+00:00
-- url     : https://prove2.me/submissions/0b922b6c-2e75-4089-b0fa-916df9ffad8f

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
    (h : HasAdj B T S) (h' : HasAdj B T' S') : HasAdj B (T + T') (S + S') := by
  intro φ ψ
  simp only [LinearMap.add_apply, map_add, h φ ψ, h' φ ψ]
end HasAdj
end GlobalTheory.CompanionTheory.CapelliAdj
