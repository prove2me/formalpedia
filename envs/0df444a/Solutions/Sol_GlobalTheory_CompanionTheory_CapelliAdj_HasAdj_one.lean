-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.CapelliAdj.HasAdj.one
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T12:21:35.555031+00:00
-- url     : https://prove2.me/submissions/56ba41c7-9209-4b4d-93fd-82cc9b9b77a1

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
theorem _root_.solution (B : V →ₗ[ℂ] V →ₗ⋆[ℂ] ℂ) : HasAdj B 1 1 := by
  intro φ ψ
  rfl
end HasAdj
end GlobalTheory.CompanionTheory.CapelliAdj
