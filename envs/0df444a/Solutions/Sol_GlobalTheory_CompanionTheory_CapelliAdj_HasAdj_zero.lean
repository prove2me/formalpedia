-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.CapelliAdj.HasAdj.zero
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T20:23:44.183702+00:00
-- url     : https://prove2.me/submissions/28e600d7-9d93-443c-8846-d8e5ab385133

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
theorem _root_.solution (B : V →ₗ[ℂ] V →ₗ⋆[ℂ] ℂ) : HasAdj B 0 0 := by
  intro φ ψ
  simp
end HasAdj
end GlobalTheory.CompanionTheory.CapelliAdj
