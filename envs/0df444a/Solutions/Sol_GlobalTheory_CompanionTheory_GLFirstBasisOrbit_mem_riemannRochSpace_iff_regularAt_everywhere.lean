-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.GLFirstBasisOrbit.mem_riemannRochSpace_iff_regularAt_everywhere
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T20:07:00.660964+00:00
-- url     : https://prove2.me/submissions/383d4189-cc53-4b39-b68e-a347611eda83

import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_ResidualSpectrum_ExponentialNegativity_GapAbsOf
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_MemRiemannRochSpaceIffRegularAtEverywhere

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix Classical PositivityTheory.Rg.Rs
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.GLFirstBasisOrbit
variable {k : Type} [Field k] {n : ℕ}
namespace GlobalTheory.CompanionTheory.GLFirstBasisOrbit
theorem _root_.solution (x : Fin (n + 1) → k) : x ∈ H0 k n ↔ x 0 = 0 := by
  simp [H0]
end GlobalTheory.CompanionTheory.GLFirstBasisOrbit
