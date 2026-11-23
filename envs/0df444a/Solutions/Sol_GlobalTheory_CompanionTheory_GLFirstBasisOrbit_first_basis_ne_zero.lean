-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.GLFirstBasisOrbit.first_basis_ne_zero
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T20:07:00.665823+00:00
-- url     : https://prove2.me/submissions/fa6a106e-430e-4aed-8571-09685366260a

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
theorem _root_.solution : e0 k n ≠ 0 := by
  intro h
  have := congrFun h 0
  simp [e0] at this
end GlobalTheory.CompanionTheory.GLFirstBasisOrbit
