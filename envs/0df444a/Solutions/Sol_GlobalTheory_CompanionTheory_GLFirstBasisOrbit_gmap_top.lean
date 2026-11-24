-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.GLFirstBasisOrbit.gmap_top
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T12:33:25.872792+00:00
-- url     : https://prove2.me/submissions/a7f4cc17-61ad-4831-ae91-f20a61a1f0cc

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
theorem _root_.solution {N : ℕ} (g : GL (Fin N) k) : gmap g ⊤ = ⊤ := by
  ext x
  simp [mem_gmap]
end GlobalTheory.CompanionTheory.GLFirstBasisOrbit
