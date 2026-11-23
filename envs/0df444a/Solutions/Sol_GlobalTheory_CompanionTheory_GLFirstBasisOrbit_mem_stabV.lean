-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.GLFirstBasisOrbit.mem_stabV
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T20:07:37.266405+00:00
-- url     : https://prove2.me/submissions/edcacf04-293d-4ef9-b134-d85676d2478f

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
variable {V Γ : Type} [AddCommGroup V] [Module ℂ V] [Group Γ]
namespace GlobalTheory.CompanionTheory.GLFirstBasisOrbit
theorem _root_.solution (red : Γ →* GL (Fin (n + 1)) k) (ρ : Γ →* Module.End ℂ V) (y : V) :
    y ∈ stabV red ρ ↔
      ∀ γ, gmap (red γ) (Submodule.span k {e0 k n}) = Submodule.span k {e0 k n} → ρ γ y = y := Iff.rfl
end GlobalTheory.CompanionTheory.GLFirstBasisOrbit
