-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.GLFirstBasisOrbit.finrank_gmap
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T20:07:21.986258+00:00
-- url     : https://prove2.me/submissions/df931398-62a5-4970-9506-dfc126aef23b

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
theorem _root_.solution {N : ℕ} (g : GL (Fin N) k) (M : Submodule k (Fin N → k)) :
    Module.finrank k (gmap g M) = Module.finrank k M := by
  have hinj : Function.Injective (Matrix.toLin' g.val) := by
    intro x y h
    have := congrArg (fun z => (g⁻¹).val *ᵥ z) h
    simpa [Matrix.toLin'_apply, Matrix.mulVec_mulVec, ← Units.val_mul] using this
  exact (Submodule.equivMapOfInjective _ hinj M).finrank_eq.symm
end GlobalTheory.CompanionTheory.GLFirstBasisOrbit
