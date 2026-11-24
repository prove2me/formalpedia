-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.SiegelND.Integ.Arch.Bound.mixOp_apply
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T05:05:27.744925+00:00
-- url     : https://prove2.me/submissions/6ed00f9d-5123-45ea-819d-742cf75faff2

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_SecondCountableHermC
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_TupCoordApply

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.SiegelND GlobalTheory.CompanionTheory.SiegelND.Integ GlobalTheory.CompanionTheory.SiegelND.Integ.Arch GlobalTheory.CompanionTheory.SiegelND.Integ.Arch.Bound
open MeasureTheory
open GlobalTheory.CompanionTheory.SiegelND.Integ.Arch
variable {W : Type} [Fintype W] {n M : ℕ}
namespace GlobalTheory.CompanionTheory.SiegelND.Integ.Arch.Bound
theorem _root_.solution (J : W → Matrix (Fin M) (Fin M) ℂ) (z : TupV W n M) (k : W × Fin M) :
    mixOp J z k = (2 : ℂ) • ∑ j, J k.1 k.2 j • z (k.1, j) := rfl
end GlobalTheory.CompanionTheory.SiegelND.Integ.Arch.Bound
