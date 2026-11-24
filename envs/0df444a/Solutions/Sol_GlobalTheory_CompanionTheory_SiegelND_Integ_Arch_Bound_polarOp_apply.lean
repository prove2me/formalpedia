-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.SiegelND.Integ.Arch.Bound.polarOp_apply
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T05:06:26.860413+00:00
-- url     : https://prove2.me/submissions/0591a756-d313-4d9f-ad39-910cc472c374

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
theorem _root_.solution (J : W → Matrix (Fin M) (Fin M) ℂ) (b : W → Matrix (Fin n) (Fin n) ℂ)
    (y : TupV W n M) : polarOp J b y = mixOp J (diagOp b y) := rfl
end GlobalTheory.CompanionTheory.SiegelND.Integ.Arch.Bound
