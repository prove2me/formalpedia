-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.DualFin.finite_dual_all
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T12:26:11.933787+00:00
-- url     : https://prove2.me/submissions/1a975fe1-daf3-43f3-876d-10d1508e2850

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_FiniteDualAll

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.DualFin
namespace GlobalTheory.CompanionTheory.DualFin
theorem _root_.solution : ∀ (R M : Type) [CommRing R] [Finite R] [AddCommGroup M] [Module R M] [Finite M], Finite (Module.Dual R M) :=
  fun R M _ _ _ _ _ =>
    Finite.of_injective (fun f : Module.Dual R M => (f : M → R)) DFunLike.coe_injective
end GlobalTheory.CompanionTheory.DualFin
