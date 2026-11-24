-- Prove2me | solution 1 for GlobalTheory.PadicUnitBall.norm_natCast_p
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T19:18:44.392381+00:00
-- url     : https://prove2.me/submissions/fc8195f6-2e0e-44de-8d4a-fc1fe1c8a68c

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_PadicMemRangeCompleteDvrPadicAlgCl

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open IsLocalRing
open GlobalTheory GlobalTheory.PadicUnitBall
variable {p : ℕ} [Fact p.Prime] {V : Type} [CommRing V] [IsDomain V] [IsDiscreteValuationRing V]
  {κ : FractionRing V →+* PadicAlgCl p}
namespace GlobalTheory.PadicUnitBall
theorem _root_.solution : ‖((p : ℕ) : PadicAlgCl p)‖ = (p : ℝ)⁻¹ := by
  have : ((p : ℕ) : PadicAlgCl p) = algebraMap ℚ_[p] (PadicAlgCl p) (p : ℚ_[p]) := by
    rw [map_natCast]
  rw [this, PadicAlgCl.norm_extends, Padic.norm_p]
end GlobalTheory.PadicUnitBall
