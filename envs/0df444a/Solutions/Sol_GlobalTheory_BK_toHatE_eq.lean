-- Prove2me | solution 1 for GlobalTheory.BK.toHatE_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T15:40:42.651818+00:00
-- url     : https://prove2.me/submissions/b6d2a645-32cd-4d9c-a0bf-6c9390523b02

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_NormPowLeNormFactorial
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_DerivationMemPow
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_SndDualLiftAlgebraMap

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.BK
open PowerSeries Filter Topology
variable (O K : Type) [CommRing O] [NormedField K] [IsUltrametricDist K] [Algebra O K]
  [IsUnitBall O K] (l e : ℕ)
variable [Fact l.Prime] [NormedAlgebra ℚ_[l] K]
variable [NeZero e] [CompleteSpace K]
variable {O K}
namespace GlobalTheory.BK
theorem _root_.solution {f : RpiE O K l e} {g : Rpi O K l e} (h : (f : K⟦X⟧) = g) :
    toHatE O K l e f = algebraMap _ _ (toHat O K l e g) := by
  have : f = algebraMap (Rpi O K l e) _ g := Subtype.ext h
  rw [this, toHatE, IsLocalization.Away.lift_eq]
  rfl
end GlobalTheory.BK
