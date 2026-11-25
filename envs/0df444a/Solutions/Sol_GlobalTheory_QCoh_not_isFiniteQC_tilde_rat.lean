-- Prove2me | solution 1 for GlobalTheory.QCoh.not_isFiniteQC_tilde_rat
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T08:08:28.16153+00:00
-- url     : https://prove2.me/submissions/fabb686f-7ed3-49af-b763-6f152329b584

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_QuasicoherentCohomology_IsLocalizedModuleGermLinearPointOfPrime
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_QuasicoherentCohomology_TopologicalKrullDimLeOfIrreducibleCloseds

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory Limits AlgebraicGeometry TopologicalSpace Opposite TensorProduct IsLocalRing
universe u
noncomputable section
open GlobalTheory GlobalTheory.QCoh
variable {X : Scheme.{u}} {F G H : X.Modules} {U V : X.Opens}
variable {R : CommRingCat.{u}}
namespace GlobalTheory.QCoh
theorem _root_.solution :
    ¬ IsFiniteQC (tilde (R := CommRingCat.of ℤ) (ModuleCat.of ℤ ℚ)) := by
  rw [isFiniteQC_tilde_iff]
  intro h
  have h : Module.Finite ℤ ℚ := h
  obtain ⟨n, hn⟩ := IsIntegrallyClosed.isIntegral_iff (R := ℤ) (K := ℚ) (x := 1 / 2) |>.1
    (Algebra.IsIntegral.isIntegral _)
  have : ((2 * n : ℤ) : ℚ) = (1 : ℤ) := by
    have hn : (n : ℚ) = 1 / 2 := hn
    push_cast
    rw [hn]; norm_num
  have := Int.cast_injective this
  omega
end GlobalTheory.QCoh
