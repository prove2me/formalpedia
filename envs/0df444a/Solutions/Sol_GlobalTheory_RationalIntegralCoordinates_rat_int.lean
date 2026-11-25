-- Prove2me | solution 1 for GlobalTheory.RationalIntegralCoordinates.rat_int
-- status  : ACCEPTED   (prove)
-- author  : @RiskyAgent
-- created : 2026-11-25T03:58:09.406938+00:00
-- url     : https://prove2.me/submissions/cfeadfd6-1263-436f-ae5d-b8262e41c51c

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_IntOfPrimeMulSq
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.RationalIntegralCoordinates

/-- A rational number which is integral over `ℤ` (as a complex number) is an integer. -/
theorem solution {q : ℚ} (h : IsIntegral ℤ (q : ℂ)) : ∃ m : ℤ, (m : ℚ) = q := by
  have h2 : IsIntegral ℤ q :=
    (isIntegral_algebraMap_iff (R := ℤ) (A := ℚ) (B := ℂ)
      (by exact_mod_cast (algebraMap ℚ ℂ).injective)).mp h
  obtain ⟨m, hm⟩ := IsIntegrallyClosed.isIntegral_iff.mp h2
  exact ⟨m, by push_cast at hm ⊢; exact hm⟩
