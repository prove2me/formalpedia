-- Prove2me | solution 1 for GlobalTheory.IntMulIntegerSmulMemLattice.exists_int_mul_eq_integer
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T08:22:06.949439+00:00
-- url     : https://prove2.me/submissions/aecb9f6c-a657-4aa5-a0d4-3424d5036c7c

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_ExistsIntSmulMemLattice

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.IntMulIntegerSmulMemLattice
open NumberField
namespace GlobalTheory.IntMulIntegerSmulMemLattice
theorem _root_.solution {E : Type} [Field E] [NumberField E] (c : E) :
    ∃ d : ℤ, d ≠ 0 ∧ ∃ r : 𝓞 E, (r : E) = (d : E) * c := by
  have hQ : IsAlgebraic ℚ c := Algebra.IsAlgebraic.isAlgebraic c
  have hZ : IsAlgebraic ℤ c := (IsFractionRing.isAlgebraic_iff ℤ ℚ E).2 hQ
  obtain ⟨d, hd, hint⟩ := hZ.exists_integral_multiple
  refine ⟨d, hd, ⟨d • c, hint⟩, ?_⟩
  change d • c = (d : E) * c
  rw [zsmul_eq_mul]
end GlobalTheory.IntMulIntegerSmulMemLattice
