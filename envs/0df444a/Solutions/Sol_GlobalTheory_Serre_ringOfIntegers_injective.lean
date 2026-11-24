-- Prove2me | solution 1 for GlobalTheory.Serre.ringOfIntegers_injective
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T08:53:18.66048+00:00
-- url     : https://prove2.me/submissions/3bf39957-a0c9-433e-9ec6-ca0ab634c99d

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_FormallyUnramifiedRingOfIntegers

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open TensorProduct
open GlobalTheory GlobalTheory.Serre
open NumberField
variable (k K E : Type*) [Field k] [CharZero k] [Field K] [Field E] [NumberField K] [NumberField E]
  [Algebra K E]
omit [NumberField K]
namespace GlobalTheory.Serre
theorem _root_.solution (τ : 𝓞 K →+* k) : Function.Injective τ := by
  rw [RingHom.injective_iff_ker_eq_bot]
  refine Ideal.eq_bot_of_comap_eq_bot (R := ℤ) ?_
  rw [RingHom.comap_ker, ← RingHom.injective_iff_ker_eq_bot]
  exact RingHom.injective_int _
end GlobalTheory.Serre
