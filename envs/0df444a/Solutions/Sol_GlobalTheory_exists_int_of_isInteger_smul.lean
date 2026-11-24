-- Prove2me | solution 1 for GlobalTheory.exists_int_of_isInteger_smul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T22:42:36.340328+00:00
-- url     : https://prove2.me/submissions/8c4cfe2a-56da-4f89-8c7d-4a9e9b3d8c08

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_AlternatingFormLatticeIntegrality

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField
open scoped nonZeroDivisors
open GlobalTheory
namespace GlobalTheory
theorem _root_.solution {F : Type} [Field F] [NumberField F] (d : 𝓞 F) (y : F)
    (h : IsLocalization.IsInteger (𝓞 F) (d • y)) : ∃ n : 𝓞 F, (n : F) = (d : F) * y := by
  obtain ⟨n, hn⟩ := h
  refine ⟨n, ?_⟩
  rw [RingOfIntegers.coe_eq_algebraMap, hn, Algebra.smul_def, ← RingOfIntegers.coe_eq_algebraMap]
end GlobalTheory
