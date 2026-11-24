-- Prove2me | solution 1 for GlobalTheory.smul_eq_zero_of_ringOfIntegers
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T23:33:48.700123+00:00
-- url     : https://prove2.me/submissions/81cecf39-4b37-4373-84ad-3cda1f87c64d

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_FinrankEqRankMulDegree

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField
open GlobalTheory
namespace GlobalTheory
theorem _root_.solution {F : Type} [Field F] [NumberField F] {M : Type}
    [AddCommGroup M] [Module (𝓞 F) M] [IsAddTorsionFree M] {a : 𝓞 F} (ha : a ≠ 0) {m : M}
    (h : a • m = 0) : m = 0 := by
  have hmem := Ideal.absNorm_mem (Ideal.span {a})
  rw [Ideal.mem_span_singleton] at hmem
  obtain ⟨b, hb⟩ := hmem
  have hn : Ideal.absNorm (Ideal.span {a}) ≠ 0 := by
    rw [Ne, Ideal.absNorm_eq_zero_iff, Ideal.span_singleton_eq_bot]; exact ha
  have h2 : (Ideal.absNorm (Ideal.span {a})) • m = 0 := by
    rw [← Nat.cast_smul_eq_nsmul (𝓞 F), hb, mul_comm, mul_smul, h, smul_zero]
  exact nsmul_right_injective hn (by simpa using h2)
end GlobalTheory
