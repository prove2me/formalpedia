-- Prove2me | solution 1 for GlobalTheory.regularPair_pow
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-27T04:42:31.079617+00:00
-- url     : https://prove2.me/submissions/44e5bdd6-681e-4ab1-8ca2-4debeccef579

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_DivMemOfMulPowDivMemOfRegularPair
import Theorems.Thm_GlobalTheory_div_mem_of_mul_pow_div_mem_of_regularPair

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory
namespace GlobalTheory
theorem _root_.solution : ∀ (K : Type) [Field K] (O : Subring K) (s t : K), s ∈ O → t ∈ O → s ≠ 0 → (∀ g ∈ O, g * t / s ∈ O → g / s ∈ O) → ∀ (m N : ℕ), ∀ g ∈ O, g * t ^ N / s ^ m ∈ O → g / s ^ m ∈ O := by
  intro K _ O s t hs ht hs0 h m N
  induction m with
  | zero => intro g hg _; simpa using hg
  | succ m ih =>
    intro g hg hgN
    have h1 : g * t ^ N / s ∈ O := by
      have h2 := O.mul_mem hgN (O.pow_mem hs m)
      have e : g * t ^ N / s ^ (m + 1) * s ^ m = g * t ^ N / s := by
        field_simp
        ring
      rwa [e] at h2
    have h3 := div_mem_of_mul_pow_div_mem_of_regularPair K O s t ht h N g hg h1
    have e1 : g / s * t ^ N / s ^ m = g * t ^ N / s ^ (m + 1) := by
      field_simp
      ring
    have e2 : g / s / s ^ m = g / s ^ (m + 1) := by
      field_simp
      ring
    rw [← e2]
    exact ih _ h3 (by rwa [e1])
end GlobalTheory
