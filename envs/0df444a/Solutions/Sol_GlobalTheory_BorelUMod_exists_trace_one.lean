-- Prove2me | solution 1 for GlobalTheory.BorelUMod.exists_trace_one
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T17:48:55.080097+00:00
-- url     : https://prove2.me/submissions/26d6eeb7-9b80-42db-8057-55487cc9e5c2

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_LineOppositeParabolicUnitaryLeviSectionEq
import Definitions.Def_Formalism_SatakeDualWeyl_StatementE
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_MemGUIffAdjJ

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.LGrp Formalism.UG
noncomputable section
open GlobalTheory GlobalTheory.BorelUMod
variable {L : Type} [Field L] [Valued L (WithZero (Multiplicative ℤ))] {n : ℕ}
variable {L : Type} [Field L] [Valued L (WithZero (Multiplicative ℤ))] {n : ℕ}
namespace GlobalTheory.BorelUMod
namespace _root_.GlobalTheory.BorelUMod
theorem _root_.solution {ϖ : L} {σ : L →+* L} {q : ℕ}
    (h : _root_.Formalism.UG.IsUnramInv ϖ σ q) :
    (∃ θ : L, Valued.v θ ≤ 1 ∧ θ + σ θ = 1) ∧ ∃ d : L, Valued.v d = 1 ∧ σ d = -d := by
  obtain ⟨hinv, -, -, -, ⟨x, hx, hxu⟩, -⟩ := h
  have hx1 : Valued.v x ≤ 1 := hx
  refine ⟨?_, σ x - x, hxu, by rw [map_sub, hinv]; ring⟩
  have h2le : Valued.v (2 : L) ≤ 1 := by
    have h11 : Valued.v ((1 : L) + 1) ≤ 1 :=
      Valuation.map_add_le _ (le_of_eq (Valuation.map_one _)) (le_of_eq (Valuation.map_one _))
    rwa [one_add_one_eq_two] at h11
  rcases h2le.lt_or_eq with h2 | h2
  · have hlt : Valued.v (2 * x) < Valued.v (σ x - x) := by
      rw [hxu, Valuation.map_mul]
      calc Valued.v (2 : L) * Valued.v x ≤ Valued.v (2 : L) * 1 := mul_le_mul' le_rfl hx1
        _ = Valued.v (2 : L) := mul_one _
        _ < 1 := h2
    have ht : Valued.v (x + σ x) = 1 := by
      have e : x + σ x = (σ x - x) + 2 * x := by ring
      rw [e, Valuation.map_add_eq_of_lt_left _ hlt, hxu]
    have ht0 : x + σ x ≠ 0 := by
      intro e
      rw [e, Valuation.map_zero] at ht
      exact zero_ne_one ht
    refine ⟨x / (x + σ x), ?_, ?_⟩
    · rw [map_div₀, ht, div_one]
      exact hx1
    · rw [map_div₀, map_add, hinv, add_comm (σ x) x, ← add_div, div_self ht0]
  · refine ⟨1 / 2, ?_, ?_⟩
    · rw [map_div₀, Valuation.map_one, h2, div_one]
    · rw [map_div₀, map_one, map_ofNat]
      have h20 : (2 : L) ≠ 0 := by
        intro e
        rw [e, Valuation.map_zero] at h2
        exact zero_ne_one h2
      rw [← add_div, one_add_one_eq_two, div_self h20]
end _root_.GlobalTheory.BorelUMod
end GlobalTheory.BorelUMod
