-- Prove2me | solution 1 for GlobalTheory.ResidueSpanScale.exists_scale
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T19:56:29.323178+00:00
-- url     : https://prove2.me/submissions/3a1107b6-08f7-4d90-a951-a5de49ba28b2

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_FinrankSpanResidueLe

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.ResidueSpanScale
namespace GlobalTheory.ResidueSpanScale
theorem _root_.solution {O K J : Type} [CommRing O] [IsDomain O] [ValuationRing O] [Field K]
    [Algebra O K] [IsFractionRing O K] [Finite J] (c : J → K) (j : J) (hj : c j ≠ 0) :
    ∃ (j₀ : J) (d : J → O), c j₀ ≠ 0 ∧ d j₀ = 1 ∧ ∀ i, c i = c j₀ * algebraMap O K (d i) := by
  classical
  haveI : Nonempty J := ⟨j⟩
  obtain ⟨j₀, h₀⟩ := Finite.exists_max (fun i => ValuationRing.valuation O K (c i))
  have hv : ValuationRing.valuation O K (c j₀) ≠ 0 := by
    intro h
    have h1 := h₀ j
    rw [h, le_zero_iff] at h1
    exact hj ((Valuation.zero_iff _).1 h1)
  have hc : c j₀ ≠ 0 := fun h => hv (by rw [h, map_zero])
  have hex : ∀ i, ∃ a : O, algebraMap O K a = c i / c j₀ := by
    intro i
    rw [← ValuationRing.mem_integer_iff, Valuation.mem_integer_iff, map_div₀]
    exact div_le_one_of_le₀ (h₀ i) zero_le
  choose d hd using hex
  refine ⟨j₀, d, hc, ?_, fun i => ?_⟩
  · apply IsFractionRing.injective O K
    rw [hd, div_self hc, map_one]
  · rw [hd]; field_simp
end GlobalTheory.ResidueSpanScale
