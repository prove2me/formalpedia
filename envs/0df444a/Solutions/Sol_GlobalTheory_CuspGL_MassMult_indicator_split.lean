-- Prove2me | solution 1 for GlobalTheory.CuspGL.MassMult.indicator_split
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T14:04:05.406871+00:00
-- url     : https://prove2.me/submissions/37ccadc2-fcab-4a3d-ad5b-195788fbe4cd

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_CommutativeAlgebra_InvariantSubspaceMobiusInverseRecEqOfFinrankLt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CharacterTheory_CharpolyBlockAndInvariantUnderStabilizerNilradicStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CharacterTheory_FinsumSubspaceStabilizerMulBlockFunctionsStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CharacterTheory_CardSubspacesMulGeneralLinearGroupCardStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CharacterTheory_EndomorphismMassEqOfLinearEquivInvariantStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CharacterTheory_EndomorphismMassMulParabolicInductionTrivial

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Polynomial GlobalTheory.CuspGL
open GlobalTheory GlobalTheory.CuspGL GlobalTheory.CuspGL.MassMult
open Classical
namespace GlobalTheory.CuspGL.MassMult
theorem _root_.solution {F : Type} [Field F] (P : F[X])
    (T : Finset (F[X] × F[X])) (hT : ∀ x, x ∈ T ↔ x.1.Monic ∧ x.2.Monic ∧ x.1 * x.2 = P)
    {a b c : F[X]} (ha : a.Monic) (hb : b.Monic) (hc : c = a * b) (z : ℂ) :
    (if c = P then z else 0) =
      ∑ x ∈ T, (if a = x.1 then z else 0) * (if b = x.2 then (1 : ℂ) else 0) := by
  by_cases hg : c = P
  · rw [if_pos hg, Finset.sum_eq_single (a, b)]
    · rw [if_pos rfl, if_pos rfl, mul_one]
    · rintro ⟨b1, b2⟩ _ hb
      by_cases h1 : a = b1
      · by_cases h2 : b = b2
        · exact absurd (by rw [h1, h2]) hb
        · rw [if_neg h2, mul_zero]
      · rw [if_neg h1, zero_mul]
    · intro hn
      exact (hn ((hT (a, b)).2 ⟨ha, hb, hc.symm.trans hg⟩)).elim
  · rw [if_neg hg]
    refine (Finset.sum_eq_zero ?_).symm
    rintro ⟨b1, b2⟩ hb
    by_cases h1 : a = b1
    · by_cases h2 : b = b2
      · refine absurd ?_ hg
        rw [hc, h1, h2]
        exact ((hT (b1, b2)).1 hb).2.2
      · rw [if_neg h2, mul_zero]
    · rw [if_neg h1, zero_mul]
end GlobalTheory.CuspGL.MassMult
