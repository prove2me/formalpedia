-- Prove2me | solution 1 for GlobalTheory.CuspGL.MassMult.finsum_subtype_dite
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T14:02:53.978475+00:00
-- url     : https://prove2.me/submissions/b0af1af0-d247-459e-898d-513fbd04e7e7

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
theorem _root_.solution {α : Type} [Fintype α] (p : α → Prop) (f : {x // p x} → ℂ) :
    ∑ᶠ x, f x = ∑ x, if h : p x then f ⟨x, h⟩ else 0 := by
  rw [finsum_eq_sum_of_fintype, ← Fintype.sum_subtype_add_sum_subtype p]
  have h1 : ∑ i : {x // ¬ p x}, (if h : p i.1 then f ⟨i.1, h⟩ else 0) = 0 :=
    Finset.sum_eq_zero fun i _ => dif_neg i.2
  rw [h1, add_zero]
  exact Finset.sum_congr rfl fun i _ => by rw [dif_pos i.2]
end GlobalTheory.CuspGL.MassMult
