-- Prove2me | solution 1 for GlobalTheory.CuspGL.Primary.eq_top_of_nilpotent
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T14:03:58.524376+00:00
-- url     : https://prove2.me/submissions/6450f8e7-efcc-4993-8f27-be01135f564b

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_CommutativeAlgebra_AbByPOfComm
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_CommutativeAlgebra_InvariantSubspaceMobiusInverseRecEqOfFinrankLt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CharacterTheory_CharpolyBlockAndInvariantUnderStabilizerNilradic
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CharacterTheory_FinsumMobiusInverseCharpolyInvariantLe
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CharacterTheory_InvariantSubspaceMobiusInverseCharpolyLinearEqui
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_MobiusInversionAffineFinrankSubspacesStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsSurjectivePiAdjoinRootKerEqRangeStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_AevalApplyMem
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_InvariantSubspaceMobiusInverseCharpolyPrimaryEq

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Polynomial GlobalTheory.CuspGL GlobalTheory.BI
open GlobalTheory GlobalTheory.CuspGL GlobalTheory.CuspGL.Primary
namespace GlobalTheory.CuspGL.Primary
theorem _root_.solution {F V : Type} [Field F] [AddCommGroup V] [Module F V] (N : Module.End F V)
    {m : ℕ} (hN : N ^ m = 0) (W : Submodule F V) (hW : ∀ x ∈ W, N x ∈ W)
    (h : ∀ v, ∃ w ∈ W, ∃ u, v = w + N u) : W = ⊤ := by
  have hp : ∀ (j : ℕ), ∀ x ∈ W, (N ^ j) x ∈ W := by
    intro j
    induction j with
    | zero => intro x hx; simpa using hx
    | succ j ih => intro x hx; rw [pow_succ, Module.End.mul_apply]; exact ih _ (hW x hx)
  have key : ∀ (j : ℕ) (v : V), ∃ w ∈ W, ∃ u, v = w + (N ^ j) u := by
    intro j
    induction j with
    | zero => intro v; exact ⟨0, W.zero_mem, v, by simp⟩
    | succ j ih =>
      intro v
      obtain ⟨w, hw, u, rfl⟩ := ih v
      obtain ⟨w', hw', u', rfl⟩ := h u
      refine ⟨w + (N ^ j) w', W.add_mem hw (hp j w' hw'), u', ?_⟩
      rw [map_add, pow_succ, Module.End.mul_apply, add_assoc]
  refine eq_top_iff.2 fun v _ => ?_
  obtain ⟨w, hw, u, rfl⟩ := key m v
  simpa [hN] using hw
end GlobalTheory.CuspGL.Primary
