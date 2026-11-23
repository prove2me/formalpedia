-- Prove2me | solution 1 for GlobalTheory.CuspGL.mangoldt_eq_zero
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T04:14:04.600198+00:00
-- url     : https://prove2.me/submissions/0618a6ff-da1b-4db1-a252-173598b76b96

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_CommutativeAlgebra_InvariantSubspaceMobiusInverseRecEqOfFinrankLt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CharacterTheory_AdditiveEqPolynomialVonMangoldtConvolutionOne

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Polynomial
open GlobalTheory GlobalTheory.CuspGL
variable {F : Type} [Field F]
namespace GlobalTheory.CuspGL
theorem _root_.solution (s : F[X] → ℂ) (P : F[X])
    (h : ¬ ∃ (f : F[X]) (m : ℕ), f.Monic ∧ Irreducible f ∧ 0 < m ∧ P = f ^ m) : mangoldt s P = 0 := by
  have : {g : F[X] | g.Monic ∧ Irreducible g ∧ ∃ k : ℕ, 0 < k ∧ P = g ^ k} = ∅ := by
    ext g
    simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false]
    rintro ⟨hg, hg', k, hk, h'⟩
    exact h ⟨g, k, hg, hg', hk, h'⟩
  rw [mangoldt, this, finsum_mem_empty]
end GlobalTheory.CuspGL
