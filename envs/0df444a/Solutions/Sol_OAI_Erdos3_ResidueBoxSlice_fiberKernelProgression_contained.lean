-- Prove2me | solution 1 for OAI.Erdos3.ResidueBoxSlice.fiberKernelProgression_contained
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-10T01:28:14.092687+00:00
-- url     : https://prove2.me/submissions/7493265e-a56e-4aaa-9391-89085deee5c6

import Mathlib
import Definitions.Def_ErdosReciprocal
import Definitions.Def_OAIErdos3B147

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Linear.KernelPrincipalFiberSliceLaw
namespace OAI

section

namespace Erdos3

open scoped BigOperators

variable {G D : Type*} [Fintype G] [DecidableEq G] [Fintype D] [DecidableEq D]
variable (B : D → Type*) [∀ a, Fintype (B a)] [∀ a, DecidableEq (B a)] (h : D → ℕ)
variable (LG : G → ℕ) (L : PrincipalTupleIndex B h → ℕ)

namespace ResidueBoxSlice

variable {B h LG L}
variable {keep : G ⊕ PrincipalTupleIndex B h → Prop} [DecidablePred keep] {q : ℕ}
variable (S : ResidueBoxSlice (fun k : {k // keep k} => Sum.elim LG L k.val) q)
variable (hlen : ∀ k, 0 < S.length k) (fixed : {k // ¬keep k} → ℤ)
variable (hfixed : ∀ k, 0 ≤ fixed k ∧ fixed k < ((Sum.elim LG L k.val : ℕ) : ℤ))
variable (hkernel : ∀ g, keep (Sum.inl g))

omit [Fintype G] [DecidableEq G] [Fintype D] [DecidableEq D]
  [∀ a, Fintype (B a)] [∀ a, DecidableEq (B a)] [DecidablePred keep] in
theorem fiberKernelProgression_contained (g : G) :
    integerProgressionSupport (S.start ⟨Sum.inl g, hkernel g⟩ : ℤ) (q : ℤ)
        (S.length ⟨Sum.inl g, hkernel g⟩) ⊆ Finset.Ico (0 : ℤ) (LG g : ℤ) := by
  apply integerProgressionSupport_subset_of_fin
  intro t
  constructor
  · positivity
  · exact_mod_cast S.inside ⟨Sum.inl g, hkernel g⟩ t.val t.isLt

end ResidueBoxSlice
end Erdos3

end

end OAI

end

theorem solution.{u_1, u_2, u_3} : type_of% @OAI.Erdos3.ResidueBoxSlice.fiberKernelProgression_contained.{u_1, u_2, u_3} := @OAI.Erdos3.ResidueBoxSlice.fiberKernelProgression_contained.{u_1, u_2, u_3}
