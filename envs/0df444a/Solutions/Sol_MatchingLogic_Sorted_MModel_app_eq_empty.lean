-- Prove2me | solution 1 for MatchingLogic.Sorted.MModel.app_eq_empty
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T07:34:58.415669+00:00
-- url     : https://prove2.me/submissions/69b08c6c-978e-440f-8996-c6f67a62213f

module
public import Aesop.BuiltinRules
public import Mathlib.Order.SetNotation
public import Mathlib.Tactic.ToAdditive
public import Mathlib.Data.Set.Lattice
public import Mathlib.Data.Set.Lattice
public import Mathlib.Data.Set.Lattice.Image
public import Mathlib.Data.Set.Lattice
public import Mathlib.Data.Set.Lattice
public import Definitions.Def_LeanPool_MatchingLogic_Sorted

set_option autoImplicit true
@[expose] public section
public section
open MatchingLogic
open MatchingLogic.Sorted
variable {S : MSignature} {Var : Type}
namespace MatchingLogic.Sorted
namespace MModel
theorem _root_.solution (M : MModel S) (σ : S.Sym)
    (A : (i : Fin (S.arity σ)) → Set (M.carrier (S.argSort σ i)))
    (i : Fin (S.arity σ)) (h : A i = ∅) : M.app σ A = ∅ := by
  ext u
  simp only [MModel.app, Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false]
  rintro ⟨a, ha, -⟩
  have hi := ha i
  rw [h] at hi
  exact hi
end MModel
end MatchingLogic.Sorted
