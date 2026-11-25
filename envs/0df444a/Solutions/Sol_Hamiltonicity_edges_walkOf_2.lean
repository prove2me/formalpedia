-- Prove2me | solution 2 for Hamiltonicity.edges_walkOf
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T21:46:43.384312+00:00
-- url     : https://prove2.me/submissions/045b9be2-428e-4c11-9727-2325d166dc31

module
public import Definitions.Def_MengerHamilton_Menger
public import Definitions.Def_MengerHamilton_CyclicArrangement

set_option autoImplicit true
@[expose] public section
public section
open SimpleGraph
open Hamiltonicity
variable {V : Type*}
namespace Hamiltonicity
theorem _root_.solution (G : SimpleGraph V) (f : ℕ → V) (hf : ∀ i, G.Adj (f i) (f (i + 1)))
    (n : ℕ) : (walkOf G f hf n).edges = (List.range n).map (fun i => s(f i, f (i + 1))) := by
  induction n with
  | zero => simp [walkOf]
  | succ n ih =>
    rw [walkOf, Walk.edges_concat, ih]
    conv_rhs => rw [List.range_succ]
    simp
end Hamiltonicity
