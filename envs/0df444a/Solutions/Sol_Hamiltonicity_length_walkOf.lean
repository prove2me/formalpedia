-- Prove2me | solution 1 for Hamiltonicity.length_walkOf
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T21:16:56.079953+00:00
-- url     : https://prove2.me/submissions/e42863f7-ddc3-4508-a03b-e482de6f65db

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
    (n : ℕ) : (walkOf G f hf n).length = n := by
  induction n with
  | zero => simp [walkOf]
  | succ n ih => rw [walkOf, Walk.length_concat, ih]
end Hamiltonicity
