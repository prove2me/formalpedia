-- Prove2me | solution 2 for Hamiltonicity.support_walkOf
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T21:46:42.1368+00:00
-- url     : https://prove2.me/submissions/38e00ebc-dedf-4e44-bfc7-9054f11ac25c

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
    (n : ℕ) : (walkOf G f hf n).support = (List.range (n + 1)).map f := by
  induction n with
  | zero => simp [walkOf]
  | succ n ih =>
    rw [walkOf, Walk.support_concat, ih]
    conv_rhs => rw [List.range_succ]
    simp
end Hamiltonicity
