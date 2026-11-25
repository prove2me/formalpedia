-- Prove2me | solution 1 for Hamiltonicity.edges_walkOf
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T21:16:53.99666+00:00
-- url     : https://prove2.me/submissions/adc1deea-c699-4b05-9a7c-60fa40346e19

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
