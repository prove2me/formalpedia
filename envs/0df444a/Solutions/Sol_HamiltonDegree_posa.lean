-- Prove2me | solution 1 for HamiltonDegree.posa
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T21:39:03.377295+00:00
-- url     : https://prove2.me/submissions/673fc365-5f9b-4935-8ce7-882ce2ff6f2e

module
public import Mathlib
public import Definitions.Def_ChvatalPosaLib_ChvatalPosa
public import Definitions.Def_ChvatalPosaHamiltonian_Solution
public import Theorems.Thm_ChvatalPosa_posa


set_option autoImplicit true
@[expose] public section
public section
open Finset SimpleGraph
open HamiltonDegree
variable {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
namespace HamiltonDegree
theorem _root_.solution (hn : 3 ≤ Fintype.card V)
    (h₁ : ∀ k : ℕ, 1 ≤ k → 2 * k < Fintype.card V - 1 → #{v | G.degree v ≤ k} < k)
    (h₂ : Odd (Fintype.card V) →
      #{v | G.degree v ≤ (Fintype.card V - 1) / 2} ≤ (Fintype.card V - 1) / 2) :
    G.IsHamiltonian :=
  ChvatalPosa.posa G hn h₁ h₂
end HamiltonDegree
