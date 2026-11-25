-- Prove2me | solution 1 for GrahamPollakTheorem.graham_pollak
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T10:30:19.642976+00:00
-- url     : https://prove2.me/submissions/12511a57-c535-45dd-bb6f-368d2ea616ab

module
public import Mathlib
public import Definitions.Def_GrahamPollakLib_GrahamPollak
public import Definitions.Def_GrahamPollak_Solution
public import Theorems.Thm_GrahamPollak_graham_pollak


set_option autoImplicit true
@[expose] public section
public section
open GrahamPollakTheorem
variable {V : Type*}
namespace GrahamPollakTheorem
theorem _root_.solution [Fintype V] [DecidableEq V] {m : ℕ} (A B : Fin m → Finset V)
    (h : IsBicliqueDecomposition A B) : Fintype.card V - 1 ≤ m :=
  GrahamPollak.graham_pollak A B h
end GrahamPollakTheorem
