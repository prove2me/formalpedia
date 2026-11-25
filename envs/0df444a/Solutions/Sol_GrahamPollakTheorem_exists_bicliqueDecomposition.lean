-- Prove2me | solution 1 for GrahamPollakTheorem.exists_bicliqueDecomposition
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T10:22:07.70745+00:00
-- url     : https://prove2.me/submissions/45f8cd07-3517-4565-aeef-abc0d8873aa3

module
public import Mathlib
public import Definitions.Def_GrahamPollakLib_GrahamPollak
public import Definitions.Def_GrahamPollak_Solution
public import Theorems.Thm_GrahamPollak_exists_bicliqueDecomposition


set_option autoImplicit true
@[expose] public section
public section
open GrahamPollakTheorem
variable {V : Type*}
namespace GrahamPollakTheorem
theorem _root_.solution (n : ℕ) (hn : 1 ≤ n) :
    ∃ A B : Fin (n - 1) → Finset (Fin n), IsBicliqueDecomposition A B :=
  GrahamPollak.exists_bicliqueDecomposition n hn
end GrahamPollakTheorem
