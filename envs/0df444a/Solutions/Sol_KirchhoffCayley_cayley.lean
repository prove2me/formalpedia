-- Prove2me | solution 1 for KirchhoffCayley.cayley
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T12:00:14.898323+00:00
-- url     : https://prove2.me/submissions/2f8ba1e2-d175-461f-9dc1-45d05ba478d5

module
public import Mathlib
public import Definitions.Def_MatrixTreeLib_MatrixTree
public import Definitions.Def_MatrixTree_Solution
public import Theorems.Thm_MatrixTree_cayley


set_option autoImplicit true
@[expose] public section
public section
open SimpleGraph Matrix Finset
open KirchhoffCayley
namespace KirchhoffCayley
theorem _root_.solution (n : ℕ) (hn : 1 ≤ n) :
    Nat.card {T : SimpleGraph (Fin n) // T.IsTree} = n ^ (n - 2) :=
  MatrixTree.cayley n hn
end KirchhoffCayley
