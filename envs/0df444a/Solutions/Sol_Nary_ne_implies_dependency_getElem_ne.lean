-- Prove2me | solution 1 for Nary.ne_implies_dependency_getElem_ne
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T04:41:04.206794+00:00
-- url     : https://prove2.me/submissions/f1a85542-44e8-412f-86c4-31ee4b94c825

import Mathlib.Data.Vector.Basic
import Definitions.Def_Bdd_Nary
import Theorems.Thm_Nary_eq_of_forall_dependency_getElem_eq

set_option autoImplicit true
open Nary
namespace Nary
theorem _root_.solution {f : Func n α β} {I J : Vector α n} :
    f I ≠ f J → ∃ i : Nary.Dependency f, I[i.1] ≠ J[i.1] := by
  contrapose
  simp only [Fin.getElem_fin, ne_eq, not_exists, not_not]
  exact Nary.eq_of_forall_dependency_getElem_eq
end Nary
