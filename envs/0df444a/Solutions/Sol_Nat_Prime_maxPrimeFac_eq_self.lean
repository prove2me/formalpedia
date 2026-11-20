-- Prove2me | solution 1 for Nat.Prime.maxPrimeFac_eq_self
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T19:12:11.15797+00:00
-- url     : https://prove2.me/submissions/a6723dd4-8967-43b3-91e6-b784eae6e50f

module
public import Mathlib.Data.Nat.PrimeFin
public import Mathlib.Order.Lattice.Nat
public import Definitions.Def_CoprimeAdjacencies_CompatMaxPrimeFac
public import Theorems.Thm_Nat_maxPrimeFac_dvd
public import Theorems.Thm_Nat_le_maxPrimeFac

set_option autoImplicit true
@[expose] public section
public section
open Nat
variable {m n p : ℕ}
namespace Nat
namespace Prime
theorem _root_.solution (hp : p.Prime) : maxPrimeFac p = p := by
  apply le_antisymm
  · exact Nat.le_of_dvd hp.pos maxPrimeFac_dvd
  · exact le_maxPrimeFac hp.ne_zero hp (dvd_refl p)
end Prime
end Nat
