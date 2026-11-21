-- Prove2me | solution 1 for MiLAC.castAdd_ne_natAdd
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-20T22:36:11.326549+00:00
-- url     : https://prove2.me/submissions/ef3625b7-bae4-406e-84b9-cef580e5f7bd

module
public import Mathlib.Analysis.Complex.Exponential
public import Mathlib.Data.Matrix.Block
public import Mathlib.Data.Matrix.PEquiv
public import Definitions.Def_LeanPool_MicrowaveNetworks_Basic

set_option autoImplicit true
@[expose] public section
public section
open MiLAC
namespace MiLAC
theorem _root_.solution {n m : ℕ} (i : Fin n) (j : Fin m) :
    Fin.castAdd m i ≠ Fin.natAdd n j :=
  Fin.ne_of_val_ne (Nat.ne_of_lt (Nat.lt_of_lt_of_le i.isLt (Nat.le_add_right n j.val)))
end MiLAC
