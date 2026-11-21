-- Prove2me | solution 1 for MiLAC.natAdd_ne_castAdd
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-20T22:36:39.790729+00:00
-- url     : https://prove2.me/submissions/c0832ee6-2b2d-4f3f-a607-ca78f7035f7a

module
public import Mathlib.Analysis.Complex.Exponential
public import Mathlib.Data.Matrix.Block
public import Mathlib.Data.Matrix.PEquiv
public import Definitions.Def_LeanPool_MicrowaveNetworks_Basic
public import Theorems.Thm_MiLAC_castAdd_ne_natAdd
attribute [local simp] MiLAC.castAdd_ne_natAdd

set_option autoImplicit true
@[expose] public section
public section
open MiLAC
namespace MiLAC
theorem _root_.solution {n m : ℕ} (i : Fin m) (j : Fin n) :
    Fin.natAdd n i ≠ Fin.castAdd m j :=
  (castAdd_ne_natAdd j i).symm
end MiLAC
