-- Prove2me | solution 1 for MiLAC.parallel_castAdd_castAdd
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-20T22:37:13.639721+00:00
-- url     : https://prove2.me/submissions/f4b23197-7fe2-4a93-8d02-505c32661769

module
public import Mathlib.Analysis.Complex.Exponential
public import Mathlib.Data.Matrix.Block
public import Mathlib.Data.Matrix.PEquiv
public import Definitions.Def_LeanPool_MicrowaveNetworks_Basic
public import Theorems.Thm_MiLAC_castAdd_ne_natAdd
public import Theorems.Thm_MiLAC_natAdd_ne_castAdd
attribute [local simp] MiLAC.castAdd_ne_natAdd
attribute [local simp] MiLAC.natAdd_ne_castAdd

set_option autoImplicit true
@[expose] public section
public section
open MiLAC
namespace MiLAC
theorem _root_.solution {n m : ℕ} (A : Network n) (B : Network m)
    (i j : Fin n) : parallel A B (Fin.castAdd m i) (Fin.castAdd m j) = A i j := by
  simp [parallel, Matrix.reindex_apply]
end MiLAC
