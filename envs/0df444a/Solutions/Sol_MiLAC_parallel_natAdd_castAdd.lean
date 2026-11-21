-- Prove2me | solution 1 for MiLAC.parallel_natAdd_castAdd
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-20T22:38:20.647182+00:00
-- url     : https://prove2.me/submissions/8c706fa3-4a5a-46f9-8ff1-1695707f2393

module
public import Mathlib.Analysis.Complex.Exponential
public import Mathlib.Data.Matrix.Block
public import Mathlib.Data.Matrix.PEquiv
public import Definitions.Def_LeanPool_MicrowaveNetworks_Basic
public import Theorems.Thm_MiLAC_castAdd_ne_natAdd
public import Theorems.Thm_MiLAC_natAdd_ne_castAdd
public import Theorems.Thm_MiLAC_parallel_castAdd_castAdd
public import Theorems.Thm_MiLAC_parallel_castAdd_natAdd
attribute [local simp] MiLAC.castAdd_ne_natAdd
attribute [local simp] MiLAC.natAdd_ne_castAdd
attribute [local simp] MiLAC.parallel_castAdd_castAdd
attribute [local simp] MiLAC.parallel_castAdd_natAdd

set_option autoImplicit true
@[expose] public section
public section
open MiLAC
namespace MiLAC
theorem _root_.solution {n m : ℕ} (A : Network n) (B : Network m)
    (i : Fin m) (j : Fin n) : parallel A B (Fin.natAdd n i) (Fin.castAdd m j) = 0 := by
  simp [parallel, Matrix.reindex_apply]
end MiLAC
