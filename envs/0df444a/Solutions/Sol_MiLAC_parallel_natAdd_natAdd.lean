-- Prove2me | solution 1 for MiLAC.parallel_natAdd_natAdd
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-20T22:38:54.309633+00:00
-- url     : https://prove2.me/submissions/492524f4-aca7-47f7-9a16-ec9dfe404090

module
public import Mathlib.Analysis.Complex.Exponential
public import Mathlib.Data.Matrix.Block
public import Mathlib.Data.Matrix.PEquiv
public import Definitions.Def_LeanPool_MicrowaveNetworks_Basic
public import Theorems.Thm_MiLAC_castAdd_ne_natAdd
public import Theorems.Thm_MiLAC_natAdd_ne_castAdd
public import Theorems.Thm_MiLAC_parallel_castAdd_castAdd
public import Theorems.Thm_MiLAC_parallel_castAdd_natAdd
public import Theorems.Thm_MiLAC_parallel_natAdd_castAdd
attribute [local simp] MiLAC.castAdd_ne_natAdd
attribute [local simp] MiLAC.natAdd_ne_castAdd
attribute [local simp] MiLAC.parallel_castAdd_castAdd
attribute [local simp] MiLAC.parallel_castAdd_natAdd
attribute [local simp] MiLAC.parallel_natAdd_castAdd

set_option autoImplicit true
@[expose] public section
public section
open MiLAC
namespace MiLAC
theorem _root_.solution {n m : ℕ} (A : Network n) (B : Network m)
    (i j : Fin m) : parallel A B (Fin.natAdd n i) (Fin.natAdd n j) = B i j := by
  simp [parallel, Matrix.reindex_apply]
end MiLAC
