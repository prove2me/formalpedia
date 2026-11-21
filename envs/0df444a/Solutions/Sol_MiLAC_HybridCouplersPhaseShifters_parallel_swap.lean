-- Prove2me | solution 1 for MiLAC.HybridCouplersPhaseShifters.parallel_swap
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-20T22:41:02.071165+00:00
-- url     : https://prove2.me/submissions/b2ce288d-2bad-4017-b113-bb6db186e88d

module
public import Definitions.Def_LeanPool_MicrowaveNetworks_Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
public import Mathlib.LinearAlgebra.Matrix.Notation
public import Definitions.Def_LeanPool_MicrowaveNetworks_HybridCouplersPhaseShifters
public import Theorems.Thm_MiLAC_castAdd_ne_natAdd
public import Theorems.Thm_MiLAC_natAdd_ne_castAdd
public import Theorems.Thm_MiLAC_parallel_castAdd_castAdd
public import Theorems.Thm_MiLAC_parallel_castAdd_natAdd
public import Theorems.Thm_MiLAC_parallel_natAdd_castAdd
public import Theorems.Thm_MiLAC_parallel_natAdd_natAdd
attribute [local simp] MiLAC.castAdd_ne_natAdd
attribute [local simp] MiLAC.natAdd_ne_castAdd
attribute [local simp] MiLAC.parallel_castAdd_castAdd
attribute [local simp] MiLAC.parallel_castAdd_natAdd
attribute [local simp] MiLAC.parallel_natAdd_castAdd
attribute [local simp] MiLAC.parallel_natAdd_natAdd



set_option autoImplicit true
@[expose] public section
public section
open MiLAC MiLAC.HybridCouplersPhaseShifters
namespace MiLAC.HybridCouplersPhaseShifters
theorem _root_.solution {n m : ℕ} (A : Network n) (B : Network m) :
    NetEquiv ⟨n + m, parallel A B⟩ ⟨m + n, parallel B A⟩ := by
  refine ⟨finSumFinEquiv.symm.trans ((Equiv.sumComm _ _).trans finSumFinEquiv), ?_⟩
  ext i j
  induction i using Fin.addCases <;> induction j using Fin.addCases <;> simp
end MiLAC.HybridCouplersPhaseShifters
