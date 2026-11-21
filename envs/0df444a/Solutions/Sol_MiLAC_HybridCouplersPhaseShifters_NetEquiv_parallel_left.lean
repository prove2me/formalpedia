-- Prove2me | solution 1 for MiLAC.HybridCouplersPhaseShifters.NetEquiv.parallel_left
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-20T22:41:03.210167+00:00
-- url     : https://prove2.me/submissions/c2772fdd-45b3-4699-a7b6-e73d87f8c9c8

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
namespace NetEquiv
theorem _root_.solution {X Y : Σ n : ℕ, Network n} (h : NetEquiv X Y) {a : ℕ}
    (A : Network a) :
    NetEquiv ⟨X.1 + a, parallel X.2 A⟩ ⟨Y.1 + a, parallel Y.2 A⟩ := by
  obtain ⟨e, he⟩ := h
  obtain ⟨k, M⟩ := X
  dsimp only at e he ⊢
  rw [he]
  refine ⟨finSumFinEquiv.symm.trans ((Equiv.sumCongr e (Equiv.refl _)).trans
    finSumFinEquiv), ?_⟩
  ext i j
  induction i using Fin.addCases <;> induction j using Fin.addCases <;> simp
end NetEquiv
end MiLAC.HybridCouplersPhaseShifters
