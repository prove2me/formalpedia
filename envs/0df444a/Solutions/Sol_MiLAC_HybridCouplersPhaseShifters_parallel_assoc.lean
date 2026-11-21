-- Prove2me | solution 1 for MiLAC.HybridCouplersPhaseShifters.parallel_assoc
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-20T22:41:02.661942+00:00
-- url     : https://prove2.me/submissions/8a783e10-1975-4726-86be-fbe24cb487de

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
theorem _root_.solution {a b c : ℕ} (A : Network a) (B : Network b) (C : Network c) :
    NetEquiv ⟨a + b + c, parallel (parallel A B) C⟩
      ⟨a + (b + c), parallel A (parallel B C)⟩ := by
  refine ⟨finCongr (add_assoc a b c), ?_⟩
  have h1 : ∀ x : Fin a, finCongr (add_assoc a b c) (Fin.castAdd c (Fin.castAdd b x)) =
      Fin.castAdd (b + c) x := fun x => by ext; simp
  have h2 : ∀ x : Fin b, finCongr (add_assoc a b c) (Fin.castAdd c (Fin.natAdd a x)) =
      Fin.natAdd a (Fin.castAdd c x) := fun x => by ext; simp
  have h3 : ∀ x : Fin c, finCongr (add_assoc a b c) (Fin.natAdd (a + b) x) =
      Fin.natAdd a (Fin.natAdd b x) := fun x => by ext; simp [add_assoc]
  ext i j
  induction i using Fin.addCases with
  | left i =>
      induction i using Fin.addCases <;>
      induction j using Fin.addCases with
      | left j => induction j using Fin.addCases <;> simp [h1, h2]
      | right j => simp [h1, h2, h3]
  | right i =>
      induction j using Fin.addCases with
      | left j => induction j using Fin.addCases <;> simp [h1, h2, h3]
      | right j => simp [h3]
end MiLAC.HybridCouplersPhaseShifters
