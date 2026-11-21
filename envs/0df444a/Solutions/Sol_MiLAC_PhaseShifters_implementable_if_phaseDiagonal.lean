-- Prove2me | solution 1 for MiLAC.PhaseShifters.implementable_if_phaseDiagonal
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-20T22:39:28.58818+00:00
-- url     : https://prove2.me/submissions/e01f1aed-9f96-44ac-b45b-0906650c5011

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
open MiLAC
open MiLAC.PhaseShifters
namespace MiLAC.PhaseShifters
theorem _root_.solution {n : ℕ} (φ : Fin n → ℝ) :
    Implementable (phaseDiagonal φ) := by
  induction n with
  | zero =>
      convert Implementable.pn (Equiv.refl (Fin 0)) using 1
      ext i
      exact Fin.elim0 i
  | succ n ih =>
      have hdecomp : phaseDiagonal φ =
          parallel (phaseDiagonal (fun i => φ (Fin.castAdd 1 i)))
            (phaseShifter (φ (Fin.natAdd n 0))) := by
        ext i j
        induction i using Fin.addCases <;> induction j using Fin.addCases <;>
          simp [phaseDiagonal, phaseShifter, Matrix.diagonal_apply, Fin.fin_one_eq_zero]
      rw [hdecomp]
      exact Implementable.parallel (ih _) (Implementable.ps _)
end MiLAC.PhaseShifters
