-- Prove2me | solution 2 for Monodromy.Choice.dispatch_exact_iff
-- status  : ACCEPTED   (prove)
-- author  : @Xiaoyang Liu
-- created : 2026-11-06T14:56:04.720017+00:00
-- url     : https://prove2.me/submissions/d5278cdb-b5e5-4657-b27d-cd465ef70810

-- Generated mechanically from the frozen source; no own-target import.
module
public import Definitions.Def_Monodromy_Choice
public import Mathlib.Analysis.Analytic.Constructions
public import Mathlib.Analysis.Analytic.IsolatedZeros
public import Mathlib.Analysis.Calculus.DSlope
public import Mathlib.Analysis.Calculus.Deriv.Add
public import Mathlib.Analysis.Calculus.Deriv.Comp
public import Mathlib.Analysis.Calculus.Deriv.Mul
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Logic.Function.Conjugate
public import Mathlib.Tactic.FunProp
public import Mathlib.Topology.Homotopy.Lifting

@[expose] public section


-- Original target, hoisted to top-level theorem solution.
open Monodromy
open Monodromy.Choice
theorem solution {ι : Type*} [Fintype ι]
    {f : ℂ → ℂ} {roots : ι → ℂ}
    (same_fiber : ∀ i j, f (roots i) = f (roots j)) :
    (∀ values : ι → ℂ, ∀ i, dispatch f roots values (roots i) = values i) ↔
      Function.Injective roots ∧ ∀ i, deriv f (roots i) ≠ 0 := by
  classical
  constructor
  · intro reads
    constructor
    · intro first second same
      by_contra different
      have one := reads (fun i => if i = first then 1 else 0) first
      have zero := reads (fun i => if i = first then 1 else 0) second
      rw [same] at one
      have impossible := one.symm.trans zero
      simp [Ne.symm different] at impossible
    · intro i critical
      have self : kernel f (roots i) (roots i) = 1 := by
        simpa [dispatch] using reads (fun j => if j = i then 1 else 0) i
      simp [kernel, critical] at self
  · rintro ⟨distinct, regular⟩ values i
    exact dispatch_root distinct same_fiber regular i
