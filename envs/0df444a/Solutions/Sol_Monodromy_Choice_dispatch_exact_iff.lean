-- Prove2me | solution 1 for Monodromy.Choice.dispatch_exact_iff
-- status  : ACCEPTED   (prove)
-- author  : @nonlocally
-- created : 2026-11-05T18:41:06.641312+00:00
-- url     : https://prove2.me/submissions/23a60268-2654-4d17-8775-d288d97004e8

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

open Monodromy
open Monodromy.Choice

theorem solution {ι : Type*} [Fintype ι]
    {f : ℂ → ℂ} {roots : ι → ℂ}
    (same_fiber : ∀ i j, f (roots i) = f (roots j)) :
    (∀ values : ι → ℂ, ∀ i, dispatch f roots values (roots i) = values i) ↔
      Function.Injective roots ∧ ∀ i, deriv f (roots i) ≠ 0 := by
  classical
  constructor
  · intro exact_readout
    have self_kernel (i : ι) : kernel f (roots i) (roots i) = 1 := by
      have h := exact_readout (Pi.single i (1 : ℂ)) i
      simpa [dispatch, Pi.single_apply] using h
    have regular : ∀ i, deriv f (roots i) ≠ 0 := by
      intro i hzero
      have h := self_kernel i
      rw [kernel, hzero, div_zero] at h
      exact zero_ne_one h
    refine ⟨?_, regular⟩
    intro i j hij
    let values : ι → ℂ := Pi.single i 1
    have hi := exact_readout values i
    have hj := exact_readout values j
    rw [← hij] at hj
    have hdelta : values i = values j := hi.symm.trans hj
    by_contra hne
    simp [values, hne] at hdelta
  · rintro ⟨distinct, regular⟩ values i
    exact dispatch_root distinct same_fiber regular i
