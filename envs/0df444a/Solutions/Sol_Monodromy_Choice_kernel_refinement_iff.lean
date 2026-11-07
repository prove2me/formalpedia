-- Prove2me | solution 1 for Monodromy.Choice.kernel_refinement_iff
-- status  : ACCEPTED   (prove)
-- author  : @Xiaoyang Liu
-- created : 2026-11-06T14:56:06.312354+00:00
-- url     : https://prove2.me/submissions/f1edb504-5684-4918-b7c8-706f46d648ed

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
theorem solution {κ : Type*} [Fintype κ]
    {f g : ℂ → ℂ} {parent : ℂ} (children : κ → ℂ)
    (distinct : Function.Injective children)
    (projects : ∀ child, g (children child) = parent)
    (regular : deriv f parent ≠ 0)
    (children_regular : ∀ child, deriv (f ∘ g) (children child) ≠ 0) :
    (∀ z, f (g z) = f parent →
      kernel f parent (g z) = ∑ child, kernel (f ∘ g) (children child) z) ↔
      ∀ z, g z = parent → ∃ child, children child = z := by
  classical
  constructor
  · intro refines z same
    by_contra missing
    have zero (child : κ) : kernel (f ∘ g) (children child) z = 0 := by
      apply kernel_other
      · intro equal
        exact missing ⟨child, equal.symm⟩
      · change f (g z) = f (g (children child))
        rw [same, projects child]
    have impossible := refines z (congrArg f same)
    rw [same, kernel_self regular] at impossible
    have total_zero : (∑ child, kernel (f ∘ g) (children child) z) = 0 :=
      Finset.sum_eq_zero (fun child _ => zero child)
    rw [total_zero] at impossible
    exact one_ne_zero impossible
  · intro complete z same_fiber
    by_cases same : g z = parent
    · obtain ⟨child, rfl⟩ := complete z same
      rw [projects child, kernel_self regular]
      have read := dispatch_root (values := fun _ : κ => (1 : ℂ)) distinct
        (fun first second => by simp only [Function.comp_apply, projects]) children_regular child
      simpa only [dispatch, mul_one] using read.symm
    · rw [kernel_other same same_fiber]
      symm
      apply Finset.sum_eq_zero
      intro child _
      apply kernel_other
      · intro equal
        exact same ((congrArg g equal).trans (projects child))
      · change f (g z) = f (g (children child))
        simpa only [projects] using same_fiber
