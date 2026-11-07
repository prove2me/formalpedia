-- Prove2me | solution 1 for Monodromy.Choice.dispatch_comp
-- status  : ACCEPTED   (prove)
-- author  : @Xiaoyang Liu
-- created : 2026-11-06T14:56:02.467576+00:00
-- url     : https://prove2.me/submissions/42be565a-45bc-4290-92cd-6ffa68e388ab

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


-- Inline helper skeleton from Monodromy.Choice.


/-!
# Selection and covering symmetry

A selective loop fixes one branch and moves another. Transport naturality
gives a precise structural obstruction: transitive commuting symmetries.
-/

@[expose] public section

namespace Monodromy.Choice

universe u v

open scoped Topology Classical





variable {E : Type u} {X : Type v} [TopologicalSpace E] [TopologicalSpace X]
variable {projection : E → X} {base : X}























end Monodromy.Choice

namespace Monodromy.Choice



end Monodromy.Choice

namespace Monodromy.Choice

theorem dslope_comp {f g : ℂ → ℂ} {r : ℂ}
    (outer : DifferentiableAt ℂ f (g r)) (inner : DifferentiableAt ℂ g r) (w : ℂ) :
    dslope (f ∘ g) r w = dslope f (g r) (g w) * dslope g r w := by
  by_cases same : w = r
  · subst w
    simpa only [dslope_same] using deriv_comp r outer inner
  · have inner_difference : (w - r) * dslope g r w = g w - g r := by
      simpa only [smul_eq_mul] using sub_smul_dslope g r w
    have outer_difference :
        (g w - g r) * dslope f (g r) (g w) = f (g w) - f (g r) := by
      simpa only [smul_eq_mul] using sub_smul_dslope f (g r) (g w)
    apply mul_left_cancel₀ (sub_ne_zero.mpr same)
    calc
      (w - r) * dslope (f ∘ g) r w = f (g w) - f (g r) := by
        simpa only [smul_eq_mul, Function.comp_apply] using sub_smul_dslope (f ∘ g) r w
      _ = (g w - g r) * dslope f (g r) (g w) := outer_difference.symm
      _ = (w - r) * (dslope f (g r) (g w) * dslope g r w) := by
        rw [← inner_difference]
        ring

/-- Outer and inner branch selectors multiply along a composite defining equation. -/
theorem kernel_comp {f g : ℂ → ℂ} {r : ℂ}
    (outer : DifferentiableAt ℂ f (g r)) (inner : DifferentiableAt ℂ g r) (w : ℂ) :
    kernel (f ∘ g) r w = kernel f (g r) (g w) * kernel g r w := by
  unfold kernel
  rw [dslope_comp outer inner, deriv_comp r outer inner]
  exact (div_mul_div_comm _ _ _ _).symm











end Monodromy.Choice

namespace Monodromy.Choice



end Monodromy.Choice

namespace Monodromy.Choice



end Monodromy.Choice

end


-- Original target, hoisted to top-level theorem solution.
open Monodromy
open Monodromy.Choice
theorem solution {ι κ : Type*} [Fintype ι] [Fintype κ]
    {f g : ℂ → ℂ} (outerRoots : ι → ℂ) (children values : ι → κ → ℂ)
    (projects : ∀ i j, g (children i j) = outerRoots i)
    (outer : ∀ i, DifferentiableAt ℂ f (outerRoots i))
    (inner : ∀ i j, DifferentiableAt ℂ g (children i j)) (w : ℂ) :
    dispatch (f ∘ g) (fun index : ι × κ => children index.1 index.2)
      (fun index : ι × κ => values index.1 index.2) w =
      ∑ i, kernel f (outerRoots i) (g w) * dispatch g (children i) (values i) w := by
  classical
  unfold dispatch
  rw [Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro i _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  have differentiable : DifferentiableAt ℂ f (g (children i j)) := by
    rw [projects]
    exact outer i
  rw [kernel_comp differentiable (inner i j), projects]
  ring
