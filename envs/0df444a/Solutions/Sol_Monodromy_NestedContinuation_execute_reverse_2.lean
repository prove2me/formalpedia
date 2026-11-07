-- Prove2me | solution 2 for Monodromy.NestedContinuation.execute_reverse
-- status  : ACCEPTED   (prove)
-- author  : @Xiaoyang Liu
-- created : 2026-11-06T15:01:19.013709+00:00
-- url     : https://prove2.me/submissions/f1525c0a-4688-4ec6-b5dc-3a08760104dd

-- Generated mechanically from the frozen source; no own-target import.
module
public import Definitions.Def_Monodromy_Logarithm
public import Lean.Elab.Tactic.Omega
public import Mathlib.Analysis.Analytic.Constructions
public import Mathlib.Analysis.Complex.CoveringMap
public import Mathlib.Analysis.Real.Pi.Bounds
public import Mathlib.Analysis.SpecialFunctions.Complex.Circle
public import Mathlib.Logic.Function.Conjugate
public import Mathlib.Tactic.FunProp
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Ring
public import Mathlib.Topology.Homotopy.Lifting
public import Theorems.Thm_Monodromy_NestedContinuation_nested_curve_unique

@[expose] public section


-- Inline helper skeleton from Monodromy.Logarithm.


/-!
# The branches of the logarithm

Restricting the exponential to imaginary arguments gives the circle covering.
Its fiber over one retains an integer. A loop transports every initial
branch by addition, proved from its actual continuous lift. Nested complex
exponentials supply a conditional upper write: the actual lower lift winds
around the upper logarithm's omitted point only on the zero branch.
-/

@[expose] public section

namespace Monodromy.Logarithm

open unitInterval















end Monodromy.Logarithm


/-! Two successive logarithmic lifts and their fixed-loop actions. -/

noncomputable section

namespace Monodromy.NestedContinuation

open unitInterval

































































































































end Monodromy.NestedContinuation


namespace Monodromy.NestedContinuation










end Monodromy.NestedContinuation

namespace Monodromy.NestedContinuation

open unitInterval









theorem executionPath_projects (path : Path base base)
    (avoids : ∀ t, path t ≠ (⟨1, one_ne_zero⟩ : Punctured)) (state : Memory) (t : I) :
    expCover (Complex.exp (executionPath path avoids state t)) = path t :=
  secondRaw_projects path avoids state t













end Monodromy.NestedContinuation

namespace Monodromy.NestedContinuation









end Monodromy.NestedContinuation


namespace Monodromy.NestedContinuation





end Monodromy.NestedContinuation


namespace Monodromy.NestedContinuation




end Monodromy.NestedContinuation


namespace Monodromy.NestedRestricted

open unitInterval

noncomputable section






















end

end Monodromy.NestedRestricted


namespace Monodromy.NestedContinuation

open unitInterval











end Monodromy.NestedContinuation

end

end


-- Original target, hoisted to top-level theorem solution.
open Monodromy
open Monodromy.NestedContinuation
open unitInterval
theorem solution (path : Path base base)
    (avoids : ∀ t, path t ≠ (⟨1, one_ne_zero⟩ : Punctured)) (state : Memory) :
    execute path.symm (avoids_symm path avoids) (execute path avoids state) = state := by
  apply Subtype.ext
  let backwards := (executionPath path avoids state).symm
  have projects : ∀ t, expCover (Complex.exp (backwards t)) = path.symm t := by
    intro t
    exact executionPath_projects path avoids state (σ t)
  have same : secondRaw path.symm (avoids_symm path avoids) (execute path avoids state) =
      backwards.toContinuousMap :=
    nested_curve_unique _ _
      (fun t => (secondRaw_projects path.symm (avoids_symm path avoids)
        (execute path avoids state) t).trans (projects t).symm)
      ((secondRaw_start path.symm (avoids_symm path avoids)
        (execute path avoids state)).trans backwards.source.symm)
  exact (congrArg (fun curve : C(I, ℂ) => curve 1) same).trans backwards.target
