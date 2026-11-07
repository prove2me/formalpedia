-- Prove2me | solution 2 for Monodromy.NestedContinuation.execute_trans
-- status  : ACCEPTED   (prove)
-- author  : @Xiaoyang Liu
-- created : 2026-11-06T15:01:20.500816+00:00
-- url     : https://prove2.me/submissions/aa0005f6-4067-4b5a-9639-ac6d1575b0c8

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



theorem sequentialPath_projects (first second : Path base base)
    (first_avoids : ∀ t, first t ≠ (⟨1, one_ne_zero⟩ : Punctured))
    (second_avoids : ∀ t, second t ≠ (⟨1, one_ne_zero⟩ : Punctured)) (state : Memory) (t : I) :
    expCover (Complex.exp (sequentialPath first second first_avoids second_avoids state t)) =
      (first.trans second) t := by
  unfold sequentialPath
  simp only [Path.trans_apply]
  split_ifs
  · exact executionPath_projects first first_avoids state _
  · exact executionPath_projects second second_avoids (execute first first_avoids state) _









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
theorem solution (first second : Path base base)
    (first_avoids : ∀ t, first t ≠ (⟨1, one_ne_zero⟩ : Punctured))
    (second_avoids : ∀ t, second t ≠ (⟨1, one_ne_zero⟩ : Punctured)) (state : Memory) :
    execute (first.trans second) (avoids_trans first second first_avoids second_avoids) state =
      execute second second_avoids (execute first first_avoids state) := by
  apply Subtype.ext
  let joined := sequentialPath first second first_avoids second_avoids state
  have same : secondRaw (first.trans second)
      (avoids_trans first second first_avoids second_avoids) state = joined.toContinuousMap :=
    nested_curve_unique _ _
      (fun t => (secondRaw_projects (first.trans second)
        (avoids_trans first second first_avoids second_avoids) state t).trans
          (sequentialPath_projects first second first_avoids second_avoids state t).symm)
      ((secondRaw_start (first.trans second)
        (avoids_trans first second first_avoids second_avoids) state).trans joined.source.symm)
  exact (congrArg (fun curve : C(I, ℂ) => curve 1) same).trans joined.target
