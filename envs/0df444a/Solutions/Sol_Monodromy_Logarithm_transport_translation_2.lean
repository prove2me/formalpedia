-- Prove2me | solution 2 for Monodromy.Logarithm.transport_translation
-- status  : ACCEPTED   (prove)
-- author  : @Xiaoyang Liu
-- created : 2026-11-06T15:01:17.382779+00:00
-- url     : https://prove2.me/submissions/64aa7578-718d-46da-a2af-81624002d52b

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
public import Theorems.Thm_Monodromy_Transport_transport_naturality

@[expose] public section


-- Original target, hoisted to top-level theorem solution.
open Monodromy
open Monodromy.Logarithm
open unitInterval
theorem solution (γ : Path (1 : Circle) 1) (k : ℤ) :
    Transport.transport Circle.isCoveringMap_exp γ (sheet k) =
      sheet (k + integers.symm
        (Transport.transport Circle.isCoveringMap_exp γ (sheet 0))) := by
  let deck : C(ℝ, ℝ) :=
    ⟨fun x => x + (k : ℝ) * (2 * Real.pi), continuous_id.add continuous_const⟩
  have square : Circle.exp ∘ deck = Circle.exp := by
    funext x
    simp [deck, Circle.exp_add]
  have mapped (j : ℤ) : Transport.mapFiber deck square (sheet j) = sheet (j + k) := by
    apply Subtype.ext
    simp [Transport.mapFiber, deck, sheet, add_mul]
  have natural := Transport.transport_naturality
    Circle.isCoveringMap_exp Circle.isCoveringMap_exp deck square γ (sheet 0)
  rw [mapped, zero_add] at natural
  have endpoint : sheet (integers.symm
      (Transport.transport Circle.isCoveringMap_exp γ (sheet 0))) =
      Transport.transport Circle.isCoveringMap_exp γ (sheet 0) :=
    integers.apply_symm_apply _
  rw [← endpoint, mapped] at natural
  simpa [add_comm] using natural
