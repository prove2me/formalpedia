-- Prove2me | solution 1 for Monodromy.Logarithm.transport_translation
-- status  : ACCEPTED   (prove)
-- author  : @nonlocally
-- created : 2026-11-05T19:36:26.040214+00:00
-- url     : https://prove2.me/submissions/d0075c2d-66b8-48fd-978e-6f8ba24fd559

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

@[expose] public section

open Monodromy
open Monodromy.Logarithm
open unitInterval

private theorem transport_naturality_aux
    {E E' X : Type*} [TopologicalSpace E] [TopologicalSpace E'] [TopologicalSpace X]
    {p : E → X} {q : E' → X}
    (cov : IsCoveringMap p) (cov' : IsCoveringMap q)
    (h : C(E, E')) (square : q ∘ h = p) {x y : X}
    (γ : Path x y) (e : Transport.Fiber p x) :
    Transport.transport cov' γ (Transport.mapFiber h square e) =
      Transport.mapFiber h square (Transport.transport cov γ e) := by
  let start : γ 0 = p (e : E) := γ.source.trans e.2.symm
  let Γ : C(I, E) := cov.liftPath γ e start
  have projects : p ∘ Γ = γ := cov.liftPath_lifts γ e start
  have starts : Γ 0 = (e : E) := cov.liftPath_zero γ e start
  have endpoint : Γ 1 = (Transport.transport cov γ e : E) := by
    exact (cov.coe_monodromy_mk γ e).symm
  let Γ' : C(I, E') := h.comp Γ
  have projects' : q ∘ Γ' = γ := by
    funext t
    change q (h (Γ t)) = γ t
    exact (congrFun square (Γ t)).trans (congrFun projects t)
  have starts' : Γ' 0 = (Transport.mapFiber h square e : E') := by
    change h (Γ 0) = h e
    rw [starts]
  apply Subtype.ext
  calc
    (Transport.transport cov' γ (Transport.mapFiber h square e) : E') = Γ' 1 :=
      cov'.monodromy_eq_apply_one projects' starts'
    _ = h (Transport.transport cov γ e) := by
      change h (Γ 1) = h (Transport.transport cov γ e)
      rw [endpoint]
    _ = (Transport.mapFiber h square (Transport.transport cov γ e) : E') := rfl

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
  have natural := transport_naturality_aux
    Circle.isCoveringMap_exp Circle.isCoveringMap_exp deck square γ (sheet 0)
  rw [mapped, zero_add] at natural
  have endpoint : sheet (integers.symm
      (Transport.transport Circle.isCoveringMap_exp γ (sheet 0))) =
      Transport.transport Circle.isCoveringMap_exp γ (sheet 0) :=
    integers.apply_symm_apply _
  rw [← endpoint, mapped] at natural
  simpa [add_comm] using natural
