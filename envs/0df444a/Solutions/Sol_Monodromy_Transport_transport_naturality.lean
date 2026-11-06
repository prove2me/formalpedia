-- Prove2me | solution 1 for Monodromy.Transport.transport_naturality
-- status  : ACCEPTED   (prove)
-- author  : @nonlocally
-- created : 2026-11-05T22:04:44.471202+00:00
-- url     : https://prove2.me/submissions/ea5715ba-ceaf-4681-9c08-4d094a76f345

module
public import Definitions.Def_Monodromy_Covering
public import Mathlib.Logic.Function.Conjugate
public import Mathlib.Tactic.FunProp
public import Mathlib.Topology.Homotopy.Lifting

@[expose] public section

open Monodromy
open Monodromy.Transport
open unitInterval
universe u v w
variable {E : Type u} {X : Type v}
variable [TopologicalSpace E] [TopologicalSpace X]
variable {p : E → X}
variable {E' : Type w} [TopologicalSpace E'] {q : E' → X}

theorem solution (cov : IsCoveringMap p) (cov' : IsCoveringMap q)
    (h : C(E, E')) (square : q ∘ h = p) {x y : X}
    (γ : Path x y) (e : Fiber p x) :
    transport cov' γ (mapFiber h square e) =
      mapFiber h square (transport cov γ e) := by
  let Γ : C(I, E) := cov.liftPath γ e (γ.source.trans e.2.symm)
  have hΓ : p ∘ Γ = γ := cov.liftPath_lifts γ e (γ.source.trans e.2.symm)
  have hΓ0 : Γ 0 = e := cov.liftPath_zero γ e (γ.source.trans e.2.symm)
  apply Subtype.ext
  change (cov'.monodromy (Path.Homotopic.Quotient.mk γ) (mapFiber h square e) : E') =
    h (cov.monodromy (Path.Homotopic.Quotient.mk γ) e)
  calc
    (cov'.monodromy (Path.Homotopic.Quotient.mk γ) (mapFiber h square e) : E') =
        h (Γ 1) := by
      apply cov'.monodromy_eq_apply_one (Γ := h.comp Γ)
      · ext t
        exact (congrFun square (Γ t)).trans (congrFun hΓ t)
      · exact congrArg h hΓ0
    _ = h (cov.monodromy (Path.Homotopic.Quotient.mk γ) e) :=
      congrArg h (cov.monodromy_eq_apply_one hΓ hΓ0).symm
