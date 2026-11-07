-- Prove2me | solution 2 for Monodromy.Transport.transport_naturality
-- status  : ACCEPTED   (prove)
-- author  : @Xiaoyang Liu
-- created : 2026-11-06T14:59:08.837116+00:00
-- url     : https://prove2.me/submissions/762ed4fd-6063-4766-823c-595b6db43fc9

-- Generated mechanically from the frozen source; no own-target import.
module
public import Definitions.Def_Monodromy_Covering
public import Mathlib.Logic.Function.Conjugate
public import Mathlib.Tactic.FunProp
public import Mathlib.Topology.Homotopy.Lifting

@[expose] public section


-- Inline helper skeleton from Monodromy.Covering.


@[expose] public section

/-!
# Transport from actual continuous covering-space lifts

The state is a point of an actual fiber of `p : E → X`. Transport is the
endpoint of mathlib's continuous path lift, not an independently axiomatized
endpoint function. Composition and homotopy invariance consequently depend on
the covering-space lifting theorems imported above.

The hypothesis `IsCoveringMap p` is explicit. This file does not establish that
a particular polynomial family is a covering, that its fibers are finite, or
that a numerical continuation algorithm computes these ideal lifts.
-/


namespace Monodromy.Transport

open unitInterval

universe u v w

variable {E : Type u} {X : Type v}
variable [TopologicalSpace E] [TopologicalSpace X]
variable {p : E → X}





/-- Transport is realized by a continuous path with the specified initial state. -/
theorem continuous_lift_exists (cov : IsCoveringMap p) {x y : X}
    (γ : Path x y) (e : Fiber p x) :
    ∃ Γ : C(I, E), p ∘ Γ = γ ∧ Γ 0 = (e : E) ∧
      Γ 1 = (transport cov γ e : E) := by
  let start : γ 0 = p (e : E) := γ.source.trans e.2.symm
  refine ⟨cov.liftPath γ e start, cov.liftPath_lifts γ e start,
    cov.liftPath_zero γ e start, ?_⟩
  exact (cov.coe_monodromy_mk γ e).symm



/-- A supplied actual continuous lift has exactly the declared transport endpoint. -/
theorem transport_eq_actual_lift (cov : IsCoveringMap p) {x y : X}
    (γ : Path x y) (e : Fiber p x) (Γ : C(I, E))
    (projects : p ∘ Γ = γ) (starts : Γ 0 = (e : E)) :
    (transport cov γ e : E) = Γ 1 := by
  exact cov.monodromy_eq_apply_one projects starts













section Naturality

variable {E' : Type w} [TopologicalSpace E'] {q : E' → X}













end Naturality

end Monodromy.Transport

/-! Coverings are preserved by continuous pullback and finite product. -/

namespace Monodromy.CoverPullback

variable {E X B : Type*} [TopologicalSpace E] [TopologicalSpace X] [TopologicalSpace B]







end Monodromy.CoverPullback

namespace Monodromy.CoverPullback

variable {E X F Y : Type*}
  [TopologicalSpace E] [TopologicalSpace X] [TopologicalSpace F] [TopologicalSpace Y]



end Monodromy.CoverPullback

namespace Monodromy.CoverPullback

variable {X : Type*} [TopologicalSpace X]



end Monodromy.CoverPullback

end


-- Original target, hoisted to top-level theorem solution.
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
  obtain ⟨Γ, projects, starts, endpoint⟩ := continuous_lift_exists cov γ e
  let Γ' : C(I, E') := h.comp Γ
  have projects' : q ∘ Γ' = γ := by
    funext t
    change q (h (Γ t)) = γ t
    exact (congrFun square (Γ t)).trans (congrFun projects t)
  have starts' : Γ' 0 = (mapFiber h square e : E') := by
    change h (Γ 0) = h e
    rw [starts]
  apply Subtype.ext
  calc
    (transport cov' γ (mapFiber h square e) : E') = Γ' 1 :=
      transport_eq_actual_lift cov' γ (mapFiber h square e) Γ' projects' starts'
    _ = h (transport cov γ e) := by
      change h (Γ 1) = h (transport cov γ e)
      rw [endpoint]
    _ = (mapFiber h square (transport cov γ e) : E') := rfl
