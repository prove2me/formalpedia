-- Prove2me | solution 1 for NashWilliams.reach_reachable_iff
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T18:16:21.084796+00:00
-- url     : https://prove2.me/submissions/53f02565-1ed3-4834-8e65-a7e6bc03ae94

module
public import Mathlib
public import Definitions.Def_TreePackingLib_NashWilliamsAux
public import Theorems.Thm_NashWilliams_step_reachable_iff

set_option autoImplicit true
@[expose] public section
public section
open Finset Fintype SimpleGraph Function
open NashWilliams
variable {V : Type*}
variable {G : SimpleGraph V} {k : ℕ}
variable [Finite V] {F₀ : Fin k → SimpleGraph V} (hF₀ : Valid G F₀)
  (hmax : ∀ F : Fin k → SimpleGraph V, Valid G F → total F ≤ total F₀)
include hF₀ hmax
namespace NashWilliams
theorem _root_.solution {F : Fin k → SimpleGraph V}
    (hF : Relation.ReflTransGen (Step G) F₀ F) (j : Fin k) (a b : V) :
    (F j ⊓ exchGraph G F₀).Reachable a b ↔ (F₀ j ⊓ exchGraph G F₀).Reachable a b := by
  induction hF with
  | refl => rfl
  | tail h hstep ih => exact (step_reachable_iff hF₀ hmax h hstep j a b).symm.trans ih
end NashWilliams
