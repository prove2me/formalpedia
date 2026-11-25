-- Prove2me | solution 1 for NashWilliams.reach_valid
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T17:57:55.581477+00:00
-- url     : https://prove2.me/submissions/3df23950-bc24-4a40-8c0c-9999f2f158f9

module
public import Mathlib
public import Definitions.Def_TreePackingLib_NashWilliamsAux
public import Theorems.Thm_NashWilliams_Step_valid
public import Theorems.Thm_NashWilliams_Step_total_eq

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
omit hmax
namespace NashWilliams
theorem _root_.solution {F : Fin k → SimpleGraph V} (hF : Relation.ReflTransGen (Step G) F₀ F) :
    Valid G F ∧ total F = total F₀ := by
  induction hF with
  | refl => exact ⟨hF₀, rfl⟩
  | tail _ hstep ih => exact ⟨hstep.valid ih.1, hstep.total_eq.trans ih.2⟩
end NashWilliams
