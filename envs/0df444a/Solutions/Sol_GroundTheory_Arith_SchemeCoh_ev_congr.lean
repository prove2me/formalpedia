-- Prove2me | solution 1 for GroundTheory.Arith.SchemeCoh.ev_congr
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T23:47:08.689618+00:00
-- url     : https://prove2.me/submissions/acd53f20-76ef-4315-aa2c-9f6e0e12b156

import Mathlib
import Definitions.Def_GroundTheory_ArithmeticGeometry_SchemeCohomology_ConsCompSuccAboveZero

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Arith GroundTheory.Arith.SchemeCoh
open CategoryTheory Opposite TopologicalSpace
universe w u v
variable {X : TopCat.{u}} {ι : Type w}
variable (P : (Opens X)ᵒᵖ ⥤ AddCommGrpCat.{u}) (U : ι → Opens X)
variable (A : X → AddCommGrpCat.{u})
variable {U}
attribute [local semireducible] inter

namespace GroundTheory.Arith.SchemeCoh
theorem _root_.solution {n : ℕ} (σ : Cochain (discPresheaf A) U n) {j₁ j₂ : Fin (n + 1) → ι}
    (h : j₁ = j₂) (x : X) (h₁ : x ∈ inter U j₁) (h₂ : x ∈ inter U j₂) :
    ev A x h₁ (σ j₁) = ev A x h₂ (σ j₂) := by
  subst h
  rfl
end GroundTheory.Arith.SchemeCoh
