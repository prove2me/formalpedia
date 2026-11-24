-- Prove2me | solution 2 for GroundTheory.Arith.SchemeCoh.res_congr
-- status  : ACCEPTED   (prove)
-- author  : @grencez
-- created : 2026-11-24T00:44:56.433952+00:00
-- url     : https://prove2.me/submissions/7f24f632-339b-4d64-8ce9-d78422d6d5b9

import Mathlib
import Definitions.Def_GroundTheory_ArithmeticGeometry_SchemeCohomology_ConsCompSuccAboveZero
import Definitions.Def_GroundTheory_ArithmeticGeometry_SchemeCohomology_InjectiveCech
import Definitions.Def_GroundTheory_ArithmeticGeometry_SchemeCohomology_Cartan
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
open CategoryTheory Opposite TopologicalSpace Limits
universe w u
variable {X : TopCat.{u}}
variable {ι : Type w} (P : (Opens X)ᵒᵖ ⥤ AddCommGrpCat.{u}) (U : ι → Opens X)


theorem solution {n : ℕ} (σ : Cochain P U n) {j₁ j₂ : Fin (n + 1) → ι} (h : j₁ = j₂)
    {V : Opens X} (h₁ : V ≤ inter U j₁) (h₂ : V ≤ inter U j₂) :
    res P h₁ (σ j₁) = res P h₂ (σ j₂) := by
  subst j₂; rfl
