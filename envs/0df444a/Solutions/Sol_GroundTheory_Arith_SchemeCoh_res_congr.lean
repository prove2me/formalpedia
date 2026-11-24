-- Prove2me | solution 1 for GroundTheory.Arith.SchemeCoh.res_congr
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T00:43:49.779966+00:00
-- url     : https://prove2.me/submissions/68b7df4d-e319-4b4e-a2fb-e05bba6c02d2

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
namespace GroundTheory.Arith.SchemeCoh
theorem _root_.solution {n : ℕ} (σ : Cochain P U n) {j₁ j₂ : Fin (n + 1) → ι} (h : j₁ = j₂)
    {V : Opens X} (h₁ : V ≤ inter U j₁) (h₂ : V ≤ inter U j₂) :
    res P h₁ (σ j₁) = res P h₂ (σ j₂) := by
  subst h
  rfl
end GroundTheory.Arith.SchemeCoh
