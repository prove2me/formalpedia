-- Prove2me | solution 1 for GroundTheory.Arith.SchemeCoh.CechAcyclic.of_retract
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T00:46:28.847306+00:00
-- url     : https://prove2.me/submissions/cb798fe1-d9fc-4623-be3c-9148de4db591

import Mathlib
import Definitions.Def_GroundTheory_ArithmeticGeometry_SchemeCohomology_ConsCompSuccAboveZero
import Theorems.Thm_GroundTheory_Arith_SchemeCoh_push_d
import Theorems.Thm_GroundTheory_Arith_SchemeCoh_push_comp
import Theorems.Thm_GroundTheory_Arith_SchemeCoh_push_id

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
variable {P}
attribute [local semireducible] inter

namespace GroundTheory.Arith.SchemeCoh
namespace CechAcyclic
theorem _root_.solution {G : (Opens X)ᵒᵖ ⥤ AddCommGrpCat.{u}} (ι' : P ⟶ G) (r : G ⟶ P)
    (hr : ι' ≫ r = 𝟙 P) (hG : CechAcyclic G U) : CechAcyclic P U := by
  intro n σ hσ
  obtain ⟨τ, hτ⟩ := hG n (push U ι' (n + 1) σ) (by rw [← push_d, hσ, map_zero])
  refine ⟨push U r n τ, ?_⟩
  rw [← push_d, hτ, push_comp, hr, push_id]
end CechAcyclic
end GroundTheory.Arith.SchemeCoh
