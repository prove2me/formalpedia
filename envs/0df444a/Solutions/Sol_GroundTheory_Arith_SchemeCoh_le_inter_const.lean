-- Prove2me | solution 1 for GroundTheory.Arith.SchemeCoh.le_inter_const
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T23:30:32.2369+00:00
-- url     : https://prove2.me/submissions/e346f0fa-6ed0-4db6-a555-5f8ae15e08f5

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
theorem _root_.solution {n : ℕ} (a : ι) : U a ≤ inter U (fun _ : Fin n => a) := by
  intro x hx
  rw [mem_inter_iff]
  exact fun _ => hx
end GroundTheory.Arith.SchemeCoh
