-- Prove2me | solution 1 for GroundTheory.Arith.SchemeCoh.d_zero_apply
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T00:43:48.177856+00:00
-- url     : https://prove2.me/submissions/7c35a355-b175-47a3-9058-73be7eb120f0

import Mathlib
import Definitions.Def_GroundTheory_ArithmeticGeometry_SchemeCohomology_ConsCompSuccAboveZero
import Definitions.Def_GroundTheory_ArithmeticGeometry_SchemeCohomology_InjectiveCech
import Definitions.Def_GroundTheory_ArithmeticGeometry_SchemeCohomology_Cartan
import Theorems.Thm_GroundTheory_Arith_SchemeCoh_d_apply


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
theorem _root_.solution (σ : Cochain P U 0) (i : Fin 2 → ι) :
    d P U 0 σ i = res P (inter_le_comp U i (0 : Fin 2).succAbove) (σ (i ∘ (0 : Fin 2).succAbove)) -
      res P (inter_le_comp U i (1 : Fin 2).succAbove) (σ (i ∘ (1 : Fin 2).succAbove)) := by
  rw [d_apply, Fin.sum_univ_two]
  simp [sub_eq_add_neg]
end GroundTheory.Arith.SchemeCoh
