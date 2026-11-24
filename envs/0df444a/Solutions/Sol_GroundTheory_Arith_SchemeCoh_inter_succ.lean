-- Prove2me | solution 1 for GroundTheory.Arith.SchemeCoh.inter_succ
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T23:30:05.10659+00:00
-- url     : https://prove2.me/submissions/ba383baa-9993-43f9-bd1f-5ee9ae81421b

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
theorem _root_.solution {n : ℕ} (i : Fin (n + 2) → ι) :
    inter U i = U (i 0) ⊓ inter U (i ∘ Fin.succ) := by
  ext x
  simp only [SetLike.mem_coe, Opens.mem_inf, mem_inter_iff, Fin.forall_fin_succ, Function.comp]
end GroundTheory.Arith.SchemeCoh
