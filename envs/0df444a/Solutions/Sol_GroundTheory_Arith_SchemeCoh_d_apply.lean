-- Prove2me | solution 1 for GroundTheory.Arith.SchemeCoh.d_apply
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T00:34:50.644966+00:00
-- url     : https://prove2.me/submissions/d39eb553-8b47-44a4-846f-cd3e8683399b

import Mathlib
import Definitions.Def_GroundTheory_ArithmeticGeometry_SchemeCohomology_ConsCompSuccAboveZero
import Theorems.Thm_GroundTheory_Arith_SchemeCoh_hom_finset_sum_apply

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
attribute [local semireducible] inter

namespace GroundTheory.Arith.SchemeCoh
theorem _root_.solution (n : ℕ) (σ : Cochain P U n) (i : Fin (n + 2) → ι) :
    d P U n σ i = ∑ k : Fin (n + 2), ((-1 : ℤ) ^ (k : ℕ)) •
      res P (inter_le_comp U i k.succAbove) (σ (i ∘ k.succAbove)) := by
  have h := hom_finset_sum_apply Finset.univ
    (fun k : Fin (n + 2) => ((-1 : ℤ) ^ (k : ℕ)) • (cechCosimplicial P U).δ k) σ
  refine (congrFun h i).trans ((Finset.sum_apply i _ _).trans ?_)
  refine Finset.sum_congr rfl fun k _ => ?_
  rfl
end GroundTheory.Arith.SchemeCoh
