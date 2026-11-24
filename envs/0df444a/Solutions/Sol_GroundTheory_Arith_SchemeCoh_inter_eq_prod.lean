-- Prove2me | solution 1 for GroundTheory.Arith.SchemeCoh.inter_eq_prod
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T00:43:48.814723+00:00
-- url     : https://prove2.me/submissions/e4b19656-b371-4654-aee9-d5921c5851c6

import Mathlib
import Definitions.Def_GroundTheory_ArithmeticGeometry_SchemeCohomology_ConsCompSuccAboveZero
import Definitions.Def_GroundTheory_ArithmeticGeometry_SchemeCohomology_Cartan
import Definitions.Def_GroundTheory_ArithmeticGeometry_SchemeCohomology_LocalizingCech
import Theorems.Thm_GroundTheory_Arith_SchemeCoh_inter_le
import Theorems.Thm_GroundTheory_Arith_SchemeCoh_inter_succ


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
universe u
variable {X : TopCat.{u}} {P : (Opens X)ᵒᵖ ⥤ AddCommGrpCat.{u}} {R : Type u} [CommRing R]
variable {D : R → Opens X} (A : LocalizingAction P D)
variable {ι : Type u} (U : ι → Opens X)
variable (h : ι → R)
include A
namespace GroundTheory.Arith.SchemeCoh
theorem _root_.solution : ∀ {m : ℕ} (I : Fin (m + 1) → ι), inter (D ∘ h) I = D (∏ a, h (I a))
  | 0, I => by
    rw [Fin.prod_univ_one]
    apply le_antisymm (inter_le _ I 0)
    intro x hx
    rw [mem_inter_iff]
    intro a
    rwa [Fin.fin_one_eq_zero a]
  | m + 1, I => by
    rw [inter_succ, solution (I ∘ Fin.succ), Fin.prod_univ_succ (fun a => h (I a)), A.D_mul]
    rfl
end GroundTheory.Arith.SchemeCoh
