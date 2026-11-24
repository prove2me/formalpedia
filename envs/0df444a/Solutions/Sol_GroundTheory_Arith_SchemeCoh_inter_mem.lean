-- Prove2me | solution 1 for GroundTheory.Arith.SchemeCoh.inter_mem
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T23:38:03.007797+00:00
-- url     : https://prove2.me/submissions/1aec6e1c-2b16-476d-a75f-baf879e53bb1

import Mathlib
import Definitions.Def_GroundTheory_ArithmeticGeometry_SchemeCohomology_ConsCompSuccAboveZero
import Definitions.Def_GroundTheory_ArithmeticGeometry_SchemeCohomology_InjectiveCech
import Definitions.Def_GroundTheory_ArithmeticGeometry_SchemeCohomology_Cartan
import Theorems.Thm_GroundTheory_Arith_SchemeCoh_inter_succ
import Theorems.Thm_GroundTheory_Arith_SchemeCoh_inter_le


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
variable (P : (Opens X)ᵒᵖ ⥤ AddCommGrpCat.{u})
  (hP : Presheaf.IsSheaf (Opens.grothendieckTopology X) P)
variable (B : Opens X → Prop)
variable {B}
namespace GroundTheory.Arith.SchemeCoh
theorem _root_.solution (hinf : ∀ V W, B V → B W → B (V ⊓ W)) {ι : Type w} (U : ι → Opens X)
    (hU : ∀ a, B (U a)) {n : ℕ} (i : Fin (n + 1) → ι) : B (inter U i) := by
  induction n with
  | zero =>
    have : inter U i = U (i 0) := le_antisymm (inter_le U i 0) (by
      intro x hx
      rw [mem_inter_iff]
      intro a
      rwa [Fin.fin_one_eq_zero a])
    rw [this]
    exact hU _
  | succ n ih =>
    rw [inter_succ]
    exact hinf _ _ (hU _) (ih _)
end GroundTheory.Arith.SchemeCoh
