-- Prove2me | solution 1 for GroundTheory.Arith.SchemeCoh.CechOrdered.subsingleton_cechH
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T05:07:37.011706+00:00
-- url     : https://prove2.me/submissions/e906828f-208e-49f6-a628-42c55c9eeae6

import Mathlib
import Definitions.Def_GroundTheory_ArithmeticGeometry_SchemeCohomology_CechLeray
import Definitions.Def_GroundTheory_ArithmeticGeometry_SchemeCohomology_CechOrdered
import Theorems.Thm_GroundTheory_Arith_SchemeCoh_CechOrdered_exists_d_eq_of_card_le

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
universe w u
open GroundTheory.Arith.SchemeCoh.CechOrdered
variable {ι : Type w} [LinearOrder ι] {X : TopCat.{u}} (P : (Opens X)ᵒᵖ ⥤ AddCommGrpCat.{u})
  (U : ι → Opens X)
variable {P U}
namespace GroundTheory.Arith.SchemeCoh.CechOrdered
theorem _root_.solution [Fintype ι] {n : ℕ} (hn : Fintype.card ι ≤ n) (hn0 : 0 < n) :
    Subsingleton (cechH P U n) := by
  obtain ⟨q, rfl⟩ : ∃ q, n = q + 1 := ⟨n - 1, by omega⟩
  refine subsingleton_of_forall_eq 0 fun c => ?_
  obtain ⟨σ, hσ, rfl⟩ := exists_cls c
  rw [cls_eq_zero_iff, coboundaries_succ]
  exact exists_d_eq_of_card_le q hn σ hσ
end GroundTheory.Arith.SchemeCoh.CechOrdered
