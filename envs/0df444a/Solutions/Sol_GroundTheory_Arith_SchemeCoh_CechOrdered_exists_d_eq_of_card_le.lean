-- Prove2me | solution 1 for GroundTheory.Arith.SchemeCoh.CechOrdered.exists_d_eq_of_card_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T04:24:26.869481+00:00
-- url     : https://prove2.me/submissions/91305242-52db-4d6b-9b82-6ab72dd15cab

import Mathlib
import Definitions.Def_GroundTheory_ArithmeticGeometry_SchemeCohomology_CechLeray
import Definitions.Def_GroundTheory_ArithmeticGeometry_SchemeCohomology_CechOrdered
import Theorems.Thm_GroundTheory_Arith_SchemeCoh_CechOrdered_altProj_eq_zero
import Theorems.Thm_GroundTheory_Arith_SchemeCoh_CechOrdered_exists_d_eq_sub_altProj

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
theorem _root_.solution [Fintype ι] (q : ℕ) (hq : Fintype.card ι ≤ q + 1)
    (σ : Cochain P U (q + 1)) (hσ : d P U (q + 1) σ = 0) : ∃ τ, d P U q τ = σ := by
  obtain ⟨τ, hτ⟩ := exists_d_eq_sub_altProj q σ hσ
  exact ⟨τ, by rw [hτ, altProj_eq_zero hq, sub_zero]⟩
end GroundTheory.Arith.SchemeCoh.CechOrdered
