-- Prove2me | solution 1 for GroundTheory.Arith.SchemeCoh.CechOrdered.exists_d_eq_sub_altProj
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T03:48:13.986246+00:00
-- url     : https://prove2.me/submissions/f31b08a8-f773-498e-9d39-eeca48956112

import Mathlib
import Definitions.Def_GroundTheory_ArithmeticGeometry_SchemeCohomology_CechLeray
import Definitions.Def_GroundTheory_ArithmeticGeometry_SchemeCohomology_CechOrdered
import Theorems.Thm_GroundTheory_Arith_SchemeCoh_CechOrdered_d_homotopy_add

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
theorem _root_.solution (q : ℕ) (σ : Cochain P U (q + 1)) (hσ : d P U (q + 1) σ = 0) :
    ∃ τ, d P U q τ = σ - altProj P U (q + 1) σ :=
  ⟨homotopy P U q σ, by rw [← d_homotopy_add, hσ, map_zero, add_zero]⟩
end GroundTheory.Arith.SchemeCoh.CechOrdered
