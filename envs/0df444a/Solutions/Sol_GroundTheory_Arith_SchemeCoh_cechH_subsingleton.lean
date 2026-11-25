-- Prove2me | solution 1 for GroundTheory.Arith.SchemeCoh.cechH_subsingleton
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T01:05:20.492252+00:00
-- url     : https://prove2.me/submissions/7903b3a3-0304-490f-9357-9c43c95a3593

import Mathlib
import Definitions.Def_GroundTheory_ArithmeticGeometry_SchemeCohomology_CechLeray
import Definitions.Def_GroundTheory_ArithmeticGeometry_SchemeCohomology_CechNaturality_Chains
import Definitions.Def_GroundTheory_ArithmeticGeometry_SchemeCohomology_CechNaturality_Ordered
import Theorems.Thm_GroundTheory_Arith_SchemeCoh_isEmpty_strictMono

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
variable {X : TopCat.{u}} {ι : Type w} (P : (Opens X)ᵒᵖ ⥤ AddCommGrpCat.{u}) (U : ι → Opens X)
namespace GroundTheory.Arith.SchemeCoh
theorem _root_.solution [Finite ι] {n : ℕ} (hn : Nat.card ι ≤ n) :
    Subsingleton (cechH P U n) := by
  let : LinearOrder ι := LinearOrder.lift' (Finite.equivFin ι) (Finite.equivFin ι).injective
  have := isEmpty_strictMono (ι := ι) hn
  have : Subsingleton (ocechH P U n) := ⟨fun a b => by
    induction a using QuotientAddGroup.induction_on with
    | H a =>
      induction b using QuotientAddGroup.induction_on with
      | H b =>
        congr 1
        exact Subtype.ext (Subsingleton.elim _ _)⟩
  exact (cechHOrderedEquiv P U n).injective.subsingleton
end GroundTheory.Arith.SchemeCoh
