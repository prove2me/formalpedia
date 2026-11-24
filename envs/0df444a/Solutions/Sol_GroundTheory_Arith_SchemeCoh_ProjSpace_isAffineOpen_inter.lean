-- Prove2me | solution 1 for GroundTheory.Arith.SchemeCoh.ProjSpace.isAffineOpen_inter
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T18:43:55.680011+00:00
-- url     : https://prove2.me/submissions/86bec652-afd3-4411-bcb3-4d107c57d1c5

import Mathlib
import Definitions.Def_GroundTheory_ArithmeticGeometry_SchemeCohomology_ProjTwistAway
import Definitions.Def_GroundTheory_ArithmeticGeometry_SchemeCohomology_ConsCompSuccAboveZero
import Definitions.Def_GroundTheory_ArithmeticGeometry_SchemeCohomology_ProjSpace
import Theorems.Thm_GroundTheory_Arith_SchemeCoh_ProjSpace_xprod_mem
import Theorems.Thm_GroundTheory_Arith_SchemeCoh_ProjSpace_inter_stdOpen

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
open AlgebraicGeometry TopologicalSpace CategoryTheory Opposite MvPolynomial
universe u
attribute [local instance] MvPolynomial.gradedAlgebra
noncomputable section
open ProjSpace
open GroundTheory.Arith.SchemeCoh.ProjSpace
variable {A : Type u} [CommRing A] {n : ℕ}
namespace GroundTheory.Arith.SchemeCoh.ProjSpace
theorem _root_.solution {p : ℕ} (i : Fin (p + 1) → Fin (n + 1)) :
    IsAffineOpen (inter (X := (projectiveSpace A n).toTopCat) (stdOpen A n) i) := by
  rw [inter_stdOpen]
  exact Proj.isAffineOpen_basicOpen (grading A n) (xprod i) (xprod_mem i) (Nat.succ_pos p)
end GroundTheory.Arith.SchemeCoh.ProjSpace
