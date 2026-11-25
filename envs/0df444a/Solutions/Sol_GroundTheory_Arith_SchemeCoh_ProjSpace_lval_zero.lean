-- Prove2me | solution 1 for GroundTheory.Arith.SchemeCoh.ProjSpace.lval_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T00:34:18.734796+00:00
-- url     : https://prove2.me/submissions/1063174b-5b08-4298-be90-00d8e5b20d69

import Mathlib
import Definitions.Def_GroundTheory_ArithmeticGeometry_SchemeCohomology_ProjLaurent
import Definitions.Def_GroundTheory_ArithmeticGeometry_SchemeCohomology_CechSeparated
import Definitions.Def_GroundTheory_ArithmeticGeometry_SchemeCohomology_ProjCechModel
import Theorems.Thm_GroundTheory_Arith_SchemeCoh_ProjSpace_awayDegEquiv_apply
import Theorems.Thm_GroundTheory_Arith_SchemeCoh_ProjSpace_lval_add
import Theorems.Thm_GroundTheory_Arith_SchemeCoh_ProjTwist_val_add
import Theorems.Thm_GroundTheory_Arith_SchemeCoh_ProjTwist_val_mkSection
import Theorems.Thm_GroundTheory_Arith_SchemeCoh_ProjTwist_val_neg
import Theorems.Thm_GroundTheory_Arith_SchemeCoh_ProjTwist_val_sub
import Theorems.Thm_GroundTheory_Arith_SchemeCoh_ProjTwist_val_zero
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GroundTheory.Arith.SchemeCoh.ProjTwist.val_add
attribute [local simp] GroundTheory.Arith.SchemeCoh.ProjTwist.val_mkSection
attribute [local simp] GroundTheory.Arith.SchemeCoh.ProjTwist.val_neg
attribute [local simp] GroundTheory.Arith.SchemeCoh.ProjTwist.val_sub
attribute [local simp] GroundTheory.Arith.SchemeCoh.ProjTwist.val_zero


attribute [local simp] GroundTheory.Arith.SchemeCoh.ProjSpace.awayDegEquiv_apply
attribute [local simp] GroundTheory.Arith.SchemeCoh.ProjSpace.lval_add

set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Arith GroundTheory.Arith.SchemeCoh
open AlgebraicGeometry TopologicalSpace CategoryTheory Opposite MvPolynomial
universe u
attribute [local instance] MvPolynomial.gradedAlgebra
noncomputable section
open GroundTheory.Arith.SchemeCoh.ProjSpace
variable {A : Type u} [CommRing A] {n : ℕ}
namespace GroundTheory.Arith.SchemeCoh.ProjSpace
theorem _root_.solution {k : ℤ} {p : ℕ} (i) :
    lval (0 : Cochain (twistAb A n k) (cover A n) p) i = 0 := by
  simp [lval]
end GroundTheory.Arith.SchemeCoh.ProjSpace
