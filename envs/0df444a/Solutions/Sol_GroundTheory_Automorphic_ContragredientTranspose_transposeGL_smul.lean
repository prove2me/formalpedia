-- Prove2me | solution 1 for GroundTheory.Automorphic.ContragredientTranspose.transposeGL_smul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T01:50:33.546363+00:00
-- url     : https://prove2.me/submissions/2e6155ea-9bc1-490a-859a-014806d1ec74

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_WhittakerOrbit
import Definitions.Def_GroundTheory_AutomorphicForms_WhittakerCriterion
import Definitions.Def_GroundTheory_AutomorphicForms_WhittakerGroups
import Definitions.Def_GroundTheory_AutomorphicForms_WhittakerDistribution
import Definitions.Def_GroundTheory_AutomorphicForms_ContragredientTranspose_MatrixSimilarity
import Definitions.Def_GroundTheory_AutomorphicForms_ContragredientTranspose_GelfandKazhdan
import Theorems.Thm_GroundTheory_Automorphic_ContragredientTranspose_thetaT_apply

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GroundTheory GroundTheory.Automorphic GroundTheory.Automorphic.ContragredientTranspose
open Set Filter Topology MulAction Matrix GroundTheory.Automorphic.Whittaker
variable {F : Type*} [Field F] {n : ℕ}
namespace GroundTheory.Automorphic.ContragredientTranspose
theorem _root_.solution (h : ConjAct (GL (Fin n) F)) (x : GL (Fin n) F) :
    transposeGL (h • x) = ConjAct.toConjAct (thetaT (ConjAct.ofConjAct h)) • transposeGL x := by
  rw [ConjAct.smul_def, ConjAct.toConjAct_smul, thetaT_apply, transposeGL_mul, transposeGL_mul,
    transposeGL_inv, inv_inv, mul_assoc]
end GroundTheory.Automorphic.ContragredientTranspose
