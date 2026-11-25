-- Prove2me | solution 1 for GroundTheory.Automorphic.conjBase_conjBase
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T00:02:58.525105+00:00
-- url     : https://prove2.me/submissions/2ed18392-113a-4dc7-8e61-7bcd3c9b89fa

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_AdelicUnitaryGroups_Anisotropic
import Definitions.Def_GroundTheory_AutomorphicForms_DefiniteClassNumber_HermTraceSelfOfHermValue
import Theorems.Thm_GroundTheory_Automorphic_conj_conj
import Theorems.Thm_GroundTheory_Automorphic_matrixCoords_zero
import Theorems.Thm_GroundTheory_Automorphic_unitaryPiEquiv_apply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GroundTheory.Automorphic.conj_conj
attribute [local simp] GroundTheory.Automorphic.matrixCoords_zero
attribute [local simp] GroundTheory.Automorphic.unitaryPiEquiv_apply



set_option autoImplicit false
noncomputable section
open GroundTheory GroundTheory.Automorphic
open Module Matrix TensorProduct
variable {K E : Type*} [Field K] [CommRing E] [Algebra K E] [Algebra.IsQuadraticExtension K E]
variable {ι : Type*} [Fintype ι] (H : Matrix ι ι E)
variable (K) (R : Type*) [CommRing R] [Algebra K R]
variable {K H R}
namespace GroundTheory.Automorphic
theorem _root_.solution (z : R ⊗[K] E) : conjBase K E R (conjBase K E R z) = z := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul r e => rw [conjBase_tmul, conjBase_tmul, conj_conj]
  | add x y hx hy => rw [map_add, map_add, hx, hy]
end GroundTheory.Automorphic
