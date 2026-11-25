-- Prove2me | solution 1 for GroundTheory.Automorphic.baseTrace_conjBase
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T00:02:16.683164+00:00
-- url     : https://prove2.me/submissions/fa01233e-dc45-425e-80cf-10010f3ecc96

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_AdelicUnitaryGroups_Anisotropic
import Definitions.Def_GroundTheory_AutomorphicForms_DefiniteClassNumber_HermTraceSelfOfHermValue
import Theorems.Thm_GroundTheory_Automorphic_baseTrace_tmul
import Theorems.Thm_GroundTheory_Automorphic_conj_apply
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
variable (K E) (R : Type*) [CommRing R] [Algebra K R]
variable {K E R}
namespace GroundTheory.Automorphic
theorem _root_.solution (z : R ⊗[K] E) : baseTrace K E R (conjBase K E R z) = baseTrace K E R z := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul r e =>
    rw [conjBase_tmul, baseTrace_tmul, baseTrace_tmul, conj_apply, map_sub,
      trace_algebraMap_quadratic]
    congr 2
    ring
  | add x y hx hy => rw [map_add, map_add, map_add, hx, hy]
end GroundTheory.Automorphic
