-- Prove2me | solution 1 for GroundTheory.Automorphic.baseTrace_tmul
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T08:33:37.061509+00:00
-- url     : https://prove2.me/submissions/87762f86-bb31-4431-96e7-6336c3f75c35

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
variable (K E) (R : Type*) [CommRing R] [Algebra K R]
variable {K E R}
omit [Algebra.IsQuadraticExtension K E]
namespace GroundTheory.Automorphic
theorem _root_.solution (r : R) (e : E) :
    baseTrace K E R (r ⊗ₜ e) = algebraMap K R (Algebra.trace K E e) * r := by
  simp [baseTrace, Algebra.smul_def]
end GroundTheory.Automorphic
