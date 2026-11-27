-- Prove2me | solution 1 for GroundTheory.Automorphic.hermValue_smul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-27T04:47:18.156862+00:00
-- url     : https://prove2.me/submissions/a1c8f002-3939-41f2-beac-23d8aac7215f

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_AdelicUnitaryGroups_Topology
import Definitions.Def_GroundTheory_AutomorphicForms_AdelicUnitaryGroups_Anisotropic
import Theorems.Thm_GroundTheory_Automorphic_conjBase_smul
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
set_option linter.unusedSectionVars false
open GroundTheory GroundTheory.Automorphic
open Module Matrix TensorProduct Topology Metric
noncomputable section
variable {K E : Type*} [Field K] [CommRing E] [Algebra K E] [Algebra.IsQuadraticExtension K E]
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable (K) (H : Matrix ι ι E) (R : Type*) [CommRing R] [Algebra K R]
variable {K H R}
namespace GroundTheory.Automorphic
theorem _root_.solution (c : R) (x : ι → R ⊗[K] E) :
    hermValue K H R (c • x) = (c * c) • hermValue K H R x := by
  unfold hermValue
  have : (fun i => conjBase K E R ((c • x) i)) = c • fun i => conjBase K E R (x i) := by
    funext i
    simp only [Pi.smul_apply, conjBase_smul]
  rw [this, Matrix.mulVec_smul, smul_dotProduct, dotProduct_smul, smul_smul]
end GroundTheory.Automorphic
