-- Prove2me | solution 1 for GroundTheory.Automorphic.hermPair_swap
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T00:12:47.88851+00:00
-- url     : https://prove2.me/submissions/56954def-53d8-4697-b033-a5af2798a208

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_AdelicUnitaryGroups_Anisotropic
import Definitions.Def_GroundTheory_AutomorphicForms_DefiniteClassNumber_HermTraceSelfOfHermValue
import Theorems.Thm_GroundTheory_Automorphic_conjBase_conjBase
import Theorems.Thm_GroundTheory_Automorphic_hermTraceBilin_apply
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


attribute [local simp] GroundTheory.Automorphic.hermTraceBilin_apply

set_option autoImplicit false
noncomputable section
open GroundTheory GroundTheory.Automorphic
open Module Matrix TensorProduct
variable {K E : Type*} [Field K] [CommRing E] [Algebra K E] [Algebra.IsQuadraticExtension K E]
variable {ι : Type*} [Fintype ι] (H : Matrix ι ι E)
variable (K) (R : Type*) [CommRing R] [Algebra K R]
variable {K H R}
namespace GroundTheory.Automorphic
theorem _root_.solution (hH : IsHermitianFor (conjHom K E) H) (x y : ι → R ⊗[K] E) :
    hermPair K H R y x = conjBase K E R (hermPair K H R x y) := by
  have hHb : (baseMatrix K H R).map (conjBase K E R) = (baseMatrix K H R)ᵀ := by
    ext i j
    have := congrFun (congrFun hH j) i
    simp only [transpose_apply, map_apply] at this
    simp only [map_apply, transpose_apply, baseMatrix, Algebra.TensorProduct.includeRight_apply,
      conjBase_tmul, ← this]
    rfl
  unfold hermPair
  rw [RingHom.map_dotProduct]
  have h1 : (conjBase K E R) ∘ (fun i => conjBase K E R (x i)) = x :=
    funext fun i => conjBase_conjBase (x i)
  have h2 : (conjBase K E R) ∘ (baseMatrix K H R *ᵥ y) =
      (baseMatrix K H R).map (conjBase K E R) *ᵥ fun i => conjBase K E R (y i) :=
    funext fun i => RingHom.map_mulVec _ _ _ i
  rw [h1, h2, hHb, Matrix.mulVec_transpose, dotProduct_comm x, Matrix.dotProduct_mulVec]
end GroundTheory.Automorphic
