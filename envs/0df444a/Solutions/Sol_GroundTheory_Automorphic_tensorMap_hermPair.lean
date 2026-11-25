-- Prove2me | solution 1 for GroundTheory.Automorphic.tensorMap_hermPair
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T00:04:23.233214+00:00
-- url     : https://prove2.me/submissions/8cb2ac28-38d4-463c-908e-a9c1e76c5381

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_AdelicUnitaryGroups_Anisotropic
import Definitions.Def_GroundTheory_AutomorphicForms_DefiniteClassNumber_HermTraceSelfOfHermValue
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
theorem _root_.solution {S : Type*} [CommRing S] [Algebra K S] (f : R →ₐ[K] S)
    (x y : ι → R ⊗[K] E) :
    tensorMap E f (hermPair K H R x y) =
      hermPair K H S (fun i => tensorMap E f (x i)) (fun i => tensorMap E f (y i)) := by
  unfold hermPair
  have h := RingHom.map_dotProduct (tensorMap E f : R ⊗[K] E →+* S ⊗[K] E)
    (fun i => conjBase K E R (x i)) (baseMatrix K H R *ᵥ y)
  simp only [RingHom.coe_coe] at h
  rw [h]
  congr 1
  · funext i
    exact tensorMap_conjBase f (x i)
  · funext i
    have := RingHom.map_mulVec (tensorMap E f : R ⊗[K] E →+* S ⊗[K] E) (baseMatrix K H R) y i
    simp only [RingHom.coe_coe] at this
    rw [Function.comp_apply, this]
    have h2 := map_includeRight_tensorMap (H := H) f
    simp only [RingHom.coe_coe] at h2
    rw [h2]
    rfl
end GroundTheory.Automorphic
