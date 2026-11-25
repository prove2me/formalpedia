-- Prove2me | solution 1 for GroundTheory.Automorphic.hermTrace_eq_sum
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T00:18:18.207809+00:00
-- url     : https://prove2.me/submissions/975cd706-e072-40de-97fd-8d93576135ce

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_AdelicUnitaryGroups_Anisotropic
import Definitions.Def_GroundTheory_AutomorphicForms_DefiniteClassNumber_HermTraceSelfOfHermValue
import Theorems.Thm_GroundTheory_Automorphic_hermTraceBilin_apply
import Theorems.Thm_GroundTheory_Automorphic_hermTrace_tensorMap
import Theorems.Thm_GroundTheory_Automorphic_sum_coords_smul_stdVec
import Theorems.Thm_GroundTheory_Automorphic_tensorMap_stdVec
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
variable [DecidableEq ι] (R : Type*) [CommRing R] [Algebra K R]
variable {κ : Type*} [Fintype κ] (b : Basis κ K E)
variable {R}
namespace GroundTheory.Automorphic
theorem _root_.solution (x y : ι → R ⊗[K] E) :
    hermTrace K H R x y = ∑ a : ι × κ, ∑ c : ι × κ, vecCoords R b x a *
      vecCoords R b y c * algebraMap K R (hermTrace K H K (stdVec K b a) (stdVec K b c)) := by
  have hval : ∀ a c : ι × κ, algebraMap K R (hermTrace K H K (stdVec K b a) (stdVec K b c)) =
      hermTrace K H R (stdVec R b a) (stdVec R b c) := by
    intro a c
    rw [← tensorMap_stdVec (R := R) b a, ← tensorMap_stdVec (R := R) b c]
    exact hermTrace_tensorMap (Algebra.ofId K R) _ _
  simp only [hval]
  conv_lhs => rw [← sum_coords_smul_stdVec b x, ← sum_coords_smul_stdVec b y]
  rw [← hermTraceBilin_apply]
  simp only [map_sum, map_smul, LinearMap.sum_apply, LinearMap.smul_apply, smul_eq_mul,
    hermTraceBilin_apply, Finset.mul_sum]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun c _ => by ring
end GroundTheory.Automorphic
