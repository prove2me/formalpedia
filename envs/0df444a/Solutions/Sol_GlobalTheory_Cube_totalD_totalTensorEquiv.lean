-- Prove2me | solution 1 for GlobalTheory.Cube.totalD_totalTensorEquiv
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T08:31:49.593828+00:00
-- url     : https://prove2.me/submissions/8125a170-b7a1-4555-a8f2-eae766d6f123

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_CubeTotalComplexAcyclicOfSlicesInductionOnCard
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_RangeRestrictCompSubtypeOfOrthogonalOfNe
import Theorems.Thm_GlobalTheory_Cube_degSign_apply
import Theorems.Thm_GlobalTheory_Cube_sum_parts
import Theorems.Thm_GlobalTheory_Cube_cubeSign_inlEmb
import Theorems.Thm_GlobalTheory_Cube_cubeSign_inrEmb
import Theorems.Thm_GlobalTheory_Cube_totalTensorEquiv_tmul

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory Limits HomologicalComplex TensorProduct
universe v u
open GlobalTheory
open GlobalTheory.Cube
variable {ι κ : Type} [LinearOrder ι] [LinearOrder κ] {K : Type u} [CommRing K]
variable [Finite ι] [Finite κ] (A : Cube.{v} ι K) (B : Cube.{v} κ K)
namespace GlobalTheory.Cube
theorem _root_.solution (z : (∀ s, A.obj s) ⊗[K] (∀ t, B.obj t)) :
    totalD (extTensor A B) (totalTensorEquiv A B z) = totalTensorEquiv A B
      ((TensorProduct.map (totalD A) 1 + TensorProduct.map (degSign A) (totalD B) :
        Module.End K _) z) := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | add x y hx hy => simp only [map_add, hx, hy]
  | tmul x y =>
    funext w
    rw [LinearMap.add_apply, map_add, Pi.add_apply, TensorProduct.map_tmul, TensorProduct.map_tmul,
      totalTensorEquiv_tmul, totalTensorEquiv_tmul, totalD_apply, totalD_apply, totalD_apply,
      sum_parts, sum_tmul, tmul_sum]
    refine congrArg₂ (· + ·) (Finset.sum_congr rfl fun i _ => ?_)
      (Finset.sum_congr rfl fun k _ => ?_)
    · have h1 : part (inlEmb ι κ) (w.erase (inlEmb ι κ i)) = (part (inlEmb ι κ) w).erase i := by
        ext; simp
      have h2 : part (inrEmb ι κ) (w.erase (inlEmb ι κ i)) = part (inrEmb ι κ) w := by
        ext; simp
      have h3 : res (extTensor A B) (Finset.erase_subset (inlEmb ι κ i) w)
          (totalTensorEquiv A B (x ⊗ₜ y) _) = _ :=
        congrArg₂ (fun a b => a ⊗ₜ[K] b) (res_congr A x h1 _ (Finset.erase_subset _ _))
          ((res_congr B y h2 _ (subset_refl _)).trans (res_self B _ _))
      refine (congrArg (cubeSign w (inlEmb ι κ i) • ·) h3).trans ?_
      rw [cubeSign_inlEmb]
      rfl
    · have h1 : part (inlEmb ι κ) (w.erase (inrEmb ι κ k)) = part (inlEmb ι κ) w := by
        ext; simp
      have h2 : part (inrEmb ι κ) (w.erase (inrEmb ι κ k)) = (part (inrEmb ι κ) w).erase k := by
        ext; simp
      have h3 : res (extTensor A B) (Finset.erase_subset (inrEmb ι κ k) w)
          (totalTensorEquiv A B (x ⊗ₜ y) _) = _ :=
        congrArg₂ (fun a b => a ⊗ₜ[K] b) ((res_congr A x h1 _ (subset_refl _)).trans (res_self A _ _))
          (res_congr B y h2 _ (Finset.erase_subset _ _))
      refine (congrArg (cubeSign w (inrEmb ι κ k) • ·) h3).trans ?_
      rw [cubeSign_inrEmb, degSign_apply, TensorProduct.tmul_smul, ← TensorProduct.smul_tmul',
        smul_smul, mul_comm]
      rfl
end GlobalTheory.Cube
