-- Prove2me | solution 1 for GroundTheory.Automorphic.Anisotropic.exists_blockHom_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T00:00:27.704516+00:00
-- url     : https://prove2.me/submissions/fd220509-a878-4fe3-aaf9-7252c7cdd704

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_AnisotropicRestrict
import Theorems.Thm_GroundTheory_Automorphic_Anisotropic_rmatHom_apply
import Theorems.Thm_GroundTheory_Automorphic_Anisotropic_exists_rmat_eq
import Theorems.Thm_GroundTheory_Automorphic_Anisotropic_lmat_eq_rmat
import Theorems.Thm_GroundTheory_Automorphic_Anisotropic_blockHom_apply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GroundTheory.Automorphic.Anisotropic.rmatHom_apply

set_option autoImplicit false
set_option maxSynthPendingDepth 1
open Matrix TensorProduct
set_option linter.unusedSectionVars false
open GroundTheory GroundTheory.Automorphic
noncomputable section
open GroundTheory.Automorphic.Anisotropic
variable {K : Type*} [Field K] {κ : Type*} [Fintype κ] [DecidableEq κ]
variable {E : Type*} [CommRing E] [Algebra K E] (b : Module.Basis κ K E)
variable (R : Type*) [CommRing R] [Algebra K R] {R' : Type*} [CommRing R'] [Algebra K R']
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
namespace GroundTheory.Automorphic.Anisotropic
theorem _root_.solution (g : Matrix (ι × κ) (ι × κ) R)
    (hg : ∀ j, blockHom b R (Matrix.scalar ι (baseBasis b R j)) * g =
      g * blockHom b R (Matrix.scalar ι (baseBasis b R j))) :
    ∃ M, blockHom b R M = g := by
  have hsc : ∀ j, blockHom b R (Matrix.scalar ι (baseBasis b R j)) =
      Matrix.compAlgEquiv ι κ R R (Matrix.scalar ι (rmat b R (baseBasis b R j))) := by
    intro j
    simp only [blockHom, AlgHom.comp_apply, AlgHom.mapMatrix_apply, Matrix.scalar_apply,
      Matrix.diagonal_map (map_zero _), rmatHom_apply]
    rfl
  have hcomm : ∀ j i i', rmat b R (baseBasis b R j) * (Matrix.comp ι ι κ κ R).symm g i i' =
      (Matrix.comp ι ι κ κ R).symm g i i' * rmat b R (baseBasis b R j) := by
    intro j i i'
    have h := hg j
    rw [hsc, ← (Matrix.compAlgEquiv ι κ R R).apply_symm_apply g, ← map_mul, ← map_mul] at h
    have h2 := (Matrix.compAlgEquiv ι κ R R).injective h
    have h3 := congrFun (congrFun h2 i) i'
    simpa [Matrix.scalar_apply, Matrix.diagonal_mul, Matrix.mul_diagonal] using h3
  have hx : ∀ i i', ∃ x, rmat b R x = (Matrix.comp ι ι κ κ R).symm g i i' := fun i i' =>
    exists_rmat_eq b R _ fun j => by rw [lmat_eq_rmat]; exact hcomm j i i'
  choose M hM using hx
  refine ⟨Matrix.of M, ?_⟩
  ext ⟨i, k⟩ ⟨i', l⟩
  rw [blockHom_apply, Matrix.of_apply, hM i i']
  rfl
end GroundTheory.Automorphic.Anisotropic
