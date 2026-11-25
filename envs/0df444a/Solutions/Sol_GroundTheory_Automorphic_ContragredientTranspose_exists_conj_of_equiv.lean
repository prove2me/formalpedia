-- Prove2me | solution 1 for GroundTheory.Automorphic.ContragredientTranspose.exists_conj_of_equiv
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T23:48:42.540999+00:00
-- url     : https://prove2.me/submissions/f1dbfe89-deca-4f8b-bbec-681567f445c0

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_ContragredientTranspose_MatrixSimilarity

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GroundTheory GroundTheory.Automorphic GroundTheory.Automorphic.ContragredientTranspose
open Polynomial
universe u
variable {F : Type u} [Field F] {n : ℕ}
namespace GroundTheory.Automorphic.ContragredientTranspose
theorem _root_.solution {x y : GL (Fin n) F}
    (E : Module.AEval' (Matrix.toLin' (x : Matrix (Fin n) (Fin n) F)) ≃ₗ[F[X]]
      Module.AEval' (Matrix.toLin' (y : Matrix (Fin n) (Fin n) F))) :
    ∃ g : GL (Fin n) F, x = g * y * g⁻¹ := by
  classical
  set φx := Matrix.toLin' (x : Matrix (Fin n) (Fin n) F) with hφx
  set φy := Matrix.toLin' (y : Matrix (Fin n) (Fin n) F) with hφy
  let L : (Fin n → F) →ₗ[F] (Fin n → F) :=
    (Module.AEval'.of φy).symm.toLinearMap ∘ₗ (E.restrictScalars F).toLinearMap ∘ₗ
      (Module.AEval'.of φx).toLinearMap
  let L' : (Fin n → F) →ₗ[F] (Fin n → F) :=
    (Module.AEval'.of φx).symm.toLinearMap ∘ₗ (E.symm.restrictScalars F).toLinearMap ∘ₗ
      (Module.AEval'.of φy).toLinearMap
  have hLL' : L ∘ₗ L' = LinearMap.id := by
    apply LinearMap.ext
    intro v
    simp [L, L']
  have hL'L : L' ∘ₗ L = LinearMap.id := by
    apply LinearMap.ext
    intro v
    simp [L, L']
  have hint : L ∘ₗ φx = φy ∘ₗ L := by
    apply LinearMap.ext
    intro v
    simp only [L, LinearMap.comp_apply, LinearEquiv.coe_coe, LinearEquiv.restrictScalars_apply]
    rw [← Module.AEval'.X_smul_of, map_smul, Module.AEval'.of_symm_X_smul]
  set P := LinearMap.toMatrix' L
  set Q := LinearMap.toMatrix' L'
  have hPQ : P * Q = 1 := by
    rw [← LinearMap.toMatrix'_comp, hLL', LinearMap.toMatrix'_id]
  have hQP : Q * P = 1 := by
    rw [← LinearMap.toMatrix'_comp, hL'L, LinearMap.toMatrix'_id]
  have hPx : P * (x : Matrix (Fin n) (Fin n) F) = y * P := by
    have h1 : P * (x : Matrix (Fin n) (Fin n) F) = LinearMap.toMatrix' (L ∘ₗ φx) := by
      rw [LinearMap.toMatrix'_comp, hφx, LinearMap.toMatrix'_toLin']
    have h2 : (y : Matrix (Fin n) (Fin n) F) * P = LinearMap.toMatrix' (φy ∘ₗ L) := by
      rw [LinearMap.toMatrix'_comp, hφy, LinearMap.toMatrix'_toLin']
    rw [h1, h2, hint]
  let g : GL (Fin n) F := ⟨Q, P, hQP, hPQ⟩
  refine ⟨g, Units.ext ?_⟩
  simp only [Units.val_mul]
  show (x : Matrix (Fin n) (Fin n) F) = Q * y * P
  calc (x : Matrix (Fin n) (Fin n) F) = (Q * P) * x := by rw [hQP, one_mul]
    _ = Q * (P * x) := Matrix.mul_assoc _ _ _
    _ = Q * (y * P) := by rw [hPx]
    _ = Q * y * P := (Matrix.mul_assoc _ _ _).symm
end GroundTheory.Automorphic.ContragredientTranspose
