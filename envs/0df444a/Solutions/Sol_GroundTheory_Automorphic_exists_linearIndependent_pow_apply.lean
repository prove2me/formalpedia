-- Prove2me | solution 1 for GroundTheory.Automorphic.exists_linearIndependent_pow_apply
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T00:25:49.253247+00:00
-- url     : https://prove2.me/submissions/054e0737-5ba3-4346-b3f6-2f39e79effa0

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_StableConjCyclic
import Theorems.Thm_GroundTheory_Automorphic_exists_linearIndependent_pow_apply_of_isAlgClosed
import Theorems.Thm_GroundTheory_Automorphic_krylov_col
import Theorems.Thm_GroundTheory_Automorphic_exists_det_krylov_ne_zero

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GroundTheory GroundTheory.Automorphic
open Polynomial Module Matrix
variable {E V : Type*} [Field E] [AddCommGroup V] [Module E V] [FiniteDimensional E V]
namespace GroundTheory.Automorphic
theorem _root_.solution [Infinite E] (f : Module.End E V)
    (hf : f.charpoly.Separable) :
    ∃ v : V, LinearIndependent E (fun k : Fin (finrank E V) => (f ^ (k : ℕ)) v) := by
  classical
  set n := finrank E V
  let b : Basis (Fin n) E V := Module.finBasis E V
  set M := LinearMap.toMatrix b b f with hM
  let φ : E →+* AlgebraicClosure E := algebraMap E (AlgebraicClosure E)
  have hchar : (Matrix.toLin' (M.map φ)).charpoly = f.charpoly.map φ := by
    rw [Matrix.charpoly_toLin', Matrix.charpoly_map, hM, LinearMap.charpoly_toMatrix]
  have hsep : (Matrix.toLin' (M.map φ)).charpoly.Separable := by
    rw [hchar]; exact hf.map
  obtain ⟨w, hw⟩ := exists_linearIndependent_pow_apply_of_isAlgClosed _ hsep
  rw [Module.finrank_fin_fun] at hw
  have hw' : (krylov (M.map φ) w).det ≠ 0 := by
    rw [← isUnit_iff_ne_zero, ← Matrix.isUnit_iff_isUnit_det,
      ← Matrix.linearIndependent_cols_iff_isUnit]
    have hcol : (krylov (M.map φ) w).col = fun k : Fin n => (Matrix.toLin' (M.map φ) ^ (k : ℕ)) w := by
      ext1 k
      rw [krylov_col, ← Matrix.toLin'_pow, Matrix.toLin'_apply]
    rw [hcol]
    exact hw
  obtain ⟨v₀, hv₀⟩ := exists_det_krylov_ne_zero φ M w hw'
  have hli : LinearIndependent E (krylov M v₀).col := by
    rw [Matrix.linearIndependent_cols_iff_isUnit, Matrix.isUnit_iff_isUnit_det,
      isUnit_iff_ne_zero]
    exact hv₀
  refine ⟨b.equivFun.symm v₀, ?_⟩
  have key : (fun k : Fin n => (f ^ (k : ℕ)) (b.equivFun.symm v₀)) =
      b.equivFun.symm ∘ (krylov M v₀).col := by
    ext1 k
    simp only [Function.comp_apply, krylov_col]
    apply b.equivFun.injective
    rw [LinearEquiv.apply_symm_apply, Basis.equivFun_apply, ← LinearMap.toMatrix_mulVec_repr b b,
      hM, LinearMap.toMatrix_pow]
    congr 1
    rw [← Basis.equivFun_apply, LinearEquiv.apply_symm_apply]
  rw [key]
  exact hli.map' _ (LinearEquiv.ker _)
end GroundTheory.Automorphic
