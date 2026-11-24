-- Prove2me | solution 1 for GlobalTheory.SmithBetween.exists_mul_eq_mul_diagonal
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T23:32:43.403833+00:00
-- url     : https://prove2.me/submissions/8c695f24-66c5-47d0-b4fa-15c1a3fbec92

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_ExistsMulEqMulDiagonal

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open IsDedekindDomain NumberField
open GlobalTheory GlobalTheory.SmithBetween
open Matrix
open IsDedekindDomain NumberField
open Matrix
namespace GlobalTheory.SmithBetween
namespace _root_.GlobalTheory.SmithBetween
theorem _root_.solution {R : Type} [CommRing R] [IsDomain R] [IsPrincipalIdealRing R]
    {n : Type} [Fintype n] [DecidableEq n] (M : Matrix n n R) (hM : M.det ≠ 0) :
    ∃ P Q : Matrix n n R, IsUnit P.det ∧ IsUnit Q.det ∧ ∃ c : n → R,
      M * Q = P * Matrix.diagonal c := by
  have hinj : Function.Injective M.mulVecLin := Matrix.mulVec_injective_of_det_ne_zero hM
  obtain ⟨m, snf⟩ := Submodule.smithNormalForm (Pi.basisFun R n) (LinearMap.range M.mulVecLin)
  have hm : m = Fintype.card n := by
    have h1 := Module.finrank_eq_card_basis snf.bN
    rw [LinearMap.finrank_range_of_inj hinj] at h1
    simpa using h1.symm
  have hf : Function.Bijective snf.f := by
    rw [Fintype.bijective_iff_injective_and_card]
    exact ⟨snf.f.injective, by simp [hm]⟩
  let g : Fin m ≃ n := Equiv.ofBijective snf.f hf
  let eN := LinearEquiv.ofInjective M.mulVecLin hinj
  let bQ : Module.Basis n R (n → R) := (snf.bN.map eN.symm).reindex g
  letI := (Pi.basisFun R n).invertibleToMatrix snf.bM
  letI := (Pi.basisFun R n).invertibleToMatrix bQ
  refine ⟨(Pi.basisFun R n).toMatrix snf.bM, (Pi.basisFun R n).toMatrix bQ, ?_, ?_,
    fun j => snf.a (g.symm j), ?_⟩
  · exact isUnit_det_of_invertible _
  · exact isUnit_det_of_invertible _
  · ext i j
    have key : M *ᵥ bQ j = snf.a (g.symm j) • snf.bM j := by
      have h2 := snf.snf (g.symm j)
      have h3 : snf.f (g.symm j) = j := g.apply_symm_apply j
      rw [h3] at h2
      rw [← h2]
      simp only [bQ, Module.Basis.reindex_apply, Module.Basis.map_apply]
      have h4 : ((eN (eN.symm (snf.bN (g.symm j)))) : n → R) =
          M.mulVecLin (eN.symm (snf.bN (g.symm j))) := rfl
      rw [LinearEquiv.apply_symm_apply] at h4
      rw [← Matrix.mulVecLin_apply, ← h4]
    have := congrFun key i
    simp only [Matrix.mul_diagonal, Module.Basis.toMatrix_apply, Pi.basisFun_repr]
    rw [Matrix.mul_apply]
    simp [Matrix.mulVec, dotProduct] at this
    simpa [mul_comm, Module.Basis.toMatrix_apply] using this
end _root_.GlobalTheory.SmithBetween
end GlobalTheory.SmithBetween
