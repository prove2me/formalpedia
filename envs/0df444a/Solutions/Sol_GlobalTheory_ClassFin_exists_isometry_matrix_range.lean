-- Prove2me | solution 1 for GlobalTheory.ClassFin.exists_isometry_matrix_range
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T12:12:10.3768+00:00
-- url     : https://prove2.me/submissions/d82be7b4-422c-4657-ac80-11ec6e4e10cd

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AdelicHermitianForms_AdelicPair
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_TraceLogLeLogDet
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_ExistsIsometryMatrixRange

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix GlobalTheory.ClassFin
open scoped Kronecker ComplexOrder TensorProduct
open GlobalTheory GlobalTheory.ClassFin
namespace GlobalTheory.ClassFin
theorem _root_.solution {ι : Type} [Fintype ι] [DecidableEq ι] (W : Submodule ℂ (ι → ℂ)) :
    ∃ (n : ℕ) (Q : Matrix ι (Fin n) ℂ), Qᴴ * Q = 1 ∧ ∀ v, v ∈ W ↔ ∃ x, v = Q *ᵥ x := by
  let W' : Submodule ℂ (EuclideanSpace ℂ ι) := W.comap (WithLp.linearEquiv 2 ℂ (ι → ℂ)).toLinearMap
  let b := stdOrthonormalBasis ℂ W'
  refine ⟨_, Matrix.of fun i j => (b j : EuclideanSpace ℂ ι) i, ?_, ?_⟩
  · ext j k
    have h := orthonormal_iff_ite.mp b.orthonormal j k
    rw [Submodule.coe_inner, PiLp.inner_apply] at h
    rw [Matrix.mul_apply, Matrix.one_apply, ← h]
    refine Finset.sum_congr rfl fun i _ => ?_
    simp [mul_comm]
  · intro v
    constructor
    · intro hv
      let w : W' := ⟨WithLp.toLp 2 v, hv⟩
      refine ⟨fun j => b.repr w j, ?_⟩
      ext i
      have h := congrArg (fun z : W' => (z : EuclideanSpace ℂ ι) i) (b.sum_repr w)
      simp only [AddSubmonoidClass.coe_finsetSum, SetLike.val_smul] at h
      have h2 : v i = (w : EuclideanSpace ℂ ι) i := rfl
      rw [h2, ← h]
      simp [Matrix.mulVec, dotProduct, mul_comm]
    · rintro ⟨x, rfl⟩
      have h : (Matrix.of fun i j => (b j : EuclideanSpace ℂ ι) i) *ᵥ x
          = ∑ j, x j • (b j : EuclideanSpace ℂ ι).ofLp := by
        ext i
        simp [Matrix.mulVec, dotProduct, mul_comm]
      rw [h]
      exact W.sum_mem fun j _ => W.smul_mem _ (b j).2
end GlobalTheory.ClassFin
