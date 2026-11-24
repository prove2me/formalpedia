-- Prove2me | solution 1 for GlobalTheory.UnitaryExtension.exists_unitary_mul_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T15:40:43.715479+00:00
-- url     : https://prove2.me/submissions/d1ddb1f3-9bf9-4344-9fd1-ad818ddcce91

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ThetaMetrics_IsKMeas
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_ExistsUnitaryOfGramEq
import Theorems.Thm_GlobalTheory_UnitaryExtension_exists_isometry_comp

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix MeasureTheory Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.B2 GlobalTheory.HCXi
open scoped ENNReal ComplexOrder
open GlobalTheory GlobalTheory.UnitaryExtension
namespace GlobalTheory.UnitaryExtension
theorem _root_.solution {n : ℕ} {ι : Type} [Fintype ι] [DecidableEq ι]
    (A B : Matrix (Fin n) ι ℂ) (h : Aᴴ * A = Bᴴ * B) :
    ∃ U : Matrix (Fin n) (Fin n) ℂ, Uᴴ * U = 1 ∧ U * A = B := by
  have key : ∀ (C : Matrix (Fin n) ι ℂ) (x : EuclideanSpace ℂ ι),
      inner ℂ (Matrix.toEuclideanLin C x) (Matrix.toEuclideanLin C x)
        = inner ℂ x (Matrix.toEuclideanLin (Cᴴ * C) x) := by
    intro C x
    rw [← LinearMap.adjoint_inner_right, ← Matrix.toEuclideanLin_conjTranspose_eq_adjoint]
    congr 1
    simp [Matrix.toLpLin_apply, Matrix.mulVec_mulVec]
  obtain ⟨u, hu⟩ := exists_isometry_comp (Matrix.toEuclideanLin A) (Matrix.toEuclideanLin B) (by
    intro x
    rw [@norm_eq_sqrt_re_inner ℂ, @norm_eq_sqrt_re_inner ℂ _ _ _ _ (Matrix.toEuclideanLin A x), key, key, h])
  refine ⟨Matrix.toEuclideanLin.symm u.toLinearMap, ?_, ?_⟩
  · apply (Matrix.toEuclideanLin (𝕜 := ℂ) (m := Fin n) (n := Fin n)).injective
    ext1 x
    apply ext_inner_left ℂ
    intro y
    have e : Matrix.toEuclideanLin ((Matrix.toEuclideanLin.symm u.toLinearMap)ᴴ * Matrix.toEuclideanLin.symm u.toLinearMap) x
        = Matrix.toEuclideanLin (Matrix.toEuclideanLin.symm u.toLinearMap)ᴴ (Matrix.toEuclideanLin (Matrix.toEuclideanLin.symm u.toLinearMap) x) := by
      generalize Matrix.toEuclideanLin.symm u.toLinearMap = U
      simp [Matrix.toLpLin_apply, Matrix.mulVec_mulVec]
    rw [e, Matrix.toEuclideanLin_conjTranspose_eq_adjoint, LinearMap.adjoint_inner_right]
    simp [Matrix.toLpLin_apply]
  · apply (Matrix.toEuclideanLin (𝕜 := ℂ) (m := Fin n) (n := ι)).injective
    ext1 x
    have e : Matrix.toEuclideanLin (Matrix.toEuclideanLin.symm u.toLinearMap * A) x
        = Matrix.toEuclideanLin (Matrix.toEuclideanLin.symm u.toLinearMap) (Matrix.toEuclideanLin A x) := by
      generalize Matrix.toEuclideanLin.symm u.toLinearMap = U
      simp [Matrix.toLpLin_apply, Matrix.mulVec_mulVec]
    rw [e, LinearEquiv.apply_symm_apply]
    exact hu x
end GlobalTheory.UnitaryExtension
