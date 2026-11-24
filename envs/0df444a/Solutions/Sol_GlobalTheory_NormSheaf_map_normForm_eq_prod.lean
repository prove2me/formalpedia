-- Prove2me | solution 1 for GlobalTheory.NormSheaf.map_normForm_eq_prod
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T19:14:46.421795+00:00
-- url     : https://prove2.me/submissions/7cf8eddd-f1a8-4ed4-9f53-60226fbe7dbf

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_NormIdeal
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsFiniteAlgebraSplittingNormForm

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MvPolynomial
noncomputable section
open GlobalTheory GlobalTheory.NormSheaf
namespace GlobalTheory.NormSheaf
theorem _root_.solution (K L Ω : Type) [Field K] [Field L] [Algebra K L] [FiniteDimensional K L]
    [Field Ω] [Algebra K Ω] (e : Fin (Module.finrank K L) ≃ (L →ₐ[K] Ω)) {m : ℕ} (x : Fin m → L) :
    (normForm K L x).map (algebraMap K Ω) = ∏ j, ∑ i, C (e j (x i)) * X i := by
  classical
  set b := Module.finBasis K L
  let V : Matrix (Fin (Module.finrank K L)) (Fin (Module.finrank K L)) Ω := .of fun i k => e i (b k)
  have hV : V.det ≠ 0 := by
    have hli := (linearIndependent_algHom_toLinearMap K L Ω).comp e e.injective
    intro h0
    obtain ⟨c, hc0, hc⟩ := Matrix.exists_vecMul_eq_zero_iff.2 h0
    refine hc0 (funext (Fintype.linearIndependent_iff.1 hli c (b.ext fun k => ?_)))
    have := congrFun hc k
    simpa [V, Matrix.vecMul, dotProduct] using this
  have key : V.map (C : Ω →+* MvPolynomial (Fin m) Ω) *
      (MvPolynomial.map (algebraMap K Ω)).mapMatrix (∑ i, (X i : MvPolynomial (Fin m) K) •
        (Algebra.leftMulMatrix b (x i)).map (C : K →+* MvPolynomial (Fin m) K)) =
      Matrix.diagonal (fun j => ∑ i, C (e j (x i)) * X i) * V.map (C : Ω →+* MvPolynomial (Fin m) Ω) := by
    ext1 j k
    have h (i : Fin m) : e j (x i) * e j (b k) =
        ∑ l, e j (b l) * algebraMap K Ω (Algebra.leftMulMatrix b (x i) l k) := by
      rw [← map_mul, ← b.sum_repr (x i * b k), map_sum]
      refine Finset.sum_congr rfl fun l _ => ?_
      rw [map_smul, Algebra.leftMulMatrix_eq_repr_mul, Algebra.smul_def, mul_comm]
    rw [Matrix.diagonal_mul, Matrix.mul_apply]
    simp only [V, Matrix.of_apply, Matrix.map_apply, RingHom.mapMatrix_apply, Matrix.sum_apply, Matrix.smul_apply,
      smul_eq_mul, map_sum, map_mul, map_X, map_C, Finset.mul_sum, Finset.sum_mul, mul_assoc]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [mul_left_comm, ← C_mul, h, map_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun l _ => ?_
    rw [C_mul]
    ring
  have hd := congrArg Matrix.det key
  rw [Matrix.det_mul, Matrix.det_mul, Matrix.det_diagonal, mul_comm, ← RingHom.mapMatrix_apply, ← RingHom.map_det,
    ← RingHom.map_det] at hd
  rw [normForm, mul_right_cancel₀ (C_eq_zero.not.2 hV) hd]
end GlobalTheory.NormSheaf
