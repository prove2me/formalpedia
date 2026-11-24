-- Prove2me | solution 1 for GlobalTheory.ClassParam.HidaSetting.isUnit_det_gram
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T12:45:22.641956+00:00
-- url     : https://prove2.me/submissions/55fadb22-e149-4e10-86fa-dbd03a9c2f5f

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_TwistedDiscreteSeries_PlusPolynomialInclusion
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_LeftMulMatrixTransfer
import Theorems.Thm_GlobalTheory_ClassParam_Iso_mul
import Theorems.Thm_GlobalTheory_ClassParam_Intw_mul
import Theorems.Thm_GlobalTheory_ClassParam_det_gram

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Polynomial TensorProduct Matrix Formalism.UG
open GlobalTheory GlobalTheory.ClassParam
variable {A B : Type} [CommRing A] [CommRing B] [Algebra A B] {r : ℕ}
variable {σ : A →+* A} {τ : B →+* B} {α : B} {b : Module.Basis (Fin r) A B}
  {J : Matrix (Fin r) (Fin r) A}
namespace GlobalTheory.ClassParam
namespace HidaSetting
theorem _root_.solution (S : HidaSetting σ τ α b) {x : B} (hx : IsUnit x) :
    IsUnit (gram τ x b).det := by
  rw [det_gram]
  refine (hx.map (Algebra.norm A)).mul ?_
  let N : Matrix (Fin r) (Fin r) A := Matrix.of fun i j => b.repr (τ (b j)) i
  have hN : ∀ j, τ (b j) = ∑ i, N i j • b i := fun j => (b.sum_repr _).symm
  have h1 : gram τ 1 b = Algebra.traceMatrix A b * N := by
    ext i j
    simp [gram, tf, Matrix.mul_apply, hN, Finset.mul_sum, Algebra.traceMatrix_apply, mul_comm]
  have h2 : N * N.map σ = 1 := by
    ext i j
    have e : b j = ∑ p, σ (N p j) • τ (b p) := by
      conv_lhs => rw [← S.hτ (b j), hN j]
      simp only [map_sum, Algebra.smul_def, map_mul, S.comp]
    have e2 := congrArg (fun y => b.repr y i) e
    simp only [map_sum, map_smul, Module.Basis.repr_self] at e2
    rw [Matrix.mul_apply, Matrix.one_apply]
    simpa [Finsupp.single_apply, eq_comm, N, mul_comm] using e2.symm
  rw [h1, Matrix.det_mul]
  exact S.perf.mul (Matrix.isUnit_det_of_right_inverse h2)
end HidaSetting
end GlobalTheory.ClassParam
