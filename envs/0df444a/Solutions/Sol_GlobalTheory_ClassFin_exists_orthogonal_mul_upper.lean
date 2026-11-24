-- Prove2me | solution 1 for GlobalTheory.ClassFin.exists_orthogonal_mul_upper
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T12:12:11.583401+00:00
-- url     : https://prove2.me/submissions/01b8b6c2-dda2-4b85-8856-48899c3b14bd

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AdelicHermitianForms_AdelicPair
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_IwasawaDecompositionRealMatrix

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
theorem _root_.solution (N : ℕ) (g : Matrix (Fin N) (Fin N) ℝ) :
    ∃ (k r : Matrix (Fin N) (Fin N) ℝ), kᵀ * k = 1 ∧ (∀ i j, j < i → r i j = 0) ∧ g = k * r := by
  classical
  let f : Fin N → EuclideanSpace ℝ (Fin N) := fun j => WithLp.toLp 2 (fun i => g i j)
  have h : Module.finrank ℝ (EuclideanSpace ℝ (Fin N)) = Fintype.card (Fin N) := by simp
  let b := InnerProductSpace.gramSchmidtOrthonormalBasis h f
  refine ⟨Matrix.of fun i j => b j i, Matrix.of fun i j => inner ℝ (b i) (f j), ?_, ?_, ?_⟩
  · ext i j
    have := orthonormal_iff_ite.mp b.orthonormal i j
    rw [Matrix.mul_apply, Matrix.one_apply, ← this, PiLp.inner_apply]
    simp [mul_comm]
  · intro i j hij
    exact InnerProductSpace.gramSchmidtOrthonormalBasis_inv_triangular h f hij
  · ext i j
    have := congrArg (fun v : EuclideanSpace ℝ (Fin N) => v i) (b.sum_repr' (f j))
    simp only [WithLp.ofLp_sum, Finset.sum_apply, PiLp.smul_apply, WithLp.ofLp_smul, Pi.smul_apply, smul_eq_mul] at this
    rw [Matrix.mul_apply]
    simp only [Matrix.of_apply]
    calc g i j = f j i := rfl
      _ = _ := this.symm
      _ = _ := Finset.sum_congr rfl fun x _ => mul_comm _ _
end GlobalTheory.ClassFin
