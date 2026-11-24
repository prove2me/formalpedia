-- Prove2me | solution 1 for GlobalTheory.JR.LinDesc.exists_leftMul_of_comm
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T18:36:31.532699+00:00
-- url     : https://prove2.me/submissions/13be31a6-98d4-4a70-bcaa-39ccdf98d579

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_LeftMulTau
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ExistsUnitLeftMulMatrixOfCommuteCompanion
import Theorems.Thm_GlobalTheory_JR_LinDesc_bas_apply
import Theorems.Thm_GlobalTheory_JR_LinDesc_leftMul_tau


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.JR Matrix MeasureTheory Filter Topology
noncomputable section
open GlobalTheory GlobalTheory.JR GlobalTheory.JR.LinDesc
namespace GlobalTheory.JR.LinDesc
theorem _root_.solution {F E : Type} [NontriviallyNormedField F] [NontriviallyNormedField E]
    [NormedAlgebra F E] [StarRing E] (A : Et F E) {r : ℕ} {τ : A.K} {p : Fin r → F}
    (hG : A.IsGen τ p) (M : Matrix (Fin r) (Fin r) F) (hM : M * companion p = companion p * M) :
    ∃ k : A.K, M = Algebra.leftMulMatrix (bas A hG) k := by
  set b := bas A hG
  set φ : A.K →ₗ[F] A.K := Matrix.toLin b b M with hφ
  have hMφ : LinearMap.toMatrix b b φ = M := by simp [hφ]
  have hlm : ∀ x : A.K, Algebra.leftMulMatrix b x = LinearMap.toMatrix b b (Algebra.lmul F A.K x) := fun x => rfl
  have hτ : φ ∘ₗ Algebra.lmul F A.K τ = Algebra.lmul F A.K τ ∘ₗ φ := by
    apply (LinearMap.toMatrix b b).injective
    rw [LinearMap.toMatrix_comp b b b, LinearMap.toMatrix_comp b b b, hMφ, ← hlm, leftMul_tau]
    exact hM
  have hτx : ∀ x, φ (τ * x) = τ * φ x := fun x => by
    have := congrArg (fun f => f x) hτ
    simpa using this
  have hpow : ∀ (n : ℕ) x, φ (τ ^ n * x) = τ ^ n * φ x := by
    intro n; induction n with
    | zero => intro x; simp
    | succ n ih => intro x; rw [pow_succ', mul_assoc, hτx, ih, ← mul_assoc]
  have hall : ∀ k x, φ (k * x) = k * φ x := by
    intro k x
    rw [← b.sum_repr k, Finset.sum_mul, Finset.sum_mul, map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [smul_mul_assoc, map_smul, smul_mul_assoc, bas_apply, hpow]
  refine ⟨φ 1, ?_⟩
  rw [← hMφ, hlm]
  congr 1
  ext x
  rw [Algebra.coe_lmul_eq_mul, LinearMap.mul_apply']
  rw [mul_comm, ← hall, mul_one]
end GlobalTheory.JR.LinDesc
