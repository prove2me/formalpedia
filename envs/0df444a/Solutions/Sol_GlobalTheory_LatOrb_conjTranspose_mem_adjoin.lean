-- Prove2me | solution 1 for GlobalTheory.LatOrb.conjTranspose_mem_adjoin
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T00:48:03.457296+00:00
-- url     : https://prove2.me/submissions/b61746cc-a436-4bd4-a688-aa7bc9f4cbc5

import Mathlib
import Definitions.Def_Formalism_SatakeDualWeyl_Statement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_MemMatLat
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_IntegralAevalEqAevalMapOfCoprimeCharpolyStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_IsIntegralMatrixOfMapsToFullRankLatticeStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsUnitaryMulIntegralOfNormMaximalOrderUnitStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsUnitaryAdjoinLatticeImageEq
import Theorems.Thm_GlobalTheory_LatOrb_exists_mul_eq_one_mem
import Theorems.Thm_GlobalTheory_FormalIsogeny_FiniteReduction_map
import Theorems.Thm_GlobalTheory_constDerivEval_X
import Theorems.Thm_GlobalTheory_mvEvalAdic_C
import Theorems.Thm_GlobalTheory_mvEvalAdic_X
import Theorems.Thm_GlobalTheory_mvEvalAdic_coe
import Theorems.Thm_GlobalTheory_pderivEval_X
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.constDerivEval_X
attribute [local simp] GlobalTheory.mvEvalAdic_C
attribute [local simp] GlobalTheory.mvEvalAdic_X
attribute [local simp] GlobalTheory.mvEvalAdic_coe
attribute [local simp] GlobalTheory.pderivEval_X



set_option autoImplicit false
open Polynomial Matrix GlobalTheory.LatOrb
noncomputable section
open GlobalTheory GlobalTheory.LatOrb
variable {K : Type} [Field K] {n : ℕ}
namespace GlobalTheory.LatOrb
theorem _root_.solution (σ : K →+* K) (γ : Matrix (Fin n) (Fin n) K)
    (hγ : (γ.map σ)ᵀ * γ = 1) {a : Matrix (Fin n) (Fin n) K} (ha : a ∈ Algebra.adjoin K {γ}) :
    (a.map σ)ᵀ ∈ Algebra.adjoin K {γ} := by
  induction ha using Algebra.adjoin_induction with
  | mem x hx =>
    rw [Set.mem_singleton_iff] at hx
    subst hx
    obtain ⟨b, hbm, hb⟩ := exists_mul_eq_one_mem (Algebra.adjoin K {x}) (Algebra.subset_adjoin rfl)
      (fun b hb => by rw [← Matrix.one_mul b, ← hγ, Matrix.mul_assoc, hb, Matrix.mul_zero])
    have : (x.map σ)ᵀ = b := by
      calc (x.map σ)ᵀ = (x.map σ)ᵀ * (x * b) := by rw [hb, Matrix.mul_one]
        _ = b := by rw [← Matrix.mul_assoc, hγ, Matrix.one_mul]
    rw [this]; exact hbm
  | algebraMap r =>
    have : ((algebraMap K (Matrix (Fin n) (Fin n) K) r).map σ)ᵀ =
        algebraMap K (Matrix (Fin n) (Fin n) K) (σ r) := by
      ext i j
      simp only [Matrix.transpose_apply, Matrix.map_apply, Matrix.algebraMap_matrix_apply]
      by_cases h : i = j
      · subst h; simp
      · simp [h, Ne.symm h]
    rw [this]; exact Subalgebra.algebraMap_mem _ _
  | add x y _ _ hx hy =>
    rw [Matrix.map_add _ (map_add σ), Matrix.transpose_add]; exact add_mem hx hy
  | mul x y _ _ hx hy =>
    rw [Matrix.map_mul, Matrix.transpose_mul]; exact mul_mem hy hx
end GlobalTheory.LatOrb
