-- Prove2me | solution 1 for GlobalTheory.minorsMatrix_mem_unitaryGroup
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T00:54:16.729851+00:00
-- url     : https://prove2.me/submissions/c6de0c7b-1de8-4c75-8769-e828c6dbaac3

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ThetaMetrics_SmulOneLeAndLeSmulOneIffEigenvalues
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_MaximalMinorsMatrixMemUnitaryGroup
import Theorems.Thm_GlobalTheory_subsetEnum_strictMonoEquivPowersetCard
import Theorems.Thm_GlobalTheory_IsLogBounded_compoundMatrix
import Theorems.Thm_GlobalTheory_IsLogBounded_det
import Theorems.Thm_GlobalTheory_compoundMatrix_conjTranspose
import Theorems.Thm_GlobalTheory_compoundMatrix_mul
import Theorems.Thm_GlobalTheory_compoundMatrix_one


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix
open scoped Classical
open GlobalTheory
namespace GlobalTheory
theorem _root_.solution : ∀ {N a : ℕ} (M : Matrix (Fin N) (Fin N) ℂ),
    M ∈ Matrix.unitaryGroup (Fin N) ℂ →
    (Matrix.of fun s s' : {s : Fin a → Fin N // StrictMono s} =>
      (Matrix.of fun i i' : Fin a => M (s'.1 i') (s.1 i)).det) ∈
      Matrix.unitaryGroup {s : Fin a → Fin N // StrictMono s} ℂ := by
  intro N a M hM
  set e := strictMonoEquivPowersetCard a (Fin N)
  have hC : (Matrix.of fun s s' : {s : Fin a → Fin N // StrictMono s} =>
      (Matrix.of fun i i' : Fin a => M (s'.1 i') (s.1 i)).det) =
      (compoundMatrix a Mᵀ).submatrix e e := by
    ext s s'
    have he : ∀ s, subsetEnum (e s) = s.1 := subsetEnum_strictMonoEquivPowersetCard a
    simp only [submatrix_apply, compoundMatrix, of_apply, he]
    rfl
  have hT : Mᵀ * (Mᵀ)ᴴ = 1 := by
    rw [mem_unitaryGroup_iff'] at hM
    have h1 : Mᵀ * (Mᵀ)ᴴ = (star M * M)ᵀ := by
      ext i j
      simp [mul_apply, mul_comm]
    rw [h1, hM, transpose_one]
  rw [hC, mem_unitaryGroup_iff, star_eq_conjTranspose, conjTranspose_submatrix,
    submatrix_mul_equiv, ← compoundMatrix_conjTranspose, ← compoundMatrix_mul, hT,
    compoundMatrix_one, submatrix_one_equiv]
end GlobalTheory
