-- Prove2me | solution 1 for GlobalTheory.LatticeCovolumeL2.det_compl
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T00:02:16.262675+00:00
-- url     : https://prove2.me/submissions/a713941e-1143-4652-b710-86869da13263

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaShiftProofs_ExistsLineBasis

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.LatticeCovolumeL2
open NumberField Matrix
namespace GlobalTheory.LatticeCovolumeL2
theorem _root_.solution {n : Type} [Fintype n] [DecidableEq n] (M Y : Matrix n n ℝ) (h : M * Y = 1) (p : n → Prop)
    [DecidablePred p] :
    (toSquareBlockProp Y (fun k => ¬ p k)).det = (toSquareBlockProp M p).det * Y.det := by
  let Z : Matrix n n ℝ := fun i k => if p k then (1 : Matrix n n ℝ) i k else Y i k
  have hMZ : ∀ i k, (M * Z) i k = if p k then M i k else (1 : Matrix n n ℝ) i k := by
    intro i k
    by_cases hk : p k
    · simp only [hk, if_true]
      rw [Matrix.mul_apply]
      simp [Z, hk, Matrix.one_apply]
    · simp only [hk, if_false]
      rw [← h, Matrix.mul_apply, Matrix.mul_apply]
      simp [Z, hk]
  have hZ : Z.det = (toSquareBlockProp Y (fun k => ¬ p k)).det := by
    rw [Matrix.twoBlockTriangular_det Z p]
    · have h1 : toSquareBlockProp Z p = 1 := by
        ext i j
        change Z i j = _
        simp [Z, j.2, Matrix.one_apply, Subtype.ext_iff]
      have h2 : toSquareBlockProp Z (fun k => ¬ p k) = toSquareBlockProp Y (fun k => ¬ p k) := by
        ext i j
        change Z i j = Y i j
        simp [Z, j.2]
      rw [h1, h2, det_one, one_mul]
    · intro i hi j hj
      have hij : i ≠ j := fun e => hi (e ▸ hj)
      simp [Z, hj, Matrix.one_apply, hij]
  have hMZd : (M * Z).det = (toSquareBlockProp M p).det := by
    rw [← det_transpose, Matrix.twoBlockTriangular_det (M * Z)ᵀ p]
    · have h1 : toSquareBlockProp (M * Z)ᵀ p = (toSquareBlockProp M p)ᵀ := by
        ext i j
        change (M * Z) j i = M j i
        rw [hMZ]
        simp [i.2]
      have h2 : toSquareBlockProp (M * Z)ᵀ (fun k => ¬ p k) = 1 := by
        ext i j
        change (M * Z) j i = if i = j then 1 else 0
        rw [hMZ]
        simp [i.2, Matrix.one_apply, Subtype.ext_iff, eq_comm]
      rw [h1, h2, det_one, mul_one, det_transpose]
    · intro i hi j hj
      have hji : j ≠ i := fun e => hi (e ▸ hj)
      simp [hMZ, hi, hji]
  have hdet : M.det * Y.det = 1 := by rw [← det_mul, h, det_one]
  rw [← hMZd, det_mul, hZ]
  linear_combination (-(toSquareBlockProp Y (fun k => ¬ p k)).det) * hdet
end GlobalTheory.LatticeCovolumeL2
