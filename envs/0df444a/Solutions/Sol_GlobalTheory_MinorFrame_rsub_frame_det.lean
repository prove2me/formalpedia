-- Prove2me | solution 1 for GlobalTheory.MinorFrame.rsub_frame_det
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T22:30:27.439447+00:00
-- url     : https://prove2.me/submissions/e931f4f7-8bca-48aa-a78a-b9f00a8a24e9

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_DetGNeZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_SumNormRowSubProdMinors
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_CauchyBinetColumnFrameProdDetPowEqSum
import Theorems.Thm_GlobalTheory_MinorFrame_eval_minorAt_frame
import Theorems.Thm_GlobalTheory_MinorFrame_rsub_frame_X
import Theorems.Thm_Formalism_GradedWeylDivisibility_rowDivL_apply
import Theorems.Thm_Formalism_HC_Frame_iotaInv_iota
import Theorems.Thm_Formalism_HC_Frame_iota_iotaInv
import Theorems.Thm_GlobalTheory_MinorFrame_det_mul_eq_sum_sm
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.GradedWeylDivisibility.rowDivL_apply
attribute [local simp] Formalism.HC.Frame.iotaInv_iota
attribute [local simp] Formalism.HC.Frame.iota_iotaInv



set_option autoImplicit false
open Classical MvPolynomial
noncomputable section
noncomputable section
open GlobalTheory GlobalTheory.MinorFrame
open scoped Matrix
variable {ι : Type} [Fintype ι]
namespace GlobalTheory.MinorFrame
theorem _root_.solution {a d : ℕ} (x₀ : Var ι d a → ℂ) (τ : ι) :
    rsub (frameMat x₀)ᴴ ((Matrix.of fun i j : Fin a => (X (τ, i, j) : MvPolynomial (ι × Fin a × Fin a) ℂ)).det) =
      ∑ s : {s : Fin a → Fin d // StrictMono s}, C (star (eval x₀ (minorAt τ s.1))) * minorAt τ s.1 := by
  rw [AlgHom.map_det]
  set A : Matrix (Fin d) (Fin a) ℂ := Matrix.of fun (r : Fin d) (i : Fin a) => x₀ (τ, r, i) with hA
  have hM : (rsub (frameMat x₀)ᴴ : MvPolynomial (ι × Fin a × Fin a) ℂ →ₐ[ℂ] Pol ι d a).mapMatrix
      (Matrix.of fun i j : Fin a => (X (τ, i, j) : MvPolynomial (ι × Fin a × Fin a) ℂ)) =
      (Aᴴ.map (C : ℂ →+* Pol ι d a)) * xMat τ d a := by
    ext i j
    simp [rsub_frame_X, xMat, Matrix.mul_apply, hA, Matrix.conjTranspose_apply]
  rw [hM, det_mul_eq_sum_sm]
  refine Finset.sum_congr rfl fun s _ => ?_
  congr 1
  · rw [eval_minorAt_frame, ← hA, Matrix.submatrix_map, ← Matrix.det_conjTranspose, Matrix.conjTranspose_submatrix]
    exact (RingHom.map_det _ _).symm
end GlobalTheory.MinorFrame
