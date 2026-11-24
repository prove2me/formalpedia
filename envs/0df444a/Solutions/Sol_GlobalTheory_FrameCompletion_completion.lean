-- Prove2me | solution 1 for GlobalTheory.FrameCompletion.completion
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T19:37:37.562468+00:00
-- url     : https://prove2.me/submissions/f4c5662b-b1ec-480a-9ca4-f37413a2306f

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_HasLenOfLatLen
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_DoubledLatticePrimitiveIsotropicFrameCompletion
import Theorems.Thm_GlobalTheory_FrameCompletion_isInt_conjT
import Theorems.Thm_GlobalTheory_FrameCompletion_isInt_submatrix
import Theorems.Thm_GlobalTheory_FrameCompletion_isInt_gramQ
import Theorems.Thm_GlobalTheory_FrameCompletion_exists_frame
import Theorems.Thm_Formalism_GradedWeylDivisibility_CoeffHom_mul
import Theorems.Thm_Formalism_UG_P_cartan_exists_glint
import Theorems.Thm_GlobalTheory_InertZeta_IsInt_mul
import Theorems.Thm_GlobalTheory_InertZeta_exists_trace_one
import Theorems.Thm_GlobalTheory_UnitarySwap_antiJ_mul_self


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism.UG Matrix GlobalTheory.InertZeta GlobalTheory.SatakeWeyl
open GlobalTheory GlobalTheory.FrameCompletion
namespace GlobalTheory.FrameCompletion
theorem _root_.solution : Completion := by
  intro L _ _ ϖ σ q n hU g U V C hf
  obtain ⟨τ, hτ, hτ1⟩ := exists_trace_one hU
  obtain ⟨hUi, hVi, hCi, hDi, h5⟩ := hf
  obtain ⟨K, hKi, hKQ, hKx⟩ := exists_frame hU.1 hU.2.1 hτ hτ1 (mat g) U V C g.2 hUi hVi hCi hDi h5
  set e := finSumFinEquiv (m := n) (n := n) with he
  set k := K.submatrix e.symm e.symm with hk
  have hQs : GlobalTheory.Doubling.dblGram e (antiJ L n) = (gramQ L n).submatrix e.symm e.symm := rfl
  have hkQ : cT σ k * GlobalTheory.Doubling.dblGram e (antiJ L n) * k = GlobalTheory.Doubling.dblGram e (antiJ L n) := by
    rw [hQs, hk, show cT σ (K.submatrix e.symm e.symm) = (cT σ K).submatrix e.symm e.symm from rfl,
      submatrix_mul_equiv, submatrix_mul_equiv, hKQ]
  have hQQ : GlobalTheory.Doubling.dblGram e (antiJ L n) * GlobalTheory.Doubling.dblGram e (antiJ L n) = 1 := by
    rw [GlobalTheory.Doubling.dblGram, GlobalTheory.Doubling.blkMat_mul, neg_mul_neg, GlobalTheory.UnitarySwap.antiJ_mul_self,
      GlobalTheory.Doubling.blkMat_one]
  have hinv : GlobalTheory.Doubling.dblGram e (antiJ L n) * cT σ k * GlobalTheory.Doubling.dblGram e (antiJ L n) * k = 1 := by
    rw [Matrix.mul_assoc, Matrix.mul_assoc, ← Matrix.mul_assoc (cT σ k), hkQ, hQQ]
  have hQi : IsInt (GlobalTheory.Doubling.dblGram e (antiJ L n)) := by
    rw [hQs]
    exact isInt_submatrix isInt_gramQ _ _
  have hki : IsInt k := isInt_submatrix hKi _ _
  obtain ⟨W, hW, hWk⟩ := P.cartan_exists_glint (intL L) k _ (mul_eq_one_comm.1 hinv) hki
    ((hQi.mul (isInt_conjT hU.2.1 hki)).mul hQi)
  refine ⟨W, ?_, hW, fun x => ?_⟩
  · show cT σ (W : Matrix (Fin (n + n)) (Fin (n + n)) L) * _ * (W : Matrix (Fin (n + n)) (Fin (n + n)) L) = _
    rw [hWk, hkQ]
  · rw [hWk, hk, GlobalTheory.Doubling.pairVec, GlobalTheory.Doubling.pairVec, submatrix_mulVec_equiv, Equiv.symm_symm, Function.comp_assoc,
      Equiv.symm_comp_self, Function.comp_id, hKx]
end GlobalTheory.FrameCompletion
