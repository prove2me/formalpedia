-- Prove2me | solution 1 for GlobalTheory.JR.GLift.exists_emb_of_last
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T17:58:45.418296+00:00
-- url     : https://prove2.me/submissions/4c8cf265-b4bf-4407-be7d-dc17164d67ae

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_NormMulApplyLeOne
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_NormSubLeMaxUltra
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ExistsIntegralGLMulDiagOneOfUnitIndicatorLiftNeZ

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
open GlobalTheory GlobalTheory.JR GlobalTheory.JR.GLift
namespace GlobalTheory.JR.GLift
theorem _root_.solution {F : Type} [Field F] (r : ℕ) (m : GL (Fin (r + 1)) F)
    (hc : (m : Matrix _ _ F) *ᵥ GlobalTheory.JR.Step.eL r F = GlobalTheory.JR.Step.eL r F)
    (hr : GlobalTheory.JR.Step.eL r F ᵥ* (m : Matrix _ _ F) = GlobalTheory.JR.Step.eL r F) :
    ∃ s : GL (Fin r) F, m = GlobalTheory.JR.Step.emb r F s := by
  classical
  set t : Matrix (Fin r) (Fin r) F := (m : Matrix _ _ F).submatrix Fin.castSucc Fin.castSucc with ht
  have hcol : ∀ i, (m : Matrix _ _ F) i (Fin.last r) = (Pi.single (Fin.last r) (1 : F) : Fin (r + 1) → F) i := by
    intro i
    have := congrFun hc i
    simpa [GlobalTheory.JR.Step.eL, Matrix.mulVec_single_one] using this
  have hrow : ∀ j, (m : Matrix _ _ F) (Fin.last r) j = (Pi.single (Fin.last r) (1 : F) : Fin (r + 1) → F) j := by
    intro j
    have := congrFun hr j
    simpa [GlobalTheory.JR.Step.eL, Matrix.single_one_vecMul] using this
  have hm : (m : Matrix _ _ F) = GlobalTheory.JR.Step.embHom r F t := by
    ext i j
    induction i using Fin.lastCases with
    | last =>
      rw [hrow j]
      induction j using Fin.lastCases with
      | last => simp [GlobalTheory.JR.Step.embHom]
      | cast j => simp [GlobalTheory.JR.Step.embHom, Fin.castSucc_ne_last]
    | cast i =>
      induction j using Fin.lastCases with
      | last => rw [hcol]; simp [GlobalTheory.JR.Step.embHom, Fin.castSucc_ne_last]
      | cast j => simp [GlobalTheory.JR.Step.embHom, ht]
  have hdet : (m : Matrix (Fin (r + 1)) (Fin (r + 1)) F).det = t.det := by
    rw [hm]
    simp [GlobalTheory.JR.Step.embHom, Matrix.det_fromBlocks_zero₂₁]
  have hu : IsUnit t.det := by
    rw [← hdet]
    exact (Matrix.isUnit_iff_isUnit_det (m : Matrix (Fin (r + 1)) (Fin (r + 1)) F)).mp (Units.isUnit m)
  refine ⟨Matrix.nonsingInvUnit t hu, ?_⟩
  ext : 1
  rw [hm]
  rfl
end GlobalTheory.JR.GLift
