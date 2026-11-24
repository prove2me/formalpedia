-- Prove2me | solution 1 for GlobalTheory.JR.Step.glNormal_of_ne_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T18:50:22.986834+00:00
-- url     : https://prove2.me/submissions/c3dbcc24-7cb8-4baf-9aa0-c7e4cf52130e

import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_FullToGlIsSelfAdjoint
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ExistsGlConjugateLastBasisNormalFormOfNeZero
import Theorems.Thm_GlobalTheory_JR_Step_full_blocks
import Theorems.Thm_GlobalTheory_JR_Step_nfMat_injective
import Theorems.Thm_GlobalTheory_JR_Step_eL_vecMul_nfMat
import Theorems.Thm_GlobalTheory_JR_Step_shiftCompanionLastRowMatrix_mulVec_firstBasis

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.JR Matrix MeasureTheory Filter Topology
open GlobalTheory GlobalTheory.JR GlobalTheory.JR.Step
namespace GlobalTheory.JR.Step
theorem _root_.solution : ∀ (k : Type) [Field k] (r : ℕ) (a : Inv (r + 1) k), a.2.1 0 ≠ 0 →
    ∃ (g : GL (Fin (r + 1)) k) (Z : Gl r k), act g (sec a) = GlobalTheory.JR.Step.lift Z (a.2.1 0) a.2.2 := by
  intro k _ r a h0
  have hu : IsUnit (GlobalTheory.JR.Step.nfMat a.2.1) :=
    Matrix.mulVec_injective_iff_isUnit.mp (GlobalTheory.JR.Step.nfMat_injective a.2.1 h0)
  refine ⟨hu.unit, GlobalTheory.JR.Step.blocks ((hu.unit : Matrix _ _ k) * companion a.1 * ((hu.unit⁻¹ : GL (Fin (r + 1)) k) : Matrix _ _ k)), ?_⟩
  have hg : ((hu.unit : GL (Fin (r + 1)) k) : Matrix _ _ k) = GlobalTheory.JR.Step.nfMat a.2.1 := rfl
  have hinv : GlobalTheory.JR.Step.eL r k ᵥ* (GlobalTheory.JR.Step.nfMat a.2.1) = a.2.1 := GlobalTheory.JR.Step.eL_vecMul_nfMat a.2.1
  unfold act sec GlobalTheory.JR.Step.lift
  refine Prod.ext ?_ (Prod.ext ?_ (Prod.ext ?_ rfl))
  · exact (GlobalTheory.JR.Step.full_blocks _).symm
  · simp only [hg]; exact GlobalTheory.JR.Step.shiftCompanionLastRowMatrix_mulVec_firstBasis a.2.1
  · show a.2.1 ᵥ* _ = _
    have hgi : GlobalTheory.JR.Step.nfMat a.2.1 * ((hu.unit⁻¹ : GL (Fin (r + 1)) k) : Matrix (Fin (r + 1)) (Fin (r + 1)) k) = 1 := by
      exact hu.unit.mul_inv
    have e : (GlobalTheory.JR.Step.eL r k ᵥ* GlobalTheory.JR.Step.nfMat a.2.1) ᵥ*
        ((hu.unit⁻¹ : GL (Fin (r + 1)) k) : Matrix (Fin (r + 1)) (Fin (r + 1)) k) = GlobalTheory.JR.Step.eL r k := by
      rw [Matrix.vecMul_vecMul, hgi, Matrix.vecMul_one]
    rw [hinv] at e
    exact e
end GlobalTheory.JR.Step
