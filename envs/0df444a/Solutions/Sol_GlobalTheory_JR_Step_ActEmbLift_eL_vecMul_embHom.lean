-- Prove2me | solution 1 for GlobalTheory.JR.Step.ActEmbLift.eL_vecMul_embHom
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T18:09:48.544745+00:00
-- url     : https://prove2.me/submissions/70470e26-9c2d-4959-ae55-712654fef268

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_NormMulApplyLeOne
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_BorderedConjugationDiagOneLiftBlockMatrix

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
open GlobalTheory GlobalTheory.JR GlobalTheory.JR.Step GlobalTheory.JR.Step.ActEmbLift
namespace GlobalTheory.JR.Step.ActEmbLift
theorem _root_.solution (k : Type) [CommRing k] (r : ℕ) (g : Matrix (Fin r) (Fin r) k) :
    eL r k ᵥ* embHom r k g = eL r k := by
  ext i
  simp only [embHom, MonoidHom.coe_mk, OneHom.coe_mk, eL, Matrix.reindex_apply]
  rw [Matrix.single_one_vecMul]
  refine Fin.lastCases ?_ (fun j => ?_) i
  · simp [Matrix.submatrix_apply, finSumFinEquiv_symm_last]
  · simp [Matrix.submatrix_apply, finSumFinEquiv_symm_last, finSumFinEquiv_symm_apply_castSucc]
end GlobalTheory.JR.Step.ActEmbLift
