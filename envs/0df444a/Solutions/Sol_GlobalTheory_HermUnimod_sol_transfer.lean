-- Prove2me | solution 1 for GlobalTheory.HermUnimod.sol_transfer
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T17:29:28.822181+00:00
-- url     : https://prove2.me/submissions/778c6002-365d-491c-a899-011f67d3110f

import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_FourierMatch
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ExistsMulStarEqOfNormOneUnramifiedQuadraticStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_UnramifiedQuadraticIntegralTraceFormPerfectStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_NormOneAddEqOne
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_UnimodularHermitianMatrixCongruentOne

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
open GlobalTheory GlobalTheory.HermUnimod
variable {E : Type} [NormedField E] [IsUltrametricDist E] [StarRing E]
namespace GlobalTheory.HermUnimod
theorem _root_.solution (hs : ∀ y : E, ‖star y‖ = ‖y‖) {n n' : Type} [Fintype n] [DecidableEq n] [Fintype n']
    [DecidableEq n'] (e : n ≃ n') (G : Matrix n n E) (h : Matrix n' n' E) (hi : ∀ i j, ‖h i j‖ ≤ 1)
    (hd : ‖h.det‖ = 1) (hh : hᴴ * reindex e e G * h = 1) :
    ∃ h : Matrix n n E, (∀ i j, ‖h i j‖ ≤ 1) ∧ ‖h.det‖ = 1 ∧ hᴴ * G * h = 1 := by
  refine ⟨reindex e.symm e.symm h, fun i j => hi _ _, by rw [det_reindex_self]; exact hd, ?_⟩
  have : reindex e.symm e.symm (hᴴ * reindex e e G * h) = 1 := by rw [hh]; simp
  rw [← this]
  simp only [reindex_apply, Equiv.symm_symm, conjTranspose_submatrix]
  rw [← submatrix_mul_equiv (hᴴ * _) h e e e, ← submatrix_mul_equiv hᴴ _ e e e]
  simp
end GlobalTheory.HermUnimod
