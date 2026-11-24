-- Prove2me | solution 1 for GlobalTheory.JR.OKCompact.charpoly_smul_eq_scaleRoots
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T18:08:35.124545+00:00
-- url     : https://prove2.me/submissions/0552ebed-68bd-4f80-a604-c7b131f89d68

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_IsTestRep
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_IsCompactFiniteEtaleHermitianPairOK

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
open GlobalTheory GlobalTheory.JR GlobalTheory.JR.OKCompact
namespace GlobalTheory.JR.OKCompact
theorem _root_.solution {K : Type} [Field K] [Infinite K] {n : ℕ} (M : Matrix (Fin n) (Fin n) K)
    {c : K} (hc : c ≠ 0) : (c • M).charpoly = M.charpoly.scaleRoots c := by
  apply Polynomial.funext
  intro x
  obtain ⟨y, rfl⟩ : ∃ y, x = c * y := ⟨c⁻¹ * x, by rw [← mul_assoc, mul_inv_cancel₀ hc, one_mul]⟩
  rw [Polynomial.scaleRoots_eval_mul, Matrix.charpoly_natDegree_eq_dim, Matrix.eval_charpoly, Matrix.eval_charpoly,
    ← Matrix.det_smul, smul_sub]
  congr 2
  ext a b
  simp only [Matrix.smul_apply, Matrix.scalar_apply, Matrix.diagonal_apply, smul_eq_mul]
  split_ifs <;> simp
end GlobalTheory.JR.OKCompact
