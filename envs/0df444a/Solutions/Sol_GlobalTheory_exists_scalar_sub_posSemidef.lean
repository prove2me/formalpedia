-- Prove2me | solution 1 for GlobalTheory.exists_scalar_sub_posSemidef
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T22:46:57.927871+00:00
-- url     : https://prove2.me/submissions/a9af1a74-1509-4fa1-96a5-0ee8adfd6f4b

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TorusHaarMeasure_ExistsScalarSubPosSemidef

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Topology Matrix
open scoped ComplexOrder ENNReal Pointwise
open GlobalTheory
open scoped MatrixOrder Matrix.Norms.L2Operator
namespace GlobalTheory
theorem _root_.solution {r : ℕ} (A : Matrix (Fin r) (Fin r) ℂ) (hA : A.IsHermitian) :
    ∃ c : ℝ, 1 ≤ c ∧ ((c : ℂ) • (1 : Matrix (Fin r) (Fin r) ℂ) - A).PosSemidef := by
  have h1 : (‖A‖ • (1 : Matrix (Fin r) (Fin r) ℂ) - A).PosSemidef := by
    have h := IsSelfAdjoint.le_algebraMap_norm_self (a := A) hA
    rw [Algebra.algebraMap_eq_smul_one] at h
    exact Matrix.le_iff.1 h
  refine ⟨1 + ‖A‖, by linarith [norm_nonneg A], ?_⟩
  have e : ((1 + ‖A‖ : ℝ) : ℂ) • (1 : Matrix (Fin r) (Fin r) ℂ) - A =
      1 + (‖A‖ • (1 : Matrix (Fin r) (Fin r) ℂ) - A) := by
    rw [Complex.coe_smul, add_smul, one_smul, add_sub_assoc]
  rw [e]
  exact Matrix.PosSemidef.one.add h1
end GlobalTheory
