-- Prove2me | solution 1 for GlobalTheory.HermFrame.conn_submatrix_equiv
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T23:40:30.022625+00:00
-- url     : https://prove2.me/submissions/6d58cf28-a3a6-4beb-a8a2-a612c01cd97c

import Mathlib
import Definitions.Def_ReciprocityTheory_AnalyticForms_MaIntEmpty
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ThetaMetrics_EventuallyDifferentiableAtOfContDiffAtTwo
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_LeTwoMulOfForallScale
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_ExtFormAdjEqNegSecondForm

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Complex ComplexConjugate Filter Topology
open scoped ComplexOrder ContDiff
noncomputable section
open GlobalTheory GlobalTheory.HermFrame
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [NormedSpace ℝ E]
  [IsScalarTower ℝ ℂ E]
variable {m n l : Type*}
variable [Fintype m] [Fintype l] [DecidableEq m] [DecidableEq l]
variable {U : Set E} {H : E → Matrix (m ⊕ l) (m ⊕ l) ℂ} {z : E} {k : WithTop ℕ∞}
namespace GlobalTheory.HermFrame
theorem _root_.solution [Fintype n] [DecidableEq n] (K : E → Matrix n n ℂ) (e : m ≃ n)
    (z ξ : E) : conn (fun x => (K x).submatrix e e) z ξ = (conn K z ξ).submatrix e e := by
  rw [conn, conn, ← submatrix_mul_equiv _ _ _ e, transpose_submatrix, inv_submatrix_equiv]
  rfl
end GlobalTheory.HermFrame
