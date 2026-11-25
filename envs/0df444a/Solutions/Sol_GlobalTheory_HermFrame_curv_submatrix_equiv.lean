-- Prove2me | solution 1 for GlobalTheory.HermFrame.curv_submatrix_equiv
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T17:48:43.899925+00:00
-- url     : https://prove2.me/submissions/cc3b6439-f65a-4aa5-a038-932d29f14756

import Mathlib
import Definitions.Def_ReciprocityTheory_AnalyticForms_MaIntEmpty
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ThetaMetrics_EventuallyDifferentiableAtOfContDiffAtTwo
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_LeTwoMulOfForallScale
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_ExtFormAdjEqNegSecondForm
import Theorems.Thm_GlobalTheory_HermFrame_conn_submatrix_equiv
import Theorems.Thm_GlobalTheory_HermFrame_opNorm_zero
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.HermFrame.opNorm_zero



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
    (z ξ η : E) : curv (fun x => (K x).submatrix e e) z ξ η = (curv K z ξ η).submatrix e e := by
  simp only [curv, conn_submatrix_equiv]
  rfl
end GlobalTheory.HermFrame
