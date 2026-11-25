-- Prove2me | solution 1 for GlobalTheory.HermFrame.mdbar_inv
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T23:48:01.221788+00:00
-- url     : https://prove2.me/submissions/ee10cf33-3cc6-4c87-8dba-67b69e1e8985

import Mathlib
import Definitions.Def_ReciprocityTheory_AnalyticForms_MaIntEmpty
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ThetaMetrics_EventuallyDifferentiableAtOfContDiffAtTwo
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_LeTwoMulOfForallScale
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_ExtFormAdjEqNegSecondForm
import Theorems.Thm_GlobalTheory_HermFrame_mdbar_mul
import Theorems.Thm_GlobalTheory_IsPshC2On_mono


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
variable {A B : E → Matrix m n ℂ} {z : E} {j k : WithTop ℕ∞}
namespace GlobalTheory.HermFrame
theorem _root_.solution [Fintype n] [DecidableEq n] {A : E → Matrix n n ℂ} (h : MContDiffAt 1 A z)
    (hu : IsUnit (A z).det) (ξ : E) :
    mdbar (fun x => (A x)⁻¹) z ξ = -((A z)⁻¹ * mdbar A z ξ * (A z)⁻¹) := by
  have h1 := mdbar_mul h (h.inv hu) ξ
  rw [mdbar_congr (B := fun _ => 1)
      ((h.eventually_isUnit hu).mono fun x hx => mul_nonsing_inv _ hx),
    mdbar_const, eq_comm, add_eq_zero_iff_eq_neg] at h1
  rw [Matrix.mul_assoc, ← Matrix.mul_neg, ← h1, nonsing_inv_mul_cancel_left _ _ hu]
end GlobalTheory.HermFrame
