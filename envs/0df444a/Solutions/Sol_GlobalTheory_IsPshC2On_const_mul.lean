-- Prove2me | solution 1 for GlobalTheory.IsPshC2On.const_mul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T17:56:07.188826+00:00
-- url     : https://prove2.me/submissions/d801df57-691a-4ad0-9d28-60cd42a50732

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ThetaMetrics_EventuallyDifferentiableAtOfContDiffAtTwo
import Theorems.Thm_GlobalTheory_leviForm_const_mul

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Complex Filter Topology ComplexConjugate
noncomputable section
open GlobalTheory
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [NormedSpace ℝ E]
  [IsScalarTower ℝ ℂ E]
variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F] [NormedSpace ℝ F]
  [IsScalarTower ℝ ℂ F]
variable {G : Type*} [NormedAddCommGroup G] [NormedSpace ℂ G] [NormedSpace ℝ G]
  [IsScalarTower ℝ ℂ G]
variable {u u' : E → ℝ} {s t : Set E}
namespace GlobalTheory
namespace IsPshC2On
theorem _root_.solution (h : IsPshC2On u s) {c : ℝ} (hc : 0 ≤ c) :
    IsPshC2On (fun x => c * u x) s := fun z hz =>
  ⟨contDiffAt_const.mul (h z hz).1, fun v => by
    rw [leviForm_const_mul c (h z hz).1]
    simpa using mul_nonneg hc ((h z hz).2 v)⟩
end IsPshC2On
end GlobalTheory
