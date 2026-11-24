-- Prove2me | solution 1 for GlobalTheory.IsPshC2On.add
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T23:10:04.151824+00:00
-- url     : https://prove2.me/submissions/9e5e0e88-1e24-40cd-83a2-ca58fcd628fb

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ThetaMetrics_EventuallyDifferentiableAtOfContDiffAtTwo
import Theorems.Thm_GlobalTheory_leviForm_add

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
theorem _root_.solution (h : IsPshC2On u s) (h' : IsPshC2On u' s) :
    IsPshC2On (fun x => u x + u' x) s := fun z hz =>
  ⟨(h z hz).1.add (h' z hz).1, fun v => by
    rw [leviForm_add (h z hz).1 (h' z hz).1]
    exact add_nonneg ((h z hz).2 v) ((h' z hz).2 v)⟩
end IsPshC2On
end GlobalTheory
