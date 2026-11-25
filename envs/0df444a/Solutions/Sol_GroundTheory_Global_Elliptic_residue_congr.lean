-- Prove2me | solution 1 for GroundTheory.Global.Elliptic.residue_congr
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T00:27:33.083725+00:00
-- url     : https://prove2.me/submissions/7373fdbc-8642-4c68-890b-9ff83c65e6d5

import Mathlib
import Definitions.Def_GroundTheory_GlobalFields_ComplexMultiplication_Residue
import Theorems.Thm_GroundTheory_Global_Elliptic_dslopeIter_congr
import Theorems.Thm_GroundTheory_Global_Elliptic_analyticAt_pow_mul_of_meromorphicShift_le
import Theorems.Thm_GroundTheory_Global_Elliptic_residue_eq_dslopeIter

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
set_option synthInstance.maxHeartbeats 400000
-- END pinned source Lake options
set_option autoImplicit false
open Complex Filter Topology Set
noncomputable section
open GroundTheory GroundTheory.Global
open GroundTheory.Global.Elliptic
namespace GroundTheory.Global.Elliptic
theorem _root_.solution {f₁ f₂ : ℂ → ℂ} {p : ℂ} (hf₁ : MeromorphicAt f₁ p)
    (h : f₁ =ᶠ[𝓝[≠] p] f₂) : residue f₁ p = residue f₂ p := by
  set n := meromorphicShift f₁ p + 1
  have h₁ : AnalyticAt ℂ (fun z ↦ (z - p) ^ (n + 1) * f₁ z) p :=
    analyticAt_pow_mul_of_meromorphicShift_le hf₁ (by omega)
  have heq : (fun z ↦ (z - p) ^ (n + 1) * f₁ z) =ᶠ[𝓝 p] fun z ↦ (z - p) ^ (n + 1) * f₂ z := by
    rw [EventuallyEq, eventually_nhdsWithin_iff] at h
    filter_upwards [h] with z hz
    rcases eq_or_ne z p with rfl | hzp
    · simp
    · rw [hz hzp]
  rw [residue_eq_dslopeIter h₁, residue_eq_dslopeIter (h₁.congr heq)]
  exact (dslopeIter_congr heq n).eq_of_nhds
end GroundTheory.Global.Elliptic
