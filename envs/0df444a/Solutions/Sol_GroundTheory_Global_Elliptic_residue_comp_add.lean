-- Prove2me | solution 1 for GroundTheory.Global.Elliptic.residue_comp_add
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T00:28:33.175593+00:00
-- url     : https://prove2.me/submissions/dff58df4-6514-4cbe-b76d-736921671ace

import Mathlib
import Definitions.Def_GroundTheory_GlobalFields_ComplexMultiplication_Residue
import Definitions.Def_GroundTheory_GlobalFields_ComplexMultiplication_RectangleIntegral
import Definitions.Def_GroundTheory_GlobalFields_ComplexMultiplication_ResidueTheorem
import Theorems.Thm_GroundTheory_Global_Elliptic_dslopeIter_comp_add
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
open scoped Interval Real
noncomputable section
open GroundTheory GroundTheory.Global
open GroundTheory.Global.Elliptic
namespace GroundTheory.Global.Elliptic
theorem _root_.solution {f : ℂ → ℂ} {a w₀ : ℂ} (hf : MeromorphicAt f (w₀ + a)) :
    residue (fun w ↦ f (w + a)) w₀ = residue f (w₀ + a) := by
  set n := meromorphicShift f (w₀ + a)
  set G : ℂ → ℂ := fun z ↦ (z - (w₀ + a)) ^ (n + 1) * f z with hGdef
  have hG : AnalyticAt ℂ G (w₀ + a) :=
    analyticAt_pow_mul_of_meromorphicShift_le hf (Nat.le_succ n)
  have e : (fun w ↦ (w - w₀) ^ (n + 1) * f (w + a)) = fun w ↦ G (w + a) := by
    funext w
    simp only [hGdef]
    congr 2
    ring
  have hana : AnalyticAt ℂ (fun w ↦ (w - w₀) ^ (n + 1) * f (w + a)) w₀ := by
    rw [e]
    have : AnalyticAt ℂ (fun w ↦ w + a) w₀ := by fun_prop
    exact hG.comp_of_eq this rfl
  rw [residue_eq_dslopeIter hana, e, dslopeIter_comp_add]
  rfl
end GroundTheory.Global.Elliptic
