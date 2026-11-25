-- Prove2me | solution 1 for GroundTheory.Global.Elliptic.residue_comp_mul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T00:28:33.882306+00:00
-- url     : https://prove2.me/submissions/326531b1-3119-4cf0-8c8d-a8f5f94be5ad

import Mathlib
import Definitions.Def_GroundTheory_GlobalFields_ComplexMultiplication_Residue
import Theorems.Thm_GroundTheory_Global_Elliptic_dslopeIter_const_mul
import Theorems.Thm_GroundTheory_Global_Elliptic_analyticAt_pow_mul_of_meromorphicShift_le
import Theorems.Thm_GroundTheory_Global_Elliptic_residue_eq_dslopeIter
import Theorems.Thm_GroundTheory_Global_Elliptic_dslopeIter_comp_mul

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
theorem _root_.solution {f : ℂ → ℂ} {c w₀ : ℂ} (hc : c ≠ 0) (hf : MeromorphicAt f (c * w₀)) :
    residue (fun w ↦ f (c * w)) w₀ = c⁻¹ * residue f (c * w₀) := by
  set n := meromorphicShift f (c * w₀)
  set G : ℂ → ℂ := fun z ↦ (z - c * w₀) ^ (n + 1) * f z with hGdef
  have hG : AnalyticAt ℂ G (c * w₀) := analyticAt_pow_mul_of_meromorphicShift_le hf (Nat.le_succ n)
  have e : (fun w ↦ (w - w₀) ^ (n + 1) * f (c * w)) = fun w ↦ c⁻¹ ^ (n + 1) * G (c * w) := by
    funext w
    simp only [hGdef]
    rw [← mul_assoc, ← mul_pow]
    congr 2
    field_simp
  have hcomp : AnalyticAt ℂ (fun w ↦ G (c * w)) w₀ := by
    have : AnalyticAt ℂ (fun w ↦ c * w) w₀ := by fun_prop
    exact hG.comp_of_eq this rfl
  have hana : AnalyticAt ℂ (fun w ↦ (w - w₀) ^ (n + 1) * f (c * w)) w₀ := by
    rw [e]
    exact analyticAt_const.mul hcomp
  rw [residue_eq_dslopeIter hana, e, dslopeIter_const_mul, dslopeIter_comp_mul hc hG]
  have : residue f (c * w₀) = dslopeIter (c * w₀) n G (c * w₀) := rfl
  rw [this, inv_pow, pow_succ]
  field_simp
end GroundTheory.Global.Elliptic
