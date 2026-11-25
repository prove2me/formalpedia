-- Prove2me | solution 1 for GroundTheory.Global.Elliptic.germ_inv
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T00:13:30.344179+00:00
-- url     : https://prove2.me/submissions/f49c70cc-fa3a-4986-9af7-328ce83ad337

import Mathlib
import Definitions.Def_GroundTheory_GlobalFields_ComplexMultiplication_AnalyticAlgebraicGerm
import Theorems.Thm_GroundTheory_Global_Elliptic_germ_eq_zero_iff
import Theorems.Thm_GroundTheory_Global_Elliptic_germ_one

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
set_option synthInstance.maxHeartbeats 400000
-- END pinned source Lake options
set_option autoImplicit false
open Filter Topology Set
noncomputable section
open GroundTheory GroundTheory.Global
open GroundTheory.Global.Elliptic
namespace GroundTheory.Global.Elliptic
theorem _root_.solution {f : ℂ → ℂ} (hf : Meromorphic f) : germ f⁻¹ = (germ f)⁻¹ := by
  by_cases h0 : f =ᶠ[codiscrete ℂ] 0
  · rw [(germ_eq_zero_iff hf).2 h0, inv_zero, germ_eq_zero_iff hf.inv]
    filter_upwards [h0] with z hz
    simp only [Pi.inv_apply, Pi.zero_apply] at hz ⊢
    rw [hz, inv_zero]
  · have hne := eventually_ne_zero_codiscrete hf h0
    have h1 : germ f * germ f⁻¹ = 1 := by
      rw [← germ_mul hf hf.inv, ← germ_one]
      apply germ_congr (hf.mul hf.inv)
      filter_upwards [hne] with z hz
      simp only [Pi.mul_apply, Pi.inv_apply, Pi.one_apply]
      exact mul_inv_cancel₀ hz
    exact (eq_inv_of_mul_eq_one_right h1)
end GroundTheory.Global.Elliptic
