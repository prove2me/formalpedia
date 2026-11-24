-- Prove2me | solution 1 for GlobalTheory.Mem.An.zsymFactor_analyticAt
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T19:19:51.180575+00:00
-- url     : https://prove2.me/submissions/79e3740d-a03a-46df-8104-f57669c4a06b

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_RayPrimes
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_DirichletLZeroSymmetry
import Theorems.Thm_GlobalTheory_Mem_An_zsym_gammaFactor_ne_zero
import Theorems.Thm_GlobalTheory_Mem_An_zsym_differentiable_gammaFactor_inv

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Filter Topology Complex GlobalTheory.Mem.An
open GlobalTheory GlobalTheory.Mem GlobalTheory.Mem.An
variable {q : ℕ}
variable [NeZero q]
namespace GlobalTheory.Mem.An
theorem _root_.solution (χ : DirichletCharacter ℂ q) {s : ℂ}
    (h1 : s.re < 1) : AnalyticAt ℂ (zsymFactor χ) s := by
  have g2 := zsym_gammaFactor_ne_zero χ⁻¹ (s := 1 - s) (by simp; linarith)
  have d1 : Differentiable ℂ (fun s : ℂ => (q : ℂ) ^ ((1 - s) - 1 / 2)) := by
    have : NeZero (q : ℂ) := ⟨by exact_mod_cast NeZero.ne q⟩
    fun_prop
  have d2 : Differentiable ℂ (fun s : ℂ => (χ⁻¹.gammaFactor (1 - s))⁻¹) :=
    (zsym_differentiable_gammaFactor_inv χ⁻¹).comp (differentiable_id.const_sub 1)
  have d3 := (d1.mul_const χ.rootNumber).mul (zsym_differentiable_gammaFactor_inv χ)
  exact (d3.analyticAt s).div (d2.analyticAt s) (inv_ne_zero g2)
end GlobalTheory.Mem.An
