-- Prove2me | solution 1 for GlobalTheory.sub_eq_of_equivalent_factors
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T23:35:30.573873+00:00
-- url     : https://prove2.me/submissions/fa325310-1c62-42e4-a17b-c6f63ea093a9

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_EntireApplyEqOfPeriodicOfSpanReal
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaShiftProofs_ExistsEqCexpQuadraticOfEquivalentFactors
import Theorems.Thm_GlobalTheory_apply_eq_of_continuous_of_cexp_eq_one

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Set Filter Topology Complex
open GlobalTheory
variable {V G : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V] [FiniteDimensional ℂ V]
namespace GlobalTheory
theorem _root_.solution (p : G → V) (lin₁ lin₂ : G → V →ₗ[ℂ] ℂ) (c₁ c₂ : G → ℂ)
    {q : V → ℂ} (hq : Continuous q)
    (h : ∀ g v, cexp (lin₁ g v + c₁ g) * cexp (q v) =
      cexp (lin₂ g v + c₂ g) * cexp (q (v + p g))) (g : G) (v : V) :
    q (v + p g) - q v = lin₁ g v - lin₂ g v + (q (p g) - q 0) := by
  have h1 := (lin₁ g).continuous_of_finiteDimensional
  have h2 := (lin₂ g).continuous_of_finiteDimensional
  have := apply_eq_of_continuous_of_cexp_eq_one
    (φ := fun v => lin₁ g v + c₁ g + q v - (lin₂ g v + c₂ g + q (v + p g))) (by fun_prop)
    (fun v => by rw [← exp_eq_exp_iff_exp_sub_eq_one, exp_add _ (q v), h, ← exp_add]) v 0
  simp only [map_zero, zero_add] at this
  linear_combination -this
end GlobalTheory
