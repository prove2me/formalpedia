-- Prove2me | solution 1 for GlobalTheory.alternating_eq_of_equivalent_factors
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T23:42:18.686443+00:00
-- url     : https://prove2.me/submissions/1ea8bc66-c448-4ce9-84c0-e3ee6b15124b

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_EntireApplyEqOfPeriodicOfSpanReal
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaShiftProofs_ExistsEqCexpQuadraticOfEquivalentFactors
import Theorems.Thm_GlobalTheory_exists_continuous_cexp_eq
import Theorems.Thm_GlobalTheory_sub_eq_of_equivalent_factors

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
theorem _root_.solution (p : G → V) (lin₁ lin₂ : G → V →ₗ[ℂ] ℂ)
    (c₁ c₂ : G → ℂ) {f : V → ℂ} (hf : Continuous f) (h0 : ∀ v, f v ≠ 0)
    (h : ∀ g v, cexp (lin₁ g v + c₁ g) * f v = cexp (lin₂ g v + c₂ g) * f (v + p g)) (g g' : G) :
    lin₁ g (p g') - lin₁ g' (p g) = lin₂ g (p g') - lin₂ g' (p g) := by
  obtain ⟨q, hq, hq'⟩ := exists_continuous_cexp_eq hf h0
  have key := sub_eq_of_equivalent_factors p lin₁ lin₂ c₁ c₂ hq (by simpa only [hq'] using h)
  have h1 := key g (p g')
  have h2 := key g' (p g)
  rw [add_comm (p g)] at h2
  linear_combination h2 - h1
end GlobalTheory
