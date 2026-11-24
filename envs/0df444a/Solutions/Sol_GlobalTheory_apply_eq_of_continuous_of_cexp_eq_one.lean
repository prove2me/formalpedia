-- Prove2me | solution 1 for GlobalTheory.apply_eq_of_continuous_of_cexp_eq_one
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T22:22:56.320543+00:00
-- url     : https://prove2.me/submissions/7e8a2b0e-ac8f-4078-a79d-69a9740ce5a1

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_EntireApplyEqOfPeriodicOfSpanReal
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaShiftProofs_ExistsEqCexpQuadraticOfEquivalentFactors

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
variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V]
namespace GlobalTheory
theorem _root_.solution {X : Type*} [TopologicalSpace X]
    [PreconnectedSpace X] {φ : X → ℂ} (hφ : Continuous φ) (h : ∀ x, cexp (φ x) = 1) (x y : X) :
    φ x = φ y := by
  have hc : (range φ).Countable := by
    refine (countable_range fun n : ℤ => (n : ℂ) * (2 * Real.pi * I)).mono ?_
    rintro _ ⟨z, rfl⟩
    obtain ⟨n, hn⟩ := exp_eq_one_iff.1 (h z)
    exact ⟨n, hn.symm⟩
  exact hc.isTotallyDisconnected _ Subset.rfl (isPreconnected_range hφ) ⟨x, rfl⟩ ⟨y, rfl⟩
end GlobalTheory
