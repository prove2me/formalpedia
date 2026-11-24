-- Prove2me | solution 1 for GlobalTheory.isFreeRingAction_arrow
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T23:02:32.808403+00:00
-- url     : https://prove2.me/submissions/fdc202b6-1dd7-458e-8a06-a767eec15b45

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_ExistsUnitSmulEqOfBijectiveToSpanSingleton
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_IsFreeRingActionIffInertiaEqBotOfIsPrime
import Theorems.Thm_GlobalTheory_FreeQuotient_coe_toInvariantsTensor
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.FreeQuotient.coe_toInvariantsTensor

set_option autoImplicit false
open scoped TensorProduct
open GlobalTheory
universe w v u
open CategoryTheory
namespace GlobalTheory
theorem _root_.solution (G R : Type*) [Group G] [Finite G] [CommRing R]
    [MulSemiringAction G (G → R)] (hact : ∀ (g : G) (f : G → R) (x : G), (g • f) x = f (g⁻¹ * x)) :
    IsFreeRingAction G (G → R) := by
  classical
  cases nonempty_fintype G
  intro g hg
  rw [Ideal.eq_top_iff_one, ← Finset.univ_sum_single (1 : G → R)]
  refine Ideal.sum_mem _ fun x _ ↦ ?_
  have : (Pi.single x ((1 : G → R) x) : G → R) =
      Pi.single x 1 * (g • (Pi.single (g⁻¹ * x) 1 : G → R) - Pi.single (g⁻¹ * x) 1) := by
    funext y
    by_cases hy : y = x
    · subst hy
      have : y ≠ g⁻¹ * y := fun h ↦ hg (by simpa using h)
      simp [hact, this]
    · simp [hy]
  rw [this]
  exact Ideal.mul_mem_left _ _ (Ideal.subset_span ⟨_, rfl⟩)
end GlobalTheory
