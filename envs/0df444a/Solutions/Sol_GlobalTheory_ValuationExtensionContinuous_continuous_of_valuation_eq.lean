-- Prove2me | solution 1 for GlobalTheory.ValuationExtensionContinuous.continuous_of_valuation_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T22:10:32.711039+00:00
-- url     : https://prove2.me/submissions/b9a7a08e-2ea2-48ff-94ba-ecb4ecafffe9

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SatakeParameters_ContinuousOfValuationEq

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open IsDedekindDomain Topology
open GlobalTheory GlobalTheory.ValuationExtensionContinuous
namespace GlobalTheory.ValuationExtensionContinuous
theorem _root_.solution {A B Γ : Type} [Ring A] [Ring B]
    [LinearOrderedCommGroupWithZero Γ] [Valued A Γ] [Valued B Γ]
    (hs : Function.Surjective (Valued.v : A → Γ)) (g : A →+* B)
    (hg : ∀ a, Valued.v (g a) = (Valued.v a : Γ)) : Continuous g := by
  refine continuous_of_continuousAt_zero g ?_
  rw [ContinuousAt, map_zero, (Valued.hasBasis_nhds_zero A Γ).tendsto_iff
    (Valued.hasBasis_nhds_zero B Γ)]
  intro γ _
  obtain ⟨k, hk⟩ := hs (MonoidWithZeroHom.ValueGroup₀.embedding γ.1)
  have hk0 : (Valued.v k : Γ) ≠ 0 := by
    rw [hk]
    exact (map_ne_zero _).mpr γ.ne_zero
  have hk1 : (Valued.v : Valuation A Γ).restrict k ≠ 0 := by simpa using hk0
  refine ⟨Units.mk0 _ hk1, trivial, fun x hx => ?_⟩
  simp only [Set.mem_setOf_eq, Units.val_mk0, Valuation.restrict_lt_iff] at hx
  simp only [Set.mem_setOf_eq]
  rw [Valuation.restrict_lt_iff_lt_embedding, hg, ← hk]
  exact hx
end GlobalTheory.ValuationExtensionContinuous
