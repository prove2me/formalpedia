-- Prove2me | solution 1 for GlobalTheory.DoubleCosetIndicator.main
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T17:41:20.646778+00:00
-- url     : https://prove2.me/submissions/82ce11ac-2680-49e6-be67-3f0283213358

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_ExistsEqSumIndicator
import Theorems.Thm_GlobalTheory_DoubleCosetIndicator_exists_eq_sum_indicator

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.DoubleCosetIndicator
namespace GlobalTheory.DoubleCosetIndicator
theorem _root_.solution : (let d1 : {G : Type} → [inst : Group G] → Subgroup G → Subgroup G → G → Set G := @(fun {G : Type} [Group G] (R K : Subgroup G) (t : G) ↦ {x : G | ∃ r ∈ R, ∃ κ ∈ K, x = r * t * κ}); ∀ {G : Type} [inst : Group G] {M : Type} [inst_1 : AddCommMonoid M] (R K : Subgroup G) (T : Finset G) (φ : G → M), (∀ r ∈ R, ∀ (x : G), φ (r * x) = φ x) → (∀ κ ∈ K, ∀ (x : G), φ (x * κ) = φ x) → (∀ (x : G), φ x ≠ (0 : M) → ∃ t ∈ T, x ∈ d1 R K t) → ∃ (c : G → M), (∀ (t : G), c t = (0 : M) ∨ c t = φ t) ∧ ∀ (x : G), φ x = ∑ t ∈ T, Set.indicator (d1 R K t) (fun (x : G) ↦ c t) x) := by
  intro d1 G _ M _ R K T φ hR hK hT
  exact exists_eq_sum_indicator R K T φ hR hK hT
end GlobalTheory.DoubleCosetIndicator
