-- Prove2me | solution 1 for GlobalTheory.Doubling.IsIwasawa.eq_iwAbs
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T17:41:38.21623+00:00
-- url     : https://prove2.me/submissions/0681747d-8d10-4747-aa4b-a91f628026e4

import Mathlib
import Definitions.Def_Formalism_SatakeDualWeyl_Statement
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_IsIwasawaOfIsCompact
import Theorems.Thm_GlobalTheory_Doubling_IsIwasawa_iwAbs_mul

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.Doubling
open scoped NNReal
open MeasureTheory
variable {G : Type} [Group G] {P : Subgroup G} (δ : P →* ℝ≥0) (K : Subgroup G)
variable {δ K}
open GlobalTheory.Doubling.IsIwasawa
variable (h : IsIwasawa δ K)
include h
namespace GlobalTheory.Doubling.IsIwasawa
theorem _root_.solution {f : G → ℝ≥0} (h1 : f 1 = 1) (hl : ∀ (p : P) g, f (p * g) = δ p * f g)
    (hr : ∀ g, ∀ k ∈ K, f (g * k) = f g) : f = iwAbs δ K := funext fun g => by
  obtain ⟨p, k, hk, rfl⟩ := h.1 g
  rw [h.iwAbs_mul _ hk, hr _ _ hk, ← mul_one (p : G), hl, h1, mul_one]
end GlobalTheory.Doubling.IsIwasawa
