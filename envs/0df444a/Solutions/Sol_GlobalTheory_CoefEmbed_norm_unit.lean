-- Prove2me | solution 1 for GlobalTheory.CoefEmbed.norm_unit
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T17:30:51.765007+00:00
-- url     : https://prove2.me/submissions/7838441c-fb4f-4778-99ad-8793f5935137

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_EmbeddingClosedIntegral
import Theorems.Thm_GlobalTheory_CoefEmbed_norm_le_one

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.CoefEmbed
open IsLocalRing Topology
variable {l : ℕ} [Fact l.Prime] {O : Type} [CommRing O] [Algebra ℤ_[l] O] [Module.Finite ℤ_[l] O]
namespace GlobalTheory.CoefEmbed
theorem _root_.solution (f : O →+* PadicAlgCl l)
    (hf : ∀ z : ℤ_[l], f (algebraMap ℤ_[l] O z) = algebraMap ℚ_[l] (PadicAlgCl l) (z : ℚ_[l]))
    {a : O} (ha : IsUnit a) : ‖f a‖ = 1 := by
  obtain ⟨b, hb⟩ := ha.exists_right_inv
  have h : ‖f a‖ * ‖f b‖ = 1 := by rw [← norm_mul, ← map_mul, hb, map_one, norm_one]
  refine le_antisymm (norm_le_one f hf a) ?_
  calc (1 : ℝ) = ‖f a‖ * ‖f b‖ := h.symm
    _ ≤ ‖f a‖ := mul_le_of_le_one_right (norm_nonneg _) (norm_le_one f hf b)
end GlobalTheory.CoefEmbed
