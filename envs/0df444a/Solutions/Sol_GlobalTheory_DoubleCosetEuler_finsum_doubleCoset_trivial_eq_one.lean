-- Prove2me | solution 1 for GlobalTheory.DoubleCosetEuler.finsum_doubleCoset_trivial_eq_one
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T14:25:06.710282+00:00
-- url     : https://prove2.me/submissions/08adc113-eaef-45cf-8d43-fa3a637c02ce

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_FinsumDoubleCosetEqFinprodLocalSums

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Filter
open scoped Classical
open GlobalTheory GlobalTheory.DoubleCosetEuler
namespace GlobalTheory.DoubleCosetEuler
theorem _root_.solution (H : Type) [Group H] (TH KH : Subgroup H) (f : H → ℂ)
    (hf : ∀ x, f x = if ∃ t ∈ TH, ∃ k ∈ KH, x = t * k then 1 else 0) :
    ∑ᶠ q : DoubleCoset.Quotient (TH : Set H) (KH : Set H), f (Quotient.out q) = 1 := by
  have h1 : ∀ q : DoubleCoset.Quotient (TH : Set H) (KH : Set H), q ≠ DoubleCoset.mk TH KH 1 →
      f (Quotient.out q) = 0 := by
    intro q hq
    rw [hf, if_neg]
    rintro ⟨t, ht, k, hk, he⟩
    apply hq
    rw [← DoubleCoset.out_eq' TH KH q, DoubleCoset.eq]
    exact ⟨t⁻¹, inv_mem ht, k⁻¹, inv_mem hk, by rw [he]; group⟩
  rw [finsum_eq_single _ (DoubleCoset.mk TH KH 1) h1, hf, if_pos]
  obtain ⟨a, b, ha, hb, he⟩ := DoubleCoset.mk_out_eq_mul TH KH (1 : H)
  exact ⟨a, ha, b, hb, by rw [he, mul_one]⟩
end GlobalTheory.DoubleCosetEuler
