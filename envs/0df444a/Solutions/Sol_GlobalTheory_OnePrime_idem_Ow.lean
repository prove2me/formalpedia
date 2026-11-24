-- Prove2me | solution 1 for GlobalTheory.OnePrime.idem_Ow
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T19:16:11.62572+00:00
-- url     : https://prove2.me/submissions/9d73a062-2ad5-4b1a-ae8d-4bd0c3851918

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_JetGauges_SplitUnramifiedPlaces
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_FiniteMaximalSpectrumOfFiniteOfIsLocalRing
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_JetHarmonics_ExistsUniqueMaximalAbovePlace

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped TensorProduct
open GlobalTheory GlobalTheory.OnePrime
open GlobalTheory.IndefiniteRowSideFullHecke.SplitUnramifiedPlaces
variable {p : ℕ} [Fact p.Prime] {R : Type} [CommRing R]
namespace GlobalTheory.OnePrime
theorem _root_.solution (w : Place p R) {d : w.Ow} (hd : IsIdempotentElem d) : d = 0 ∨ d = 1 := by
  obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective d
  have hx : x * x - x ∈ Ideal.span {1 - w.e} :=
    Ideal.Quotient.eq.mp (by rw [map_mul]; exact hd)
  obtain ⟨c, hc⟩ := Ideal.mem_span_singleton'.mp hx
  have hee : w.e * w.e = w.e := w.idem
  have he1 : Ideal.Quotient.mk (Ideal.span {1 - w.e}) w.e = 1 := by
    rw [← map_one (Ideal.Quotient.mk _), Ideal.Quotient.eq]
    exact Ideal.mem_span_singleton'.mpr ⟨-1, by ring⟩
  have hf : IsIdempotentElem (w.e * x) := by
    show w.e * x * (w.e * x) = w.e * x
    linear_combination (x * x - c) * hee - w.e * hc
  have hfe : w.e * x * w.e = w.e * x := by linear_combination x * hee
  have hmk : Ideal.Quotient.mk (Ideal.span {1 - w.e}) (w.e * x) =
      Ideal.Quotient.mk (Ideal.span {1 - w.e}) x := by
    rw [map_mul, he1, one_mul]
  rcases w.primitive _ hf hfe with h0 | h1
  · left
    rw [← hmk, h0, map_zero]
  · right
    rw [← hmk, h1, he1]
end GlobalTheory.OnePrime
