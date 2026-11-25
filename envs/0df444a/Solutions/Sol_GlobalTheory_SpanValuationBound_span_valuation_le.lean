-- Prove2me | solution 1 for GlobalTheory.SpanValuationBound.span_valuation_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T09:33:36.489177+00:00
-- url     : https://prove2.me/submissions/38f790fa-b425-4e14-b982-6613c73e902c

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_SpanValuationLe

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.SpanValuationBound
open IsDedekindDomain
namespace GlobalTheory.SpanValuationBound
theorem _root_.solution {L : Type} [Field L] [NumberField L] {S : Set L}
    (w : HeightOneSpectrum (NumberField.RingOfIntegers L)) {γ : WithZero (Multiplicative ℤ)}
    (hS : ∀ x ∈ S, (HeightOneSpectrum.valuation L w : L → WithZero (Multiplicative ℤ)) x ≤ γ) :
    ∀ x ∈ Submodule.span (NumberField.RingOfIntegers L) S,
      (HeightOneSpectrum.valuation L w : L → WithZero (Multiplicative ℤ)) x ≤ γ := by
  intro x hx
  induction hx using Submodule.span_induction with
  | mem y hy => exact hS y hy
  | zero => simp
  | add y z _ _ hy hz =>
    exact le_trans (Valuation.map_add _ y z) (max_le hy hz)
  | smul a y _ hy =>
    rw [Algebra.smul_def, map_mul]
    calc (HeightOneSpectrum.valuation L w) (algebraMap _ L a) * (HeightOneSpectrum.valuation L w) y
        ≤ 1 * γ := mul_le_mul' (HeightOneSpectrum.valuation_le_one w a) hy
      _ = γ := one_mul γ
end GlobalTheory.SpanValuationBound
