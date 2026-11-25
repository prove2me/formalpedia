-- Prove2me | solution 1 for GlobalTheory.T.eq_zero_of_integral_char_eq_zero_of_periodic_open
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T18:14:30.717908+00:00
-- url     : https://prove2.me/submissions/d42aca42-8c39-4234-af21-df48493f6712

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_FourierUniquenessOfOpenSubgroup
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_FourierUniquenessOfOpenSubgroupStatement
import Theorems.Thm_GlobalTheory_fourier_uniqueness_of_openSubgroup


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory
set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ {H A : Type} [AddCommGroup H] [TopologicalSpace H] [IsTopologicalAddGroup H] [MeasurableSpace H] [BorelSpace H] (μ : Measure H) [μ.IsAddHaarMeasure] [AddCommGroup A] (χ : A → H → ℂ), (∀ a s t, χ a (s + t) = χ a s * χ a t) → (∀ a, χ a 0 = 1) → (∀ t, χ 0 t = 1) → (∀ a b t, χ (a + b) t = χ a t * χ b t) → ∀ L : AddSubgroup H, IsOpen (L : Set H) → (∀ x, x ∉ L → ∃ a, (∀ l ∈ L, χ a l = 1) ∧ χ a x ≠ 1) → ∀ (φ : H → ℂ) (Kc : Set H), IsCompact Kc → (∀ t, t ∉ Kc → φ t = 0) → (∀ t, ∀ l ∈ L, φ (t + l) = φ t) → (∀ a, (∀ l ∈ L, χ a l = 1) → ∫ t, χ a t * φ t ∂μ = 0) → φ = 0 := by
  first | exact @GlobalTheory.fourier_uniqueness_of_openSubgroup | exact GlobalTheory.fourier_uniqueness_of_openSubgroup | (intros; apply GlobalTheory.fourier_uniqueness_of_openSubgroup <;> assumption)
end _root_.GlobalTheory.T
