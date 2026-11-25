-- Prove2me | solution 1 for GroundTheory.Global.finite_and_card_fiber_rationalPrimeUnder_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T00:16:30.611091+00:00
-- url     : https://prove2.me/submissions/d8b407de-8881-4c07-bf69-6fcd6bb249b9

import Mathlib
import Definitions.Def_GroundTheory_GlobalFields_TateThesis_DegreeOnePrimes
import Theorems.Thm_GroundTheory_Global_card_primesOver_le_finrank
import Theorems.Thm_GroundTheory_Global_under_int_ne_bot
import Theorems.Thm_GroundTheory_Global_span_rationalPrimeUnder

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
set_option synthInstance.maxHeartbeats 400000
-- END pinned source Lake options
set_option autoImplicit false
open GroundTheory GroundTheory.Global
open NumberField IsDedekindDomain Filter Topology Set
noncomputable section
variable {K L : Type*} [Field L] [NumberField L]
namespace GroundTheory.Global
theorem _root_.solution (n : ℕ) :
    Finite {w : HeightOneSpectrum (𝓞 L) // rationalPrimeUnder w = n} ∧
      Nat.card {w : HeightOneSpectrum (𝓞 L) // rationalPrimeUnder w = n} ≤
        Module.finrank ℤ (𝓞 L) := by
  rcases isEmpty_or_nonempty {w : HeightOneSpectrum (𝓞 L) // rationalPrimeUnder w = n} with h | h
  · exact ⟨inferInstance, by simp⟩
  obtain ⟨w₀⟩ := h
  set P := w₀.1.asIdeal.under ℤ with hPdef
  have : P.IsMaximal := Ideal.IsPrime.isMaximal inferInstance (under_int_ne_bot w₀.1)
  have : Finite (P.primesOver (𝓞 L)) := (IsDedekindDomain.primesOver_finite P (𝓞 L)).to_subtype
  have hP : ∀ w : {w : HeightOneSpectrum (𝓞 L) // rationalPrimeUnder w = n},
      w.1.asIdeal.under ℤ = P := by
    intro w
    rw [hPdef, ← span_rationalPrimeUnder, ← span_rationalPrimeUnder, w.2, w₀.2]
  let f : {w : HeightOneSpectrum (𝓞 L) // rationalPrimeUnder w = n} → P.primesOver (𝓞 L) :=
    fun w => ⟨w.1.asIdeal, w.1.isPrime, ⟨(hP w).symm⟩⟩
  have hf : Function.Injective f := by
    intro a b hab
    exact Subtype.ext (HeightOneSpectrum.ext (congrArg Subtype.val hab))
  exact ⟨Finite.of_injective f hf,
    (Nat.card_le_card_of_injective f hf).trans (card_primesOver_le_finrank P)⟩
end GroundTheory.Global
