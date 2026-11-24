-- Prove2me | solution 1 for GlobalTheory.QNorm.valuation_of_eq_comap
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T19:58:54.2148+00:00
-- url     : https://prove2.me/submissions/987ef89d-2535-48ad-99bd-d4bd84cf7fc2

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AdelicHermitianForms_SqSubLeNormSub
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_WithZeroEqOfLeExpIff
import Theorems.Thm_GlobalTheory_QNorm_intValuation_of_eq_comap

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain GlobalTheory.QNorm
open scoped WithZero
open GlobalTheory GlobalTheory.QNorm
open NumberField IsDedekindDomain
open scoped WithZero
namespace GlobalTheory.QNorm
namespace _root_.GlobalTheory.QNorm
theorem _root_.solution {E : Type} [Field E] [NumberField E] (σ : E ≃+* E)
    (w w' : HeightOneSpectrum (𝓞 E))
    (h : w'.asIdeal = w.asIdeal.comap (RingOfIntegers.mapRingEquiv σ)) (y : E) :
    w'.valuation E y = w.valuation E (σ y) := by
  obtain ⟨a, b, hb, rfl⟩ := IsFractionRing.div_surjective (A := 𝓞 E) y
  have hσ : ∀ r : 𝓞 E, σ (algebraMap (𝓞 E) E r) =
      algebraMap (𝓞 E) E (RingOfIntegers.mapRingEquiv σ r) := fun r => rfl
  rw [map_div₀ σ, hσ, hσ, map_div₀, map_div₀]
  simp only [HeightOneSpectrum.valuation_of_algebraMap]
  rw [_root_.GlobalTheory.QNorm.intValuation_of_eq_comap _ w w' h a,
    _root_.GlobalTheory.QNorm.intValuation_of_eq_comap _ w w' h b]
end _root_.GlobalTheory.QNorm
end GlobalTheory.QNorm
