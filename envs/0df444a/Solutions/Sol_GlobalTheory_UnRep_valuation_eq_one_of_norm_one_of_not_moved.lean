-- Prove2me | solution 1 for GlobalTheory.UnRep.valuation_eq_one_of_norm_one_of_not_moved
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T21:59:03.661792+00:00
-- url     : https://prove2.me/submissions/6e07a5b2-0dd0-4114-a70a-29750b20cd05

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AdelicHermitianForms_IsHermForm
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_ValuationEqOneOfNormOneOfNotMoved
import Theorems.Thm_GlobalTheory_UnRep_intValuation_map_le_of_map_le

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain GlobalTheory.AdLat GlobalTheory.UnRep
open scoped TensorProduct Matrix
open GlobalTheory GlobalTheory.UnRep
namespace GlobalTheory.UnRep
theorem _root_.solution :
    ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (c : E ≃ₐ[F] E),
      (∀ x, c (c x) = x) → ∀ (u : E) (P : HeightOneSpectrum (𝓞 E)), u * c u = 1 →
        ¬ Moved c P.asIdeal → P.valuation E u = 1 := by
  intro F E _ _ _ _ _ c hc u P hu hP
  let σ : 𝓞 E →+* 𝓞 E := RingOfIntegers.mapRingHom (c : E →+* E)
  have hσ : ∀ a : 𝓞 E, ((σ a : 𝓞 E) : E) = c (a : E) := fun a => rfl
  have hσσ : ∀ a, σ (σ a) = a := fun a => by
    apply RingOfIntegers.ext
    rw [hσ, hσ, hc]
  have hle : P.asIdeal.map σ ≤ P.asIdeal := by
    rw [Ideal.map_le_iff_le_comap]
    intro a ha
    by_contra hb
    exact hP ⟨a, ha, σ a, hσ a, hb⟩
  have hint : ∀ a, P.intValuation (σ a) = P.intValuation a := fun a => by
    apply le_antisymm (intValuation_map_le_of_map_le σ P hle a)
    have := intValuation_map_le_of_map_le σ P hle (σ a)
    rwa [hσσ] at this
  have hval : ∀ a : 𝓞 E, P.valuation E (c (a : E)) = P.valuation E (a : E) := fun a => by
    rw [← hσ]
    change P.valuation E (algebraMap (𝓞 E) E (σ a)) = P.valuation E (algebraMap (𝓞 E) E a)
    rw [P.valuation_of_algebraMap, P.valuation_of_algebraMap, hint]
  have hcu : P.valuation E (c u) = P.valuation E u := by
    obtain ⟨a, b, -, rfl⟩ := IsFractionRing.div_surjective (A := 𝓞 E) u
    rw [map_div₀, map_div₀, map_div₀]
    exact congrArg₂ (· / ·) (hval a) (hval b)
  have h2 : P.valuation E u ^ 2 = 1 := by
    have := congrArg (P.valuation E) hu
    rwa [map_mul, hcu, map_one, ← sq] at this
  exact (pow_eq_one_iff_of_nonneg zero_le' two_ne_zero).1 h2
end GlobalTheory.UnRep
