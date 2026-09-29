-- Prove2me | solution 1 for NumberField.AdeleRing.finite_setOf_valued_snd_ne_one
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.93214+00:00
-- url     : https://prove2.me/submissions/6ef31bef-bd7c-5312-859e-54e9c71db250

import Mathlib
import Definitions.Def_IsDedekindDomain_FiniteUnitIdelesOutside
import Definitions.Def_M4aHerbrand_IdeleClassVocab
import Definitions.Def_NumberField_PlaceTransport
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_NumberField_AdeleRing_finite_setOf_valued_snd_ne_one

set_option autoImplicit false
open IsDedekindDomain NumberField
open scoped NumberField.PlaceTransport

theorem solution
    (K : Type) [Field K] [NumberField K] (x : (AdeleRing (𝓞 K) K)ˣ) :
    {w : HeightOneSpectrum (𝓞 K) | Valued.v (((x : AdeleRing (𝓞 K) K).2 : FiniteAdeleRing (𝓞 K) K) w) ≠ 1}.Finite := by

  have h1 : ∀ᶠ w in Filter.cofinite, ((x : AdeleRing (𝓞 K) K).2 : FiniteAdeleRing (𝓞 K) K) w ∈ (w.adicCompletionIntegers K : Set (w.adicCompletion K)) :=
    ((x : AdeleRing (𝓞 K) K).2 : FiniteAdeleRing (𝓞 K) K).2
  have h2 : ∀ᶠ w in Filter.cofinite, (((x⁻¹ : (AdeleRing (𝓞 K) K)ˣ) : AdeleRing (𝓞 K) K).2 : FiniteAdeleRing (𝓞 K) K) w ∈ (w.adicCompletionIntegers K : Set (w.adicCompletion K)) :=
    (((x⁻¹ : (AdeleRing (𝓞 K) K)ˣ) : AdeleRing (𝓞 K) K).2 : FiniteAdeleRing (𝓞 K) K).2
  have h12 := h1.and h2
  rw [Filter.eventually_cofinite] at h12
  refine h12.subset fun w hw => ?_
  simp only [Set.mem_setOf_eq, not_and_or] at hw ⊢

  by_contra h
  push Not at h
  obtain ⟨hx, hxi⟩ := h
  rw [SetLike.mem_coe, HeightOneSpectrum.mem_adicCompletionIntegers] at hx hxi
  have hmul : ((x : AdeleRing (𝓞 K) K).2 : FiniteAdeleRing (𝓞 K) K) w * (((x⁻¹ : (AdeleRing (𝓞 K) K)ˣ) : AdeleRing (𝓞 K) K).2 : FiniteAdeleRing (𝓞 K) K) w = 1 := by
    have h : ((((x * x⁻¹ : (AdeleRing (𝓞 K) K)ˣ) : AdeleRing (𝓞 K) K).2 : FiniteAdeleRing (𝓞 K) K) w) = 1 := by rw [mul_inv_cancel]; rfl
    exact h
  have hv : Valued.v (((x : AdeleRing (𝓞 K) K).2 : FiniteAdeleRing (𝓞 K) K) w) * Valued.v ((((x⁻¹ : (AdeleRing (𝓞 K) K)ˣ) : AdeleRing (𝓞 K) K).2 : FiniteAdeleRing (𝓞 K) K) w) = 1 := by
    rw [← map_mul, hmul, map_one]
  apply hw
  apply le_antisymm hx

  calc (1 : WithZero (Multiplicative ℤ)) = Valued.v (((x : AdeleRing (𝓞 K) K).2 : FiniteAdeleRing (𝓞 K) K) w) * Valued.v ((((x⁻¹ : (AdeleRing (𝓞 K) K)ˣ) : AdeleRing (𝓞 K) K).2 : FiniteAdeleRing (𝓞 K) K) w) := hv.symm
    _ ≤ Valued.v (((x : AdeleRing (𝓞 K) K).2 : FiniteAdeleRing (𝓞 K) K) w) * 1 := mul_le_mul_right hxi _
    _ = _ := mul_one _

end S_NumberField_AdeleRing_finite_setOf_valued_snd_ne_one
end P2MW
export P2MW.S_NumberField_AdeleRing_finite_setOf_valued_snd_ne_one (solution)
