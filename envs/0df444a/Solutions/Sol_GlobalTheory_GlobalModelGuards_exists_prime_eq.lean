-- Prove2me | solution 1 for GlobalTheory.GlobalModelGuards.exists_prime_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T17:50:25.616519+00:00
-- url     : https://prove2.me/submissions/987c10f9-90d9-4477-a92e-2a5f16c23d39

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_Clauses
import Definitions.Def_Development_AbelianVarietyTheory_Counterexamples_ModuliSurvey_ExistsGoodLevel
import Theorems.Thm_GlobalTheory_GlobalModelGuards_exists_incl
import Theorems.Thm_GlobalTheory_GlobalModelGuards_not_isUnit

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.GlobalModelGuards
open AlgebraicGeometry CategoryTheory Limits NumberField
open ReciprocityTheory.ChartRestriction.G.Geo.Tor
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H}
namespace GlobalTheory.GlobalModelGuards
theorem _root_.solution {l : Level H} (c : Coeff l) (W : ValuationSubring ℂ) (p : ℕ) (hp : p.Prime)
    (hW : (p : ℂ) ∈ W.nonunits) [NumberField c.F] :
    ∃ v : IsDedekindDomain.HeightOneSpectrum (𝓞 c.F), (p : 𝓞 c.F) ∈ v.asIdeal ∧
      v.valuationSubringAtPrime c.F = c.V W := by
  obtain ⟨b, hb, -⟩ := exists_incl c W
  have hn := not_isUnit c W p hW
  have hpm : (p : 𝓞 c.F) ∈ (IsLocalRing.maximalIdeal (c.V W)).comap b := by
    rw [Ideal.mem_comap, map_natCast]; exact hn
  let v : IsDedekindDomain.HeightOneSpectrum (𝓞 c.F) :=
    ⟨(IsLocalRing.maximalIdeal (c.V W)).comap b, inferInstance, fun h => by
      rw [h, Ideal.mem_bot] at hpm
      exact hp.ne_zero (by exact_mod_cast hpm)⟩
  refine ⟨v, hpm, ?_⟩
  haveI : IsLocalization v.asIdeal.primeCompl (v.valuationSubringAtPrime c.F) :=
    Localization.subalgebra.isLocalization_ofField c.F v.asIdeal.primeCompl v.asIdeal.primeCompl_le_nonZeroDivisors
  haveI : IsDiscreteValuationRing (v.valuationSubringAtPrime c.F) :=
    IsLocalization.AtPrime.isDiscreteValuationRing_of_dedekind_domain (𝓞 c.F) v.ne_bot _
  refine ValuationSubring.eq_of_le_of_ne_top _ ?_ ?_
  · intro x hx
    obtain ⟨⟨a, s⟩, h⟩ := IsLocalization.surj v.asIdeal.primeCompl (⟨x, hx⟩ : v.valuationSubringAtPrime c.F)
    have hs : IsUnit (b s) := by
      by_contra h'
      exact s.2 h'
    obtain ⟨u, hu⟩ := hs.exists_right_inv
    have h1 : x * ((s : 𝓞 c.F) : c.F) = (a : c.F) := congrArg Subtype.val h
    have h2 : ((s : 𝓞 c.F) : c.F) * (u : c.F) = 1 := by
      rw [← hb]; exact congrArg Subtype.val hu
    have : x = ((b a * u : c.V W) : c.F) := by
      push_cast
      rw [hb, ← h1, mul_assoc, h2, mul_one]
    rw [this]; exact (b a * u).2
  · intro h
    apply hn
    have hp0 : (p : c.F) ≠ 0 := by exact_mod_cast hp.ne_zero
    refine IsUnit.of_mul_eq_one ⟨(p : c.F)⁻¹, h ▸ ValuationSubring.mem_top _⟩ (Subtype.ext ?_)
    simp [hp0]
end GlobalTheory.GlobalModelGuards
