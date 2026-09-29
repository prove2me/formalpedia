-- Prove2me | solution 1 for NumberField.natCard_units_adicCompletionIntegers_quotient_range_powMonoidHom
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.93214+00:00
-- url     : https://prove2.me/submissions/7f0a5a0b-453e-57ba-a613-e9aed0a73672

import Mathlib
import Theorems.Thm_IsDiscreteValuationRing_index_range_powMonoidHom_units_eq
import Theorems.Thm_IsDedekindDomain_HeightOneSpectrum_isAdicComplete_adicCompletionIntegers
import Theorems.Thm_IsDedekindDomain_HeightOneSpectrum_finite_residueField_adicCompletionIntegers
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_NumberField_natCard_units_adicCompletionIntegers_quotient_range_powMonoidHom
p2m_attr_erase "simp" "IsLocalRing.principalUnits_zero"

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 1600000
set_option maxHeartbeats 3200000

namespace P2mS26C4u
open IsDedekindDomain

theorem natCast_adicCompletionIntegers_ne_zero {K : Type*} [Field K] [NumberField K]
    (v : HeightOneSpectrum (NumberField.RingOfIntegers K)) {n : ℕ} (hn : n ≠ 0) :
    ((n : ℕ) : v.adicCompletionIntegers K) ≠ 0 := by
  intro h
  have h' : ((n : ℕ) : v.adicCompletion K) ≠ 0 := by
    rw [← map_natCast (algebraMap K (v.adicCompletion K)) n, map_ne_zero]
    exact Nat.cast_ne_zero.2 hn
  apply h'
  have h2 := congrArg ((↑) : v.adicCompletionIntegers K → v.adicCompletion K) h
  simpa using h2

theorem pos_of_primitiveRoots_nonempty {M : Type*} [CommRing M] [IsDomain M] {n : ℕ}
    (h : (primitiveRoots n M).Nonempty) : 0 < n := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · obtain ⟨ζ, hζ⟩ := h
    simp at hζ
  · exact hn

end P2mS26C4u

theorem solution {K : Type*} [Field K] [NumberField K]
    (v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))
    {n : ℕ} (hμ : (primitiveRoots n (v.adicCompletion K)).Nonempty) :
    Nat.card ((v.adicCompletionIntegers K)ˣ ⧸
        (powMonoidHom n : (v.adicCompletionIntegers K)ˣ →* (v.adicCompletionIntegers K)ˣ).range)
      = n * Nat.card (v.adicCompletionIntegers K ⧸ Ideal.span {(n : v.adicCompletionIntegers K)}) := by
  classical
  have hn0 : 0 < n := P2mS26C4u.pos_of_primitiveRoots_nonempty hμ
  obtain ⟨ζ, hζ⟩ := hμ
  haveI : NeZero n := ⟨hn0.ne'⟩
  have hζ' : IsPrimitiveRoot ζ n := (mem_primitiveRoots hn0).1 hζ
  haveI : IsAdicComplete (IsLocalRing.maximalIdeal (v.adicCompletionIntegers K)) (v.adicCompletionIntegers K) :=
    IsDedekindDomain.HeightOneSpectrum.isAdicComplete_adicCompletionIntegers K v
  haveI : Finite (IsLocalRing.ResidueField (v.adicCompletionIntegers K)) :=
    IsDedekindDomain.HeightOneSpectrum.finite_residueField_adicCompletionIntegers K v
  have hnR := P2mS26C4u.natCast_adicCompletionIntegers_ne_zero v hn0.ne'

  have hvζ : Valued.v ζ = (1 : WithZero (Multiplicative ℤ)) := by
    have h1 : (Valued.v ζ) ^ n = 1 := by rw [← map_pow, hζ'.pow_eq_one, map_one]
    rcases lt_trichotomy (Valued.v ζ) 1 with h | h | h
    · exact absurd h1 (ne_of_lt (pow_lt_one' h hn0.ne'))
    · exact h
    · exact absurd h1 (ne_of_gt (one_lt_pow' h hn0.ne'))
  let ζR : v.adicCompletionIntegers K :=
    ⟨ζ, (IsDedekindDomain.HeightOneSpectrum.mem_adicCompletionIntegers (NumberField.RingOfIntegers K) K v).2 hvζ.le⟩
  have hζR : IsPrimitiveRoot ζR n :=
    IsPrimitiveRoot.of_map_of_injective (f := (v.adicCompletionIntegers K).subtype) (by exact hζ')
      Subtype.coe_injective
  have hG1 := IsDiscreteValuationRing.index_range_powMonoidHom_units_eq (R := v.adicCompletionIntegers K) hnR
  change (powMonoidHom n : (v.adicCompletionIntegers K)ˣ →* (v.adicCompletionIntegers K)ˣ).range.index = _
  rw [hG1, hζR.card_rootsOfUnity]

end S_NumberField_natCard_units_adicCompletionIntegers_quotient_range_powMonoidHom
end P2MW
export P2MW.S_NumberField_natCard_units_adicCompletionIntegers_quotient_range_powMonoidHom (solution)
