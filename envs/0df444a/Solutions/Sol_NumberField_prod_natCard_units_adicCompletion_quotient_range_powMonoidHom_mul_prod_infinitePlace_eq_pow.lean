-- Prove2me | solution 1 for NumberField.prod_natCard_units_adicCompletion_quotient_range_powMonoidHom_mul_prod_infinitePlace_eq_pow
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.93214+00:00
-- url     : https://prove2.me/submissions/e0aeb772-4d79-57b5-a631-02699fbc1038

import Mathlib
import Theorems.Thm_NumberField_natCard_units_adicCompletion_quotient_range_powMonoidHom
import Theorems.Thm_NumberField_InfinitePlace_natCard_units_completion_quotient_range_powMonoidHom_of_isComplex
import Theorems.Thm_NumberField_InfinitePlace_natCard_units_completion_quotient_range_powMonoidHom_of_isReal
import Theorems.Thm_NumberField_prod_natCard_adicCompletionIntegers_quotient_span_natCast_eq_pow_finrank
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_NumberField_prod_natCard_units_adicCompletion_quotient_range_powMonoidHom_mul_prod_infinitePlace_eq_pow
p2m_attr_erase "instance" "IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions"
p2m_attr_erase "simp" "IsLocalRing.principalUnits_zero"

set_option autoImplicit false

theorem solution
    {K : Type*} [Field K] [NumberField K] {p : ℕ} (hp : p.Prime) (hζ : (primitiveRoots p K).Nonempty)
    (S : Finset (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K)))
    (hS : ∀ v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K),
      (p : NumberField.RingOfIntegers K) ∈ v.asIdeal → v ∈ S) :
    (∏ v ∈ S, Nat.card ((v.adicCompletion K)ˣ ⧸ (powMonoidHom p : (v.adicCompletion K)ˣ →* (v.adicCompletion K)ˣ).range))
        * ∏ w : NumberField.InfinitePlace K,
            Nat.card ((w.Completion)ˣ ⧸ (powMonoidHom p : (w.Completion)ˣ →* (w.Completion)ˣ).range)
      = p ^ (2 * (S.card + Fintype.card (NumberField.InfinitePlace K))) := by
  classical
  obtain ⟨ζ, hζmem⟩ := hζ
  have hζ' : IsPrimitiveRoot ζ p := (mem_primitiveRoots hp.pos).1 hζmem

  have hfin : ∀ v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K),
      Nat.card ((v.adicCompletion K)ˣ ⧸ (powMonoidHom p : (v.adicCompletion K)ˣ →* (v.adicCompletion K)ˣ).range)
        = p ^ 2 * Nat.card (v.adicCompletionIntegers K ⧸ Ideal.span {(p : v.adicCompletionIntegers K)}) := by
    intro v
    have hμ : (primitiveRoots p (v.adicCompletion K)).Nonempty :=
      ⟨algebraMap K (v.adicCompletion K) ζ, (mem_primitiveRoots hp.pos).2
        (hζ'.map_of_injective (algebraMap K (v.adicCompletion K)).injective)⟩
    exact (NumberField.natCard_units_adicCompletion_quotient_range_powMonoidHom v hμ).1
  have hfinprod : ∏ v ∈ S, Nat.card ((v.adicCompletion K)ˣ ⧸
        (powMonoidHom p : (v.adicCompletion K)ˣ →* (v.adicCompletion K)ˣ).range)
      = p ^ (2 * S.card + Module.finrank ℚ K) := by
    simp_rw [hfin]
    rw [Finset.prod_mul_distrib, Finset.prod_const,
      NumberField.prod_natCard_adicCompletionIntegers_quotient_span_natCast_eq_pow_finrank hp S hS,
      ← pow_mul, ← pow_add]
  rw [hfinprod, ← NumberField.InfinitePlace.card_add_two_mul_card_eq_rank,
    NumberField.InfinitePlace.card_eq_nrRealPlaces_add_nrComplexPlaces]

  rcases hp.eq_two_or_odd' with rfl | hodd
  ·
    have hinf : ∀ w : NumberField.InfinitePlace K,
        Nat.card ((w.Completion)ˣ ⧸ (powMonoidHom 2 : (w.Completion)ˣ →* (w.Completion)ˣ).range)
          = if w.IsReal then 2 else 1 := by
      intro w
      split_ifs with hw
      · rw [NumberField.InfinitePlace.natCard_units_completion_quotient_range_powMonoidHom_of_isReal w hw two_pos,
          if_pos even_two]
      · exact NumberField.InfinitePlace.natCard_units_completion_quotient_range_powMonoidHom_of_isComplex w
          (NumberField.InfinitePlace.not_isReal_iff_isComplex.1 hw) two_pos
    simp_rw [hinf]
    rw [Finset.prod_ite, Finset.prod_const_one, mul_one, Finset.prod_const]
    have hr : (Finset.univ.filter fun w : NumberField.InfinitePlace K => w.IsReal).card
        = NumberField.InfinitePlace.nrRealPlaces K := by
      rw [NumberField.InfinitePlace.nrRealPlaces, Fintype.card_subtype]
    rw [hr, ← pow_add]
    congr 1
    ring
  ·
    have hp2 : 2 < p := lt_of_le_of_ne hp.two_le (by rintro rfl; exact Nat.not_odd_iff_even.2 even_two hodd)
    have hr0 : NumberField.InfinitePlace.nrRealPlaces K = 0 :=
      NumberField.InfinitePlace.IsPrimitiveRoot.nrRealPlaces_eq_zero_of_two_lt hp2 hζ'
    have hcomplex : ∀ w : NumberField.InfinitePlace K, w.IsComplex := by
      intro w
      rw [← NumberField.InfinitePlace.not_isReal_iff_isComplex]
      intro hw
      have : 0 < NumberField.InfinitePlace.nrRealPlaces K := by
        rw [NumberField.InfinitePlace.nrRealPlaces]
        exact Fintype.card_pos_iff.2 ⟨⟨w, hw⟩⟩
      omega
    have hinf : ∀ w : NumberField.InfinitePlace K,
        Nat.card ((w.Completion)ˣ ⧸ (powMonoidHom p : (w.Completion)ˣ →* (w.Completion)ˣ).range) = 1 :=
      fun w => NumberField.InfinitePlace.natCard_units_completion_quotient_range_powMonoidHom_of_isComplex w
        (hcomplex w) hp.pos
    simp_rw [hinf]
    rw [Finset.prod_const_one, mul_one, hr0]
    congr 1
    ring

end S_NumberField_prod_natCard_units_adicCompletion_quotient_range_powMonoidHom_mul_prod_infinitePlace_eq_pow
end P2MW
export P2MW.S_NumberField_prod_natCard_units_adicCompletion_quotient_range_powMonoidHom_mul_prod_infinitePlace_eq_pow (solution)
