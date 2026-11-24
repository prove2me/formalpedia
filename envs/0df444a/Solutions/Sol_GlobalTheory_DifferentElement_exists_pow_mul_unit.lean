-- Prove2me | solution 1 for GlobalTheory.DifferentElement.exists_pow_mul_unit
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T14:23:37.394922+00:00
-- url     : https://prove2.me/submissions/cc0845b4-ed5b-43e7-bcdb-5b79733bf37a

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_DivisorBase_ConjugateOrderData
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_PullbackSections_HolomorphicFamilies_PadicValNatAbsNormEqZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsDifferentExponentDenominator

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open NumberField IsDedekindDomain GlobalTheory.IndefiniteRowSideFullHecke.DifferentConductorValuations UniqueFactorizationMonoid
open GlobalTheory GlobalTheory.DifferentElement
namespace GlobalTheory.DifferentElement
theorem _root_.solution {E : Type} [Field E] [NumberField E] {O : Type} [CommRing O] [IsDomain O]
    [IsDiscreteValuationRing O] (ι : 𝓞 E →+* O) (hQ0 : Ideal.comap ι (IsLocalRing.maximalIdeal O) ≠ ⊥) {ϖ : O} (e : ℕ)
    (he : Ideal.map ι (Ideal.comap ι (IsLocalRing.maximalIdeal O)) = Ideal.span {ϖ ^ e}) (z : 𝓞 E) (hz : z ≠ 0) :
    ∃ u : Oˣ, ι z = ϖ ^ (e * multiplicity (Ideal.comap ι (IsLocalRing.maximalIdeal O)) (Ideal.span {z})) * u := by
  set Q := Ideal.comap ι (IsLocalRing.maximalIdeal O) with hQdef
  have hQp : Q.IsPrime := Ideal.comap_isPrime ι _
  set k := multiplicity Q (Ideal.span {z})
  have hz0 : Ideal.span {z} ≠ ⊥ := by rwa [Ne, Ideal.span_singleton_eq_bot]
  have hfin : FiniteMultiplicity Q (Ideal.span {z}) :=
    FiniteMultiplicity.of_prime_left (Ideal.prime_of_isPrime hQ0 hQp) hz0
  obtain ⟨J, hJ⟩ := pow_multiplicity_dvd Q (Ideal.span {z})
  have hJQ : ¬ J ≤ Q := by
    intro hle
    have : Q ^ (k + 1) ∣ Ideal.span {z} := by
      rw [hJ, pow_succ]
      exact mul_dvd_mul_left _ (Ideal.dvd_iff_le.2 hle)
    exact (hfin.pow_dvd_iff_le_multiplicity.1 this).not_gt (Nat.lt_succ_self k)
  obtain ⟨s, hsJ, hsQ⟩ := SetLike.not_le_iff_exists.1 hJQ
  have hsu : IsUnit (ι s) := by
    by_contra h
    exact hsQ (Ideal.mem_comap.2 ((IsLocalRing.mem_maximalIdeal _).2 h))
  have hJt : Ideal.map ι J = ⊤ := Ideal.eq_top_of_isUnit_mem _ (Ideal.mem_map_of_mem ι hsJ) hsu
  have h1 : Ideal.span {ι z} = Ideal.span {ϖ ^ (e * k)} := by
    rw [← Set.image_singleton, ← Ideal.map_span, hJ, Ideal.map_mul, Ideal.map_pow, he, hJt, Ideal.mul_top,
      Ideal.span_singleton_pow, pow_mul]
  obtain ⟨u, hu⟩ := (Ideal.span_singleton_eq_span_singleton.1 h1).symm
  exact ⟨u, hu.symm⟩
end GlobalTheory.DifferentElement
