-- Prove2me | solution 1 for IsPrimitiveRoot.exists_algHom_apply_eq_of_geom_sum_eq_zero_and_eq_mul_one_sub_and_pow_sub_one_eq_mul_of_adjoin_eq_top
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:08.353894+00:00
-- url     : https://prove2.me/submissions/ce270d61-d5bb-509d-9813-6d4286d85f88

import Mathlib
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_IsPrimitiveRoot_exists_algHom_apply_eq_of_geom_sum_eq_zero_and_eq_mul_one_sub_and_pow_sub_one_eq_mul_of_adjoin_eq_top

set_option autoImplicit false

open Polynomial IsLocalRing Finset

theorem solution
    (q : ℕ) [Fact q.Prime] (hq : 3 ≤ q)
    (A₀ : Type) [CommRing A₀] [IsDomain A₀] [IsDiscreteValuationRing A₀]
    (hA₀q : IsLocalRing.maximalIdeal A₀ = Ideal.span {(q : A₀)})
    (A : Type) [CommRing A] [IsDomain A] [IsDiscreteValuationRing A] [Algebra A₀ A]
    (hinj : Function.Injective (algebraMap A₀ A)) [Module.Finite A₀ A]
    (ζ : A) (hζ : IsPrimitiveRoot ζ q) (hadj : Algebra.adjoin A₀ {ζ} = ⊤)
    (ϖ : A) (hϖ : IsLocalRing.maximalIdeal A = Ideal.span {ϖ}) :
    (∀ (S : Type) [CommRing S] [Algebra A₀ S] (z : S), (∑ i ∈ Finset.range q, z ^ i) = 0 →
        ∃ f : A →ₐ[A₀] S, f ζ = z) ∧
    (∃ u : A, IsUnit u ∧ ϖ = u * (1 - ζ)) ∧
    (∃ ε : A, IsUnit ε ∧ ϖ ^ (q - 1) = ε * (q : A)) := by
  classical
  have hqp : q.Prime := Fact.out
  have hq1 : 1 < q := hqp.one_lt
  obtain ⟨n, hn⟩ : ∃ n : ℕ, q = n + 1 := ⟨q - 1, by omega⟩
  obtain ⟨m, hm⟩ : ∃ m : ℕ, n = m + 1 := ⟨n - 1, by omega⟩
  haveI : Module.IsTorsionFree A₀ A := (Module.isTorsionFree_iff_algebraMap_injective).mpr hinj

  have hqA₀ : (q : A₀) ∈ maximalIdeal A₀ := by
    rw [hA₀q]; exact Ideal.mem_span_singleton_self _
  have hqA : (q : A) ∈ maximalIdeal A := by
    have hmax : (Ideal.comap (algebraMap A₀ A) (maximalIdeal A)).IsMaximal :=
      Ideal.isMaximal_comap_of_isIntegral_of_isMaximal (maximalIdeal A)
    have heq : Ideal.comap (algebraMap A₀ A) (maximalIdeal A) = maximalIdeal A₀ := eq_maximalIdeal hmax
    have h1 : (q : A₀) ∈ Ideal.comap (algebraMap A₀ A) (maximalIdeal A) := by rw [heq]; exact hqA₀
    rw [Ideal.mem_comap, map_natCast] at h1
    exact h1

  haveI : CharP (ResidueField A) q := by
    have h0 : ((q : ℕ) : ResidueField A) = 0 := by
      rw [← map_natCast (residue A), residue_eq_zero_iff]; exact hqA
    exact ringChar.of_eq (CharP.ringChar_of_prime_eq_zero hqp h0)
  have hζ1 : residue A ζ = 1 := by
    have hζq : (residue A ζ) ^ q = 1 := by rw [← map_pow, hζ.pow_eq_one, map_one]
    have h := sub_pow_char (R := ResidueField A) (p := q) (residue A ζ) 1
    rw [hζq, one_pow, sub_self] at h
    exact sub_eq_zero.mp ((pow_eq_zero_iff hqp.ne_zero).mp h)
  have hπm : (1 - ζ) ∈ maximalIdeal A := by
    rw [← residue_eq_zero_iff, map_sub, map_one, hζ1, sub_self]

  have hgeom_unit : ∀ k : ℕ, k < q → k ≠ 0 → IsUnit (∑ i ∈ range k, ζ ^ i) := by
    intro k hk hk0
    by_contra hnu
    have hmem : (∑ i ∈ range k, ζ ^ i) ∈ maximalIdeal A := (mem_maximalIdeal _).mpr hnu
    rw [← residue_eq_zero_iff, map_sum] at hmem
    simp only [map_pow, hζ1, one_pow, sum_const, card_range, nsmul_eq_mul, mul_one] at hmem
    have hdvd := (CharP.cast_eq_zero_iff (ResidueField A) q k).mp hmem
    exact hk0 (Nat.eq_zero_of_dvd_of_lt hdvd hk)

  have hζ' : IsPrimitiveRoot ζ (n + 1) := hn ▸ hζ
  have hprod : ∏ k ∈ range n, (1 - ζ ^ (k + 1)) = (q : A) := by
    rw [hζ'.prod_one_sub_pow_eq_order, hn, Nat.cast_succ]
  have hfac : ∀ k : ℕ, 1 - ζ ^ (k + 1) = (1 - ζ) * ∑ i ∈ range (k + 1), ζ ^ i :=
    fun k => (mul_neg_geom_sum ζ (k + 1)).symm
  have hvu : IsUnit (∏ k ∈ range n, ∑ i ∈ range (k + 1), ζ ^ i) := by
    rw [IsUnit.prod_iff]
    intro k hk
    refine hgeom_unit (k + 1) ?_ (Nat.succ_ne_zero k)
    rw [hn]; exact Nat.succ_lt_succ (mem_range.mp hk)
  obtain ⟨v, hv⟩ := hvu
  have hπq : (1 - ζ) ^ n * ↑v = (q : A) := by
    rw [hv, ← hprod, ← card_range n, ← prod_const, card_range, ← prod_mul_distrib]
    exact prod_congr rfl (fun k _ => (hfac k).symm)

  have hadjπ : Algebra.adjoin A₀ {(1 - ζ)} = ⊤ := by
    rw [eq_top_iff, ← hadj]
    apply Algebra.adjoin_le
    rw [Set.singleton_subset_iff, SetLike.mem_coe]
    have hmem : (1 : A) - (1 - ζ) ∈ Algebra.adjoin A₀ {(1 - ζ)} :=
      Subalgebra.sub_mem _ (Subalgebra.one_mem _) (Algebra.self_mem_adjoin_singleton A₀ (1 - ζ))
    rwa [sub_sub_cancel] at hmem
  have hdecomp : ∀ x : A, ∃ a : A₀, ∃ y : A, x = algebraMap A₀ A a + (1 - ζ) * y := by
    intro x
    have hx : x ∈ Algebra.adjoin A₀ {(1 - ζ)} := by rw [hadjπ]; exact Algebra.mem_top
    rw [Algebra.adjoin_singleton_eq_range_aeval, AlgHom.mem_range] at hx
    obtain ⟨p, rfl⟩ := hx
    refine ⟨p.coeff 0, aeval (1 - ζ) p.divX, ?_⟩
    conv_lhs => rw [← X_mul_divX_add p]
    rw [map_add, map_mul, aeval_X, aeval_C, add_comm]

  have hϖm : ϖ ∈ maximalIdeal A := by rw [hϖ]; exact Ideal.mem_span_singleton_self ϖ
  have hϖπ : ϖ ∈ Ideal.span {(1 - ζ)} := by
    obtain ⟨a, y, hay⟩ := hdecomp ϖ
    have ha : a ∈ maximalIdeal A₀ := by
      by_contra ha
      have hau : IsUnit a := by rwa [mem_maximalIdeal, mem_nonunits_iff, not_not] at ha
      have hmem : algebraMap A₀ A a ∈ maximalIdeal A := by
        have h2 : algebraMap A₀ A a = ϖ - (1 - ζ) * y := by rw [hay]; ring
        rw [h2]; exact Ideal.sub_mem _ hϖm (Ideal.mul_mem_right _ _ hπm)
      exact (mem_maximalIdeal _).mp hmem (hau.map _)
    rw [hA₀q, Ideal.mem_span_singleton'] at ha
    obtain ⟨b, hb⟩ := ha
    rw [Ideal.mem_span_singleton']
    refine ⟨algebraMap A₀ A b * ↑v * (1 - ζ) ^ m + y, ?_⟩
    rw [hay, ← hb, map_mul, map_natCast, ← hπq, hm]; ring
  have hπϖ : (1 - ζ) ∈ Ideal.span {ϖ} := by rw [← hϖ]; exact hπm
  have hassoc : Associated ϖ (1 - ζ) := by
    apply Ideal.span_singleton_eq_span_singleton.mp
    apply le_antisymm
    · rw [Ideal.span_singleton_le_iff_mem]; exact hϖπ
    · rw [Ideal.span_singleton_le_iff_mem]; exact hπϖ
  obtain ⟨w, hw⟩ := hassoc
  have hϖeq : ϖ = ↑w⁻¹ * (1 - ζ) := by
    rw [← hw, mul_comm ϖ, Units.inv_mul_cancel_left]
  refine ⟨?_, ⟨↑w⁻¹, Units.isUnit _, hϖeq⟩, ⟨↑(w⁻¹ ^ n * v⁻¹), Units.isUnit _, ?_⟩⟩
  swap
  ·
    have hnq : q - 1 = n := by omega
    rw [hnq, hϖeq, mul_pow, ← hπq, Units.val_mul, Units.val_pow_eq_pow_val]
    rw [mul_assoc, ← mul_assoc (↑v⁻¹ : A), mul_comm (↑v⁻¹ : A) ((1 - ζ) ^ n), mul_assoc,
      Units.inv_mul, mul_one]

  intro S _ _ z hz
  have hint : IsIntegral A₀ ζ := Algebra.IsIntegral.isIntegral ζ
  have hΦζ : aeval ζ (cyclotomic q A₀) = 0 := by
    rw [cyclotomic_prime, map_sum]
    simp only [map_pow, aeval_X]
    exact hζ.geom_sum_eq_zero hq1
  have hΦz : aeval z (cyclotomic q A₀) = 0 := by
    rw [cyclotomic_prime, map_sum]
    simp only [map_pow, aeval_X]
    exact hz

  have hq0 : (q : A₀) ≠ 0 := by
    intro h
    apply IsDiscreteValuationRing.not_a_field A₀
    rw [hA₀q, h, Ideal.span_singleton_eq_bot]
  set P : A₀[X] := ((cyclotomic q ℤ).comp (X + 1)).map (Int.castRingHom A₀) with hP
  have hX1 : (X + 1 : A₀[X]) = X + C 1 := by rw [C_1]
  have hPeq : P = (cyclotomic q A₀).comp (X + 1) := by
    rw [hP, map_comp, map_cyclotomic, Polynomial.map_add, map_X, Polynomial.map_one]
  have hPmonic : P.Monic := by
    rw [hPeq, hX1]
    exact (cyclotomic.monic q A₀).comp (monic_X_add_C 1) (by rw [natDegree_X_add_C]; exact one_ne_zero)
  have hE := cyclotomic_comp_X_add_one_isEisensteinAt q
  have hPE : P.IsEisensteinAt (maximalIdeal A₀) := by
    refine hPmonic.isEisensteinAt_of_mem_of_notMem (maximalIdeal.isMaximal A₀).ne_top ?_ ?_
    · intro i hi
      have hi' : i < ((cyclotomic q ℤ).comp (X + 1)).natDegree := lt_of_lt_of_le hi natDegree_map_le
      have hci := hE.mem hi'
      obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp hci
      rw [hP, coeff_map, ← hc, smul_eq_mul, map_mul]
      refine Ideal.mul_mem_left _ _ ?_
      rw [map_natCast]
      exact hqA₀
    · have h0 : P.coeff 0 = (q : A₀) := by
        rw [hPeq, coeff_zero_eq_eval_zero, eval_comp, eval_add, eval_X, eval_one, zero_add,
          eval_one_cyclotomic_prime]
      rw [h0, hA₀q, Ideal.span_singleton_pow, Ideal.mem_span_singleton]
      rintro ⟨c, hc⟩
      have h2 : (q : A₀) * (1 - q * c) = 0 := by
        rw [mul_sub, mul_one, ← mul_assoc, ← pow_two, ← hc, sub_self]
      rcases mul_eq_zero.mp h2 with h | h
      · exact hq0 h
      · have hu : IsUnit (q : A₀) := isUnit_iff_exists_inv.mpr ⟨c, (sub_eq_zero.mp h).symm⟩
        exact (mem_maximalIdeal _).mp hqA₀ hu
  have hPdeg : 0 < P.natDegree := by
    rw [hPeq, natDegree_comp, natDegree_cyclotomic, Nat.totient_prime hqp, hX1, natDegree_X_add_C]
    omega
  have hPirr : Irreducible P :=
    hPE.irreducible (maximalIdeal.isMaximal A₀).isPrime hPmonic.isPrimitive hPdeg
  have hirr : Irreducible (cyclotomic q A₀) := by
    have hPe : P = algEquivAevalXAddC (1 : A₀) (cyclotomic q A₀) := by
      rw [hPeq, algEquivAevalXAddC_apply, comp_eq_aeval, hX1]
    rw [hPe] at hPirr
    exact (MulEquiv.irreducible_iff (algEquivAevalXAddC (1 : A₀))).mp hPirr

  have hmin : minpoly A₀ ζ = cyclotomic q A₀ := by
    obtain ⟨c, hc⟩ := minpoly.isIntegrallyClosed_dvd hint hΦζ
    have hcu : IsUnit c := by
      rcases hirr.isUnit_or_isUnit hc with h | h
      · exact absurd h (minpoly.not_isUnit A₀ ζ)
      · exact h
    exact eq_of_monic_of_associated (minpoly.monic hint) (cyclotomic.monic q A₀)
      ⟨hcu.unit, by rw [IsUnit.unit_spec]; exact hc.symm⟩
  have hsurj : Function.Surjective (aeval ζ : A₀[X] →ₐ[A₀] A) := by
    rw [← AlgHom.range_eq_top, ← Algebra.adjoin_singleton_eq_range_aeval, hadj]
  have hker : RingHom.ker (aeval ζ : A₀[X] →ₐ[A₀] A).toRingHom ≤
      RingHom.ker (aeval z : A₀[X] →ₐ[A₀] S).toRingHom := by
    rw [minpoly.ker_eval hint, hmin, Ideal.span_le, Set.singleton_subset_iff, SetLike.mem_coe,
      RingHom.mem_ker]
    exact hΦz
  refine ⟨AlgHom.liftOfSurjective (aeval ζ) hsurj (aeval z) hker, ?_⟩
  have happ := AlgHom.liftOfSurjective_apply (aeval ζ) hsurj (aeval z) hker X
  rwa [aeval_X, aeval_X] at happ

end S_IsPrimitiveRoot_exists_algHom_apply_eq_of_geom_sum_eq_zero_and_eq_mul_one_sub_and_pow_sub_one_eq_mul_of_adjoin_eq_top
end P2MW
export P2MW.S_IsPrimitiveRoot_exists_algHom_apply_eq_of_geom_sum_eq_zero_and_eq_mul_one_sub_and_pow_sub_one_eq_mul_of_adjoin_eq_top (solution)
