-- Prove2me | solution 1 for NumberField.natCast_factorization_natAbs_discr_eq_finsum_inertiaDeg_mul_addCharLevel_psiLocal
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.93214+00:00
-- url     : https://prove2.me/submissions/a1ceea4c-0b6c-5b05-8b83-feac14e78c5e

import Definitions.Def_LanglandsTunnell_ConverseData
import Definitions.Def_LanglandsTunnell_RankinSelbergEuler
import Mathlib.NumberTheory.NumberField.Discriminant.Different
import Mathlib.NumberTheory.RamificationInertia.Inertia
import Mathlib.RingTheory.DedekindDomain.Factorization
import Mathlib.Data.Nat.Factorization.Basic
import Theorems.Thm_LanglandsTunnell_TateLocal_addCharLevel_psiLocal_eq_count_differentIdeal
import Theorems.Thm_IsDedekindDomain_HeightOneSpectrum_exists_prime_and_asIdeal_eq_span_ringOfIntegers_rat
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_NumberField_natCast_factorization_natAbs_discr_eq_finsum_inertiaDeg_mul_addCharLevel_psiLocal

set_option autoImplicit false

p2m_open "IsDedekindDomain NumberField P2MW.S_NumberField_natCast_factorization_natAbs_discr_eq_finsum_inertiaDeg_mul_addCharLevel_psiLocal.NumberField NumberField.StandardAddChar LanglandsTunnell.RankinSelberg LanglandsTunnell.TateLocal"

open scoped nonZeroDivisors

namespace NumberField
p2m_export "NumberField" "discr mk place RingOfIntegers absNorm_differentIdeal RingOfIntegers.rank"
namespace DiscFactorization
p2m_open "NumberField"

theorem absNorm_span_natCast_rat (p : ℕ) : Ideal.absNorm (Ideal.span {(p : 𝓞 ℚ)}) = p := by
  rw [Ideal.absNorm_span_singleton]
  have h : (p : 𝓞 ℚ) = algebraMap ℤ (𝓞 ℚ) (p : ℤ) := by simp
  rw [h, Algebra.norm_algebraMap, NumberField.RingOfIntegers.rank, Module.finrank_self, pow_one, Int.natAbs_natCast]

theorem eq_of_asIdeal_eq_span {v v' : HeightOneSpectrum (𝓞 ℚ)} {p : ℕ}
    (hv : v.asIdeal = Ideal.span {(p : 𝓞 ℚ)}) (hv' : v'.asIdeal = Ideal.span {(p : 𝓞 ℚ)}) : v = v' :=
  HeightOneSpectrum.ext (hv.trans hv'.symm)

open scoped Classical in

theorem factorization_absNorm_asIdeal (K : Type) [Field K] [NumberField K]
    (v : HeightOneSpectrum (𝓞 ℚ)) (p : ℕ) (hp : p.Prime) (hvp : v.asIdeal = Ideal.span {(p : 𝓞 ℚ)})
    (w : HeightOneSpectrum (𝓞 K)) :
    (Ideal.absNorm w.asIdeal).factorization p =
      if w ∈ primeFibre ℚ K v then v.asIdeal.inertiaDeg' w.asIdeal else 0 := by
  classical

  set v' : HeightOneSpectrum (𝓞 ℚ) := w.under (𝓞 ℚ) with hv'def
  haveI : w.asIdeal.LiesOver v'.asIdeal := (Ideal.liesOver_iff _ _).mpr rfl
  haveI := v'.isPrime
  have hN : Ideal.absNorm w.asIdeal = Ideal.absNorm v'.asIdeal ^ v'.asIdeal.inertiaDeg' w.asIdeal :=
    Ideal.absNorm_eq_pow_inertiaDeg_of_liesOver w.asIdeal v'.asIdeal v'.isPrime v'.ne_bot
  obtain ⟨p', hp', hv'p⟩ := IsDedekindDomain.HeightOneSpectrum.exists_prime_and_asIdeal_eq_span_ringOfIntegers_rat v'
  have hN' : Ideal.absNorm v'.asIdeal = p' := by rw [hv'p, absNorm_span_natCast_rat]
  rw [hN, hN', Nat.factorization_pow, Finsupp.smul_apply, smul_eq_mul, hp'.factorization, Finsupp.single_apply]
  by_cases hw : w ∈ primeFibre ℚ K v
  ·
    have hvv : v' = v := hw
    have hpp : p' = p := by
      have h1 : Ideal.absNorm v.asIdeal = p := by rw [hvp, absNorm_span_natCast_rat]
      rw [← hN', hvv, h1]
    rw [if_pos hw, if_pos hpp, mul_one, hvv]
  · have hpp : p' ≠ p := by
      intro h
      apply hw
      show w.under (𝓞 ℚ) = v
      rw [← hv'def]
      exact eq_of_asIdeal_eq_span (h ▸ hv'p) hvp
    rw [if_neg hw, if_neg hpp, mul_zero]

end NumberField.DiscFactorization

open NumberField.DiscFactorization in

theorem solution
    (K : Type) [Field K] [NumberField K] (v : HeightOneSpectrum (𝓞 ℚ)) :
    (((discr K).natAbs.factorization (Ideal.absNorm v.asIdeal) : ℕ) : ℤ) =
      ∑ᶠ w ∈ primeFibre ℚ K v,
        (v.asIdeal.inertiaDeg' w.asIdeal : ℤ) * addCharLevel (psiLocal K w) := by
  classical
  obtain ⟨p, hp, hvp⟩ := IsDedekindDomain.HeightOneSpectrum.exists_prime_and_asIdeal_eq_span_ringOfIntegers_rat v
  have hNv : Ideal.absNorm v.asIdeal = p := by rw [hvp, absNorm_span_natCast_rat]
  rw [hNv]

  set I : Ideal (𝓞 K) := differentIdeal ℤ (𝓞 K) with hIdef
  have hI0 : I ≠ ⊥ := differentIdeal_ne_bot
  set n : HeightOneSpectrum (𝓞 K) → ℕ := fun w => (Associates.mk w.asIdeal).count (Associates.mk I).factors
    with hndef
  have hlev : ∀ w : HeightOneSpectrum (𝓞 K), addCharLevel (psiLocal K w) = (n w : ℤ) := by
    intro w
    rw [LanglandsTunnell.TateLocal.addCharLevel_psiLocal_eq_count_differentIdeal, FractionalIdeal.count_coe K w hI0]

  have hfinN : {w : HeightOneSpectrum (𝓞 K) | n w ≠ 0}.Finite := by
    have h := Filter.eventually_cofinite.mp (Associates.finite_factors hI0)
    refine h.subset fun w hw => ?_
    simp only [Set.mem_setOf_eq] at hw ⊢
    exact_mod_cast hw
  have hsub : ∀ w : HeightOneSpectrum (𝓞 K), w ∈ primeFibre ℚ K v →
      w.asIdeal ∈ IsDedekindDomain.primesOverFinset v.asIdeal (𝓞 K) := by
    intro w hw
    rw [mem_primeFibre] at hw
    rw [IsDedekindDomain.mem_primesOverFinset_iff v.ne_bot]
    refine ⟨w.isPrime, (Ideal.liesOver_iff _ _).mpr ?_⟩
    rw [← hw]
    rfl
  have hfinF : (primeFibre ℚ K v).Finite :=
    ((IsDedekindDomain.primesOverFinset v.asIdeal (𝓞 K)).finite_toSet.preimage
      (f := fun w : HeightOneSpectrum (𝓞 K) => w.asIdeal) (fun a _ b _ h => HeightOneSpectrum.ext h)).subset
      (fun w hw => hsub w hw)
  set U : Finset (HeightOneSpectrum (𝓞 K)) := hfinN.toFinset ∪ hfinF.toFinset with hU

  have hdisc : (discr K).natAbs = Ideal.absNorm I := (NumberField.absNorm_differentIdeal K (𝓞 K)).symm
  have hprod : I = ∏ w ∈ U, w.asIdeal ^ n w := by
    conv_lhs => rw [← Ideal.finprod_heightOneSpectrum_factorization hI0]
    rw [finprod_eq_prod_of_mulSupport_subset _ (s := U) ?_]
    · exact Finset.prod_congr rfl fun w _ => rfl
    · intro w hw
      rw [Function.mem_mulSupport] at hw
      simp only [hU, Finset.coe_union, Set.mem_union, Set.Finite.coe_toFinset, Set.mem_setOf_eq]
      left
      intro h0
      apply hw
      rw [IsDedekindDomain.HeightOneSpectrum.maxPowDividing]
      change w.asIdeal ^ n w = 1
      rw [h0, pow_zero]
  have habs : Ideal.absNorm I = ∏ w ∈ U, Ideal.absNorm w.asIdeal ^ n w := by
    conv_lhs => rw [hprod]
    rw [map_prod]
    exact Finset.prod_congr rfl fun w _ => map_pow _ _ _
  have hne : ∀ w ∈ U, Ideal.absNorm w.asIdeal ^ n w ≠ 0 := by
    intro w _
    exact pow_ne_zero _ (by rw [Ne, Ideal.absNorm_eq_zero_iff]; exact w.ne_bot)
  have hL : (discr K).natAbs.factorization p =
      ∑ w ∈ U, n w * (if w ∈ primeFibre ℚ K v then v.asIdeal.inertiaDeg' w.asIdeal else 0) := by
    rw [hdisc, habs, Nat.factorization_prod hne, Finset.sum_apply']
    refine Finset.sum_congr rfl fun w _ => ?_
    rw [Nat.factorization_pow, Finsupp.smul_apply, smul_eq_mul, factorization_absNorm_asIdeal K v p hp hvp w]

  set g : HeightOneSpectrum (𝓞 K) → ℤ := fun w =>
    ((n w * (if w ∈ primeFibre ℚ K v then v.asIdeal.inertiaDeg' w.asIdeal else 0) : ℕ) : ℤ) with hgdef
  have hsubU : hfinF.toFinset ⊆ U := by rw [hU]; exact Finset.subset_union_right
  have hz : ∀ w ∈ U, w ∉ hfinF.toFinset → g w = 0 := by
    intro w _ hw
    have hw' : w ∉ primeFibre ℚ K v := fun h => hw (hfinF.mem_toFinset.mpr h)
    simp only [hgdef, if_neg hw', mul_zero, Nat.cast_zero]
  have hc : ∀ w ∈ hfinF.toFinset, g w = (v.asIdeal.inertiaDeg' w.asIdeal : ℤ) * addCharLevel (psiLocal K w) := by
    intro w hw
    have hw' : w ∈ primeFibre ℚ K v := hfinF.mem_toFinset.mp hw
    simp only [hgdef, if_pos hw', hlev w]
    push_cast
    ring
  have hR : ∑ w ∈ U, g w =
      ∑ᶠ w ∈ primeFibre ℚ K v, (v.asIdeal.inertiaDeg' w.asIdeal : ℤ) * addCharLevel (psiLocal K w) := by
    rw [finsum_mem_eq_finite_toFinset_sum _ hfinF, ← Finset.sum_subset hsubU hz]
    exact Finset.sum_congr rfl hc
  rw [hL, ← hR, Nat.cast_sum]

end S_NumberField_natCast_factorization_natAbs_discr_eq_finsum_inertiaDeg_mul_addCharLevel_psiLocal
end P2MW
export P2MW.S_NumberField_natCast_factorization_natAbs_discr_eq_finsum_inertiaDeg_mul_addCharLevel_psiLocal (solution)
