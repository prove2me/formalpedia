-- Prove2me | solution 1 for HeckeCharacter.mem_iff_forall_valued_algebraMap_finiteAdeleRing_le
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:07.331093+00:00
-- url     : https://prove2.me/submissions/2c66054b-8428-56a9-b96b-a9222ee78ae3

import Mathlib
import Definitions.Def_LanglandsTunnell_ArtinCoreCTM
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_HeckeCharacter_mem_iff_forall_valued_algebraMap_finiteAdeleRing_le

set_option autoImplicit false

open NumberField IsDedekindDomain Deep.NTSupply HeckeCharacter LanglandsTunnell.P2.Artin
open scoped nonZeroDivisors

theorem solution
    (K : Type*) [Field K] [NumberField K] (𝔣 : Ideal (𝓞 K)) (h𝔣 : 𝔣 ≠ ⊥) (r : 𝓞 K) :
    r ∈ 𝔣 ↔ ∀ v : HeightOneSpectrum (𝓞 K), v.asIdeal ∣ 𝔣 →
      Valued.v ((algebraMap K (FiniteAdeleRing (𝓞 K) K) (r : K)) v) ≤
        WithZero.exp (-((Associates.mk v.asIdeal).count (Associates.mk 𝔣).factors : ℤ)) := by
  classical
  have h𝔣0 : 𝔣 ≠ 0 := by rwa [Ne, Submodule.zero_eq_bot]
  have hmk : Associates.mk 𝔣 ≠ 0 := Associates.mk_ne_zero.mpr h𝔣0

  have hloc : ∀ v : HeightOneSpectrum (𝓞 K),
      Valued.v ((algebraMap K (FiniteAdeleRing (𝓞 K) K) (r : K)) v) ≤
        WithZero.exp (-((Associates.mk v.asIdeal).count (Associates.mk 𝔣).factors : ℤ)) ↔
      v.asIdeal ^ (Associates.mk v.asIdeal).count (Associates.mk 𝔣).factors ∣ Ideal.span {r} := by
    intro v
    rw [FiniteAdeleRing.algebraMap_apply, HeightOneSpectrum.valuedAdicCompletion_eq_valuation',
      show ((r : 𝓞 K) : K) = algebraMap (𝓞 K) K r from rfl, HeightOneSpectrum.valuation_of_algebraMap,
      HeightOneSpectrum.intValuation_le_pow_iff_dvd]
  simp_rw [hloc]
  rw [← Ideal.dvd_span_singleton]
  constructor
  · intro h v _
    refine dvd_trans ?_ h
    rw [← Associates.mk_le_mk_iff_dvd, Associates.mk_pow]
    exact (Associates.prime_pow_dvd_iff_le hmk v.associates_irreducible).mpr le_rfl
  · intro h
    rw [← Ideal.finprod_heightOneSpectrum_factorization h𝔣0,
      finprod_eq_prod_of_mulSupport_subset _ (s := (Ideal.hasFiniteMulSupport h𝔣0).toFinset)
        (by rw [Set.Finite.coe_toFinset])]
    refine Finset.prod_dvd_of_coprime ?_ ?_
    · intro v _ w _ hvw
      show IsCoprime (v.maxPowDividing 𝔣) (w.maxPowDividing 𝔣)
      simp only [HeightOneSpectrum.maxPowDividing]
      refine IsCoprime.pow ?_
      rw [Ideal.isCoprime_iff_sup_eq]
      exact v.isMaximal.coprime_of_ne w.isMaximal fun heq => hvw (HeightOneSpectrum.ext heq)
    · intro v _
      by_cases hv : v.asIdeal ∣ 𝔣
      · exact h v hv
      · have h0 : (Associates.mk v.asIdeal).count (Associates.mk 𝔣).factors = 0 := by
          by_contra hne
          exact hv (Associates.mk_le_mk_iff_dvd.mp
            (Associates.le_of_count_ne_zero hmk v.associates_irreducible hne))
        simp only [HeightOneSpectrum.maxPowDividing, h0, pow_zero]
        exact one_dvd _

end S_HeckeCharacter_mem_iff_forall_valued_algebraMap_finiteAdeleRing_le
end P2MW
export P2MW.S_HeckeCharacter_mem_iff_forall_valued_algebraMap_finiteAdeleRing_le (solution)
