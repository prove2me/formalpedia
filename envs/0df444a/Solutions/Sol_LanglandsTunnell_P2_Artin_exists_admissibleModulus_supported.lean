-- Prove2me | solution 1 for LanglandsTunnell.P2.Artin.exists_admissibleModulus_supported
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:08.670037+00:00
-- url     : https://prove2.me/submissions/842a9dce-98b7-5056-853a-45a54dc85db3

import Definitions.Def_LanglandsTunnell_ArtinCoreCTM
import Definitions.Def_M4aHerbrand_GenuineDescent
import Definitions.Def_LanglandsTunnell_ArtinFrobenius
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_LanglandsTunnell_P2_Artin_exists_admissibleModulus_supported

set_option autoImplicit false
attribute [local instance] FractionRing.liftAlgebra
attribute [local instance] Ideal.Quotient.field

noncomputable section

open NumberField IsDedekindDomain LanglandsTunnell.P2.Artin

variable {K L : Type*} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]

private theorem residue_isSeparable (v : HeightOneSpectrum (𝓞 K)) :
    Algebra.IsSeparable ((𝓞 K) ⧸ v.asIdeal) ((𝓞 L) ⧸ primeAbove K L v) := by
  haveI : Finite ((𝓞 K) ⧸ v.asIdeal) := Ideal.finiteQuotientOfFreeOfNeBot _ v.ne_bot
  haveI : v.asIdeal.IsMaximal := v.isPrime.isMaximal v.ne_bot
  haveI : Algebra.IsAlgebraic ((𝓞 K) ⧸ v.asIdeal) ((𝓞 L) ⧸ primeAbove K L v) :=
    Algebra.IsAlgebraic.of_finite _ _
  haveI : PerfectField ((𝓞 K) ⧸ v.asIdeal) := PerfectField.ofFinite
  exact Algebra.IsAlgebraic.isSeparable_of_perfectField

variable [IsGalois K L]

private theorem not_unramifiedAt_of_inertia_ne_bot (v : HeightOneSpectrum (𝓞 K))
    (h : (primeAbove K L v).inertia (L ≃ₐ[K] L) ≠ ⊥) :
    ¬ Algebra.IsUnramifiedAt (𝓞 K) (primeAbove K L v) := by
  intro hur
  haveI : (primeAbove K L v).IsPrime := (primeAbove_isMaximal K L v).isPrime
  haveI := residue_isSeparable (L := L) v
  have hcard : Nat.card ((primeAbove K L v).inertia (L ≃ₐ[K] L)) =
      (v.asIdeal).ramificationIdxIn (𝓞 L) :=
    Ideal.card_inertia_eq_ramificationIdxIn v.asIdeal (primeAbove K L v)
  have hIn : (v.asIdeal).ramificationIdxIn (𝓞 L) =
      v.asIdeal.ramificationIdx' (primeAbove K L v) :=
    (Ideal.ramificationIdxIn_eq_ramificationIdx v.asIdeal (primeAbove K L v) (L ≃ₐ[K] L)).trans
      (Ideal.ramificationIdx'_eq_ramificationIdx v.asIdeal (primeAbove K L v) v.ne_bot).symm
  have he1 : v.asIdeal.ramificationIdx' (primeAbove K L v) = 1 := by
    rw [Ideal.ramificationIdx'_eq_ramificationIdx v.asIdeal (primeAbove K L v) v.ne_bot]
    exact Ideal.ramificationIdx_eq_one_of_isUnramifiedAt
  have h1 : 1 < Nat.card ((primeAbove K L v).inertia (L ≃ₐ[K] L)) :=
    (Subgroup.one_lt_card_iff_ne_bot _).mpr h
  rw [hcard, hIn, he1] at h1
  exact lt_irrefl 1 h1

private theorem primeAbove_dvd_differentIdeal (v : HeightOneSpectrum (𝓞 K))
    (h : (primeAbove K L v).inertia (L ≃ₐ[K] L) ≠ ⊥) :
    primeAbove K L v ∣ differentIdeal (𝓞 K) (𝓞 L) := by
  haveI : (primeAbove K L v).IsPrime := (primeAbove_isMaximal K L v).isPrime
  exact dvd_differentIdeal_iff.mpr (not_unramifiedAt_of_inertia_ne_bot v h)

private theorem finite_inertiaRamified :
    {v : HeightOneSpectrum (𝓞 K) |
      (primeAbove K L v).inertia (L ≃ₐ[K] L) ≠ ⊥}.Finite := by
  have hD : differentIdeal (𝓞 K) (𝓞 L) ≠ 0 := by
    simpa [Ideal.zero_eq_bot] using differentIdeal_ne_bot (A := 𝓞 K) (B := 𝓞 L)
  have hT : {Q : HeightOneSpectrum (𝓞 L) | Q.asIdeal ∣ differentIdeal (𝓞 K) (𝓞 L)}.Finite :=
    Ideal.finite_factors hD
  have himg : ((fun v : HeightOneSpectrum (𝓞 K) =>
      (⟨primeAbove K L v, (primeAbove_isMaximal K L v).isPrime, primeAbove_ne_bot K L v⟩ :
        HeightOneSpectrum (𝓞 L))) ''
      {v | (primeAbove K L v).inertia (L ≃ₐ[K] L) ≠ ⊥}).Finite := by
    refine hT.subset ?_
    rintro Q ⟨v, hv, rfl⟩
    exact primeAbove_dvd_differentIdeal v hv
  refine Set.Finite.of_finite_image himg ?_
  intro v _ v' _ hvv'
  have h1 : primeAbove K L v = primeAbove K L v' := congrArg HeightOneSpectrum.asIdeal hvv'
  have h2 : v.asIdeal = v'.asIdeal := by
    rw [← under_primeAbove K L v, ← under_primeAbove K L v', h1]
  cases v; cases v'
  simpa using h2

theorem solution (K L : Type*) [Field K]
    [NumberField K] [Field L] [NumberField L] [Algebra K L] [IsGalois K L] :
    ∃ 𝔣₀ : Ideal (𝓞 K), LanglandsTunnell.P2.Artin.IsAdmissibleModulus K L 𝔣₀ ∧
      ∀ v₀ : HeightOneSpectrum (𝓞 K), v₀.asIdeal ∣ 𝔣₀ →
        ∃ Q : Ideal (𝓞 L), Q.IsPrime ∧ Q.LiesOver v₀.asIdeal ∧
          Q.inertia (L ≃ₐ[K] L) ≠ ⊥ := by
  classical
  have hfin := finite_inertiaRamified (K := K) (L := L)
  refine ⟨∏ v ∈ hfin.toFinset, v.asIdeal ^ admissibleExp K v, ⟨?_, ?_⟩, ?_⟩
  · rw [← Ideal.zero_eq_bot, Finset.prod_ne_zero_iff]
    intro v _
    exact pow_ne_zero _ (by rw [Ideal.zero_eq_bot]; exact v.ne_bot)
  · intro v hv
    exact Finset.dvd_prod_of_mem _ (hfin.mem_toFinset.mpr hv)
  · intro v₀ hdvd
    have hP : Prime v₀.asIdeal := Ideal.prime_of_isPrime v₀.ne_bot v₀.isPrime
    obtain ⟨v, hvS, hdvd'⟩ := hP.exists_mem_finset_dvd hdvd
    have hle : v.asIdeal ≤ v₀.asIdeal := Ideal.le_of_dvd (hP.dvd_of_dvd_pow hdvd')
    have heq : v.asIdeal = v₀.asIdeal :=
      (v.isPrime.isMaximal v.ne_bot).eq_of_le v₀.isPrime.ne_top hle
    have hv : (primeAbove K L v).inertia (L ≃ₐ[K] L) ≠ ⊥ := hfin.mem_toFinset.mp hvS
    have hvv0 : v = v₀ := by cases v; cases v₀; simpa using heq
    refine ⟨primeAbove K L v₀, (primeAbove_isMaximal K L v₀).isPrime,
      primeAbove_liesOver K L v₀, ?_⟩
    rw [← hvv0]
    exact hv

end

end S_LanglandsTunnell_P2_Artin_exists_admissibleModulus_supported
end P2MW
export P2MW.S_LanglandsTunnell_P2_Artin_exists_admissibleModulus_supported (solution)
