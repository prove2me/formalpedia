-- Prove2me | solution 1 for IsRegularLocalRing.of_etale_of_isLocalRing_of_maximalIdeal_eq_span_pair
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:08.353894+00:00
-- url     : https://prove2.me/submissions/916213fd-d1f5-587e-92d5-449b206e3563

import Mathlib
import Theorems.Thm_IsLocalRing_isAdicComplete_of_module_finite
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_IsRegularLocalRing_of_etale_of_isLocalRing_of_maximalIdeal_eq_span_pair

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 1600000
set_option maxHeartbeats 6400000

open IsLocalRing Polynomial

universe u v

namespace KFDimFin

open Order

variable {A : Type u} {B : Type v} [CommRing A] [CommRing B] [Algebra A B] [Algebra.IsIntegral A B]

noncomputable def contract (q : PrimeSpectrum B) : PrimeSpectrum A :=
  ⟨q.asIdeal.comap (algebraMap A B), inferInstance⟩

theorem contract_strictMono : StrictMono (contract (A := A) (B := B)) := by
  intro p q hpq
  have hlt : p.asIdeal < q.asIdeal := (PrimeSpectrum.asIdeal_lt_asIdeal p q).mpr hpq
  haveI := p.isPrime
  have := Ideal.IsIntegral.comap_lt_comap (R := A) hlt
  exact (PrimeSpectrum.asIdeal_lt_asIdeal _ _).mp this

theorem le_dim : ringKrullDim B ≤ ringKrullDim A :=
  krullDim_le_of_strictMono _ contract_strictMono

theorem exists_lift (hinj : Function.Injective (algebraMap A B)) :
    ∀ (n : ℕ) (p : LTSeries (PrimeSpectrum A)), p.length = n →
      ∃ q : LTSeries (PrimeSpectrum B), q.length = n ∧
        q.last.asIdeal.comap (algebraMap A B) = p.last.asIdeal := by
  intro n
  induction n with
  | zero =>
    intro p hp
    haveI := p.last.isPrime
    have hbot : (⊥ : Ideal B).comap (algebraMap A B) ≤ p.last.asIdeal := by
      rw [← RingHom.ker_eq_comap_bot, (RingHom.injective_iff_ker_eq_bot _).mp hinj]
      exact bot_le
    obtain ⟨Q, -, hQp, hQ⟩ := Ideal.exists_ideal_over_prime_of_isIntegral p.last.asIdeal ⊥ hbot
    exact ⟨RelSeries.singleton _ ⟨Q, hQp⟩, rfl, by simpa using hQ⟩
  | succ n ih =>
    intro p hp
    have hpos : p.length ≠ 0 := by omega
    obtain ⟨q', hq'len, hq'⟩ := ih p.eraseLast (by simp [hp])
    have hrel : p.eraseLast.last < p.last := RelSeries.eraseLast_last_rel_last p hpos
    have hrelI : p.eraseLast.last.asIdeal < p.last.asIdeal := (PrimeSpectrum.asIdeal_lt_asIdeal _ _).mpr hrel
    haveI := p.last.isPrime
    haveI := q'.last.isPrime
    have hle : q'.last.asIdeal.comap (algebraMap A B) ≤ p.last.asIdeal := by
      rw [hq']; exact hrelI.le
    obtain ⟨Q, hQge, hQp, hQ⟩ := Ideal.exists_ideal_over_prime_of_isIntegral p.last.asIdeal q'.last.asIdeal hle
    have hlt : q'.last < ⟨Q, hQp⟩ := by
      rw [← PrimeSpectrum.asIdeal_lt_asIdeal]
      refine lt_of_le_of_ne hQge ?_
      intro heq
      apply hrelI.ne
      rw [← hq', ← hQ]
      exact congrArg _ heq
    refine ⟨q'.snoc ⟨Q, hQp⟩ hlt, by simp [hq'len], ?_⟩
    simpa using hQ

theorem dim_le (hinj : Function.Injective (algebraMap A B)) : ringKrullDim A ≤ ringKrullDim B := by
  unfold ringKrullDim krullDim
  refine iSup_le fun p => ?_
  obtain ⟨q, hq, -⟩ := exists_lift hinj p.length p rfl
  exact le_iSup_of_le q (by rw [hq])

end KFDimFin

theorem solution
    {R : Type u} [CommRing R] [IsRegularLocalRing R] [IsAdicComplete (maximalIdeal R) R]
    (ϖ s : R) (hmax : maximalIdeal R = Ideal.span {ϖ, s}) (hdim : ringKrullDim R = 2)
    (R₁ : Type v) [CommRing R₁] [IsLocalRing R₁] [Algebra R R₁] [Module.Finite R R₁] [Algebra.Etale R R₁] :
    IsRegularLocalRing R₁ ∧ ringKrullDim R₁ = 2 ∧
      maximalIdeal R₁ = Ideal.span {algebraMap R R₁ ϖ, algebraMap R R₁ s} ∧
      IsAdicComplete (maximalIdeal R₁) R₁ := by
  classical
  haveI : IsNoetherianRing R := inferInstance
  haveI : IsLocalRing R := inferInstance

  haveI : IsNoetherianRing R₁ := isNoetherian_of_tower R (inferInstance : IsNoetherian R R₁)
  haveI : Algebra.IsIntegral R R₁ := inferInstance

  haveI hloc : IsLocalHom (algebraMap R R₁) := by
    constructor
    intro x hx
    by_contra hnu
    have hxm : x ∈ maximalIdeal R := (IsLocalRing.mem_maximalIdeal _).mpr hnu
    have hcomax : ((maximalIdeal R₁).comap (algebraMap R R₁)).IsMaximal :=
      Ideal.isMaximal_comap_of_isIntegral_of_isMaximal (maximalIdeal R₁)
    have heq : (maximalIdeal R₁).comap (algebraMap R R₁) = maximalIdeal R := IsLocalRing.eq_maximalIdeal hcomax
    have : algebraMap R R₁ x ∈ maximalIdeal R₁ := by rw [← Ideal.mem_comap, heq]; exact hxm
    exact (IsLocalRing.mem_maximalIdeal _).mp this hx

  have hm : (maximalIdeal R).map (algebraMap R R₁) = maximalIdeal R₁ := Algebra.FormallyUnramified.map_maximalIdeal
  have hm₁ : maximalIdeal R₁ = Ideal.span {algebraMap R R₁ ϖ, algebraMap R R₁ s} := by
    rw [← hm, hmax, Ideal.map_span, Set.image_insert_eq, Set.image_singleton]

  haveI : Module.FaithfullyFlat R R₁ := Module.FaithfullyFlat.of_flat_of_isLocalHom
  have hinj : Function.Injective (algebraMap R R₁) := by
    exact FaithfulSMul.algebraMap_injective R R₁
  have hdim₁ : ringKrullDim R₁ = 2 := by
    rw [← hdim]
    exact le_antisymm KFDimFin.le_dim (KFDimFin.dim_le hinj)

  have hreg : IsRegularLocalRing R₁ := by
    apply IsRegularLocalRing.of_spanFinrank_maximalIdeal_le
    rw [hdim₁, hm₁]
    have h := Submodule.spanFinrank_span_le_encard (R := R₁) (M := R₁) ({algebraMap R R₁ ϖ, algebraMap R R₁ s} : Set R₁)
    have h2 : ({algebraMap R R₁ ϖ, algebraMap R R₁ s} : Set R₁).encard ≤ 2 := by
      refine (Set.encard_insert_le _ _).trans ?_
      rw [Set.encard_singleton]; rfl
    have : ((Ideal.span {algebraMap R R₁ ϖ, algebraMap R R₁ s}).spanFinrank : ℕ∞) ≤ 2 := h.trans h2
    exact_mod_cast this

  have hcompl : IsAdicComplete (maximalIdeal R₁) R₁ := IsLocalRing.isAdicComplete_of_module_finite (𝒪 := R)
  exact ⟨hreg, hdim₁, hm₁, hcompl⟩

end S_IsRegularLocalRing_of_etale_of_isLocalRing_of_maximalIdeal_eq_span_pair
end P2MW
export P2MW.S_IsRegularLocalRing_of_etale_of_isLocalRing_of_maximalIdeal_eq_span_pair (solution)
