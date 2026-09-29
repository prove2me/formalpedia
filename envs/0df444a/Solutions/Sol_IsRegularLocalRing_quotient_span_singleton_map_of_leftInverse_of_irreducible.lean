-- Prove2me | solution 1 for IsRegularLocalRing.quotient_span_singleton_map_of_leftInverse_of_irreducible
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:08.353894+00:00
-- url     : https://prove2.me/submissions/b9bd0955-8f99-596b-ab1b-8879497fbfc7

import Mathlib
import Theorems.Thm_IsRegularLocalRing_quotient_span_singleton_of_notMem_sq_of_forall_minimalPrimes_notMem
import Theorems.Thm_IsRegularLocalRing_isDomain
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_IsRegularLocalRing_quotient_span_singleton_map_of_leftInverse_of_irreducible

set_option autoImplicit false

open IsLocalRing

set_option maxHeartbeats 1600000

namespace SecSmooth

open IsLocalRing

theorem map_maximalIdeal_le_of_surjective {R A : Type*} [CommRing R] [IsLocalRing R] [CommRing A] [IsLocalRing A]
    (s : R →+* A) (hs : Function.Surjective s) : (maximalIdeal R).map s ≤ maximalIdeal A := by
  have hmax : ((maximalIdeal A).comap s).IsMaximal := Ideal.comap_isMaximal_of_surjective s hs
  have heq : (maximalIdeal A).comap s = maximalIdeal R := (IsLocalRing.eq_maximalIdeal hmax)
  rw [Ideal.map_le_iff_le_comap, heq]

theorem map_irreducible_notMem_maximalIdeal_sq {R A : Type*} [CommRing R] [IsLocalRing R] [CommRing A] [IsDomain A]
    [IsDiscreteValuationRing A] (i : A →+* R) (s : R →+* A) (hs : Function.Surjective s) (hsi : s.comp i = RingHom.id A)
    {ϖ : A} (hϖ : Irreducible ϖ) : i ϖ ∉ maximalIdeal R ^ 2 := by
  intro hmem
  have h1 : s (i ϖ) = ϖ := by rw [← RingHom.comp_apply, hsi, RingHom.id_apply]
  have h2 : ϖ ∈ (maximalIdeal A) ^ 2 := by
    rw [← h1]
    have := Ideal.mem_map_of_mem s hmem
    rw [Ideal.map_pow] at this
    exact Ideal.pow_right_mono (map_maximalIdeal_le_of_surjective s hs) 2 this
  have hϖ' := (IsDiscreteValuationRing.irreducible_iff_uniformizer ϖ).mp hϖ
  rw [hϖ', Ideal.span_singleton_pow, Ideal.mem_span_singleton] at h2
  obtain ⟨t, ht⟩ := h2
  have hϖ0 : ϖ ≠ 0 := hϖ.ne_zero
  have hunit : IsUnit ϖ := by
    refine IsUnit.of_mul_eq_one t ?_
    have : ϖ * (ϖ * t) = ϖ * 1 := by rw [mul_one, ← mul_assoc, ← pow_two]; exact ht.symm
    exact mul_left_cancel₀ hϖ0 this
  exact hϖ.not_isUnit hunit

end SecSmooth

theorem solution
    {R A : Type*} [CommRing R] [IsRegularLocalRing R] [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
    (i : A →+* R) (s : R →+* A) (hs : Function.Surjective s) (hsi : s.comp i = RingHom.id A)
    {ϖ : A} (hϖ : Irreducible ϖ) :
    ∃ _ : IsRegularLocalRing (R ⧸ Ideal.span {i ϖ}),
      (maximalIdeal (R ⧸ Ideal.span {i ϖ})).spanFinrank + 1 = (maximalIdeal R).spanFinrank ∧
        ringKrullDim (R ⧸ Ideal.span {i ϖ}) + 1 = ringKrullDim R := by
  classical

  have hxs : s (i ϖ) = ϖ := by rw [← RingHom.comp_apply, hsi, RingHom.id_apply]
  have hxm : i ϖ ∈ maximalIdeal R := by
    rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
    intro hu
    exact hϖ.not_isUnit (hxs ▸ hu.map s)
  have hx2 : i ϖ ∉ maximalIdeal R ^ 2 := SecSmooth.map_irreducible_notMem_maximalIdeal_sq i s hs hsi hϖ
  haveI : IsDomain R := IsRegularLocalRing.isDomain R
  have hx0 : i ϖ ≠ 0 := fun h0 => hϖ.ne_zero (by rw [← hxs, h0, map_zero])

  have hmin : ∀ p ∈ minimalPrimes R, i ϖ ∉ p := by
    intro p hp hxp
    have hle : p ≤ ⊥ := hp.2 ⟨Ideal.bot_prime, le_rfl⟩ bot_le
    exact hx0 (by simpa using hle hxp)

  haveI : Nontrivial (R ⧸ Ideal.span {i ϖ}) :=
    Ideal.Quotient.nontrivial_iff.mpr (Ideal.span_singleton_ne_top (fun hu => hϖ.not_isUnit (hxs ▸ hu.map s)))
  haveI : IsLocalRing (R ⧸ Ideal.span {i ϖ}) := .of_surjective' _ Ideal.Quotient.mk_surjective

  obtain ⟨hreg, hfin⟩ :=
    IsRegularLocalRing.quotient_span_singleton_of_notMem_sq_of_forall_minimalPrimes_notMem R hxm hx2 hmin
  refine ⟨hreg, hfin, ?_⟩

  haveI := hreg
  rw [← IsRegularLocalRing.spanFinrank_maximalIdeal (R := R), ← IsRegularLocalRing.spanFinrank_maximalIdeal (R := R ⧸ Ideal.span {i ϖ}),
    ← hfin]
  push_cast
  rfl

end S_IsRegularLocalRing_quotient_span_singleton_map_of_leftInverse_of_irreducible
end P2MW
export P2MW.S_IsRegularLocalRing_quotient_span_singleton_map_of_leftInverse_of_irreducible (solution)
