-- Prove2me | solution 1 for IsIntegrallyClosed.exists_isRegular_pair_of_two_le_ringKrullDim
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:07.85352+00:00
-- url     : https://prove2.me/submissions/dc667970-7e5a-5267-8ff3-f676cca19f5f

import Mathlib
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_IsIntegrallyClosed_exists_isRegular_pair_of_two_le_ringKrullDim

set_option autoImplicit false

open scoped Pointwise

theorem solution
    {B : Type*} [CommRing B] [IsDomain B] [IsNoetherianRing B] [IsLocalRing B] [IsIntegrallyClosed B]
    (hdim : 2 ≤ ringKrullDim B) (t : B) (ht : t ∈ IsLocalRing.maximalIdeal B) (ht0 : t ≠ 0) :
    ∃ b : B, b ∈ IsLocalRing.maximalIdeal B ∧ RingTheory.Sequence.IsRegular B [t, b] := by
  classical
  set 𝔪 : Ideal B := IsLocalRing.maximalIdeal B with h𝔪
  have h𝔪max : 𝔪.IsMaximal := IsLocalRing.maximalIdeal.isMaximal B

  have key : ∃ b ∈ 𝔪, IsSMulRegular (QuotSMulTop t B) b := by
    by_contra hcon
    push_neg at hcon

    have hsub : (𝔪 : Set B) ⊆ ⋃ p ∈ associatedPrimes B (QuotSMulTop t B), (p : Set B) := by
      rw [biUnion_associatedPrimes_eq_compl_regular]
      exact fun b hb => hcon b hb
    have hfin := associatedPrimes.finite B (QuotSMulTop t B)
    have hsub' : (𝔪 : Set B) ⊆ ⋃ p ∈ (↑hfin.toFinset : Set (Ideal B)), (p : Set B) := by
      simpa only [Set.Finite.coe_toFinset] using hsub
    obtain ⟨p, hp, h𝔪p⟩ := (Ideal.subset_union_prime (f := fun q : Ideal B => q) 𝔪 𝔪
      (fun q hq _ _ => ((hfin.mem_toFinset).mp hq).isPrime)).mp hsub'
    have hpA : IsAssociatedPrime p (QuotSMulTop t B) := (hfin.mem_toFinset).mp hp
    have hp𝔪 : p = 𝔪 := (h𝔪max.eq_of_le hpA.isPrime.ne_top h𝔪p).symm

    obtain ⟨-, x, hx⟩ := isAssociatedPrime_iff.mp hpA
    rw [hp𝔪] at hx
    have hann : ∀ m ∈ 𝔪, m • x = 0 := fun m hm => by
      have h : m ∈ (⊥ : Submodule B (QuotSMulTop t B)).colon {x} := hx ▸ hm
      exact (Submodule.mem_bot B).mp (Submodule.mem_colon_singleton.mp h)
    have hx0 : x ≠ 0 := by
      intro h0
      apply h𝔪max.ne_top
      rw [Ideal.eq_top_iff_one, hx]
      exact Submodule.mem_colon_singleton.mpr (by rw [h0, smul_zero]; exact Submodule.zero_mem _)
    obtain ⟨b₀, rfl⟩ := Submodule.Quotient.mk_surjective (t • (⊤ : Submodule B B)) x
    have hb₀ : b₀ ∉ t • (⊤ : Submodule B B) := fun h => hx0 ((Submodule.Quotient.mk_eq_zero _).mpr h)

    have hdiv : ∀ m ∈ 𝔪, ∃ c : B, t * c = m * b₀ := fun m hm => by
      have h1 : (Submodule.Quotient.mk (m * b₀) : QuotSMulTop t B) = 0 := by
        have h := hann m hm
        rwa [← Submodule.Quotient.mk_smul, smul_eq_mul] at h
      rw [Submodule.Quotient.mk_eq_zero] at h1
      obtain ⟨c, -, hc⟩ := (Submodule.mem_smul_pointwise_iff_exists _ _ _).mp h1
      exact ⟨c, by simpa [smul_eq_mul] using hc⟩
    choose! e he using hdiv
    by_cases hcase : ∀ m ∈ 𝔪, e m ∈ 𝔪
    ·
      let K := FractionRing B
      have hinj : Function.Injective (algebraMap B K) := IsFractionRing.injective B K
      have htK : algebraMap B K t ≠ 0 := (map_ne_zero_iff _ hinj).mpr ht0
      set c : K := algebraMap B K b₀ / algebraMap B K t with hc
      have hcm : ∀ m ∈ 𝔪, c * algebraMap B K m = algebraMap B K (e m) := fun m hm => by
        rw [hc, div_mul_eq_mul_div, div_eq_iff htK, ← map_mul, ← map_mul, mul_comm (e m) t, he m hm, mul_comm b₀ m]
      let N : Submodule B K := Submodule.map (Algebra.linearMap B K) 𝔪
      have hN0 : N ≠ ⊥ := by
        intro h
        have h' : algebraMap B K t ∈ N := Submodule.mem_map_of_mem (f := Algebra.linearMap B K) ht
        rw [h, Submodule.mem_bot] at h'
        exact htK h'
      have hNfg : N.FG := (IsNoetherian.noetherian 𝔪).map (Algebra.linearMap B K)
      have hcN : ∀ n ∈ N, c • n ∈ N := by
        rintro n ⟨m, hm, rfl⟩
        refine ⟨e m, hcase m hm, ?_⟩
        simp only [Algebra.linearMap_apply, smul_eq_mul]
        exact (hcm m hm).symm
      have hcint : IsIntegral B c := isIntegral_of_smul_mem_submodule N hN0 hNfg c hcN
      obtain ⟨y, hy⟩ := IsIntegrallyClosed.isIntegral_iff.mp hcint
      apply hb₀
      refine (Submodule.mem_smul_pointwise_iff_exists _ _ _).mpr ⟨y, Submodule.mem_top, ?_⟩
      apply hinj
      rw [smul_eq_mul, map_mul, hy, hc, ← mul_div_assoc, mul_div_cancel_left₀ _ htK]
    ·
      push_neg at hcase
      obtain ⟨m, hm, hem⟩ := hcase
      have hu : IsUnit (e m) := by
        by_contra h
        exact hem ((IsLocalRing.mem_maximalIdeal _).mpr (mem_nonunits_iff.mpr h))
      obtain ⟨u, hu'⟩ := hu
      have h𝔪eq : 𝔪 = Ideal.span {m} := by
        refine le_antisymm ?_ ((Ideal.span_singleton_le_iff_mem _).mpr hm)
        intro m' hm'
        have h1 : t * (m' * e m) = t * (m * e m') := by
          calc t * (m' * e m) = m' * (t * e m) := by ring
            _ = m' * (m * b₀) := by rw [he m hm]
            _ = m * (m' * b₀) := by ring
            _ = m * (t * e m') := by rw [he m' hm']
            _ = t * (m * e m') := by ring
        have h2 : m' * e m = m * e m' := mul_left_cancel₀ ht0 h1
        rw [Ideal.mem_span_singleton']
        refine ⟨e m' * ↑u⁻¹, ?_⟩
        calc e m' * ↑u⁻¹ * m = (m * e m') * ↑u⁻¹ := by ring
          _ = (m' * e m) * ↑u⁻¹ := by rw [h2]
          _ = m' * (↑u * ↑u⁻¹) := by rw [← hu']; ring
          _ = m' := by rw [Units.mul_inv, mul_one]
      haveI hprinc : (Ideal.span {m} : Ideal B).IsPrincipal := ⟨⟨m, rfl⟩⟩
      haveI : 𝔪.IsPrime := h𝔪max.isPrime
      have hmin : IsLocalRing.maximalIdeal B ∈ (Ideal.span {m} : Ideal B).minimalPrimes := by
        rw [← h𝔪eq, Ideal.minimalPrimes_eq_subsingleton_self]
        exact Set.mem_singleton _
      have hh : (IsLocalRing.maximalIdeal B).height ≤ 1 :=
        Ideal.height_le_one_of_isPrincipal_of_mem_minimalPrimes_of_isLocalRing (Ideal.span {m}) hmin
      have h2 : (2 : WithBot ℕ∞) ≤ ((IsLocalRing.maximalIdeal B).height : WithBot ℕ∞) := by
        rw [IsLocalRing.maximalIdeal_height_eq_ringKrullDim]; exact hdim
      have h2' : (2 : ℕ∞) ≤ (IsLocalRing.maximalIdeal B).height := by
        rw [← WithBot.coe_le_coe, WithBot.coe_ofNat]
        exact h2
      have h21 : (2 : ℕ∞) ≤ 1 := h2'.trans hh
      exact absurd h21 (by decide)

  obtain ⟨b, hb, hreg⟩ := key
  refine ⟨b, hb, ?_⟩
  have hannB : Module.annihilator B B ≠ ⊤ := by
    intro h
    have h1 : (1 : B) ∈ Module.annihilator B B := h ▸ Submodule.mem_top
    rw [Module.mem_annihilator] at h1
    exact one_ne_zero ((one_smul B (1 : B)).symm.trans (h1 1))
  have hjac : ∀ r ∈ [t, b], r ∈ (Module.annihilator B B).jacobson := by
    intro r hr
    rw [IsLocalRing.jacobson_eq_maximalIdeal _ hannB]
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact ht
    · exact hb
  have htreg : IsSMulRegular B t := fun x y h => mul_left_cancel₀ ht0 h
  rw [RingTheory.Sequence.isRegular_iff_isWeaklyRegular_of_subset_jacobson_annihilator hjac,
    RingTheory.Sequence.isWeaklyRegular_cons_iff, RingTheory.Sequence.isWeaklyRegular_singleton_iff]
  exact ⟨htreg, hreg⟩

end S_IsIntegrallyClosed_exists_isRegular_pair_of_two_le_ringKrullDim
end P2MW
export P2MW.S_IsIntegrallyClosed_exists_isRegular_pair_of_two_le_ringKrullDim (solution)
