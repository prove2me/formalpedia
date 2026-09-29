-- Prove2me | solution 1 for MvPowerSeries.subst_injective_of_finite_projective_quotient_of_X_pow_mem_span
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.620212+00:00
-- url     : https://prove2.me/submissions/71b25c3f-126b-558f-8d6e-e3dc43df3e49

import Mathlib
import Theorems.Thm_MvPowerSeries_exists_basis_subst_of_finite_quotient_of_isLocalRing
import Theorems.Thm_MvPowerSeries_exists_algEquiv_tensorProduct_quotient_span_map_of_X_pow_mem
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_MvPowerSeries_subst_injective_of_finite_projective_quotient_of_X_pow_mem_span
p2m_attr_erase "instance" "instTopologicallyFGOfFiniteType"

set_option autoImplicit false

open scoped TensorProduct

namespace Ws28K2G1

open MvPowerSeries

theorem local_ker {S : Type} [CommRing S] [IsLocalRing S] [IsNoetherianRing S] {n : ℕ}
    (ρ : Fin n → MvPowerSeries (Fin n) S) (hρ0 : ∀ i, constantCoeff (ρ i) = 0)
    (hN : ∃ N : ℕ, ∀ i : Fin n, (X i : MvPowerSeries (Fin n) S) ^ N ∈ Ideal.span (Set.range ρ))
    (hfin : Module.Finite S (MvPowerSeries (Fin n) S ⧸ Ideal.span (Set.range ρ)))
    (G : MvPowerSeries (Fin n) S) (hG : subst ρ G = 0) : G = 0 := by
  classical
  obtain ⟨d, b, hb⟩ := MvPowerSeries.exists_basis_subst_of_finite_quotient_of_isLocalRing ρ hρ0 hN hfin
  have hρ : HasSubst ρ := hasSubst_of_constantCoeff_zero hρ0
  have h0 : subst ρ (0 : MvPowerSeries (Fin n) S) = 0 := by rw [← coe_substAlgHom hρ, map_zero]
  rcases Nat.eq_zero_or_pos d with hd | hd
  · subst hd
    obtain ⟨c, hc, -⟩ := hb G
    rw [hc]; simp
  · let j₀ : Fin d := ⟨0, hd⟩
    have h1 : (0 : MvPowerSeries (Fin n) S) = ∑ j, subst ρ ((0 : Fin d → MvPowerSeries (Fin n) S) j) * b j := by
      simp [h0]
    have h2 : (0 : MvPowerSeries (Fin n) S) = ∑ j, subst ρ ((Pi.single j₀ G : Fin d → MvPowerSeries (Fin n) S) j) * b j := by
      rw [Finset.sum_eq_single j₀]
      · rw [Pi.single_eq_same, hG, zero_mul]
      · intro j _ hj; rw [Pi.single_eq_of_ne hj, h0, zero_mul]
      · intro h; exact absurd (Finset.mem_univ j₀) h
    have := (hb 0).unique h2 h1
    have := congrFun this j₀
    rwa [Pi.single_eq_same] at this

theorem finite_quotient_map {B : Type} [CommRing B] {S : Type} [CommRing S] [Algebra B S] {n : ℕ}
    (ρ : Fin n → MvPowerSeries (Fin n) B)
    (hN : ∃ N : ℕ, ∀ i : Fin n, (X i : MvPowerSeries (Fin n) B) ^ N ∈ Ideal.span (Set.range ρ))
    (hfin : Module.Finite B (MvPowerSeries (Fin n) B ⧸ Ideal.span (Set.range ρ))) :
    Module.Finite S (MvPowerSeries (Fin n) S ⧸ Ideal.span (Set.range fun i => map (algebraMap B S) (ρ i))) := by
  obtain ⟨e, -⟩ := MvPowerSeries.exists_algEquiv_tensorProduct_quotient_span_map_of_X_pow_mem (S := S) ρ hN
  exact Module.Finite.equiv e.toLinearEquiv

end Ws28K2G1

open Ws28K2G1 MvPowerSeries in
theorem solution
    {B : Type} [CommRing B] [IsNoetherianRing B] {n : ℕ}
    (ρ : Fin n → MvPowerSeries (Fin n) B) (hρ0 : ∀ i, MvPowerSeries.constantCoeff (ρ i) = 0)
    (hN : ∃ N : ℕ, ∀ i : Fin n, (MvPowerSeries.X i : MvPowerSeries (Fin n) B) ^ N ∈ Ideal.span (Set.range ρ))
    (hfin : Module.Finite B (MvPowerSeries (Fin n) B ⧸ Ideal.span (Set.range ρ)))
    (hproj : Module.Projective B (MvPowerSeries (Fin n) B ⧸ Ideal.span (Set.range ρ)))
    (H H' : MvPowerSeries (Fin n) B) (h : MvPowerSeries.subst ρ H = MvPowerSeries.subst ρ H') : H = H' := by
  classical
  have hρ : HasSubst ρ := hasSubst_of_constantCoeff_zero hρ0

  rw [← sub_eq_zero]
  set G := H - H' with hGdef
  have hG : subst ρ G = 0 := by
    rw [hGdef, ← coe_substAlgHom hρ, map_sub, coe_substAlgHom hρ, h, sub_self]

  ext dd
  rw [map_zero]
  refine eq_zero_of_localization _ fun J hJ => ?_
  let S := Localization.AtPrime J
  let φ : B →+* S := algebraMap B S

  let ρ' : Fin n → MvPowerSeries (Fin n) S := fun i => map φ (ρ i)
  have hρ0' : ∀ i, constantCoeff (ρ' i) = 0 := fun i => by
    show constantCoeff (map φ (ρ i)) = 0
    rw [constantCoeff_map, hρ0, map_zero]
  have hN' : ∃ N : ℕ, ∀ i : Fin n, (X i : MvPowerSeries (Fin n) S) ^ N ∈ Ideal.span (Set.range ρ') := by
    obtain ⟨N, hNN⟩ := hN
    refine ⟨N, fun i => ?_⟩
    have := Ideal.mem_map_of_mem (map φ : MvPowerSeries (Fin n) B →+* MvPowerSeries (Fin n) S) (hNN i)
    rw [map_pow, map_X, Ideal.map_span, ← Set.range_comp] at this
    exact this
  have hfin' := finite_quotient_map (S := S) ρ hN hfin
  haveI : IsNoetherianRing S := IsLocalization.isNoetherianRing J.primeCompl S inferInstance
  have hG' : subst ρ' (map φ G) = 0 := by
    rw [← map_subst hρ, hG, map_zero]
  have := local_ker ρ' hρ0' hN' hfin' (map φ G) hG'
  have := congrArg (coeff dd) this
  rwa [coeff_map, map_zero] at this

end S_MvPowerSeries_subst_injective_of_finite_projective_quotient_of_X_pow_mem_span
end P2MW
export P2MW.S_MvPowerSeries_subst_injective_of_finite_projective_quotient_of_X_pow_mem_span (solution)
