-- Prove2me | solution 1 for NumberField.PlaceTransport.exists_pow_dvd_natCard_inf_decomp_smul_of_isPGroup_of_not_dvd_index
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.93214+00:00
-- url     : https://prove2.me/submissions/05c0e513-89bc-5f5e-b124-f1e0e239e7b7

import Mathlib
import Definitions.Def_NumberField_PlaceTransport
import Definitions.Def_NumberField_PlaceDecompositionAction
import Definitions.Def_NumberField_LevelArithmeticModP
import Theorems.Thm_NumberField_PlaceTransport_stabilizer_eq_decomp
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_NumberField_PlaceTransport_exists_pow_dvd_natCard_inf_decomp_smul_of_isPGroup_of_not_dvd_index

set_option autoImplicit false
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 1600000
p2m_open "IsDedekindDomain NumberField P2MW.S_NumberField_PlaceTransport_exists_pow_dvd_natCard_inf_decomp_smul_of_isPGroup_of_not_dvd_index.NumberField"
p2m_open_scoped "NumberField.LevelArith NumberField.PlaceDecomp NumberField.PlaceTransport P2MW.S_NumberField_PlaceTransport_exists_pow_dvd_natCard_inf_decomp_smul_of_isPGroup_of_not_dvd_index.NumberField.PlaceTransport Pointwise"

theorem solution
    (p : ℕ) [Fact p.Prime] (E K : Type) [Field E] [NumberField E] [Field K] [NumberField K] [Algebra E K]
    (H : Subgroup (K ≃ₐ[E] K)) (hH : IsPGroup p ↥H) (hidx : ¬ p ∣ H.index)
    (w : HeightOneSpectrum (𝓞 K)) (k : ℕ) (hk : p ^ k ∣ Nat.card ↥(NumberField.PlaceDecomp.decomp E K w)) :
    ∃ g : K ≃ₐ[E] K, p ^ k ∣ Nat.card ↥(H ⊓ NumberField.PlaceDecomp.decomp E K (g • w)) := by
  classical
  have hp : p.Prime := Fact.out
  have hD : MulAction.stabilizer (K ≃ₐ[E] K) w = NumberField.PlaceDecomp.decomp E K w :=
    NumberField.PlaceTransport.stabilizer_eq_decomp E K w

  obtain ⟨Q⟩ : Nonempty (Sylow p ↥(NumberField.PlaceDecomp.decomp E K w)) := inferInstance
  have hkQ : p ^ k ∣ Nat.card ↥(Q : Subgroup ↥(NumberField.PlaceDecomp.decomp E K w)) := by
    rw [Sylow.card_eq_multiplicity]
    exact pow_dvd_pow p ((hp.pow_dvd_iff_le_factorization Nat.card_pos.ne').mp hk)

  set Q' : Subgroup (K ≃ₐ[E] K) :=
    (Q : Subgroup ↥(NumberField.PlaceDecomp.decomp E K w)).map (NumberField.PlaceDecomp.decomp E K w).subtype
    with hQ'def
  have hQ'le : Q' ≤ NumberField.PlaceDecomp.decomp E K w := Subgroup.map_subtype_le _
  have hQ'p : IsPGroup p ↥Q' := Q.isPGroup'.map _
  have hQ'card : Nat.card ↥Q' = Nat.card ↥(Q : Subgroup ↥(NumberField.PlaceDecomp.decomp E K w)) :=
    Subgroup.card_map_of_injective (Subgroup.subtype_injective _)

  obtain ⟨PH, hHPH⟩ := hH.exists_le_sylow
  have hHeq : H = (PH : Subgroup (K ≃ₐ[E] K)) := by
    obtain ⟨a, ha⟩ := hH.exists_card_eq
    have hfac : (Nat.card (K ≃ₐ[E] K)).factorization p = a := by
      rw [← H.card_mul_index, Nat.factorization_mul Nat.card_pos.ne' H.index_ne_zero_of_finite, ha,
        hp.factorization_pow, Finsupp.add_apply, Finsupp.single_eq_same,
        Nat.factorization_eq_zero_of_not_dvd hidx, add_zero]
    apply Subgroup.eq_of_le_of_card_ge hHPH
    rw [Sylow.card_eq_multiplicity, hfac, ha]

  obtain ⟨P', hQ'P'⟩ := hQ'p.exists_le_sylow
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq (K ≃ₐ[E] K) P' PH
  refine ⟨g, ?_⟩
  have h1 : MulAut.conj g • Q' ≤ H := by
    calc MulAut.conj g • Q' ≤ MulAut.conj g • (P' : Subgroup (K ≃ₐ[E] K)) :=
          Subgroup.pointwise_smul_le_pointwise_smul_iff.mpr hQ'P'
      _ = ((g • P' : Sylow p (K ≃ₐ[E] K)) : Subgroup (K ≃ₐ[E] K)) := Sylow.coe_subgroup_smul.symm
      _ = H := by rw [hg, ← hHeq]
  have h2 : MulAut.conj g • Q' ≤ NumberField.PlaceDecomp.decomp E K (g • w) := by
    intro x hx
    rw [Subgroup.mem_pointwise_smul_iff_inv_smul_mem] at hx
    have hy : (MulAut.conj g)⁻¹ • x ∈ MulAction.stabilizer (K ≃ₐ[E] K) w := by
      rw [hD]
      exact hQ'le hx
    rw [MulAction.mem_stabilizer_iff, MulAut.smul_def, MulAut.conj_inv_apply] at hy
    rw [← NumberField.PlaceTransport.stabilizer_eq_decomp, MulAction.mem_stabilizer_iff, ← mul_smul,
      show x * g = g * (g⁻¹ * x * g) by group, mul_smul, hy]
  have hc : Nat.card ↥(MulAut.conj g • Q') = Nat.card ↥Q' :=
    (Nat.card_congr (Subgroup.equivSMul (MulAut.conj g) Q').toEquiv).symm
  calc p ^ k ∣ Nat.card ↥(Q : Subgroup ↥(NumberField.PlaceDecomp.decomp E K w)) := hkQ
    _ = Nat.card ↥(MulAut.conj g • Q') := by rw [hc, hQ'card]
    _ ∣ Nat.card ↥(H ⊓ NumberField.PlaceDecomp.decomp E K (g • w)) := Subgroup.card_dvd_of_le (le_inf h1 h2)

namespace NumberField p2m_export "NumberField" "place PlaceTransport.mem_smul_asIdeal_iff PlaceDecomp.decomp LevelArith.placesOverPrimes PlaceTransport.stabilizer_eq_decomp" namespace PlaceTransport p2m_export "NumberField.PlaceTransport" "mem_smul_asIdeal_iff stabilizer_eq_decomp" end NumberField.PlaceTransport
p2m_open_scoped "NumberField NumberField.PlaceTransport" in

theorem NumberField.PlaceTransport.smul_mem_placesOverPrimes
    (E K : Type) [Field E] [Field K] [NumberField K] [Algebra E K] (S : Set Nat.Primes)
    (σ : K ≃ₐ[E] K) {w : HeightOneSpectrum (𝓞 K)} (hw : w ∈ NumberField.LevelArith.placesOverPrimes K S) :
    σ • w ∈ NumberField.LevelArith.placesOverPrimes K S := by
  obtain ⟨q, hq, hqw⟩ := hw
  refine ⟨q, hq, ?_⟩
  rw [NumberField.PlaceTransport.mem_smul_asIdeal_iff]
  have : σ⁻¹ • (((q : ℕ) : 𝓞 K)) = ((q : ℕ) : 𝓞 K) :=
    map_natCast (MulSemiringAction.toRingHom (K ≃ₐ[E] K) (𝓞 K) σ⁻¹) q
  rw [this]
  exact hqw

p2m_open_scoped "NumberField NumberField.PlaceTransport" in

theorem NumberField.PlaceTransport.exists_mem_pow_dvd_natCard_inf_decomp_of_isPGroup_of_not_dvd_index
    (p : ℕ) [Fact p.Prime] (E K : Type) [Field E] [NumberField E] [Field K] [NumberField K] [Algebra E K]
    (H : Subgroup (K ≃ₐ[E] K)) (hH : IsPGroup p ↥H) (hidx : ¬ p ∣ H.index)
    (T : Set (HeightOneSpectrum (𝓞 K))) (hT : ∀ (σ : K ≃ₐ[E] K) (w : HeightOneSpectrum (𝓞 K)), w ∈ T → σ • w ∈ T)
    (k : ℕ) (hk : ∀ w ∈ T, p ^ k ∣ Nat.card ↥(NumberField.PlaceDecomp.decomp E K w)) (hne : T.Nonempty) :
    ∃ w ∈ T, p ^ k ∣ Nat.card ↥(H ⊓ NumberField.PlaceDecomp.decomp E K w) := by
  obtain ⟨w₀, hw₀⟩ := hne
  obtain ⟨g, hg⟩ :=
    solution p E K H hH hidx w₀ k (hk w₀ hw₀)
  exact ⟨g • w₀, hT g w₀ hw₀, hg⟩

end S_NumberField_PlaceTransport_exists_pow_dvd_natCard_inf_decomp_smul_of_isPGroup_of_not_dvd_index
end P2MW
export P2MW.S_NumberField_PlaceTransport_exists_pow_dvd_natCard_inf_decomp_smul_of_isPGroup_of_not_dvd_index (solution)
