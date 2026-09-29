-- Prove2me | solution 1 for IntermediateField.finite_units_quotient_range_powMonoidHom_padic
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:07.85352+00:00
-- url     : https://prove2.me/submissions/24b3c4d5-2e72-530e-b89b-ca68be60692c

import Mathlib
import Definitions.Def_ExtCitation_LocalLevelResidues
import Definitions.Def_LocalRing_PrincipalUnits
import Theorems.Thm_ExtCitation_LocalLevel_isDiscreteValuationRing_Rw
import Theorems.Thm_ExtCitation_LocalLevel_isAdicComplete_Rw
import Theorems.Thm_ExtCitation_LocalLevel_exists_valuation_units_Kw
import Theorems.Thm_ExtCitation_LocalLevel_index_principalUnits_Rw
import Theorems.Thm_IsDiscreteValuationRing_exists_mem_principalUnits_pow_eq
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_IntermediateField_finite_units_quotient_range_powMonoidHom_padic

set_option autoImplicit false
set_option maxHeartbeats 1600000

open ExtCitation.LocalLevel IsLocalRing

theorem solution
    (q : ℕ) [Fact q.Prime] (K : IntermediateField ℚ_[q] (PadicAlgCl q)) [FiniteDimensional ℚ_[q] K]
    (n : ℕ) (hn : 0 < n) :
    Finite ((↥K)ˣ ⧸ (powMonoidHom n : (↥K)ˣ →* (↥K)ˣ).range) := by
  classical
  haveI : IsDiscreteValuationRing (Rw q K) := ExtCitation.LocalLevel.isDiscreteValuationRing_Rw q K
  haveI : IsAdicComplete (IsLocalRing.maximalIdeal (Rw q K)) (Rw q K) := ExtCitation.LocalLevel.isAdicComplete_Rw q K

  have hn0 : ((n : Rw q K) : Rw q K) ≠ 0 := by
    intro h
    have h' : ((n : K) : K) = 0 := by
      have := congrArg (fun x : Rw q K => (x : K)) h
      simpa using this
    haveI : CharZero K := charZero_of_injective_algebraMap (algebraMap ℚ_[q] K).injective
    exact (Nat.cast_ne_zero.2 hn.ne') h'
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible (Rw q K)
  obtain ⟨e, he'⟩ := IsDiscreteValuationRing.associated_pow_irreducible hn0 hϖ
  have he : Ideal.span {((n : Rw q K) : Rw q K)} = IsLocalRing.maximalIdeal (Rw q K) ^ e := by
    rw [Ideal.span_singleton_eq_span_singleton.2 he', ← Ideal.span_singleton_pow, hϖ.maximalIdeal_eq]

  obtain ⟨hfi, -⟩ := ExtCitation.LocalLevel.index_principalUnits_Rw q K (k := e + 1 + e) (by omega)
  haveI := hfi
  haveI : Finite ((Rw q K)ˣ ⧸ principalUnits (Rw q K) (e + 1 + e)) := Subgroup.finite_quotient_of_finiteIndex

  obtain ⟨v, hvsurj, hvker, -, -⟩ := ExtCitation.LocalLevel.exists_valuation_units_Kw q K
  obtain ⟨π, hπ⟩ := hvsurj (Multiplicative.ofAdd 1)

  let ι : (Rw q K)ˣ →* (↥K)ˣ := Units.map ((Rw q K).subtype : Rw q K →* K)
  set P : Subgroup (↥K)ˣ := (powMonoidHom n : (↥K)ˣ →* (↥K)ˣ).range with hP
  have hιW : ∀ w ∈ principalUnits (Rw q K) (e + 1 + e), ι w ∈ P := by
    intro w hw
    obtain ⟨u, -, rfl⟩ := IsDiscreteValuationRing.exists_mem_principalUnits_pow_eq hn he
      (k := e + 1) (by omega) hw
    rw [map_pow]
    exact ⟨ι u, rfl⟩
  have hπn : (QuotientGroup.mk π : (↥K)ˣ ⧸ P) ^ (n : ℤ) = 1 := by
    rw [zpow_natCast, ← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff]
    exact ⟨π, rfl⟩

  let f : ((Rw q K)ˣ ⧸ principalUnits (Rw q K) (e + 1 + e)) × Fin n → (↥K)ˣ ⧸ P :=
    fun y => QuotientGroup.mk (ι y.1.out) * (QuotientGroup.mk π) ^ (y.2 : ℕ)
  refine Finite.of_surjective f fun z => ?_
  induction z using QuotientGroup.induction_on with | _ x =>

  set m : ℤ := Multiplicative.toAdd (v x) with hm
  have hvx : v x = Multiplicative.ofAdd m := by rw [hm, ofAdd_toAdd]
  set u : (↥K)ˣ := x * (π ^ m)⁻¹ with hu
  have hux : u * π ^ m = x := inv_mul_cancel_right x (π ^ m)
  have hvu : v u = 1 := by
    rw [hu, map_mul, map_inv, map_zpow, hπ, hvx, ← ofAdd_zsmul, smul_eq_mul, mul_one, mul_inv_cancel]
  obtain ⟨hu₁, hu₂⟩ := (hvker u).1 hvu
  let ur : (Rw q K)ˣ := ⟨⟨(u : K), hu₁⟩, ⟨((u⁻¹ : (↥K)ˣ) : K), hu₂⟩, Subtype.ext u.mul_inv, Subtype.ext u.inv_mul⟩
  have hιur : ι ur = u := Units.ext rfl

  have hn' : (0 : ℤ) < n := by exact_mod_cast hn
  have hi : (m % n).toNat < n := by
    have h1 := Int.emod_nonneg m hn'.ne'
    have h2 := Int.emod_lt_of_pos m hn'
    omega
  refine ⟨(QuotientGroup.mk ur, ⟨(m % n).toNat, hi⟩), ?_⟩
  obtain ⟨w, hw⟩ := QuotientGroup.mk_out_eq_mul (principalUnits (Rw q K) (e + 1 + e)) ur
  have hcls : (QuotientGroup.mk (ι (QuotientGroup.mk ur : (Rw q K)ˣ ⧸ principalUnits (Rw q K) (e + 1 + e)).out)
      : (↥K)ˣ ⧸ P) = QuotientGroup.mk u := by
    rw [hw, map_mul, hιur, QuotientGroup.eq, mul_inv_rev, inv_mul_cancel_right]
    exact P.inv_mem (hιW w w.2)
  have hpow : (QuotientGroup.mk π : (↥K)ˣ ⧸ P) ^ (m % n).toNat = (QuotientGroup.mk π : (↥K)ˣ ⧸ P) ^ m := by
    rw [← zpow_natCast, Int.toNat_of_nonneg (Int.emod_nonneg m hn'.ne'), ← zpow_eq_zpow_emod m hπn]
  show QuotientGroup.mk (ι (QuotientGroup.mk ur : (Rw q K)ˣ ⧸ principalUnits (Rw q K) (e + 1 + e)).out)
      * (QuotientGroup.mk π : (↥K)ˣ ⧸ P) ^ (m % n).toNat = (QuotientGroup.mk x : (↥K)ˣ ⧸ P)
  rw [hcls, hpow, ← QuotientGroup.mk_zpow, ← QuotientGroup.mk_mul, hux]

end S_IntermediateField_finite_units_quotient_range_powMonoidHom_padic
end P2MW
export P2MW.S_IntermediateField_finite_units_quotient_range_powMonoidHom_padic (solution)
