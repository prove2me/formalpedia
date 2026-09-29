-- Prove2me | solution 1 for NumberField.isOpen_range_powMonoidHom_units_adicCompletion
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.93214+00:00
-- url     : https://prove2.me/submissions/a968be65-d298-53d8-b8bc-3b92dbbc180d

import Mathlib
import Definitions.Def_LocalRing_PrincipalUnits
import Theorems.Thm_IsDiscreteValuationRing_exists_mem_principalUnits_pow_eq
import Theorems.Thm_IsDedekindDomain_HeightOneSpectrum_isAdicComplete_adicCompletionIntegers
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_NumberField_isOpen_range_powMonoidHom_units_adicCompletion

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 1600000
set_option maxHeartbeats 3200000

namespace P2mS26B7
open IsLocalRing IsDedekindDomain

theorem exists_span_natCast_eq_maximalIdeal_pow {R : Type*} [CommRing R] [IsDomain R]
    [IsDiscreteValuationRing R] {n : ℕ} (hn : (n : R) ≠ 0) :
    ∃ e : ℕ, Ideal.span {(n : R)} = maximalIdeal R ^ e := by
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible R
  obtain ⟨e, he⟩ := IsDiscreteValuationRing.ideal_eq_span_pow_irreducible
    (show Ideal.span {(n : R)} ≠ ⊥ by simpa [Ideal.span_singleton_eq_bot] using hn) hϖ
  exact ⟨e, by rw [he, hϖ.maximalIdeal_eq, Ideal.span_singleton_pow]⟩

theorem natCast_adicCompletionIntegers_ne_zero {K : Type*} [Field K] [NumberField K]
    (v : HeightOneSpectrum (NumberField.RingOfIntegers K)) {n : ℕ} (hn : n ≠ 0) :
    ((n : ℕ) : v.adicCompletionIntegers K) ≠ 0 := by
  intro h
  have h' : ((n : ℕ) : v.adicCompletion K) ≠ 0 := by
    rw [← map_natCast (algebraMap K (v.adicCompletion K)) n, map_ne_zero]
    exact Nat.cast_ne_zero.2 hn
  apply h'
  have h2 := congrArg ((↑) : v.adicCompletionIntegers K → v.adicCompletion K) h
  simpa using h2

end P2mS26B7

theorem solution {K : Type*} [Field K] [NumberField K]
    (v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K)) {n : ℕ} (hn : 0 < n) :
    IsOpen ((powMonoidHom n : (v.adicCompletion K)ˣ →* (v.adicCompletion K)ˣ).range : Set (v.adicCompletion K)ˣ) := by
  classical
  haveI : IsAdicComplete (IsLocalRing.maximalIdeal (v.adicCompletionIntegers K)) (v.adicCompletionIntegers K) :=
    IsDedekindDomain.HeightOneSpectrum.isAdicComplete_adicCompletionIntegers K v
  have hnR := P2mS26B7.natCast_adicCompletionIntegers_ne_zero v hn.ne'
  obtain ⟨e, hne⟩ := P2mS26B7.exists_span_natCast_eq_maximalIdeal_pow hnR
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible (v.adicCompletionIntegers K)
  have hle : ∀ y : v.adicCompletionIntegers K, Valued.v (y : v.adicCompletion K) ≤ 1 := fun y =>
    (IsDedekindDomain.HeightOneSpectrum.mem_adicCompletionIntegers (NumberField.RingOfIntegers K) K v).1 y.2
  have hϖ0 : ((ϖ : v.adicCompletionIntegers K) : v.adicCompletion K) ≠ 0 := fun h =>
    hϖ.ne_zero (Subtype.ext h)

  have hvϖ : Valued.v ((ϖ : v.adicCompletionIntegers K) : v.adicCompletion K) < 1 := by
    refine lt_of_le_of_ne (hle ϖ) fun h1 => hϖ.1 ?_
    exact ⟨⟨ϖ, ⟨((ϖ : v.adicCompletionIntegers K) : v.adicCompletion K)⁻¹,
      (IsDedekindDomain.HeightOneSpectrum.mem_adicCompletionIntegers (NumberField.RingOfIntegers K) K v).2
        (by rw [map_inv₀, h1, inv_one])⟩,
      Subtype.ext (mul_inv_cancel₀ hϖ0), Subtype.ext (inv_mul_cancel₀ hϖ0)⟩, rfl⟩
  have hc0 : ((ϖ : v.adicCompletionIntegers K) : v.adicCompletion K) ^ (e + 1 + e) ≠ 0 := pow_ne_zero _ hϖ0
  have hvc : Valued.v (((ϖ : v.adicCompletionIntegers K) : v.adicCompletion K) ^ (e + 1 + e)) < 1 := by
    rw [map_pow]; exact pow_lt_one' hvϖ (by omega)

  have hO : IsOpen ((v.adicCompletionIntegers K : Set (v.adicCompletion K))) :=
    Valued.isOpen_valuationSubring _
  have hT : IsOpen ((fun y : v.adicCompletion K =>
      (((ϖ : v.adicCompletionIntegers K) : v.adicCompletion K) ^ (e + 1 + e))⁻¹ * (y - 1)) ⁻¹'
        (v.adicCompletionIntegers K : Set (v.adicCompletion K))) :=
    hO.preimage (continuous_const.mul (continuous_id.sub continuous_const))
  have h1T : (1 : v.adicCompletion K) ∈ (fun y : v.adicCompletion K =>
      (((ϖ : v.adicCompletionIntegers K) : v.adicCompletion K) ^ (e + 1 + e))⁻¹ * (y - 1)) ⁻¹'
        (v.adicCompletionIntegers K : Set (v.adicCompletion K)) := by
    show (((ϖ : v.adicCompletionIntegers K) : v.adicCompletion K) ^ (e + 1 + e))⁻¹ * (1 - 1)
      ∈ v.adicCompletionIntegers K
    rw [sub_self, mul_zero]; exact zero_mem _
  apply Subgroup.isOpen_of_mem_nhds _ (g := 1)
  have hB' := (Units.continuous_val.continuousAt (x := (1 : (v.adicCompletion K)ˣ))).preimage_mem_nhds
    (by rw [Units.val_one]; exact hT.mem_nhds h1T)
  refine Filter.mem_of_superset hB' ?_
  intro x hx
  have hy : Valued.v ((((ϖ : v.adicCompletionIntegers K) : v.adicCompletion K) ^ (e + 1 + e))⁻¹
      * ((x : v.adicCompletion K) - 1)) ≤ 1 :=
    (IsDedekindDomain.HeightOneSpectrum.mem_adicCompletionIntegers (NumberField.RingOfIntegers K) K v).1 hx
  have hx1 : (x : v.adicCompletion K) - 1 = ((ϖ : v.adicCompletionIntegers K) : v.adicCompletion K) ^ (e + 1 + e)
      * ((((ϖ : v.adicCompletionIntegers K) : v.adicCompletion K) ^ (e + 1 + e))⁻¹ * ((x : v.adicCompletion K) - 1)) :=
    (mul_inv_cancel_left₀ hc0 _).symm
  have hvx1 : Valued.v ((x : v.adicCompletion K) - 1) < 1 := by
    rw [hx1, map_mul]
    exact lt_of_le_of_lt (mul_le_of_le_one_right' hy) hvc
  have hvx : Valued.v (x : v.adicCompletion K) = 1 := by
    have h : (x : v.adicCompletion K) = 1 + ((x : v.adicCompletion K) - 1) := by ring
    rw [h]; exact Valuation.map_one_add_of_lt _ hvx1

  let w : (v.adicCompletionIntegers K)ˣ :=
    ⟨⟨x, (IsDedekindDomain.HeightOneSpectrum.mem_adicCompletionIntegers (NumberField.RingOfIntegers K) K v).2 hvx.le⟩,
      ⟨((x⁻¹ : (v.adicCompletion K)ˣ) : v.adicCompletion K),
        (IsDedekindDomain.HeightOneSpectrum.mem_adicCompletionIntegers (NumberField.RingOfIntegers K) K v).2
          (by rw [Units.val_inv_eq_inv_val, map_inv₀, hvx, inv_one])⟩,
      Subtype.ext x.val_inv, Subtype.ext x.inv_val⟩

  have hw : w ∈ IsLocalRing.principalUnits (v.adicCompletionIntegers K) (e + 1 + e) := by
    rw [IsLocalRing.mem_principalUnits_iff, hϖ.maximalIdeal_eq, Ideal.span_singleton_pow, Ideal.mem_span_singleton']
    refine ⟨⟨(((ϖ : v.adicCompletionIntegers K) : v.adicCompletion K) ^ (e + 1 + e))⁻¹
      * ((x : v.adicCompletion K) - 1), hx⟩, ?_⟩
    apply Subtype.ext
    change (((ϖ : v.adicCompletionIntegers K) : v.adicCompletion K) ^ (e + 1 + e))⁻¹ * ((x : v.adicCompletion K) - 1)
        * ((ϖ : v.adicCompletionIntegers K) : v.adicCompletion K) ^ (e + 1 + e) = (x : v.adicCompletion K) - 1
    rw [mul_comm, mul_inv_cancel_left₀ hc0]
  obtain ⟨u, -, hu⟩ := IsDiscreteValuationRing.exists_mem_principalUnits_pow_eq hn hne (Nat.lt_succ_self e) hw
  show x ∈ (powMonoidHom n : (v.adicCompletion K)ˣ →* (v.adicCompletion K)ˣ).range
  refine ⟨Units.map ((v.adicCompletionIntegers K).subtype : v.adicCompletionIntegers K →+* v.adicCompletion K).toMonoidHom u, ?_⟩
  rw [powMonoidHom_apply, ← map_pow, hu]
  exact Units.ext rfl

end S_NumberField_isOpen_range_powMonoidHom_units_adicCompletion
end P2MW
export P2MW.S_NumberField_isOpen_range_powMonoidHom_units_adicCompletion (solution)
