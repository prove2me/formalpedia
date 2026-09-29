-- Prove2me | solution 1 for NumberField.natCard_units_adicCompletion_quotient_range_powMonoidHom
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.93214+00:00
-- url     : https://prove2.me/submissions/6fb9cf78-7c75-5985-a2e0-2c9c82874c92

import Mathlib
import Theorems.Thm_MonoidHom_index_range_powMonoidHom_eq_mul_of_exact
import Theorems.Thm_NumberField_natCard_units_adicCompletionIntegers_quotient_range_powMonoidHom
import Theorems.Thm_IsDedekindDomain_HeightOneSpectrum_finite_residueField_adicCompletionIntegers
import Theorems.Thm_IsDiscreteValuationRing_natCard_quotient_maximalIdeal_pow
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_NumberField_natCard_units_adicCompletion_quotient_range_powMonoidHom
p2m_attr_erase "simp" "IsLocalRing.principalUnits_zero"

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 1600000
set_option maxHeartbeats 3200000

namespace P2mS26C4
open IsLocalRing IsDedekindDomain

theorem exists_span_natCast_eq_maximalIdeal_pow {R : Type*} [CommRing R] [IsDomain R]
    [IsDiscreteValuationRing R] {n : ℕ} (hn : (n : R) ≠ 0) :
    ∃ e : ℕ, Ideal.span {(n : R)} = maximalIdeal R ^ e := by
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible R
  obtain ⟨e, he⟩ := IsDiscreteValuationRing.ideal_eq_span_pow_irreducible
    (show Ideal.span {(n : R)} ≠ ⊥ by simpa [Ideal.span_singleton_eq_bot] using hn) hϖ
  exact ⟨e, by rw [he, hϖ.maximalIdeal_eq, Ideal.span_singleton_pow]⟩

theorem natCard_quotient_span_natCast_ne_zero {R : Type*} [CommRing R] [IsDomain R]
    [IsDiscreteValuationRing R] [Finite (IsLocalRing.ResidueField R)] {n : ℕ} (hn : (n : R) ≠ 0) :
    Nat.card (R ⧸ Ideal.span {(n : R)}) ≠ 0 := by
  obtain ⟨e, hne⟩ := exists_span_natCast_eq_maximalIdeal_pow hn
  rw [hne, IsDiscreteValuationRing.natCard_quotient_maximalIdeal_pow]
  exact pow_ne_zero _ Nat.card_pos.ne'

theorem index_range_powMonoidHom_multiplicativeInt (n : ℕ) :
    ((powMonoidHom n : Multiplicative ℤ →* Multiplicative ℤ).range).index = n := by
  have hPz : (powMonoidHom n : Multiplicative ℤ →* Multiplicative ℤ).range
      = AddSubgroup.toSubgroup (AddSubgroup.zmultiples (n : ℤ)) := by
    ext x
    change (∃ y, y ^ n = x) ↔ Multiplicative.toAdd x ∈ AddSubgroup.zmultiples (n : ℤ)
    rw [Int.mem_zmultiples_iff]
    constructor
    · rintro ⟨y, rfl⟩
      exact ⟨Multiplicative.toAdd y, by rw [toAdd_pow, nsmul_eq_mul]⟩
    · rintro ⟨c, hc⟩
      refine ⟨Multiplicative.ofAdd c, Multiplicative.toAdd.injective ?_⟩
      rw [toAdd_pow, toAdd_ofAdd, nsmul_eq_mul, hc]
  rw [hPz, AddSubgroup.index_toSubgroup, AddSubgroup.index,
    Nat.card_congr (Int.quotientZMultiplesNatEquivZMod n).toEquiv, Nat.card_zmod]

theorem valued_algebraMap {K : Type*} [Field K] [NumberField K]
    (v : HeightOneSpectrum (NumberField.RingOfIntegers K)) (x : K) :
    Valued.v (algebraMap K (v.adicCompletion K) x) = v.valuation K x := by
  rw [IsDedekindDomain.HeightOneSpectrum.algebraMap_adicCompletion]
  exact IsDedekindDomain.HeightOneSpectrum.valuedAdicCompletion_eq_valuation' _ x

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

theorem pos_of_primitiveRoots_nonempty {M : Type*} [CommRing M] [IsDomain M] {n : ℕ}
    (h : (primitiveRoots n M).Nonempty) : 0 < n := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · obtain ⟨ζ, hζ⟩ := h
    simp at hζ
  · exact hn

end P2mS26C4

theorem solution {K : Type*} [Field K] [NumberField K]
    (v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))
    {n : ℕ} (hμ : (primitiveRoots n (v.adicCompletion K)).Nonempty) :
    Nat.card ((v.adicCompletion K)ˣ ⧸ (powMonoidHom n : (v.adicCompletion K)ˣ →* (v.adicCompletion K)ˣ).range)
        = n ^ 2 * Nat.card (v.adicCompletionIntegers K ⧸ Ideal.span {(n : v.adicCompletionIntegers K)}) ∧
      Nat.card ((v.adicCompletion K)ˣ ⧸ (powMonoidHom n : (v.adicCompletion K)ˣ →* (v.adicCompletion K)ˣ).range) ≠ 0 := by
  classical
  have hn0 : 0 < n := P2mS26C4.pos_of_primitiveRoots_nonempty hμ
  haveI : Finite (IsLocalRing.ResidueField (v.adicCompletionIntegers K)) :=
    IsDedekindDomain.HeightOneSpectrum.finite_residueField_adicCompletionIntegers K v
  have hnR := P2mS26C4.natCast_adicCompletionIntegers_ne_zero v hn0.ne'
  have hle : ∀ y : v.adicCompletionIntegers K, Valued.v (y : v.adicCompletion K) ≤ 1 := fun y =>
    (IsDedekindDomain.HeightOneSpectrum.mem_adicCompletionIntegers (NumberField.RingOfIntegers K) K v).1 y.2

  let ι : (v.adicCompletionIntegers K)ˣ →* (v.adicCompletion K)ˣ :=
    Units.map ((v.adicCompletionIntegers K).subtype : v.adicCompletionIntegers K →+* v.adicCompletion K).toMonoidHom
  let φ : (v.adicCompletion K)ˣ →* Multiplicative ℤ :=
    (WithZero.unitsWithZeroEquiv : (WithZero (Multiplicative ℤ))ˣ ≃* Multiplicative ℤ).toMonoidHom.comp
      (Units.map ((Valued.v : Valuation (v.adicCompletion K) (WithZero (Multiplicative ℤ))).toMonoidWithZeroHom.toMonoidHom))
  have hι : Function.Injective ι := by
    intro a b h
    apply Units.ext; apply Subtype.ext
    exact congrArg (fun x : (v.adicCompletion K)ˣ => (x : v.adicCompletion K)) h
  have hφker : ∀ x : (v.adicCompletion K)ˣ, x ∈ φ.ker ↔ Valued.v (x : v.adicCompletion K) = 1 := by
    intro x
    rw [MonoidHom.mem_ker]
    change WithZero.unitsWithZeroEquiv (Units.map _ x) = 1 ↔ _
    rw [MulEquiv.map_eq_one_iff, Units.ext_iff, Units.coe_map, Units.val_one]
    rfl
  have hexact : ι.range = φ.ker := by
    ext x
    rw [hφker]
    constructor
    · rintro ⟨w, rfl⟩
      change Valued.v ((w : v.adicCompletionIntegers K) : v.adicCompletion K) = 1
      have h := congrArg (fun y : v.adicCompletionIntegers K => Valued.v (y : v.adicCompletion K)) w.val_inv
      simp only [MulMemClass.coe_mul, OneMemClass.coe_one, map_mul, map_one] at h
      apply le_antisymm (hle _)
      calc (1 : WithZero (Multiplicative ℤ))
          = Valued.v ((w : v.adicCompletionIntegers K) : v.adicCompletion K)
            * Valued.v (((w⁻¹ : (v.adicCompletionIntegers K)ˣ) : v.adicCompletionIntegers K) : v.adicCompletion K) := h.symm
        _ ≤ Valued.v ((w : v.adicCompletionIntegers K) : v.adicCompletion K) * 1 := mul_le_mul' le_rfl (hle _)
        _ = _ := mul_one _
    · intro hx
      refine ⟨⟨⟨x, (IsDedekindDomain.HeightOneSpectrum.mem_adicCompletionIntegers (NumberField.RingOfIntegers K) K v).2 hx.le⟩,
        ⟨((x⁻¹ : (v.adicCompletion K)ˣ) : v.adicCompletion K),
          (IsDedekindDomain.HeightOneSpectrum.mem_adicCompletionIntegers (NumberField.RingOfIntegers K) K v).2 ?_⟩, ?_, ?_⟩, ?_⟩
      · rw [Units.val_inv_eq_inv_val, map_inv₀, hx, inv_one]
      · exact Subtype.ext x.val_inv
      · exact Subtype.ext x.inv_val
      · exact Units.ext rfl
  have hφ : Function.Surjective φ := by
    obtain ⟨π, hπ⟩ := IsDedekindDomain.HeightOneSpectrum.valuation_exists_uniformizer K v
    have hπ0 : algebraMap K (v.adicCompletion K) π ≠ 0 := by
      intro h
      have h' : Valued.v (algebraMap K (v.adicCompletion K) π) = 0 := by rw [h, map_zero]
      rw [P2mS26C4.valued_algebraMap, hπ] at h'
      exact WithZero.coe_ne_zero h'
    let u : (v.adicCompletion K)ˣ := Units.mk0 _ hπ0
    have hu : φ u = Multiplicative.ofAdd (-1 : ℤ) := by
      have h : Units.map ((Valued.v : Valuation (v.adicCompletion K) (WithZero (Multiplicative ℤ))).toMonoidWithZeroHom.toMonoidHom) u
          = WithZero.unitsWithZeroEquiv.symm (Multiplicative.ofAdd (-1 : ℤ)) := by
        apply Units.ext
        change Valued.v (algebraMap K (v.adicCompletion K) π) = ((Multiplicative.ofAdd (-1 : ℤ) : Multiplicative ℤ) : WithZero (Multiplicative ℤ))
        rw [P2mS26C4.valued_algebraMap, hπ]
        rfl
      change WithZero.unitsWithZeroEquiv (Units.map _ u) = _
      rw [h, MulEquiv.apply_symm_apply]
    intro m
    refine ⟨u ^ (-Multiplicative.toAdd m), ?_⟩
    rw [map_zpow, hu]
    apply Multiplicative.toAdd.injective
    rw [toAdd_zpow, toAdd_ofAdd, smul_eq_mul, mul_neg_one, neg_neg]
  have hF : ∀ x : Multiplicative ℤ, x ^ n = 1 → x = 1 := by
    intro x hx
    apply Multiplicative.toAdd.injective
    have h := congrArg Multiplicative.toAdd hx
    rw [toAdd_pow, toAdd_one, nsmul_eq_mul, mul_eq_zero] at h
    rcases h with h | h
    · exact absurd h (by exact_mod_cast hn0.ne')
    · rw [h, toAdd_one]
  have hG2 := MonoidHom.index_range_powMonoidHom_eq_mul_of_exact ι φ hι hφ hexact hF
  rw [P2mS26C4.index_range_powMonoidHom_multiplicativeInt] at hG2
  have hC4u := NumberField.natCard_units_adicCompletionIntegers_quotient_range_powMonoidHom v hμ
  have key : Nat.card ((v.adicCompletion K)ˣ ⧸ (powMonoidHom n : (v.adicCompletion K)ˣ →* (v.adicCompletion K)ˣ).range)
      = n ^ 2 * Nat.card (v.adicCompletionIntegers K ⧸ Ideal.span {(n : v.adicCompletionIntegers K)}) := by
    change (powMonoidHom n : (v.adicCompletion K)ˣ →* (v.adicCompletion K)ˣ).range.index = _
    rw [hG2]
    change n * Nat.card ((v.adicCompletionIntegers K)ˣ ⧸
      (powMonoidHom n : (v.adicCompletionIntegers K)ˣ →* (v.adicCompletionIntegers K)ˣ).range) = _
    rw [hC4u, ← mul_assoc, sq]
  exact ⟨key, key ▸ mul_ne_zero (pow_ne_zero 2 hn0.ne') (P2mS26C4.natCard_quotient_span_natCast_ne_zero hnR)⟩

end S_NumberField_natCard_units_adicCompletion_quotient_range_powMonoidHom
end P2MW
export P2MW.S_NumberField_natCard_units_adicCompletion_quotient_range_powMonoidHom (solution)
