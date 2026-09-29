-- Prove2me | solution 1 for NumberField.PlaceDecomp.card_over_mul_card_decomp_above
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.93214+00:00
-- url     : https://prove2.me/submissions/f4c189b7-a3de-501d-9fbf-7c7320b8130c

import Mathlib
import Definitions.Def_NumberField_PlaceAbove
import Definitions.Def_NumberField_PlaceDecompositionAction
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_NumberField_PlaceDecomp_card_over_mul_card_decomp_above

set_option autoImplicit false
open IsDedekindDomain NumberField

namespace P2mS26BLF

open IsDedekindDomain NumberField
open scoped Pointwise

lemma eq_of_forall_le_exp_neg_iff {a b : WithZero (Multiplicative ℤ)} (ha : a ≠ 0) (hb : b ≠ 0) (ha1 : a ≤ 1) (hb1 : b ≤ 1)
    (h : ∀ n : ℕ, a ≤ WithZero.exp (-(n : ℤ)) ↔ b ≤ WithZero.exp (-(n : ℤ))) : a = b := by
  obtain ⟨α, rfl⟩ : ∃ α : ℤ, a = WithZero.exp α := ⟨_, (WithZero.exp_log ha).symm⟩
  obtain ⟨β, rfl⟩ : ∃ β : ℤ, b = WithZero.exp β := ⟨_, (WithZero.exp_log hb).symm⟩
  rw [← WithZero.exp_zero, WithZero.exp_le_exp] at ha1 hb1
  simp only [WithZero.exp_le_exp] at h
  have h1 := (h (-α).toNat).1 (by omega)
  have h2 := (h (-β).toNat).2 (by omega)
  congr 1
  omega

section comap
variable {R R' : Type*} [CommRing R] [IsDedekindDomain R] [CommRing R'] [IsDedekindDomain R']

theorem intValuation_comap (e : R ≃+* R') (v : HeightOneSpectrum R') (r : R) :
    (HeightOneSpectrum.comap e.toRingHom e.surjective v).intValuation r = v.intValuation (e r) := by
  rcases eq_or_ne r 0 with rfl | hr
  · simp
  apply eq_of_forall_le_exp_neg_iff (HeightOneSpectrum.intValuation_ne_zero _ _ hr)
    (HeightOneSpectrum.intValuation_ne_zero _ _ (by simpa using hr)) (HeightOneSpectrum.intValuation_le_one _ _)
    (HeightOneSpectrum.intValuation_le_one _ _)
  intro n
  rw [HeightOneSpectrum.intValuation_le_pow_iff_mem, HeightOneSpectrum.intValuation_le_pow_iff_mem,
    HeightOneSpectrum.comap_asIdeal]
  change r ∈ Ideal.comap e v.asIdeal ^ n ↔ e r ∈ v.asIdeal ^ n
  rw [← Ideal.map_symm, ← Ideal.map_pow, Ideal.map_symm, Ideal.mem_comap]

end comap

variable (E K : Type) [Field E] [Field K] [NumberField K] [Algebra E K]

noncomputable abbrev galInt (σ : K ≃ₐ[E] K) : 𝓞 K ≃+* 𝓞 K := RingOfIntegers.mapRingEquiv (σ : K ≃+* K)

omit [NumberField K] in
theorem coe_galInt (σ : K ≃ₐ[E] K) (x : 𝓞 K) : ((galInt E K σ x : 𝓞 K) : K) = σ (x : K) :=
  RingOfIntegers.mapRingEquiv_apply _ _

noncomputable def pullback (σ : K ≃ₐ[E] K) (w : HeightOneSpectrum (𝓞 K)) : HeightOneSpectrum (𝓞 K) :=
  HeightOneSpectrum.comap (galInt E K σ).toRingHom (galInt E K σ).surjective w

theorem valuation_apply_eq_valuation_pullback (σ : K ≃ₐ[E] K) (w : HeightOneSpectrum (𝓞 K)) (y : K) :
    w.valuation K (σ y) = (pullback E K σ w).valuation K y := by
  obtain ⟨⟨r, s⟩, rfl⟩ := IsLocalization.mk'_surjective (nonZeroDivisors (𝓞 K)) y
  have hs : (galInt E K σ s : 𝓞 K) ∈ nonZeroDivisors (𝓞 K) :=
    mem_nonZeroDivisors_of_ne_zero (by simp)
  have hσ : σ (IsLocalization.mk' K r s) = IsLocalization.mk' K (galInt E K σ r) ⟨galInt E K σ s, hs⟩ := by
    rw [IsFractionRing.mk'_eq_div, IsFractionRing.mk'_eq_div, map_div₀]
    change σ ((r : 𝓞 K) : K) / σ ((s : 𝓞 K) : K) = ((galInt E K σ r : 𝓞 K) : K) / ((galInt E K σ s : 𝓞 K) : K)
    rw [coe_galInt, coe_galInt]
  rw [hσ, HeightOneSpectrum.valuation_of_mk', HeightOneSpectrum.valuation_of_mk', pullback,
    intValuation_comap, intValuation_comap]

theorem inv_smul_valuationSubring (σ : K ≃ₐ[E] K) (w : HeightOneSpectrum (𝓞 K)) :
    σ⁻¹ • (w.valuation K).valuationSubring = ((pullback E K σ w).valuation K).valuationSubring := by
  ext x
  rw [ValuationSubring.mem_inv_pointwise_smul_iff, Valuation.mem_valuationSubring_iff, Valuation.mem_valuationSubring_iff,
    AlgEquiv.smul_def, valuation_apply_eq_valuation_pullback]

omit [NumberField K] in

theorem inv_smul_asIdeal (σ : K ≃ₐ[E] K) (w : HeightOneSpectrum (𝓞 K)) :
    σ⁻¹ • w.asIdeal = (pullback E K σ w).asIdeal := by
  ext r
  rw [Ideal.mem_inv_pointwise_smul_iff]
  rfl

theorem eq_of_valuationSubring_eq {w w' : HeightOneSpectrum (𝓞 K)}
    (h : (w.valuation K).valuationSubring = (w'.valuation K).valuationSubring) : w = w' := by
  have he := (Valuation.isEquiv_iff_valuationSubring _ _).2 h
  rw [Valuation.isEquiv_iff_val_lt_one] at he
  apply HeightOneSpectrum.ext
  ext r
  rw [← HeightOneSpectrum.valuation_lt_one_iff_mem (K := K), ← HeightOneSpectrum.valuation_lt_one_iff_mem (K := K)]
  exact he

theorem mem_decomp_iff (σ : K ≃ₐ[E] K) (w : HeightOneSpectrum (𝓞 K)) :
    σ ∈ NumberField.PlaceDecomp.decomp E K w ↔ σ ∈ MulAction.stabilizer (K ≃ₐ[E] K) w.asIdeal := by
  rw [← Subgroup.inv_mem_iff (NumberField.PlaceDecomp.decomp E K w), ← Subgroup.inv_mem_iff (MulAction.stabilizer _ w.asIdeal)]
  change σ⁻¹ • (w.valuation K).valuationSubring = (w.valuation K).valuationSubring ↔ σ⁻¹ • w.asIdeal = w.asIdeal
  rw [inv_smul_valuationSubring, inv_smul_asIdeal]
  constructor
  · intro h
    rw [eq_of_valuationSubring_eq K h]
  · intro h
    rw [HeightOneSpectrum.ext h]

theorem decomp_eq_stabilizer (w : HeightOneSpectrum (𝓞 K)) :
    NumberField.PlaceDecomp.decomp E K w = MulAction.stabilizer (K ≃ₐ[E] K) w.asIdeal :=
  Subgroup.ext fun σ => mem_decomp_iff E K σ w

end P2mS26BLF

open scoped Pointwise in
theorem solution (E K : Type) [Field E] [NumberField E] [Field K] [NumberField K]
    [Algebra E K] [IsGalois E K] (v : HeightOneSpectrum (𝓞 E)) :
    Nat.card {w : HeightOneSpectrum (𝓞 K) // w.under (𝓞 E) = v} *
      Nat.card (NumberField.PlaceDecomp.decomp E K (NumberField.PlaceAbove.above E K v)) = Nat.card (K ≃ₐ[E] K) := by
  classical
  set w₀ := NumberField.PlaceAbove.above E K v with hw₀def
  have hw₀ : Ideal.under (𝓞 E) w₀.asIdeal = v.asIdeal := NumberField.PlaceAbove.comap_above E K v
  haveI : w₀.asIdeal.IsPrime := w₀.isPrime
  haveI : w₀.asIdeal.LiesOver v.asIdeal := (Ideal.liesOver_iff _ _).2 hw₀.symm
  have hinj : Function.Injective (algebraMap (𝓞 E) (𝓞 K)) := fun x y hxy => by
    apply IsIntegralClosure.algebraMap_injective (𝓞 E) ℤ E
    apply (algebraMap E K).injective
    have := congrArg (algebraMap (𝓞 K) K) hxy
    rwa [← IsScalarTower.algebraMap_apply, ← IsScalarTower.algebraMap_apply,
      IsScalarTower.algebraMap_apply (𝓞 E) E K, IsScalarTower.algebraMap_apply (𝓞 E) E K] at this

  have horb := Algebra.IsInvariant.orbit_eq_primesOver (𝓞 E) (𝓞 K) (K ≃ₐ[E] K) v.asIdeal w₀.asIdeal
  have hmem : ∀ P : MulAction.orbit (K ≃ₐ[E] K) w₀.asIdeal,
      (P : Ideal (𝓞 K)).IsPrime ∧ v.asIdeal = Ideal.under (𝓞 E) (P : Ideal (𝓞 K)) := fun P => by
    have h := (Set.ext_iff.1 horb (P : Ideal (𝓞 K))).1 P.2
    exact ⟨h.1, (Ideal.liesOver_iff _ _).1 h.2⟩
  have e : {w : HeightOneSpectrum (𝓞 K) // w.under (𝓞 E) = v} ≃ MulAction.orbit (K ≃ₐ[E] K) w₀.asIdeal :=
    { toFun := fun w => ⟨w.1.asIdeal, by
        rw [horb]
        exact ⟨w.1.isPrime, (Ideal.liesOver_iff _ _).2 (congrArg HeightOneSpectrum.asIdeal w.2).symm⟩⟩
      invFun := fun P => ⟨⟨P.1, (hmem P).1, fun h0 => v.ne_bot (by
          rw [(hmem P).2, h0]
          exact Ideal.comap_bot_of_injective _ hinj)⟩,
        HeightOneSpectrum.ext (hmem P).2.symm⟩
      left_inv := fun w => rfl
      right_inv := fun P => rfl }
  rw [Nat.card_congr e, P2mS26BLF.decomp_eq_stabilizer E K w₀, ← Nat.card_prod]
  exact Nat.card_congr (MulAction.orbitProdStabilizerEquivGroup (K ≃ₐ[E] K) w₀.asIdeal)

end S_NumberField_PlaceDecomp_card_over_mul_card_decomp_above
end P2MW
export P2MW.S_NumberField_PlaceDecomp_card_over_mul_card_decomp_above (solution)
