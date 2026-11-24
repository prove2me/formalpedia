-- Prove2me | solution 1 for GlobalTheory.LocalNorm.exists_binary_eq_adicCompletion
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T19:10:21.415043+00:00
-- url     : https://prove2.me/submissions/85be8c91-55ea-42c8-a490-23d5367ef179

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_Signature
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_ExistsEqTransposeMulMapOfIdempotent
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_ExistsBinaryEqAdicCompletion
import Theorems.Thm_GlobalTheory_LocalNorm_exists_add_mul_sq_eq_of_norm

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField Matrix
open scoped nonZeroDivisors
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.LocalNorm
namespace GlobalTheory.LocalNorm
theorem _root_.solution {F : Type*} [Field F] [NumberField F]
    (v : IsDedekindDomain.HeightOneSpectrum (𝓞 F)) {a n u : 𝓞 F}
    (hD : a ^ 2 - 4 * n ∉ v.asIdeal) (hu : u ∉ v.asIdeal) :
    ∃ r s : v.adicCompletion F, r ^ 2 + algebraMap F _ (a : F) * r * s
      + algebraMap F _ (n : F) * s ^ 2 = algebraMap F _ (u : F) := by
  haveI := v.isMaximal
  haveI : Finite (𝓞 F ⧸ v.asIdeal) := v.asIdeal.finiteQuotientOfFreeOfNeBot v.ne_bot
  letI := Ideal.Quotient.field v.asIdeal
  obtain ⟨r, s, hrs⟩ := UnramifiedHermitian.exists_binary_eq_of_finite
    (a := Ideal.Quotient.mk v.asIdeal a) (n := Ideal.Quotient.mk v.asIdeal n)
    (by
      intro h
      apply hD
      rw [← Ideal.Quotient.eq_zero_iff_mem]
      simpa only [map_sub, map_mul, map_pow, map_ofNat] using h)
    (Ideal.Quotient.mk v.asIdeal u)
  obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective r
  obtain ⟨s, rfl⟩ := Ideal.Quotient.mk_surjective s
  have hN : u - (r ^ 2 + a * r * s + n * s ^ 2) ∈ v.asIdeal := by
    rw [← Ideal.Quotient.eq]
    simpa only [map_add, map_mul, map_pow] using hrs.symm
  have hN' : r ^ 2 + a * r * s + n * s ^ 2 ∉ v.asIdeal := fun h => hu (by
    simpa using v.asIdeal.add_mem hN h)
  set φ : 𝓞 F →+* v.adicCompletion F := (algebraMap F _).comp (algebraMap (𝓞 F) F) with hφ
  have hval : ∀ z : 𝓞 F, Valued.v (φ z) = v.intValuation z := fun z => by
    rw [← v.valuation_of_algebraMap (K := F), ← v.valuedAdicCompletion_eq_valuation' (K := F)]
    rfl
  have hle : ∀ z, ‖φ z‖ ≤ 1 := fun z => by
    rw [Valued.toNormedField.norm_le_one_iff, hval]; exact v.intValuation_le_one z
  have hlt : ∀ z ∈ v.asIdeal, ‖φ z‖ < 1 := fun z hz => by
    rw [Valued.toNormedField.norm_lt_one_iff, hval]
    exact (v.intValuation_lt_one_iff_mem z).2 hz
  have heq : ∀ z ∉ v.asIdeal, ‖φ z‖ = 1 := fun z hz => by
    refine le_antisymm (hle z) (not_lt.1 fun h => hz ?_)
    rw [Valued.toNormedField.norm_lt_one_iff, hval] at h
    exact (v.intValuation_lt_one_iff_mem z).1 h
  have hD1 := heq _ hD
  have hN1 := heq _ hN'
  have hD0 : φ (a ^ 2 - 4 * n) ≠ 0 := fun h => by simp [h] at hD1
  have hN0 : φ (r ^ 2 + a * r * s + n * s ^ 2) ≠ 0 := fun h => by simp [h] at hN1
  obtain ⟨t, ht⟩ := exists_add_mul_sq_eq_of_norm (K := v.adicCompletion F)
    (c := -(φ n / φ (a ^ 2 - 4 * n)))
    (e := φ (u - (r ^ 2 + a * r * s + n * s ^ 2)) / φ (r ^ 2 + a * r * s + n * s ^ 2))
    (by rw [norm_neg, norm_div, hD1, div_one]; exact hle n)
    (by rw [norm_div, hN1, div_one]; exact hlt _ hN)
  simp only [map_sub, map_add, map_mul, map_pow, map_ofNat] at ht hD0 hN0
  change ∃ r' s', r' ^ 2 + φ a * r' * s' + φ n * s' ^ 2 = φ u
  generalize φ a = A, φ n = N, φ u = U, φ r = R, φ s = S at *
  obtain ⟨y, hy⟩ : ∃ y, (A ^ 2 - 4 * N) * y = 1 := ⟨_, mul_inv_cancel₀ hD0⟩
  have hy' : (A ^ 2 - 4 * N)⁻¹ = y := inv_eq_of_mul_eq_one_right hy
  rw [eq_div_iff hN0, div_eq_mul_inv, hy'] at ht
  refine ⟨R * (1 - 2 * N * y * t) - N * S * (A * y * t),
    R * (A * y * t) + S * (1 - 2 * N * y * t) + A * S * (A * y * t), ?_⟩
  linear_combination ht + (R ^ 2 + A * R * S + N * S ^ 2) * (t - N * y * t ^ 2) * hy
end GlobalTheory.LocalNorm
