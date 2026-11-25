-- Prove2me | solution 1 for GlobalTheory.CommonValuation.exists_common_valuation
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T17:31:38.220861+00:00
-- url     : https://prove2.me/submissions/081bf648-f0a0-4d02-b4c9-7d3c3c9aa2d2

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_ExistsFiniteSeparableCompositum
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_RamificationIndexValuationCompat
import Theorems.Thm_GlobalTheory_CommonValuation_exists_eq_pow
import Theorems.Thm_GlobalTheory_CommonValuation_exists_dvr
import Theorems.Thm_GlobalTheory_CommonValuation_le_one_of_ringOfIntegers
import Theorems.Thm_GlobalTheory_CommonValuation_exists_centre
import Theorems.Thm_GlobalTheory_exists_finite_separable_compositum
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_IsGrpPullback_comp
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_LBIso_symm
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_LBIso_trans


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain
open GlobalTheory GlobalTheory.CommonValuation
namespace GlobalTheory.CommonValuation
theorem _root_.solution : ∀ (k k' : Type) [Field k] [NumberField k] [Field k'] [NumberField k'] (i : k →+* k') (𝔭 : HeightOneSpectrum (𝓞 k)) (𝔓 : HeightOneSpectrum (𝓞 k')) (ε : ℕ) (V K : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] [Field K] [Algebra V K] [IsFractionRing V K] (em : k →+* K) (e : ℕ), (∀ z : k, 𝔓.valuation k' (i z) = 𝔭.valuation k z ^ ε) → 0 < e → (∀ z : k, (IsDiscreteValuationRing.maximalIdeal V).valuation K (em z) = 𝔭.valuation k z ^ e) → ∃ (W L : Type) (_ : CommRing W) (_ : IsDomain W) (_ : IsDiscreteValuationRing W) (_ : Field L) (_ : Algebra W L) (_ : IsFractionRing W L) (f : V →+* W) (g : K →+* L) (em' : k' →+* L) (e' d : ℕ), (∀ z : V, algebraMap W L (f z) = g (algebraMap V K z)) ∧ em'.comp i = g.comp em ∧ 0 < e' ∧ e' * ε = d * e ∧ (∀ z : k', (IsDiscreteValuationRing.maximalIdeal W).valuation L (em' z) = 𝔓.valuation k' z ^ e') ∧ ∀ y : K, (IsDiscreteValuationRing.maximalIdeal W).valuation L (g y) = (IsDiscreteValuationRing.maximalIdeal V).valuation K y ^ d := by
  intro k k' _ _ _ _ i 𝔭 𝔓 ε V K _ _ _ _ _ _ em e hε he hem
  let _ : Algebra k k' := i.toAlgebra
  let N := IntermediateField.normalClosure k k' (AlgebraicClosure k')
  have : NumberField N := NumberField.of_module_finite k N
  obtain ⟨L, _, _, j, _, _, hj⟩ := exists_finite_separable_compositum k K N em
  have hj' : ∀ z, j (algebraMap k N z) = algebraMap K L (em z) := fun z => DFunLike.congr_fun hj z
  obtain ⟨W, _, _, _, _, _, f, hf, hfm⟩ := exists_dvr V K L
  let w := (IsDiscreteValuationRing.maximalIdeal W).valuation L
  obtain ⟨d, hd, hdv⟩ := exists_eq_pow (IsDiscreteValuationRing.maximalIdeal V) (w.comap (algebraMap K L))
    (fun r => by
      rw [Valuation.comap_apply, ← hf]
      exact (IsDiscreteValuationRing.maximalIdeal W).valuation_le_one (f r))
    (fun r => by
      rw [Valuation.comap_apply, ← hf]
      exact ((IsDiscreteValuationRing.maximalIdeal W).valuation_lt_one_iff_mem (K := L) (f r)).trans (hfm r))
  have hε0 : ε ≠ 0 := by
    rintro rfl
    simpa using hε 0
  obtain ⟨Q, hQ, hQm⟩ := exists_centre (w.comap j)
  obtain ⟨Q', hQ', hQo⟩ := (inferInstance : Nonempty (𝔓.asIdeal.primesOver (𝓞 N)))
  have hpow : ∀ {x : WithZero (Multiplicative ℤ)} {n : ℕ}, n ≠ 0 → (x ^ n < 1 ↔ x < 1) := fun hn =>
    pow_lt_one_iff_of_nonneg zero_le hn
  have hund : Q.under (𝓞 k) = Q'.under (𝓞 k) := by
    ext r
    rw [← Ideal.under_under (B := 𝓞 k') Q', ← hQo.over]
    change algebraMap _ _ r ∈ Q ↔ algebraMap _ _ r ∈ 𝔓.asIdeal
    rw [hQm, ← 𝔓.valuation_lt_one_iff_mem (K := k')]
    change w (j (algebraMap k N r)) < 1 ↔ 𝔓.valuation k' (i r) < 1
    rw [hj', hε, hpow hε0]
    change w.comap (algebraMap K L) _ < 1 ↔ _
    rw [hdv, hem, hpow hd.ne', hpow he.ne']
  obtain ⟨σ, hσ⟩ := Algebra.IsInvariant.exists_smul_of_under_eq (𝓞 k) (𝓞 N) (N ≃ₐ[k] N) Q' Q hund.symm
  let em' : k' →+* L := j.comp (σ.toRingEquiv.toRingHom.comp (algebraMap k' N))
  have hc : ∀ z, em' (i z) = algebraMap K L (em z) := fun z => by
    rw [← hj', ← σ.commutes z, IsScalarTower.algebraMap_apply k k' N]
    rfl
  obtain ⟨e', he', hv⟩ := exists_eq_pow 𝔓 (w.comap em') (le_one_of_ringOfIntegers _) (fun r => by
    rw [hQo.over]
    change _ ↔ algebraMap _ _ r ∈ Q'
    rw [← Ideal.smul_mem_pointwise_smul_iff (a := σ), ← hσ, hQm]
    rfl)
  refine ⟨W, L, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, f,
    algebraMap K L, em', e', d, hf, RingHom.ext hc, he', ?_, hv, hdv⟩
  obtain ⟨π, hπ⟩ := 𝔭.valuation_exists_uniformizer k
  have h1 := hv (i π)
  rw [Valuation.comap_apply, hc, hε] at h1
  have h2 := hdv (em π)
  rw [Valuation.comap_apply, h1, hem, hπ, ← pow_mul, ← pow_mul, ← WithZero.exp_nsmul, ← WithZero.exp_nsmul,
    WithZero.exp_inj] at h2
  simp only [smul_neg, nsmul_eq_mul, mul_one, neg_inj, Nat.cast_inj] at h2
  rw [mul_comm, h2, mul_comm]
end GlobalTheory.CommonValuation
