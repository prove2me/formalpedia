-- Prove2me | solution 1 for IsDedekindDomain.HeightOneSpectrum.stabilizer_asIdeal_eq_decompositionSubgroup_valuationSubring
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:07.85352+00:00
-- url     : https://prove2.me/submissions/9ecb4e68-d900-576f-ad29-c9fc66ffe2ca

import Mathlib
import Definitions.Def_NumberField_PlaceDecompositionAction
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_IsDedekindDomain_HeightOneSpectrum_stabilizer_asIdeal_eq_decompositionSubgroup_valuationSubring

set_option autoImplicit false

open NumberField IsDedekindDomain IsDedekindDomain.HeightOneSpectrum
open scoped NumberField.PlaceDecomp Pointwise

namespace XC0D

section valuationStab

variable (K M : Type*) [Field K] [Field M] [NumberField K] [NumberField M] [Algebra K M] (w : HeightOneSpectrum (𝓞 M))

theorem WithZero.eq_of_forall_le_exp_neg_iff {a b : WithZero (Multiplicative ℤ)} (ha : a ≠ 0) (hb : b ≠ 0) (ha1 : a ≤ 1) (hb1 : b ≤ 1)
    (h : ∀ n : ℕ, a ≤ WithZero.exp (-(n : ℤ)) ↔ b ≤ WithZero.exp (-(n : ℤ))) : a = b := by

  obtain ⟨m, hm⟩ : ∃ m : ℕ, a = WithZero.exp (-(m : ℤ)) := by
    refine ⟨(WithZero.log a).natAbs, ?_⟩
    have hlog : WithZero.log a ≤ 0 := by
      rw [← WithZero.exp_log ha, ← WithZero.exp_zero, WithZero.exp_le_exp] at ha1; exact ha1
    rw [Int.ofNat_natAbs_of_nonpos hlog, neg_neg, WithZero.exp_log ha]
  obtain ⟨n, hn⟩ : ∃ n : ℕ, b = WithZero.exp (-(n : ℤ)) := by
    refine ⟨(WithZero.log b).natAbs, ?_⟩
    have hlog : WithZero.log b ≤ 0 := by
      rw [← WithZero.exp_log hb, ← WithZero.exp_zero, WithZero.exp_le_exp] at hb1; exact hb1
    rw [Int.ofNat_natAbs_of_nonpos hlog, neg_neg, WithZero.exp_log hb]
  apply le_antisymm
  · rw [hn]; exact (h n).2 (hn ▸ le_rfl)
  · rw [hm]; exact (h m).1 (hm ▸ le_rfl)

variable {K M w}

theorem intValuation_smul_of_mem_stabilizer {σ : M ≃ₐ[K] M} (hσ : σ ∈ MulAction.stabilizer (M ≃ₐ[K] M) w.asIdeal)
    (r : 𝓞 M) : w.intValuation (σ • r) = w.intValuation r := by
  by_cases hr : r = 0
  · subst hr; simp
  have hσr : σ • r ≠ 0 := fun h => hr (by simpa using congrArg (fun y => σ⁻¹ • y) h)
  have hpow : ∀ n : ℕ, σ • (w.asIdeal ^ n) = w.asIdeal ^ n := fun n => by
    rw [smul_pow', MulAction.mem_stabilizer_iff.1 hσ]
  refine WithZero.eq_of_forall_le_exp_neg_iff (w.intValuation_ne_zero _ hσr) (w.intValuation_ne_zero _ hr)
    (w.intValuation_le_one _) (w.intValuation_le_one _) fun n => ?_
  rw [HeightOneSpectrum.intValuation_le_pow_iff_mem, HeightOneSpectrum.intValuation_le_pow_iff_mem]
  constructor
  · intro h
    rwa [← hpow n, Ideal.smul_mem_pointwise_smul_iff] at h
  · intro h
    rw [← hpow n]
    exact Ideal.smul_mem_pointwise_smul_iff.2 h

theorem valuation_smul_of_mem_stabilizer {σ : M ≃ₐ[K] M} (hσ : σ ∈ MulAction.stabilizer (M ≃ₐ[K] M) w.asIdeal)
    (x : M) : w.valuation M (σ x) = w.valuation M x := by
  obtain ⟨a, b, hb, rfl⟩ := IsFractionRing.div_surjective (A := 𝓞 M) x
  have hcoe : ∀ r : 𝓞 M, σ (algebraMap (𝓞 M) M r) = algebraMap (𝓞 M) M (σ • r) := fun r => rfl
  rw [map_div₀, hcoe, hcoe, map_div₀, map_div₀, HeightOneSpectrum.valuation_of_algebraMap, HeightOneSpectrum.valuation_of_algebraMap,
    HeightOneSpectrum.valuation_of_algebraMap, HeightOneSpectrum.valuation_of_algebraMap,
    intValuation_smul_of_mem_stabilizer hσ, intValuation_smul_of_mem_stabilizer hσ]

variable (K M w)

theorem stabilizer_le_decompositionSubgroup :
    MulAction.stabilizer (M ≃ₐ[K] M) w.asIdeal ≤ ((w.valuation M).valuationSubring).decompositionSubgroup K := by
  intro σ hσ
  rw [ValuationSubring.decompositionSubgroup, MulAction.mem_stabilizer_iff]
  ext x
  rw [ValuationSubring.mem_pointwise_smul_iff_inv_smul_mem, Valuation.mem_valuationSubring_iff, Valuation.mem_valuationSubring_iff,
    AlgEquiv.smul_def, valuation_smul_of_mem_stabilizer (inv_mem hσ)]

theorem stabilizer_eq_decompositionSubgroup :
    MulAction.stabilizer (M ≃ₐ[K] M) w.asIdeal = ((w.valuation M).valuationSubring).decompositionSubgroup K := by
  refine le_antisymm (stabilizer_le_decompositionSubgroup K M w) fun σ hσ => ?_
  rw [ValuationSubring.decompositionSubgroup, MulAction.mem_stabilizer_iff] at hσ

  have hA : ∀ x : M, w.valuation M (σ⁻¹ x) ≤ 1 ↔ w.valuation M x ≤ 1 := fun x => by
    rw [← Valuation.mem_valuationSubring_iff, ← Valuation.mem_valuationSubring_iff, ← AlgEquiv.smul_def,
      ← ValuationSubring.mem_pointwise_smul_iff_inv_smul_mem, hσ]
  have hA' : ∀ x : M, w.valuation M (σ x) ≤ 1 ↔ w.valuation M x ≤ 1 := fun x => by
    have := hA (σ x)
    rw [show σ⁻¹ (σ x) = x from σ.symm_apply_apply x] at this
    exact this.symm
  have hlt : ∀ x : M, w.valuation M (σ x) < 1 ↔ w.valuation M x < 1 := by

    have key : ∀ y : M, w.valuation M y < 1 ↔ (w.valuation M y ≤ 1 ∧ (y = 0 ∨ ¬ w.valuation M y⁻¹ ≤ 1)) := by
      intro y
      by_cases hy : y = 0
      · simp [hy]
      · rw [map_inv₀, inv_le_one₀ ((Valuation.pos_iff _).2 hy)]
        constructor
        · intro h; exact ⟨h.le, Or.inr (not_le.2 h)⟩
        · rintro ⟨h1, (h2 | h2)⟩
          · exact absurd h2 hy
          · exact not_le.1 h2
    intro x
    rw [key, key, hA', ← map_inv₀, hA', map_inv₀]
    simp [EmbeddingLike.map_eq_zero_iff]
  rw [MulAction.mem_stabilizer_iff]
  apply le_antisymm
  · intro r hr
    rw [Ideal.mem_pointwise_smul_iff_inv_smul_mem] at hr
    rw [← HeightOneSpectrum.valuation_lt_one_iff_mem (K := M)] at hr ⊢
    have := (hlt (algebraMap (𝓞 M) M (σ⁻¹ • r))).2
    rw [show σ (algebraMap (𝓞 M) M (σ⁻¹ • r)) = algebraMap (𝓞 M) M r from by
      change algebraMap (𝓞 M) M (σ • (σ⁻¹ • r)) = _; rw [smul_inv_smul]] at this
    exact this hr
  · intro r hr
    rw [Ideal.mem_pointwise_smul_iff_inv_smul_mem]
    rw [← HeightOneSpectrum.valuation_lt_one_iff_mem (K := M)] at hr ⊢
    have := (hlt (algebraMap (𝓞 M) M (σ⁻¹ • r))).1
    rw [show σ (algebraMap (𝓞 M) M (σ⁻¹ • r)) = algebraMap (𝓞 M) M r from by
      change algebraMap (𝓞 M) M (σ • (σ⁻¹ • r)) = _; rw [smul_inv_smul]] at this
    exact this hr

end valuationStab

end XC0D

theorem solution
    (E F : Type*) [Field E] [NumberField E] [Field F] [NumberField F] [Algebra E F]
    (w : HeightOneSpectrum (𝓞 F)) :
    MulAction.stabilizer (F ≃ₐ[E] F) w.asIdeal = ((w.valuation F).valuationSubring).decompositionSubgroup E := by
  exact XC0D.stabilizer_eq_decompositionSubgroup E F w

end S_IsDedekindDomain_HeightOneSpectrum_stabilizer_asIdeal_eq_decompositionSubgroup_valuationSubring
end P2MW
export P2MW.S_IsDedekindDomain_HeightOneSpectrum_stabilizer_asIdeal_eq_decompositionSubgroup_valuationSubring (solution)
