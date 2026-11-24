-- Prove2me | solution 1 for GlobalTheory.SplitSep.exists_sep
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T21:08:02.268864+00:00
-- url     : https://prove2.me/submissions/9e60271c-794d-4dae-a047-79f46765c0ba

import Mathlib
import Definitions.Def_ReciprocityTheory_Automorphisms_Unitary
import Definitions.Def_ReciprocityTheory_Automorphisms_PlaceA
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SatakeParameters_ExistsIntegerUnitSplitPlaceConjugatePrime
import Theorems.Thm_GlobalTheory_SplitSep_exists_near
import Theorems.Thm_ReciprocityTheory_Aut_adic_valued_algebraMap


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain Polynomial
noncomputable section
open GlobalTheory GlobalTheory.SplitSep
variable {L : Type} [Field L] [NumberField L] [IsCMField L]
local notation3 "L⁺" => NumberField.maximalRealSubfield L
local notation3 "cc" => IsCMField.complexConj L
variable (L)
namespace GlobalTheory.SplitSep
theorem _root_.solution (s : ReciprocityTheory.Aut.SplitPlace L) :
    ∃ e : 𝓞 L, Valued.v (s.i (e : L)) = 1 ∧
      Valued.v (s.i (IsCMField.complexConj L (e : L))) < 1 := by
  obtain ⟨θ, hθ⟩ : ∃ θ : L, cc θ ≠ θ := by
    by_contra h
    push_neg at h
    exact IsCMField.complexConj_ne_one L (AlgEquiv.ext h)
  obtain ⟨δ, hδ⟩ : ∃ δ : L, δ = θ - cc θ := ⟨_, rfl⟩
  have hcδ : cc δ = -δ := by rw [hδ, map_sub, IsCMField.complexConj_apply_apply, neg_sub]
  have hδ0 : δ ≠ 0 := by rw [hδ]; exact sub_ne_zero.mpr (Ne.symm hθ)
  obtain ⟨t, ht_def⟩ : ∃ t : s.v.adicCompletion L⁺, t = s.i δ := ⟨_, rfl⟩
  have ht : t ≠ 0 := by rw [ht_def]; exact (_root_.map_ne_zero s.i).mpr hδ0
  have h2 : (2 : s.v.adicCompletion L⁺) ≠ 0 := by
    have e : (2 : s.v.adicCompletion L⁺) = algebraMap L⁺ _ 2 := by rw [map_ofNat]
    rw [e]
    exact (_root_.map_ne_zero _).mpr two_ne_zero
  have h2half : (2 : s.v.adicCompletion L⁺)⁻¹ + 2⁻¹ = 1 := by
    rw [← two_mul, mul_inv_cancel₀ h2]
  obtain ⟨a, ha⟩ := exists_near s.v (fun z => z - 2⁻¹) (by fun_prop) (2⁻¹) (by simp)
  have h0 : t⁻¹ * 2⁻¹ * t - 2⁻¹ = 0 := by
    rw [mul_comm t⁻¹, mul_assoc, inv_mul_cancel₀ ht, mul_one, sub_self]
  obtain ⟨b, hb⟩ := exists_near s.v (fun z => z * t - 2⁻¹)
    ((continuous_id.mul continuous_const).sub continuous_const) (t⁻¹ * 2⁻¹)
    (by simp only [h0, map_zero]; exact zero_lt_one)
  obtain ⟨x, hx⟩ : ∃ x : L, x = algebraMap L⁺ L a + algebraMap L⁺ L b * δ := ⟨_, rfl⟩
  have hix : s.i x = algebraMap L⁺ (s.v.adicCompletion L⁺) a +
      algebraMap L⁺ (s.v.adicCompletion L⁺) b * t := by
    rw [hx, map_add, map_mul, AlgHom.commutes, AlgHom.commutes, ht_def]
  have hcx : cc x = algebraMap L⁺ L a - algebraMap L⁺ L b * δ := by
    rw [hx, map_add, map_mul, AlgEquiv.commutes, AlgEquiv.commutes, hcδ]; ring
  have hicx : s.i (cc x) = algebraMap L⁺ (s.v.adicCompletion L⁺) a -
      algebraMap L⁺ (s.v.adicCompletion L⁺) b * t := by
    rw [hcx, map_sub, map_mul, AlgHom.commutes, AlgHom.commutes, ht_def]
  have hx1 : Valued.v (s.i x) = 1 := by
    have e : s.i x - 1 = (algebraMap L⁺ (s.v.adicCompletion L⁺) a - 2⁻¹) +
        (algebraMap L⁺ (s.v.adicCompletion L⁺) b * t - 2⁻¹) := by
      rw [hix]; linear_combination h2half
    refine (Valued.v.map_eq_of_sub_lt ?_).trans (map_one _)
    rw [map_one, e]
    exact lt_of_le_of_lt (Valuation.map_add _ _ _) (max_lt ha hb)
  have hcx1 : Valued.v (s.i (cc x)) < 1 := by
    have e : s.i (cc x) = (algebraMap L⁺ (s.v.adicCompletion L⁺) a - 2⁻¹) -
        (algebraMap L⁺ (s.v.adicCompletion L⁺) b * t - 2⁻¹) := by
      rw [hicx]; ring
    rw [e]
    exact lt_of_le_of_lt (Valuation.map_sub _ _ _) (max_lt ha hb)
  have hT : cc (x + cc x) = x + cc x := by
    rw [map_add, IsCMField.complexConj_apply_apply, add_comm]
  have hN : cc (x * cc x) = x * cc x := by
    rw [map_mul, IsCMField.complexConj_apply_apply, mul_comm]
  let T : L⁺ := ⟨x + cc x, (IsCMField.complexConj_eq_self_iff (K := L) _).mp hT⟩
  let N : L⁺ := ⟨x * cc x, (IsCMField.complexConj_eq_self_iff (K := L) _).mp hN⟩
  have hTL : algebraMap L⁺ L T = x + cc x := rfl
  have hNL : algebraMap L⁺ L N = x * cc x := rfl
  have hvT : s.v.valuation L⁺ T ≤ 1 := by
    rw [← ReciprocityTheory.Aut.adic_valued_algebraMap s.v, ← s.i.commutes, hTL, map_add]
    exact (Valuation.map_add _ _ _).trans (max_le hx1.le hcx1.le)
  have hvN : s.v.valuation L⁺ N ≤ 1 := by
    rw [← ReciprocityTheory.Aut.adic_valued_algebraMap s.v, ← s.i.commutes, hNL, map_mul,
      Valuation.map_mul, hx1, one_mul]
    exact hcx1.le
  obtain ⟨n₁, d₁, hd₁⟩ := HeightOneSpectrum.exists_primeCompl_mul_eq_of_integer s.v T hvT
  obtain ⟨n₂, d₂, hd₂⟩ := HeightOneSpectrum.exists_primeCompl_mul_eq_of_integer s.v N hvN
  obtain ⟨m, hm_def⟩ : ∃ m : 𝓞 L⁺, m = (d₁ : 𝓞 L⁺) * d₂ := ⟨_, rfl⟩
  have hm : m ∉ s.v.asIdeal := by rw [hm_def]; exact (d₁ * d₂).2
  obtain ⟨mK, hmK⟩ : ∃ mK : L⁺, mK = algebraMap (𝓞 L⁺) L⁺ m := ⟨_, rfl⟩
  have hp' : algebraMap (𝓞 L⁺) L⁺ (n₁ * d₂) = mK * T := by
    rw [map_mul, ← hd₁, hmK, hm_def, map_mul]; ring
  have hq' : algebraMap (𝓞 L⁺) L⁺ (n₂ * d₁ ^ 2 * d₂) = mK ^ 2 * N := by
    rw [map_mul, map_mul, map_pow, ← hd₂, hmK, hm_def, map_mul]; ring
  have hp : algebraMap (𝓞 L⁺) L (n₁ * d₂) = algebraMap L⁺ L mK * (x + cc x) := by
    rw [IsScalarTower.algebraMap_apply (𝓞 L⁺) L⁺ L, hp', map_mul, hTL]
  have hq : algebraMap (𝓞 L⁺) L (n₂ * d₁ ^ 2 * d₂) = (algebraMap L⁺ L mK) ^ 2 * (x * cc x) := by
    rw [IsScalarTower.algebraMap_apply (𝓞 L⁺) L⁺ L, hq', map_mul, map_pow, hNL]
  obtain ⟨y, hy_def⟩ : ∃ y : L, y = algebraMap L⁺ L mK * x := ⟨_, rfl⟩
  have hyA : IsIntegral (𝓞 L⁺) y := by
    refine ⟨X ^ 2 - C (n₁ * (d₂ : 𝓞 L⁺)) * X + C (n₂ * (d₁ : 𝓞 L⁺) ^ 2 * d₂), by monicity!, ?_⟩
    rw [eval₂_add, eval₂_sub, eval₂_mul, eval₂_C, eval₂_C, eval₂_X, eval₂_X_pow, hp, hq, hy_def]
    ring
  have hy : IsIntegral ℤ y := isIntegral_trans y hyA
  have hvm : Valued.v (algebraMap L⁺ (s.v.adicCompletion L⁺) mK) = 1 := by
    rw [ReciprocityTheory.Aut.adic_valued_algebraMap s.v, hmK]
    exact (HeightOneSpectrum.valuation_eq_one_iff_notMem s.v).mpr hm
  refine ⟨⟨y, hy⟩, ?_, ?_⟩
  · show Valued.v (s.i y) = 1
    rw [hy_def, map_mul, s.i.commutes, Valuation.map_mul, hvm, hx1, one_mul]
  · show Valued.v (s.i (cc y)) < 1
    rw [hy_def, map_mul, AlgEquiv.commutes, map_mul, s.i.commutes, Valuation.map_mul, hvm, one_mul]
    exact hcx1
end GlobalTheory.SplitSep
