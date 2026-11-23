-- Prove2me | solution 1 for GlobalTheory.ringOfIntegers_sqrt_neg_three_mod_four
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T07:56:45.715059+00:00
-- url     : https://prove2.me/submissions/2ee84823-6834-45ea-8fc6-1e26e02de734

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_DedekindZetaEqSumRealEisenstein
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CubicalLineBundles_RingOfIntegersSqrtNegThreeModFour
import Theorems.Thm_GlobalTheory_exists_integer_generator_of_sq_eq_neg
import Theorems.Thm_GlobalTheory_eq_I_mul_sqrt_or_of_sq_eq_neg
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
open NumberField Module
namespace GlobalTheory
open QuadraticZeta
private theorem norm_sq_add_norm_sq_sub_eq_complete_square {K : Type*} [Field K] [NumberField K] {d : ℕ}
    (h2 : finrank ℚ K = 2) (hd : d % 4 = 3) {r : K} (hr : r ^ 2 = -d) :
    (∀ x : K, ∃ a b : ℚ, x = a + b * r) ∧ ∃ τ : K →+* K, τ r = -r := by
  have hli : LinearIndependent ℚ ![(1 : K), r] := by
    rw [LinearIndependent.pair_iff]
    intro s t hst
    rw [Rat.smul_def, Rat.smul_def, mul_one] at hst
    by_cases ht : t = 0
    · subst ht
      simp at hst
      exact ⟨hst, rfl⟩
    · exfalso
      have htK : (t : K) ≠ 0 := Rat.cast_ne_zero.mpr ht
      have hr' : r = ((-s / t : ℚ) : K) := by
        push_cast
        field_simp
        linear_combination hst
      have h0 : (((-s / t) ^ 2 + d : ℚ) : K) = 0 := by
        rw [Rat.cast_add, Rat.cast_pow, ← hr', hr]
        push_cast
        ring
      have h0' : (-s / t) ^ 2 + (d : ℚ) = 0 := by exact_mod_cast h0
      have hdpos : (0 : ℚ) < d := by exact_mod_cast (show 0 < d by omega)
      nlinarith [sq_nonneg (-s / t)]
  let B := basisOfLinearIndependentOfCardEqFinrank hli (by simp [h2])
  have hB0 : B 0 = 1 := by simp [B]
  have hB1 : B 1 = r := by simp [B]
  have hdec : ∀ x : K, ∃ a b : ℚ, x = a + b * r := by
    intro x
    refine ⟨B.repr x 0, B.repr x 1, ?_⟩
    conv_lhs => rw [← B.sum_repr x]
    rw [Fin.sum_univ_two, hB0, hB1, Rat.smul_def, Rat.smul_def, mul_one]
  refine ⟨hdec, ?_⟩
  have hf : ∀ a b : ℚ, (B.constr ℚ ![(1 : K), -r]) ((a : K) + b * r) = a - b * r := by
    intro a b
    have e : ((a : K) + b * r) = a • B 0 + b • B 1 := by
      rw [hB0, hB1, Rat.smul_def, Rat.smul_def, mul_one]
    rw [e, map_add, map_smul, map_smul, Basis.constr_basis, Basis.constr_basis]
    simp [Rat.smul_def, sub_eq_add_neg]
  have hone : (B.constr ℚ ![(1 : K), -r]) 1 = 1 := by simpa using hf 1 0
  have hmul : ∀ x y : K, (B.constr ℚ ![(1 : K), -r]) (x * y) =
      (B.constr ℚ ![(1 : K), -r]) x * (B.constr ℚ ![(1 : K), -r]) y := by
    intro x y
    obtain ⟨a, b, rfl⟩ := hdec x
    obtain ⟨c, e, rfl⟩ := hdec y
    have hxy : ((a : K) + b * r) * (c + e * r) =
        ((a * c - d * b * e : ℚ) : K) + ((a * e + b * c : ℚ) : K) * r := by
      push_cast
      linear_combination ((b : K) * e) * hr
    rw [hxy, hf, hf, hf]
    push_cast
    linear_combination (-((b : K) * e)) * hr
  exact ⟨(AlgHom.ofLinearMap (B.constr ℚ ![(1 : K), -r]) hone hmul).toRingHom,
    by show (B.constr ℚ ![(1 : K), -r]) r = -r; simpa using hf 0 1⟩
end GlobalTheory
end

set_option autoImplicit false
open NumberField Module
open GlobalTheory
open QuadraticZeta
namespace GlobalTheory
theorem _root_.solution (d : ℕ) (hsq : Squarefree d) (hd : d % 4 = 3)
    (K : Type) [Field K] [NumberField K] (h2 : Module.finrank ℚ K = 2) (r : K)
    (hr : r ^ 2 = -(d : K)) :
    ∃ (w : 𝓞 K) (bar : 𝓞 K →+* 𝓞 K), 2 * (w : K) = 1 + r ∧ w + bar w = 1 ∧
      (∀ c : 𝓞 K, ∃ m n : ℤ, c = m + n * w) ∧
      (∀ σ : K →+* ℂ, ¬ ComplexEmbedding.IsReal σ ∧
        ∀ c : 𝓞 K, σ (bar c : K) = starRingEnd ℂ (σ (c : K))) ∧
      ∃ σ : K →+* ℂ, σ r = Complex.I * √d := by
  obtain ⟨hdec, τ, hτ⟩ := norm_sq_add_norm_sq_sub_eq_complete_square h2 hd hr
  obtain ⟨w, hw2, hgen⟩ := exists_integer_generator_of_sq_eq_neg h2 hsq hd hr
  have hσr : ∀ σ : K →+* ℂ, σ r = Complex.I * √d ∨ σ r = -(Complex.I * √d) := fun σ =>
    eq_I_mul_sqrt_or_of_sq_eq_neg (by rw [← map_pow, hr, map_neg, map_natCast])
  have hconj : ∀ σ : K →+* ℂ, starRingEnd ℂ (σ r) = -σ r := by
    intro σ
    rcases hσr σ with h | h <;> rw [h] <;> simp [Complex.conj_ofReal]
  have hcomp : ∀ σ : K →+* ℂ, ∀ x : K, σ (τ x) = starRingEnd ℂ (σ x) := by
    intro σ x
    obtain ⟨a, b, rfl⟩ := hdec x
    simp only [map_add, map_mul, map_ratCast, hτ, map_neg, hconj]
  refine ⟨w, RingOfIntegers.mapRingHom τ, hw2, ?_, hgen, ?_, ?_⟩
  · apply RingOfIntegers.ext
    have hw' : (w : K) = (1 + r) / 2 := by linear_combination hw2 / 2
    show (w : K) + τ (w : K) = 1
    rw [hw', map_div₀, map_add, map_one, hτ, map_ofNat]
    ring
  · intro σ
    refine ⟨?_, ?_⟩
    · intro hreal
      have h1 := RingHom.congr_fun (ComplexEmbedding.isReal_iff.mp hreal) r
      rw [ComplexEmbedding.conjugate_coe_eq, hconj] at h1
      have h0 : σ r = 0 := by linear_combination (-1 / 2 : ℂ) * h1
      have hr0 : r = 0 := by simpa using h0
      rw [hr0] at hr
      have hd0 : (d : K) = 0 := by linear_combination hr
      have : d = 0 := by exact_mod_cast hd0
      omega
    · intro c
      simpa using hcomp σ c
  · obtain σ₀ : K →+* ℂ := by
      have : 0 < Fintype.card (K →+* ℂ) := by rw [NumberField.Embeddings.card]; omega
      exact (Fintype.card_pos_iff.mp this).some
    rcases hσr σ₀ with h | h
    · exact ⟨σ₀, h⟩
    · refine ⟨σ₀.comp τ, ?_⟩
      rw [RingHom.comp_apply, hτ, map_neg, h, neg_neg]
end GlobalTheory
