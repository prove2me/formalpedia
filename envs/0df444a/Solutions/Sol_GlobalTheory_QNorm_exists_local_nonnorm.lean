-- Prove2me | solution 1 for GlobalTheory.QNorm.exists_local_nonnorm
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T20:19:04.653209+00:00
-- url     : https://prove2.me/submissions/f76f7928-ff93-4874-b578-831900936650

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AdelicHermitianForms_SqSubLeNormSub
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_ExistsNormalFormNonsquareAdicCompletion
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_ExistsUnitEvenOrderQuadraticNormValuesOneModFour
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_ExistsGlobalUniformizerResidueRepresentativesStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_ExistsLocalNonnormOfNonsquareAdicCompletion
import Theorems.Thm_GlobalTheory_Idele_adelicMulEquiv_mk
import Theorems.Thm_GlobalTheory_QNorm_exists_evenNorms_unit
import Theorems.Thm_GlobalTheory_QNorm_exists_normal_form_of_not_isSquare
import Theorems.Thm_GlobalTheory_QNorm_exists_uniformizer_and_residue_representatives
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.Idele.adelicMulEquiv_mk


section
open NumberField IsDedekindDomain GlobalTheory.QNorm
open scoped WithZero
namespace GlobalTheory.QNorm
open NumberField IsDedekindDomain in
open scoped WithZero in
private theorem exists_even_valuation_of_mul_sq_eq_norm {K : Type} [Field K]
    (w : Valuation K (WithZero (Multiplicative ℤ))) (Δ y s p q : K)
    (hΔ : _root_.GlobalTheory.QNorm.EvenNorms w Δ) (hs : s ≠ 0) (hy : y ≠ 0)
    (h : y * s ^ 2 = p ^ 2 - Δ * q ^ 2) : ∃ n : ℤ, w y = WithZero.exp (2 * n) := by
  have hpq : p ≠ 0 ∨ q ≠ 0 := by
    by_contra hc
    push_neg at hc
    rw [hc.1, hc.2] at h
    simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, mul_zero, sub_self,
      mul_eq_zero, pow_eq_zero_iff] at h
    tauto
  obtain ⟨n, hn⟩ := hΔ p q hpq
  rw [← h, map_mul, map_pow] at hn
  have hws : w s = WithZero.exp (w s).log :=
    (WithZero.exp_log ((Valuation.ne_zero_iff w).mpr hs)).symm
  rw [hws, ← WithZero.exp_nsmul] at hn
  refine ⟨n - (w s).log, ?_⟩
  have key : w y = WithZero.exp (2 * n) * WithZero.exp (-(2 • (w s).log)) := by
    rw [← hn, mul_assoc, ← WithZero.exp_add, add_neg_cancel, WithZero.exp_zero, mul_one]
  rw [key, ← WithZero.exp_add]
  congr 1
  rw [nsmul_eq_mul]
  push_cast
  ring
open NumberField IsDedekindDomain in
open scoped WithZero in
private theorem not_norm_of_odd_valuation_of_norm_mul {K : Type} [Field K]
    (w : Valuation K (WithZero (Multiplicative ℤ))) (δ Δ y c d : K) (hδ : δ ≠ 0)
    (hΔ : _root_.GlobalTheory.QNorm.EvenNorms w Δ) (hy : y ≠ 0)
    (hodd : ∀ n : ℤ, w y ≠ WithZero.exp (2 * n)) (hc : y = c ^ 2 - δ * Δ * d ^ 2) :
    ¬ ∃ a b : K, y = a ^ 2 - δ * b ^ 2 := by
  rintro ⟨a, b, hab⟩
  have main : ∀ e : K, e ^ 2 = c ^ 2 → a + e ≠ 0 → False := by
    intro e he hs
    have hc2 : y = e ^ 2 - δ * Δ * d ^ 2 := by rw [he]; exact hc
    obtain ⟨n, hn⟩ := exists_even_valuation_of_mul_sq_eq_norm w Δ y (a + e) (a * e + y) (δ * b * d)
      hΔ hs hy (by linear_combination (e ^ 2 - y) * hab + δ * b ^ 2 * hc2)
    exact hodd n hn
  by_cases h1 : a + c = 0
  · by_cases h2 : a + -c = 0
    · have hca : c = -a := by linear_combination h1
      have hb : δ * b ^ 2 = δ * (Δ * d ^ 2) := by
        rw [hca] at hc
        linear_combination hab - hc
      have hb' : b ^ 2 = Δ * d ^ 2 := mul_left_cancel₀ hδ hb
      by_cases hd : d = 0
      · rw [hd] at hb'
        have hb0 : b = 0 := by simpa using hb'
        rw [hb0] at hab
        obtain ⟨n, hn⟩ := exists_even_valuation_of_mul_sq_eq_norm w Δ y 1 a 0 hΔ one_ne_zero hy
          (by rw [hab]; ring)
        exact hodd n hn
      · obtain ⟨n, hn⟩ := hΔ (b / d) 1 (Or.inr one_ne_zero)
        have hz : (b / d) ^ 2 - Δ * 1 ^ 2 = 0 := by
          rw [div_pow, hb']
          field_simp
          ring
        rw [hz, map_zero] at hn
        exact WithZero.exp_ne_zero hn.symm
    · exact main (-c) (by ring) h2
  · exact main c rfl h1
end GlobalTheory.QNorm
end

set_option autoImplicit false
open NumberField IsDedekindDomain GlobalTheory.QNorm
open scoped WithZero
open GlobalTheory GlobalTheory.QNorm
open NumberField IsDedekindDomain
open scoped WithZero
namespace GlobalTheory.QNorm
namespace _root_.GlobalTheory.QNorm
theorem _root_.solution : ∀ (F : Type) [Field F] [NumberField F]
    (v : HeightOneSpectrum (𝓞 F)) (δ : v.adicCompletion F), δ ≠ 0 → ¬ IsSquare δ →
    ∃ x : v.adicCompletion F, x ≠ 0 ∧ ¬ ∃ a b : v.adicCompletion F, x = a ^ 2 - δ * b ^ 2 := by
  intro F _ _ v δ hδ hns
  obtain ⟨c, hc0, hcases⟩ := _root_.GlobalTheory.QNorm.exists_normal_form_of_not_isSquare F v δ hδ hns
  have hδ' : δ * c ^ 2 ≠ 0 := mul_ne_zero hδ (pow_ne_zero 2 hc0)
  suffices h : ∃ x : v.adicCompletion F, x ≠ 0 ∧
      ¬ ∃ a b : v.adicCompletion F, x = a ^ 2 - δ * c ^ 2 * b ^ 2 by
    obtain ⟨x, hx0, hx⟩ := h
    refine ⟨x, hx0, ?_⟩
    rintro ⟨a, b, hab⟩
    refine hx ⟨a, b / c, ?_⟩
    rw [hab]
    field_simp
  obtain ⟨Δ, hΔ, hΔ1, hΔ4⟩ := _root_.GlobalTheory.QNorm.exists_evenNorms_unit F v
  have hΔ0 : Δ ≠ 0 := by
    intro h
    rw [h, map_zero] at hΔ1
    exact zero_ne_one hΔ1
  rcases hcases with ⟨n, hn⟩ | ⟨h1, h4, n, hn⟩ | hE
  · refine ⟨-(δ * c ^ 2 * Δ), neg_ne_zero.mpr (mul_ne_zero hδ' hΔ0),
      not_norm_of_odd_valuation_of_norm_mul Valued.v (δ * c ^ 2) Δ _ 0 1 hδ' hΔ
        (neg_ne_zero.mpr (mul_ne_zero hδ' hΔ0)) ?_ (by ring)⟩
    intro m hm
    rw [Valuation.map_neg, map_mul, hn, hΔ1, mul_one, WithZero.exp_inj] at hm
    omega
  · have hy : (1 : v.adicCompletion F) - δ * c ^ 2 * Δ =
        -((δ * c ^ 2 - 1) + δ * c ^ 2 * (Δ - 1)) := by
      ring
    have hwy : Valued.v ((1 : v.adicCompletion F) - δ * c ^ 2 * Δ) =
        WithZero.exp (2 * n + 1) := by
      rw [hy, Valuation.map_neg, Valuation.map_add_eq_of_lt_left _
        (by rw [map_mul, h1, one_mul]; exact lt_of_le_of_lt hΔ4 h4), hn]
    have hy0 : (1 : v.adicCompletion F) - δ * c ^ 2 * Δ ≠ 0 := by
      intro h
      rw [h, map_zero] at hwy
      exact WithZero.exp_ne_zero hwy.symm
    refine ⟨_, hy0, not_norm_of_odd_valuation_of_norm_mul Valued.v (δ * c ^ 2) Δ _ 1 1 hδ' hΔ hy0 ?_
      (by ring)⟩
    intro m hm
    rw [hwy, WithZero.exp_inj] at hm
    omega
  · obtain ⟨⟨π, -, hπ⟩, -⟩ := _root_.GlobalTheory.QNorm.exists_uniformizer_and_residue_representatives F v
    have hx0 : algebraMap F (v.adicCompletion F) π ≠ 0 := by
      intro h
      rw [h, map_zero] at hπ
      exact WithZero.exp_ne_zero hπ.symm
    refine ⟨_, hx0, ?_⟩
    rintro ⟨a, b, hab⟩
    have hab' : a ≠ 0 ∨ b ≠ 0 := by
      by_contra h
      push_neg at h
      rw [h.1, h.2] at hab
      apply hx0
      rw [hab]
      ring
    obtain ⟨m, hm⟩ := hE a b hab'
    rw [← hab, hπ, WithZero.exp_inj] at hm
    omega
end _root_.GlobalTheory.QNorm
end GlobalTheory.QNorm
