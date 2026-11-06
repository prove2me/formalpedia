-- Prove2me | solution 1 for GuthMaynard.Affine.integral_mul_Hfun_le
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-06T00:14:14.801204+00:00
-- url     : https://prove2.me/submissions/57dd0a74-494f-4eee-aa30-776ae56fbf63

import Mathlib
import Definitions.Def_GuthMaynard
import Definitions.Def_GuthMaynardAffine
section
namespace GuthMaynard.Affine
open GuthMaynard MeasureTheory FourierTransform Complex
open scoped ENNReal

theorem J_eq (M K : ℝ) (f : ℝ → ℝ) :
    J M K f = ⨆ (M₁ : ℝ) (_ : M₁ ∈ Set.Ioo 0 M) (M₂ : ℝ) (_ : M₂ ∈ Set.Ioo 0 M) (M₃ : ℝ)
      (_ : M₃ ∈ Set.Ioo 0 M), ∫⁻ u : ℝ, ENNReal.ofReal (gsum K M₁ M₂ M₃ f u ^ 2) := rfl


end GuthMaynard.Affine
end

section
namespace GuthMaynard.Affine.PartT
open GuthMaynard GuthMaynard.Affine MeasureTheory FourierTransform Complex
open scoped ENNReal

theorem cont_hcs {C : ℝ} {f : ℝ → ℝ} (hf : Continuous f)
    (hsupp : Function.support f ⊆ Set.Icc (1 / C) C) : HasCompactSupport f :=
  HasCompactSupport.intro isCompact_Icc fun x hx => by
    by_contra h; exact hx (hsupp h)

theorem mem_dyadic {M : ℝ} {m : ℤ} (h : m ∈ dyadic M) : M < m ∧ (m : ℝ) ≤ 2 * M := by
  simp only [dyadic, Finset.mem_Ioc] at h
  exact ⟨Int.floor_lt.1 h.1, Int.le_floor.1 h.2⟩

theorem dyadic_eq_empty {M : ℝ} (h0 : 0 < M) (h : M < 1 / 2) : dyadic M = ∅ := by
  ext m
  simp only [Finset.notMem_empty, iff_false]
  intro hm
  obtain ⟨h1, h2⟩ := mem_dyadic hm
  have : (m : ℝ) < 1 := by linarith
  have : (0 : ℝ) < m := by linarith
  have h3 : m < 1 := by exact_mod_cast ‹(m : ℝ) < 1›
  have h4 : 0 < m := by exact_mod_cast this
  omega

theorem card_dyadic_le {M : ℝ} (h0 : 0 < M) : ((dyadic M).card : ℝ) ≤ 3 * M := by
  by_cases hM : M < 1 / 2
  · rw [dyadic_eq_empty h0 hM]; simp; linarith
  push Not at hM
  simp only [dyadic, Int.card_Ioc]
  have h1 : (⌊2 * M⌋ : ℝ) ≤ 2 * M := Int.floor_le _
  have h2 : M - 1 < (⌊M⌋ : ℝ) := Int.sub_one_lt_floor _
  rcases le_or_gt (⌊2 * M⌋ - ⌊M⌋) 0 with h | h
  · rw [Int.toNat_of_nonpos h]; simp; linarith
  · have : (((⌊2 * M⌋ - ⌊M⌋).toNat : ℤ) : ℝ) = (⌊2 * M⌋ : ℝ) - ⌊M⌋ := by
      rw [Int.toNat_of_nonneg h.le]; push_cast; ring
    rw [← Int.cast_natCast, this]
    linarith

/-- The `m₁` range. -/
noncomputable abbrev A1 (M₁ : ℝ) : Finset ℤ := dyadic M₁ ∪ (dyadic M₁).map (Equiv.neg ℤ).toEmbedding

theorem mem_A1 {M₁ : ℝ} {m : ℤ} (h : m ∈ A1 M₁) : M₁ < |(m : ℝ)| ∧ |(m : ℝ)| ≤ 2 * M₁ := by
  simp only [A1, Finset.mem_union, Finset.mem_map, Equiv.coe_toEmbedding, Equiv.neg_apply] at h
  rcases h with h | ⟨n, hn, rfl⟩
  · obtain ⟨h1, h2⟩ := mem_dyadic h
    have : (0 : ℝ) ≤ m := by
      by_contra hc; push Not at hc
      have := lt_trans h1 hc
      have hM : 0 ≤ M₁ ∨ M₁ < 0 := le_or_gt 0 M₁
      rcases hM with hM | hM <;> linarith
    rw [abs_of_nonneg this]; exact ⟨h1, h2⟩
  · obtain ⟨h1, h2⟩ := mem_dyadic hn
    push_cast
    rw [abs_neg]
    by_cases hn0 : (0 : ℝ) ≤ n
    · rw [abs_of_nonneg hn0]; exact ⟨h1, h2⟩
    · push Not at hn0
      rw [abs_of_neg hn0]; constructor <;> linarith

theorem card_A1_le {M₁ : ℝ} (h0 : 0 < M₁) : ((A1 M₁).card : ℝ) ≤ 6 * M₁ := by
  have := Finset.card_union_le (dyadic M₁) ((dyadic M₁).map (Equiv.neg ℤ).toEmbedding)
  rw [Finset.card_map] at this
  have h2 : ((A1 M₁).card : ℝ) ≤ (dyadic M₁).card + (dyadic M₁).card := by exact_mod_cast this
  linarith [card_dyadic_le h0]

theorem card_Icc_le {K M₃ : ℝ} (hK : 0 < K) (h3 : 0 < M₃) :
    ((Finset.Icc (-⌊K * M₃⌋) ⌊K * M₃⌋).card : ℝ) ≤ 2 * K * M₃ + 1 := by
  have hk : 0 ≤ ⌊K * M₃⌋ := Int.floor_nonneg.2 (by positivity)
  have h1 : (⌊K * M₃⌋ : ℝ) ≤ K * M₃ := Int.floor_le _
  rw [Int.card_Icc, ← Int.cast_natCast, Int.toNat_of_nonneg (by omega)]
  push_cast
  linarith

/-- `gsum` as one sum over triples. -/
theorem gsum_eq (K M₁ M₂ M₃ : ℝ) (f : ℝ → ℝ) (u : ℝ) :
    gsum K M₁ M₂ M₃ f u = ∑ p ∈ A1 M₁ ×ˢ dyadic M₂ ×ˢ Finset.Icc (-⌊K * M₃⌋) ⌊K * M₃⌋,
      f ((p.1 * u + p.2.2) / p.2.1) := by
  rw [Finset.sum_product, gsum]
  refine Finset.sum_congr rfl fun m₁ _ => ?_
  rw [Finset.sum_product]

/-- Change of variables for one term. -/
theorem integral_term (g : ℝ → ℝ) (m₁ m₂ m₃ : ℝ) (h1 : m₁ ≠ 0) (h2 : m₂ ≠ 0) :
    ∫ u, g ((m₁ * u + m₃) / m₂) = |m₂ / m₁| * ∫ u, g u := by
  have e : (fun u => g ((m₁ * u + m₃) / m₂)) = fun u => (fun y => g (y + m₃ / m₂)) ((m₁ / m₂) * u) := by
    funext u; congr 1; field_simp
  rw [e, Measure.integral_comp_mul_left (fun y => g (y + m₃ / m₂)) (m₁ / m₂),
    integral_add_right_eq_self, smul_eq_mul, inv_div]

theorem integrable_term {g : ℝ → ℝ} (hg : Integrable g) (m₁ m₂ m₃ : ℝ) (h1 : m₁ ≠ 0)
    (h2 : m₂ ≠ 0) : Integrable (fun u => g ((m₁ * u + m₃) / m₂)) := by
  have e : (fun u => g ((m₁ * u + m₃) / m₂)) = fun u => (fun y => g (y + m₃ / m₂)) ((m₁ / m₂) * u) := by
    funext u; congr 1; field_simp
  rw [e]
  exact (hg.comp_add_right (m₃ / m₂)).comp_mul_left' (div_ne_zero h1 h2)

/-- The trivial (Cauchy–Schwarz) bound `J(f) ≪ (1+K)² M⁶ ∫ f²`. -/
theorem lintegral_gsum_sq_le_trivial (C K : ℝ) (hC : 1 ≤ C) (hK : 0 < K) (f : ℝ → ℝ)
    (hf : Continuous f) (hnn : ∀ u, 0 ≤ f u) (hsupp : Function.support f ⊆ Set.Icc (1 / C) C)
    (M M₁ M₂ M₃ : ℝ) (h₁ : M₁ ∈ Set.Ioo 0 M) (h₂ : M₂ ∈ Set.Ioo 0 M) (h₃ : M₃ ∈ Set.Ioo 0 M) :
    ∫⁻ u : ℝ, ENNReal.ofReal (gsum K M₁ M₂ M₃ f u ^ 2) ≤
      ENNReal.ofReal (3000 * (1 + K) ^ 2 * M ^ 6 * ∫ u, f u ^ 2) := by
  obtain ⟨h10, h1M⟩ := h₁
  obtain ⟨h20, h2M⟩ := h₂
  obtain ⟨h30, h3M⟩ := h₃
  by_cases hM : M < 1 / 2
  · have : ∀ u, gsum K M₁ M₂ M₃ f u = 0 := by
      intro u; simp [gsum, dyadic_eq_empty h20 (by linarith : M₂ < 1 / 2)]
    simp [this]
  push Not at hM
  set P := A1 M₁ ×ˢ dyadic M₂ ×ˢ Finset.Icc (-⌊K * M₃⌋) ⌊K * M₃⌋ with hP
  set N : ℝ := (P.card : ℝ) with hN
  have hcs : HasCompactSupport f := cont_hcs hf hsupp
  have hcs2 : HasCompactSupport (fun u => f u ^ 2) :=
    HasCompactSupport.intro isCompact_Icc fun x hx => by
      have : f x = 0 := by by_contra h; exact hx (hsupp h)
      simp [this]
  have hf2 : Integrable (fun u => f u ^ 2) := (hf.pow 2).integrable_of_hasCompactSupport hcs2
  set I := ∫ u, f u ^ 2 with hI
  have hI0 : 0 ≤ I := integral_nonneg fun u => sq_nonneg _
  -- facts on P
  have hPmem : ∀ p ∈ P, (p.1 : ℝ) ≠ 0 ∧ (p.2.1 : ℝ) ≠ 0 ∧ |(p.2.1 : ℝ) / p.1| ≤ 2 * M₂ / M₁ := by
    intro p hp
    simp only [hP, Finset.mem_product] at hp
    obtain ⟨a1, a2⟩ := mem_A1 hp.1
    obtain ⟨b1, b2⟩ := mem_dyadic hp.2.1
    have hp1 : (p.1 : ℝ) ≠ 0 := by intro h; rw [h] at a1; simp at a1; linarith
    refine ⟨hp1, by intro h; rw [h] at b1; linarith, ?_⟩
    rw [abs_div, abs_of_pos (by linarith : (0 : ℝ) < p.2.1), div_le_div_iff₀ (by linarith) h10]
    nlinarith
  have hint : ∀ p ∈ P, Integrable (fun u => f ((p.1 * u + p.2.2) / p.2.1) ^ 2) := by
    intro p hp
    obtain ⟨a, b, -⟩ := hPmem p hp
    exact integrable_term hf2 _ _ _ a b
  have hsum_int : Integrable (fun u => N * ∑ p ∈ P, f ((p.1 * u + p.2.2) / p.2.1) ^ 2) :=
    (integrable_finsetSum P hint).const_mul N
  calc ∫⁻ u : ℝ, ENNReal.ofReal (gsum K M₁ M₂ M₃ f u ^ 2)
      ≤ ∫⁻ u : ℝ, ENNReal.ofReal (N * ∑ p ∈ P, f ((p.1 * u + p.2.2) / p.2.1) ^ 2) := by
        refine lintegral_mono fun u => ENNReal.ofReal_le_ofReal ?_
        rw [gsum_eq]
        exact sq_sum_le_card_mul_sum_sq
    _ = ENNReal.ofReal (∫ u, N * ∑ p ∈ P, f ((p.1 * u + p.2.2) / p.2.1) ^ 2) := by
        rw [ofReal_integral_eq_lintegral_ofReal hsum_int
          (Filter.Eventually.of_forall fun u => by positivity)]
    _ ≤ ENNReal.ofReal (3000 * (1 + K) ^ 2 * M ^ 6 * I) := by
        apply ENNReal.ofReal_le_ofReal
        rw [integral_const_mul, integral_finsetSum P hint]
        have hterm : ∀ p ∈ P, ∫ u, f ((p.1 * u + p.2.2) / p.2.1) ^ 2 ≤ 2 * M₂ / M₁ * I := by
          intro p hp
          obtain ⟨a, b, c⟩ := hPmem p hp
          rw [integral_term (fun y => f y ^ 2) _ _ _ a b]
          exact mul_le_mul_of_nonneg_right c hI0
        have hs : ∑ p ∈ P, ∫ u, f ((p.1 * u + p.2.2) / p.2.1) ^ 2 ≤ N * (2 * M₂ / M₁ * I) := by
          refine (Finset.sum_le_sum hterm).trans ?_
          rw [Finset.sum_const, nsmul_eq_mul]
        have hN0 : 0 ≤ N := by positivity
        have hNle : N ≤ 6 * M₁ * (3 * M * ((2 * K + 2) * M)) := by
          rw [hN, hP, Finset.card_product, Finset.card_product]
          push_cast
          have ha := card_A1_le h10
          have hb := card_dyadic_le h20
          have hc := card_Icc_le hK h30
          have hc' : 2 * K * M₃ + 1 ≤ (2 * K + 2) * M := by nlinarith
          have hb' : 3 * M₂ ≤ 3 * M := by linarith
          exact mul_le_mul ha (mul_le_mul (hb.trans hb') (hc.trans hc') (by positivity)
            (by positivity)) (by positivity) (by positivity)
        calc N * ∑ p ∈ P, ∫ u, f ((p.1 * u + p.2.2) / p.2.1) ^ 2
            ≤ N * (N * (2 * M₂ / M₁ * I)) := mul_le_mul_of_nonneg_left hs hN0
          _ = N * N * (2 * M₂ / M₁) * I := by ring
          _ ≤ (6 * M₁ * (3 * M * ((2 * K + 2) * M))) * (6 * M₁ * (3 * M * ((2 * K + 2) * M)))
                * (2 * M / M₁) * I := by
              gcongr
          _ = 2592 * M₁ * M ^ 5 * (1 + K) ^ 2 * I := by field_simp; ring
          _ ≤ 3000 * (1 + K) ^ 2 * M ^ 6 * I := by
              have : M₁ * M ^ 5 ≤ M ^ 6 := by
                have := pow_pos (by linarith : (0 : ℝ) < M) 5
                nlinarith
              have h0 : 0 ≤ (1 + K) ^ 2 * I := by positivity
              have h6 : 0 ≤ M ^ 6 := by positivity
              calc 2592 * M₁ * M ^ 5 * (1 + K) ^ 2 * I = 2592 * (M₁ * M ^ 5) * ((1 + K) ^ 2 * I) := by
                    ring
                _ ≤ 2592 * M ^ 6 * ((1 + K) ^ 2 * I) := by gcongr
                _ ≤ 3000 * M ^ 6 * ((1 + K) ^ 2 * I) := by gcongr; norm_num
                _ = 3000 * (1 + K) ^ 2 * M ^ 6 * I := by ring

end GuthMaynard.Affine.PartT
end

section
namespace GuthMaynard.Affine
open GuthMaynard MeasureTheory FourierTransform Complex
open scoped ENNReal
alias lintegral_gsum_sq_le_trivial := GuthMaynard.Affine.PartT.lintegral_gsum_sq_le_trivial

end GuthMaynard.Affine
end

section
namespace GuthMaynard.Affine.PartT
open GuthMaynard GuthMaynard.Affine MeasureTheory FourierTransform Complex
open scoped ENNReal

end GuthMaynard.Affine.PartT
end

section
namespace GuthMaynard.Affine
open GuthMaynard MeasureTheory FourierTransform Complex
open scoped ENNReal

end GuthMaynard.Affine
end

section
namespace GuthMaynard.Affine.PartT
open GuthMaynard GuthMaynard.Affine MeasureTheory FourierTransform Complex
open scoped ENNReal

end GuthMaynard.Affine.PartT
end

section
namespace GuthMaynard.Affine
open GuthMaynard MeasureTheory FourierTransform Complex
open scoped ENNReal

end GuthMaynard.Affine
end

section
namespace GuthMaynard.Affine
open GuthMaynard GuthMaynard.Affine MeasureTheory FourierTransform
open scoped ENNReal
/-! ## Fixed objects -/


























end GuthMaynard.Affine
end

section
namespace GuthMaynard.Affine.PartB
open GuthMaynard GuthMaynard.Affine GuthMaynard.Affine MeasureTheory FourierTransform
open scoped ENNReal

end GuthMaynard.Affine.PartB
end

section
namespace GuthMaynard.Affine
open GuthMaynard GuthMaynard.Affine MeasureTheory FourierTransform
open scoped ENNReal

end GuthMaynard.Affine
end

section
namespace GuthMaynard.Affine.PartB
open GuthMaynard GuthMaynard.Affine GuthMaynard.Affine MeasureTheory FourierTransform
open scoped ENNReal

end GuthMaynard.Affine.PartB
end

section
namespace GuthMaynard.Affine
open GuthMaynard GuthMaynard.Affine MeasureTheory FourierTransform
open scoped ENNReal

end GuthMaynard.Affine
end

section
namespace GuthMaynard.Affine.PartB
open GuthMaynard GuthMaynard.Affine GuthMaynard.Affine MeasureTheory FourierTransform
open scoped ENNReal

end GuthMaynard.Affine.PartB
end

section
namespace GuthMaynard.Affine
open GuthMaynard GuthMaynard.Affine MeasureTheory FourierTransform
open scoped ENNReal

end GuthMaynard.Affine
end

section
namespace GuthMaynard.Affine.PartB
open GuthMaynard GuthMaynard.Affine GuthMaynard.Affine MeasureTheory FourierTransform
open scoped ENNReal

end GuthMaynard.Affine.PartB
end

section
namespace GuthMaynard.Affine
open GuthMaynard GuthMaynard.Affine MeasureTheory FourierTransform
open scoped ENNReal

end GuthMaynard.Affine
end

section
namespace GuthMaynard.Affine.PartB
open GuthMaynard GuthMaynard.Affine GuthMaynard.Affine MeasureTheory FourierTransform
open scoped ENNReal

end GuthMaynard.Affine.PartB
end

section
namespace GuthMaynard.Affine
open GuthMaynard GuthMaynard.Affine MeasureTheory FourierTransform
open scoped ENNReal

end GuthMaynard.Affine
end

section
namespace GuthMaynard.Affine.PartB
open GuthMaynard GuthMaynard.Affine GuthMaynard.Affine MeasureTheory FourierTransform
open scoped ENNReal

end GuthMaynard.Affine.PartB
end

section
namespace GuthMaynard.Affine
open GuthMaynard GuthMaynard.Affine MeasureTheory FourierTransform
open scoped ENNReal

end GuthMaynard.Affine
end

section
namespace GuthMaynard.Affine.PartB
open GuthMaynard GuthMaynard.Affine GuthMaynard.Affine MeasureTheory FourierTransform
open scoped ENNReal

end GuthMaynard.Affine.PartB
end

section
namespace GuthMaynard.Affine
open GuthMaynard GuthMaynard.Affine MeasureTheory FourierTransform
open scoped ENNReal

end GuthMaynard.Affine
end

section
namespace GuthMaynard.Affine.PartB
open GuthMaynard GuthMaynard.Affine GuthMaynard.Affine MeasureTheory FourierTransform
open scoped ENNReal

end GuthMaynard.Affine.PartB
end

section
namespace GuthMaynard.Affine
open GuthMaynard GuthMaynard.Affine MeasureTheory FourierTransform
open scoped ENNReal

end GuthMaynard.Affine
end

section
namespace GuthMaynard.Affine.PartB
open GuthMaynard GuthMaynard.Affine GuthMaynard.Affine MeasureTheory FourierTransform
open scoped ENNReal

end GuthMaynard.Affine.PartB
end

section
namespace GuthMaynard.Affine
open GuthMaynard GuthMaynard.Affine MeasureTheory FourierTransform
open scoped ENNReal

end GuthMaynard.Affine
end

section
namespace GuthMaynard.Affine.PartS
open GuthMaynard GuthMaynard.Affine GuthMaynard.Affine MeasureTheory FourierTransform Complex
open scoped ENNReal Convolution SchwartzMap RealInnerProductSpace

/-! ### Large `M`: Lipschitz bound, mass lower bound, Riemann sums -/

end GuthMaynard.Affine.PartS
end

section
namespace GuthMaynard.Affine
open GuthMaynard GuthMaynard.Affine MeasureTheory FourierTransform
open scoped ENNReal

end GuthMaynard.Affine
end

section
namespace GuthMaynard.Affine.PartS
open GuthMaynard GuthMaynard.Affine GuthMaynard.Affine MeasureTheory FourierTransform Complex
open scoped ENNReal Convolution SchwartzMap RealInnerProductSpace

end GuthMaynard.Affine.PartS
end

section
namespace GuthMaynard.Affine
open GuthMaynard GuthMaynard.Affine MeasureTheory FourierTransform
open scoped ENNReal

end GuthMaynard.Affine
end

section
namespace GuthMaynard.Affine.PartS
open GuthMaynard GuthMaynard.Affine GuthMaynard.Affine MeasureTheory FourierTransform Complex
open scoped ENNReal Convolution SchwartzMap RealInnerProductSpace

end GuthMaynard.Affine.PartS
end

section
namespace GuthMaynard.Affine
open GuthMaynard GuthMaynard.Affine MeasureTheory FourierTransform
open scoped ENNReal

end GuthMaynard.Affine
end

section
namespace GuthMaynard.Affine.PartS
open GuthMaynard GuthMaynard.Affine GuthMaynard.Affine MeasureTheory FourierTransform Complex
open scoped ENNReal Convolution SchwartzMap RealInnerProductSpace

end GuthMaynard.Affine.PartS
end

section
namespace GuthMaynard.Affine
open GuthMaynard GuthMaynard.Affine MeasureTheory FourierTransform
open scoped ENNReal

end GuthMaynard.Affine
end

section
namespace GuthMaynard.Affine.PartS
open GuthMaynard GuthMaynard.Affine GuthMaynard.Affine MeasureTheory FourierTransform Complex
open scoped ENNReal Convolution SchwartzMap RealInnerProductSpace

end GuthMaynard.Affine.PartS
end

section
namespace GuthMaynard.Affine
open GuthMaynard GuthMaynard.Affine MeasureTheory FourierTransform
open scoped ENNReal

end GuthMaynard.Affine
end

section
namespace GuthMaynard.Affine.PartS
open GuthMaynard GuthMaynard.Affine GuthMaynard.Affine MeasureTheory FourierTransform Complex
open scoped ENNReal Convolution SchwartzMap RealInnerProductSpace

end GuthMaynard.Affine.PartS
end

section
namespace GuthMaynard.Affine
open GuthMaynard GuthMaynard.Affine MeasureTheory FourierTransform
open scoped ENNReal

end GuthMaynard.Affine
end

section
namespace GuthMaynard.Affine.PartS
open GuthMaynard GuthMaynard.Affine GuthMaynard.Affine MeasureTheory FourierTransform Complex
open scoped ENNReal Convolution SchwartzMap RealInnerProductSpace

end GuthMaynard.Affine.PartS
end

section
namespace GuthMaynard.Affine
open GuthMaynard GuthMaynard.Affine MeasureTheory FourierTransform
open scoped ENNReal

end GuthMaynard.Affine
end

section
namespace GuthMaynard.Affine.PartS
open GuthMaynard GuthMaynard.Affine GuthMaynard.Affine MeasureTheory FourierTransform Complex
open scoped ENNReal Convolution SchwartzMap RealInnerProductSpace

end GuthMaynard.Affine.PartS
end

section
namespace GuthMaynard.Affine
open GuthMaynard GuthMaynard.Affine MeasureTheory FourierTransform
open scoped ENNReal

end GuthMaynard.Affine
end

section
namespace GuthMaynard.Affine.PartG
open GuthMaynard GuthMaynard.Affine GuthMaynard.Affine MeasureTheory FourierTransform
open scoped ENNReal

end GuthMaynard.Affine.PartG
end

section
namespace GuthMaynard.Affine
open GuthMaynard GuthMaynard.Affine MeasureTheory FourierTransform
open scoped ENNReal

end GuthMaynard.Affine
end

section
namespace GuthMaynard.Affine.PartG
open GuthMaynard GuthMaynard.Affine GuthMaynard.Affine MeasureTheory FourierTransform
open scoped ENNReal

end GuthMaynard.Affine.PartG
end

section
namespace GuthMaynard.Affine
open GuthMaynard GuthMaynard.Affine MeasureTheory FourierTransform
open scoped ENNReal

end GuthMaynard.Affine
end

section
namespace GuthMaynard.Affine.PartG
open GuthMaynard GuthMaynard.Affine GuthMaynard.Affine MeasureTheory FourierTransform
open scoped ENNReal

end GuthMaynard.Affine.PartG
end

section
namespace GuthMaynard.Affine
open GuthMaynard GuthMaynard.Affine MeasureTheory FourierTransform
open scoped ENNReal

end GuthMaynard.Affine
end

section
namespace GuthMaynard.Affine.PartG
open GuthMaynard GuthMaynard.Affine GuthMaynard.Affine MeasureTheory FourierTransform
open scoped ENNReal

end GuthMaynard.Affine.PartG
end

section
namespace GuthMaynard.Affine
open GuthMaynard GuthMaynard.Affine MeasureTheory FourierTransform
open scoped ENNReal

end GuthMaynard.Affine
end

section
namespace GuthMaynard.Affine.PartG
open GuthMaynard GuthMaynard.Affine GuthMaynard.Affine MeasureTheory FourierTransform
open scoped ENNReal

end GuthMaynard.Affine.PartG
end

section
namespace GuthMaynard.Affine
open GuthMaynard GuthMaynard.Affine MeasureTheory FourierTransform
open scoped ENNReal

end GuthMaynard.Affine
end

section
namespace GuthMaynard.Affine.PartG
open GuthMaynard GuthMaynard.Affine GuthMaynard.Affine MeasureTheory FourierTransform
open scoped ENNReal

end GuthMaynard.Affine.PartG
end

section
namespace GuthMaynard.Affine
open GuthMaynard GuthMaynard.Affine MeasureTheory FourierTransform
open scoped ENNReal

end GuthMaynard.Affine
end

section
namespace GuthMaynard.Affine.PartG
open GuthMaynard GuthMaynard.Affine GuthMaynard.Affine MeasureTheory FourierTransform
open scoped ENNReal

end GuthMaynard.Affine.PartG
end

section
namespace GuthMaynard.Affine
open GuthMaynard GuthMaynard.Affine MeasureTheory FourierTransform
open scoped ENNReal

end GuthMaynard.Affine
end

section
namespace GuthMaynard.Affine.PartB
open GuthMaynard GuthMaynard.Affine GuthMaynard.Affine MeasureTheory FourierTransform
open scoped ENNReal

end GuthMaynard.Affine.PartB
end

section
namespace GuthMaynard.Affine
open GuthMaynard GuthMaynard.Affine MeasureTheory FourierTransform
open scoped ENNReal

end GuthMaynard.Affine
end

section
namespace GuthMaynard.Affine.PartR
open GuthMaynard GuthMaynard.Affine GuthMaynard.Affine MeasureTheory FourierTransform
open scoped ENNReal

end GuthMaynard.Affine.PartR
end

section
namespace GuthMaynard.Affine
open GuthMaynard GuthMaynard.Affine MeasureTheory FourierTransform
open scoped ENNReal

end GuthMaynard.Affine
end

section
namespace GuthMaynard.Affine.PartZ
open GuthMaynard GuthMaynard.Affine GuthMaynard.Affine MeasureTheory FourierTransform
open scoped ENNReal
theorem mem_dyadic {M : ℝ} {m : ℤ} (h : m ∈ dyadic M) : M < m ∧ (m : ℝ) ≤ 2 * M := by
  simp only [dyadic, Finset.mem_Ioc] at h
  exact ⟨Int.floor_lt.1 h.1, Int.le_floor.1 h.2⟩

end GuthMaynard.Affine.PartZ
end

section
namespace GuthMaynard.Affine
open GuthMaynard GuthMaynard.Affine MeasureTheory FourierTransform
open scoped ENNReal

end GuthMaynard.Affine
end

section
namespace GuthMaynard.Affine.PartR
open GuthMaynard GuthMaynard.Affine GuthMaynard.Affine MeasureTheory FourierTransform
open scoped ENNReal

end GuthMaynard.Affine.PartR
end

section
namespace GuthMaynard.Affine
open GuthMaynard GuthMaynard.Affine MeasureTheory FourierTransform
open scoped ENNReal

end GuthMaynard.Affine
end

section
namespace GuthMaynard.Affine.PartR
open GuthMaynard GuthMaynard.Affine GuthMaynard.Affine MeasureTheory FourierTransform
open scoped ENNReal

end GuthMaynard.Affine.PartR
end

section
namespace GuthMaynard.Affine
open GuthMaynard GuthMaynard.Affine MeasureTheory FourierTransform
open scoped ENNReal


end GuthMaynard.Affine
end

section
namespace GuthMaynard.Affine.PartZ
open GuthMaynard GuthMaynard.Affine GuthMaynard.Affine MeasureTheory FourierTransform
open scoped ENNReal
theorem hasCompactSupport_of_Icc {g : ℝ → ℝ} {a b : ℝ} (h : Function.support g ⊆ Set.Icc a b) :
    HasCompactSupport g :=
  isCompact_Icc.of_isClosed_subset (isClosed_tsupport g) (closure_minimal h isClosed_Icc)

theorem hcs_term {f : ℝ → ℝ} (hcs : HasCompactSupport f) {a b c : ℝ} (ha : a ≠ 0) (hc : c ≠ 0) :
    HasCompactSupport (fun u => f ((a * u + b) / c)) := by
  have e : (fun u => f ((a * u + b) / c)) =
      f ∘ (Homeomorph.addRight (b / c)) ∘ (Homeomorph.mulLeft₀ (a / c) (div_ne_zero ha hc)) := by
    funext u; simp only [Function.comp, Homeomorph.coe_addRight, Homeomorph.coe_mulLeft₀]
    congr 1; field_simp
  rw [e, ← Function.comp_assoc]
  exact (hcs.comp_homeomorph _).comp_homeomorph _

theorem dyadic_pos {M : ℝ} (hM : 0 ≤ M) {m : ℤ} (h : m ∈ dyadic M) : (0 : ℝ) < m := by
  have := (mem_dyadic h).1; linarith

theorem Hfun_continuous (C M₂ : ℝ) {g : ℝ → ℝ} (hg : Continuous g) :
    Continuous (Hfun C M₂ g) := by
  unfold Hfun
  refine continuous_finsetSum _ fun m₂ _ => continuous_finsetSum _ fun m₂' _ =>
    continuous_finsetSum _ fun j _ => ?_
  exact hg.comp (by fun_prop)

theorem Hfun_nonneg (C M₂ : ℝ) {g : ℝ → ℝ} (hg : ∀ u, 0 ≤ g u) (u : ℝ) : 0 ≤ Hfun C M₂ g u :=
  Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => hg _

theorem Hfun_hasCompactSupport (C M₂ : ℝ) (hM₂ : 0 ≤ M₂) {g : ℝ → ℝ} (hcs : HasCompactSupport g) :
    HasCompactSupport (Hfun C M₂ g) := by
  have e : Hfun C M₂ g = ∑ m₂ ∈ dyadic M₂, ∑ m₂' ∈ dyadic M₂,
      ∑ j ∈ Finset.Icc (-⌊8 * C * M₂⌋) ⌊8 * C * M₂⌋, fun u : ℝ => g ((m₂ * u + j) / m₂') := by
    funext u; simp only [Hfun, Finset.sum_apply]
  rw [e]
  exact HasCompactSupport.finset_sum fun m₂ hm₂ => HasCompactSupport.finset_sum fun m₂' hm₂' =>
    HasCompactSupport.finset_sum fun j _ =>
      hcs_term hcs (dyadic_pos hM₂ hm₂).ne' (dyadic_pos hM₂ hm₂').ne'

theorem Hfun_le_gsum (C M₂ : ℝ) {g : ℝ → ℝ} (hg : ∀ u, 0 ≤ g u) (u : ℝ) :
    Hfun C M₂ g u ≤ gsum (8 * C) M₂ M₂ M₂ g u := by
  unfold Hfun gsum
  exact Finset.sum_le_sum_of_subset_of_nonneg Finset.subset_union_left fun _ _ _ =>
    Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => hg _

theorem integral_mul_Hfun_le (C : ℝ) (hC : 1 ≤ C) (M M₂ : ℝ) (hM₂ : M₂ ∈ Set.Ioo 0 M)
    (f g : ℝ → ℝ) (hf : Continuous f) (hfs : Function.support f ⊆ Set.Icc (1 / C) C)
    (hg : Continuous g) (hgnn : ∀ u, 0 ≤ g u)
    (hgs : Function.support g ⊆ Set.Icc (1 / (2 * C)) (2 * C)) :
    ∫ u, f u * Hfun C M₂ g u ≤ √(∫ u, f u ^ 2) * √((J M (8 * C) g).toReal) := by
  have hM₂0 : 0 ≤ M₂ := hM₂.1.le
  have hfcs := hasCompactSupport_of_Icc hfs
  have hgcs := hasCompactSupport_of_Icc hgs
  set H := Hfun C M₂ g with hH
  have hHc : Continuous H := Hfun_continuous C M₂ hg
  have hHcs : HasCompactSupport H := Hfun_hasCompactSupport C M₂ hM₂0 hgcs
  have hHnn : ∀ u, 0 ≤ H u := Hfun_nonneg C M₂ hgnn
  -- `J` is finite
  have hC2 : 1 ≤ 2 * C := by linarith
  have hK : 0 < 8 * C := by linarith
  have hJfin : J M (8 * C) g ≠ ⊤ := by
    refine ne_top_of_le_ne_top ENNReal.ofReal_ne_top (b := ENNReal.ofReal
      (3000 * (1 + 8 * C) ^ 2 * M ^ 6 * ∫ u, g u ^ 2)) ?_
    rw [J_eq]
    exact iSup₂_le fun M₁ h₁ => iSup₂_le fun M₂ h₂ => iSup₂_le fun M₃ h₃ =>
      lintegral_gsum_sq_le_trivial (2 * C) (8 * C) hC2 hK g hg hgnn hgs M M₁ M₂ M₃ h₁ h₂ h₃
  have hHJ : ∫⁻ u, ENNReal.ofReal (H u ^ 2) ≤ J M (8 * C) g := by
    rw [J_eq]
    refine le_trans ?_ (le_iSup₂_of_le M₂ hM₂ (le_iSup₂_of_le M₂ hM₂ (le_iSup₂_of_le M₂ hM₂ le_rfl)))
    exact lintegral_mono fun u => ENNReal.ofReal_le_ofReal
      (pow_le_pow_left₀ (hHnn u) (Hfun_le_gsum C M₂ hgnn u) 2)
  have hH2 : ∫ u, H u ^ 2 ≤ (J M (8 * C) g).toReal := by
    rw [integral_eq_lintegral_of_nonneg_ae (ae_of_all _ fun u => sq_nonneg _)
      (hHc.pow 2).aestronglyMeasurable]
    exact ENNReal.toReal_mono hJfin hHJ
  have hfL : MemLp f (ENNReal.ofReal 2) volume := hf.memLp_of_hasCompactSupport hfcs
  have hHL : MemLp H (ENNReal.ofReal 2) volume := hHc.memLp_of_hasCompactSupport hHcs
  have hholder := integral_mul_norm_le_Lp_mul_Lq Real.HolderConjugate.two_two hfL hHL
  have hint1 : Integrable (fun u => f u * H u) :=
    (hf.mul hHc).integrable_of_hasCompactSupport hfcs.mul_right
  have hint2 : Integrable (fun u => ‖f u‖ * ‖H u‖) :=
    (hf.norm.mul hHc.norm).integrable_of_hasCompactSupport hfcs.norm.mul_right
  have hle : ∫ u, f u * H u ≤ ∫ u, ‖f u‖ * ‖H u‖ :=
    integral_mono hint1 hint2 fun u => by
      rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (hHnn u)]
      exact mul_le_mul_of_nonneg_right (le_abs_self _) (hHnn u)
  have e1 : (∫ u, ‖f u‖ ^ (2 : ℝ)) = ∫ u, f u ^ 2 := by
    congr 1; funext u; rw [Real.rpow_two, Real.norm_eq_abs, sq_abs]
  have e2 : (∫ u, ‖H u‖ ^ (2 : ℝ)) = ∫ u, H u ^ 2 := by
    congr 1; funext u; rw [Real.rpow_two, Real.norm_eq_abs, sq_abs]
  rw [e1, e2, ← Real.sqrt_eq_rpow, ← Real.sqrt_eq_rpow] at hholder
  calc ∫ u, f u * H u ≤ _ := hle.trans hholder
    _ ≤ √(∫ u, f u ^ 2) * √((J M (8 * C) g).toReal) :=
        mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt hH2) (Real.sqrt_nonneg _)

end GuthMaynard.Affine.PartZ
end

section
namespace GuthMaynard.Affine
open GuthMaynard GuthMaynard.Affine MeasureTheory FourierTransform
open scoped ENNReal

end GuthMaynard.Affine
end

section
namespace GuthMaynard.Affine.PartZ
open GuthMaynard GuthMaynard.Affine GuthMaynard.Affine MeasureTheory FourierTransform
open scoped ENNReal

end GuthMaynard.Affine.PartZ
end

section
namespace GuthMaynard.Affine
open GuthMaynard GuthMaynard.Affine MeasureTheory FourierTransform
open scoped ENNReal


alias integral_mul_Hfun_le_dev := GuthMaynard.Affine.PartZ.integral_mul_Hfun_le
end GuthMaynard.Affine
end


theorem solution : type_of% @GuthMaynard.Affine.integral_mul_Hfun_le_dev := @GuthMaynard.Affine.integral_mul_Hfun_le_dev
