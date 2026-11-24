-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.SW.Core.RowCompletion.exists_scale
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T13:15:15.467801+00:00
-- url     : https://prove2.me/submissions/90d82750-c837-4f51-aa47-bcb2e7519896

import Mathlib
import Definitions.Def_CompanionTheory_SpectralGeometry_CountingDefinitions_AdelicEulerProducts_CountData
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_CuspRepresentativesFinite

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain MeasureTheory Matrix Topology GlobalTheory.CompanionTheory.SW.Core
open scoped ENNReal NNReal MatrixGroups
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.SW GlobalTheory.CompanionTheory.SW.Core GlobalTheory.CompanionTheory.SW.Core.RowCompletion
open nonZeroDivisors
variable {F : Type} [Field F] [NumberField F]
namespace GlobalTheory.CompanionTheory.SW.Core.RowCompletion
theorem _root_.solution (J I : (Ideal (𝓞 F))⁰) (h : ClassGroup.mk0 I = ClassGroup.mk0 J)
    {c d : 𝓞 F} (hI : (I : Ideal (𝓞 F)) = Ideal.span {c, d}) :
    ∃ l : F, l ≠ 0 ∧ |((Algebra.norm ℚ l : ℚ) : ℝ)| ≤ (Ideal.absNorm (J : Ideal (𝓞 F)) : ℝ) ∧
      ((J : Ideal (𝓞 F)) : FractionalIdeal (𝓞 F)⁰ F) =
        FractionalIdeal.spanSingleton _ (l * (c : F)) +
          FractionalIdeal.spanSingleton _ (l * (d : F)) := by
  obtain ⟨x, y, hx, hy, hxy⟩ := ClassGroup.mk0_eq_mk0_iff.1 h
  have hxF : (x : F) ≠ 0 := by simpa using hx
  have hyF : (y : F) ≠ 0 := by simpa using hy
  refine ⟨(x : F) / (y : F), div_ne_zero hxF hyF, ?_, ?_⟩
  · have hn := congrArg Ideal.absNorm hxy
    rw [map_mul, map_mul, Ideal.absNorm_span_singleton, Ideal.absNorm_span_singleton] at hn
    have key : ∀ w : 𝓞 F, (((Algebra.norm ℤ w).natAbs : ℕ) : ℝ) =
        |((Algebra.norm ℚ (w : F) : ℚ) : ℝ)| := by
      intro w
      rw [← Algebra.coe_norm_int]
      simp [Nat.cast_natAbs]
    have hmul : Algebra.norm ℚ (x : F) = Algebra.norm ℚ (y : F) * Algebra.norm ℚ ((x : F) / (y : F)) := by
      rw [← map_mul, mul_div_cancel₀ _ hyF]
    have hnR : (((Algebra.norm ℤ x).natAbs : ℕ) : ℝ) * (Ideal.absNorm (I : Ideal (𝓞 F)) : ℝ) =
        (((Algebra.norm ℤ y).natAbs : ℕ) : ℝ) * (Ideal.absNorm (J : Ideal (𝓞 F)) : ℝ) := by
      exact_mod_cast hn
    rw [key, key, hmul] at hnR
    have hb : |((Algebra.norm ℚ (y : F) : ℚ) : ℝ)| ≠ 0 := by
      have : Algebra.norm ℚ (y : F) ≠ 0 := Algebra.norm_ne_zero_iff.2 hyF
      simpa using this
    have hI1 : (1 : ℝ) ≤ (Ideal.absNorm (I : Ideal (𝓞 F)) : ℝ) := by
      have : Ideal.absNorm (I : Ideal (𝓞 F)) ≠ 0 := by
        rw [Ne, Ideal.absNorm_eq_zero_iff]
        exact nonZeroDivisors.ne_zero I.2
      exact_mod_cast Nat.one_le_iff_ne_zero.2 this
    set t := |((Algebra.norm ℚ ((x : F) / (y : F)) : ℚ) : ℝ)| with ht
    have h3 : t * (Ideal.absNorm (I : Ideal (𝓞 F)) : ℝ) = (Ideal.absNorm (J : Ideal (𝓞 F)) : ℝ) := by
      apply mul_left_cancel₀ hb
      rw [← hnR]
      push_cast
      rw [abs_mul]
      ring
    have ht0 : 0 ≤ t := abs_nonneg _
    calc t = t * 1 := (mul_one t).symm
      _ ≤ t * (Ideal.absNorm (I : Ideal (𝓞 F)) : ℝ) := mul_le_mul_of_nonneg_left hI1 ht0
      _ = _ := h3
  · have hF := congrArg (fun K : Ideal (𝓞 F) => (K : FractionalIdeal (𝓞 F)⁰ F)) hxy
    simp only [FractionalIdeal.coeIdeal_mul, FractionalIdeal.coeIdeal_span_singleton] at hF
    rw [hI, Ideal.span_insert, FractionalIdeal.coeIdeal_sup,
      FractionalIdeal.coeIdeal_span_singleton, FractionalIdeal.coeIdeal_span_singleton] at hF
    simp only [← RingOfIntegers.coe_eq_algebraMap] at hF
    calc ((J : Ideal (𝓞 F)) : FractionalIdeal (𝓞 F)⁰ F)
        = FractionalIdeal.spanSingleton _ (y : F)⁻¹ * (FractionalIdeal.spanSingleton _ (y : F) *
            ((J : Ideal (𝓞 F)) : FractionalIdeal (𝓞 F)⁰ F)) := by
          rw [← mul_assoc, FractionalIdeal.spanSingleton_mul_spanSingleton, inv_mul_cancel₀ hyF,
            FractionalIdeal.spanSingleton_one, one_mul]
      _ = FractionalIdeal.spanSingleton _ (y : F)⁻¹ * (FractionalIdeal.spanSingleton _ (x : F) *
            (FractionalIdeal.spanSingleton _ (c : F) + FractionalIdeal.spanSingleton _ (d : F))) := by
          rw [hF]
      _ = _ := by
          simp only [mul_add, FractionalIdeal.spanSingleton_mul_spanSingleton]
          congr 2 <;> field_simp
end GlobalTheory.CompanionTheory.SW.Core.RowCompletion
