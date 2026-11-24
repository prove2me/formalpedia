-- Prove2me | solution 1 for GlobalTheory.NormLe.absNorm_le_abs_norm
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T19:14:39.674023+00:00
-- url     : https://prove2.me/submissions/9a910233-4c67-4dd8-ba70-ec6792cb3b32

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_DivisorBase_OmegaFactorization
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_AbsNormLeAbsNormMulDivAbsNormOfEisensteinIndexPa

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField Complex
open scoped nonZeroDivisors
open GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization
open GlobalTheory GlobalTheory.NormLe
namespace GlobalTheory.NormLe
theorem _root_.solution {F : Type} [Field F] [NumberField F] (𝔟 : Frac F) {b : F}
    (hb : b ∈ (𝔟 : FractionalIdeal (𝓞 F)⁰ F)) (hb0 : b ≠ 0) :
    FractionalIdeal.absNorm (𝔟 : FractionalIdeal (𝓞 F)⁰ F) ≤ |Algebra.norm ℚ b| := by
  set B : FractionalIdeal (𝓞 F)⁰ F := (𝔟 : FractionalIdeal (𝓞 F)⁰ F)
  set S : FractionalIdeal (𝓞 F)⁰ F := FractionalIdeal.spanSingleton (𝓞 F)⁰ b
  set J : FractionalIdeal (𝓞 F)⁰ F := ((𝔟⁻¹ : Frac F) : FractionalIdeal (𝓞 F)⁰ F) * S
  have hSB : S ≤ B := (FractionalIdeal.spanSingleton_le_iff_mem).2 hb
  have hSJ : S = B * J := by
    simp only [J, B, ← mul_assoc, Units.mul_inv, one_mul]
  have hJ1 : J ≤ 1 := by
    have : J ≤ ((𝔟⁻¹ : Frac F) : FractionalIdeal (𝓞 F)⁰ F) * B := by
      simp only [J]; gcongr
    simpa [B, Units.inv_mul] using this
  obtain ⟨I₀, hI₀⟩ := FractionalIdeal.le_one_iff_exists_coeIdeal.1 hJ1
  have hS0 : S ≠ 0 := by
    rw [Ne, FractionalIdeal.spanSingleton_eq_zero_iff]; exact hb0
  have hJ0 : J ≠ 0 := by
    rintro h; rw [h, mul_zero] at hSJ; exact hS0 hSJ
  have hN : (1 : ℚ) ≤ FractionalIdeal.absNorm J := by
    rw [← hI₀, FractionalIdeal.coeIdeal_absNorm]
    have : Ideal.absNorm I₀ ≠ 0 := by
      intro h
      rw [Ideal.absNorm_eq_zero_iff] at h
      apply hJ0; rw [← hI₀, h]; simp
    exact_mod_cast Nat.one_le_iff_ne_zero.2 this
  have key : FractionalIdeal.absNorm S = FractionalIdeal.absNorm B * FractionalIdeal.absNorm J := by
    rw [hSJ, map_mul]
  rw [← FractionalIdeal.absNorm_span_singleton (𝓞 F) b]
  change FractionalIdeal.absNorm B ≤ FractionalIdeal.absNorm S
  rw [key]
  have := FractionalIdeal.absNorm_nonneg B
  nlinarith
end GlobalTheory.NormLe
