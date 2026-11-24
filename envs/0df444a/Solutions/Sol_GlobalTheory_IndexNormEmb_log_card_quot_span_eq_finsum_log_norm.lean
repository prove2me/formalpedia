-- Prove2me | solution 1 for GlobalTheory.IndexNormEmb.log_card_quot_span_eq_finsum_log_norm
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T17:58:41.253431+00:00
-- url     : https://prove2.me/submissions/bee7995c-ffe1-4428-9a4c-d167f29faaba

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_LogCardQuotSpanEqFinsumLogNormEmbeddings
import Theorems.Thm_GlobalTheory_IndexNormEmb_card_quot_span_eq

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped nonZeroDivisors
open GlobalTheory
open GlobalTheory.IndexNormEmb
namespace GlobalTheory.IndexNormEmb
theorem _root_.solution : ∀ (B : Type) [CommRing B] [IsDomain B] [CharZero B] [Module.Finite ℤ B] (b : B),
    b ≠ 0 → Finite (B ⧸ Ideal.span {b}) ∧
      Real.log (Nat.card (B ⧸ Ideal.span {b})) = ∑ᶠ τ : B →+* ℂ, Real.log ‖τ b‖ := by
  intro B _ _ _ _ b hb
  classical
  haveI : IsLocalization (Algebra.algebraMapSubmonoid B ℤ⁰) (FractionRing B) :=
    Algebra.IsAlgebraic.instIsLocalizationAlgebraMapSubmonoidNonZeroDivisors ℤ B (FractionRing B)
  haveI : IsScalarTower ℤ ℚ (FractionRing B) :=
    ⟨fun n q x => by rw [zsmul_eq_mul, zsmul_eq_mul, Algebra.smul_def, Algebra.smul_def, map_mul, map_intCast, mul_assoc]⟩
  haveI : @IsScalarTower ℤ ℚ (FractionRing B) Algebra.toSMul Algebra.toSMul Algebra.toSMul :=
    IsScalarTower.of_algebraMap_eq' (RingHom.ext_int _ _)
  haveI : FiniteDimensional ℚ (FractionRing B) := Module.Finite.of_isLocalization ℤ B ℤ⁰
  have hcard := card_quot_span_eq B b hb
  have hN0 : Algebra.norm ℤ b ≠ 0 := Algebra.norm_ne_zero_iff.mpr hb
  refine ⟨Nat.finite_of_card_ne_zero (by rw [hcard]; exact Int.natAbs_ne_zero.mpr hN0), ?_⟩
  have hN : algebraMap ℤ ℂ (Algebra.norm ℤ b) =
      ∏ σ : FractionRing B →ₐ[ℚ] ℂ, σ (algebraMap B (FractionRing B) b) := by
    rw [IsScalarTower.algebraMap_apply ℤ ℚ ℂ,
      ← Algebra.norm_localization ℤ (Sₘ := FractionRing B) ℤ⁰, Algebra.norm_eq_prod_embeddings]
  have hx : algebraMap B (FractionRing B) b ≠ 0 :=
    (map_ne_zero_iff _ (IsFractionRing.injective B (FractionRing B))).mpr hb
  rw [← finsum_comp_equiv (embEquiv B), finsum_eq_sum_of_fintype]
  change _ = ∑ σ : FractionRing B →ₐ[ℚ] ℂ, Real.log ‖σ (algebraMap B (FractionRing B) b)‖
  rw [← Real.log_prod (fun σ _ => norm_ne_zero_iff.mpr ((map_ne_zero_iff _ σ.toRingHom.injective).mpr hx)),
    ← norm_prod, ← hN, hcard, Nat.cast_natAbs, eq_intCast, Complex.norm_intCast, Int.cast_abs]
end GlobalTheory.IndexNormEmb
