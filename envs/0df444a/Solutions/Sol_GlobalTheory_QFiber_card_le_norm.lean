-- Prove2me | solution 1 for GlobalTheory.QFiber.card_le_norm
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T22:44:48.921961+00:00
-- url     : https://prove2.me/submissions/902539a3-2324-4f24-8bf0-e74eca1f6134

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_DivisorBase_OmegaFactorization
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_CardDivisorsLeAbsNormNumberFieldStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_CardHilbertEisensteinFourierFiberLeNorm
import Theorems.Thm_GlobalTheory_QFiber_coe_toIdeal
import Theorems.Thm_GlobalTheory_QFiber_nrm_nonneg
import Theorems.Thm_GlobalTheory_QFiber_emb_nonempty
import Theorems.Thm_GlobalTheory_T_card_divisors_le_absNorm_numberField


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
noncomputable section
open GlobalTheory GlobalTheory.QFiber
open FractionalIdeal
variable {F : Type} [Field F] [NumberField F]
namespace GlobalTheory.QFiber
theorem _root_.solution : ∀ (F : Type) [Field F] [NumberField F] [IsTotallyReal F] (𝔞 𝔟 : Frac F) (ξ : F)
    (s : Finset (Quotient (qRel 𝔞 𝔟))), (∀ c ∈ s, c.out.1.1 * c.out.1.2 = ξ) →
    (s.card : ℝ) ≤ |(Algebra.norm ℚ ξ : ℝ)| / (nrm 𝔞 * nrm 𝔟) := by
  intro F _ _ _ 𝔞 𝔟 ξ s hs
  classical
  rcases s.eq_empty_or_nonempty with rfl | ⟨c0, hc0⟩
  · simp only [Finset.card_empty, Nat.cast_zero]
    exact div_nonneg (abs_nonneg _) (mul_nonneg (nrm_nonneg 𝔞) (nrm_nonneg 𝔟))
  have hA : ((𝔞 : FractionalIdeal (𝓞 F)⁰ F)) ≠ 0 := 𝔞.ne_zero
  have hB : ((𝔟 : FractionalIdeal (𝓞 F)⁰ F)) ≠ 0 := 𝔟.ne_zero
  have hξ : ξ ≠ 0 := by
    obtain ⟨τ⟩ := emb_nonempty (F := F)
    have h := c0.out.2.2.2 τ
    rw [hs c0 hc0] at h
    intro h0
    rw [h0, map_zero] at h
    exact lt_irrefl _ h
  have hle : ∀ c : Quotient (qRel 𝔞 𝔟),
      spanSingleton (𝓞 F)⁰ c.out.1.1 * (𝔞 : FractionalIdeal (𝓞 F)⁰ F)⁻¹ ≤ 1 := fun c => by
    calc _ ≤ (𝔞 : FractionalIdeal (𝓞 F)⁰ F) * (𝔞 : FractionalIdeal (𝓞 F)⁰ F)⁻¹ :=
          by gcongr; exact spanSingleton_le_iff_mem.mpr c.out.2.1
      _ = 1 := mul_inv_cancel₀ hA
  have hIle : ∀ c ∈ s, spanSingleton (𝓞 F)⁰ ξ * (𝔞 : FractionalIdeal (𝓞 F)⁰ F)⁻¹ * (𝔟 : FractionalIdeal (𝓞 F)⁰ F)⁻¹ ≤
      spanSingleton (𝓞 F)⁰ c.out.1.1 * (𝔞 : FractionalIdeal (𝓞 F)⁰ F)⁻¹ := by
    intro c hc
    have hb : spanSingleton (𝓞 F)⁰ c.out.1.2 * (𝔟 : FractionalIdeal (𝓞 F)⁰ F)⁻¹ ≤ 1 := by
      calc _ ≤ (𝔟 : FractionalIdeal (𝓞 F)⁰ F) * (𝔟 : FractionalIdeal (𝓞 F)⁰ F)⁻¹ :=
            by gcongr; exact spanSingleton_le_iff_mem.mpr c.out.2.2.1
        _ = 1 := mul_inv_cancel₀ hB
    rw [← hs c hc, ← spanSingleton_mul_spanSingleton]
    calc spanSingleton (𝓞 F)⁰ c.out.1.1 * spanSingleton (𝓞 F)⁰ c.out.1.2 * (𝔞 : FractionalIdeal (𝓞 F)⁰ F)⁻¹ *
          (𝔟 : FractionalIdeal (𝓞 F)⁰ F)⁻¹ =
          (spanSingleton (𝓞 F)⁰ c.out.1.1 * (𝔞 : FractionalIdeal (𝓞 F)⁰ F)⁻¹) *
          (spanSingleton (𝓞 F)⁰ c.out.1.2 * (𝔟 : FractionalIdeal (𝓞 F)⁰ F)⁻¹) := by ring
      _ ≤ (spanSingleton (𝓞 F)⁰ c.out.1.1 * (𝔞 : FractionalIdeal (𝓞 F)⁰ F)⁻¹) * 1 := by gcongr
      _ = _ := mul_one _
  have hI1 := (hIle c0 hc0).trans (hle c0)
  set I := toIdeal (spanSingleton (𝓞 F)⁰ ξ * (𝔞 : FractionalIdeal (𝓞 F)⁰ F)⁻¹ * (𝔟 : FractionalIdeal (𝓞 F)⁰ F)⁻¹) with hIdef
  let f : Quotient (qRel 𝔞 𝔟) → Ideal (𝓞 F) := fun c =>
    toIdeal (spanSingleton (𝓞 F)⁰ c.out.1.1 * (𝔞 : FractionalIdeal (𝓞 F)⁰ F)⁻¹)
  have hIJ : ∀ c ∈ s, I ≤ f c := by
    intro c hc
    rw [← coeIdeal_le_coeIdeal F, coe_toIdeal hI1, coe_toIdeal (hle c)]
    exact hIle c hc
  have hI0 : I ≠ ⊥ := by
    intro h
    have h' := coe_toIdeal hI1
    rw [← hIdef, h, coeIdeal_bot] at h'
    have := h'.symm
    simp only [mul_eq_zero, spanSingleton_eq_zero_iff, inv_eq_zero] at this
    tauto
  have hinj : Set.InjOn f s := by
    intro c hc c' hc' hcc
    have h1 : spanSingleton (𝓞 F)⁰ c.out.1.1 * (𝔞 : FractionalIdeal (𝓞 F)⁰ F)⁻¹ =
        spanSingleton (𝓞 F)⁰ c'.out.1.1 * (𝔞 : FractionalIdeal (𝓞 F)⁰ F)⁻¹ := by
      rw [← coe_toIdeal (hle c), ← coe_toIdeal (hle c')]
      exact congrArg _ hcc
    have h2 := mul_right_cancel₀ (inv_ne_zero hA) h1
    obtain ⟨u, hu⟩ := spanSingleton_eq_spanSingleton.mp h2
    rw [Units.smul_def, Algebra.smul_def] at hu
    have hν : c.out.1.1 ≠ 0 := left_ne_zero_of_mul (by rw [hs c hc]; exact hξ)
    have hu0 : algebraMap (𝓞 F) F (u : 𝓞 F) ≠ 0 := by
      rw [ne_eq, map_eq_zero_iff _ (IsFractionRing.injective (𝓞 F) F)]; exact u.ne_zero
    have h4 : algebraMap (𝓞 F) F (u : 𝓞 F) * (((u⁻¹ : (𝓞 F)ˣ) : 𝓞 F) : F) = 1 := by
      rw [mul_comm]; exact unit_inv_mul u
    have e1 := hs c hc
    have e2 := hs c' hc'
    rw [← hu] at e2
    have hb : c'.out.1.2 = (((u⁻¹ : (𝓞 F)ˣ) : 𝓞 F) : F) * c.out.1.2 := by
      apply mul_left_cancel₀ (mul_ne_zero hu0 hν)
      linear_combination e2 - e1 - c.out.1.1 * c.out.1.2 * h4
    rw [← Quotient.out_eq c, ← Quotient.out_eq c']
    apply Quotient.sound
    refine ⟨u⁻¹, ?_, hb⟩
    rw [inv_inv, ← hu]
  have key : (FractionalIdeal.absNorm ((I : Ideal (𝓞 F)) : FractionalIdeal (𝓞 F)⁰ F) : ℚ) =
      |Algebra.norm ℚ ξ| / (FractionalIdeal.absNorm (𝔞 : FractionalIdeal (𝓞 F)⁰ F) *
        FractionalIdeal.absNorm (𝔟 : FractionalIdeal (𝓞 F)⁰ F)) := by
    rw [coe_toIdeal hI1, map_mul, map_mul, map_inv₀, map_inv₀, absNorm_span_singleton]
    ring
  rw [coeIdeal_absNorm] at key
  calc (s.card : ℝ) = ((s.image f).card : ℝ) := by rw [Finset.card_image_of_injOn hinj]
    _ ≤ (Ideal.absNorm I : ℝ) := by
      exact_mod_cast GlobalTheory.T.card_divisors_le_absNorm_numberField F I hI0 (s.image f) (by
        intro J hJ
        obtain ⟨c, hc, rfl⟩ := Finset.mem_image.mp hJ
        exact hIJ c hc)
    _ = _ := by
      unfold nrm
      have := congrArg (Rat.cast : ℚ → ℝ) key
      push_cast at this
      exact this
end GlobalTheory.QFiber
