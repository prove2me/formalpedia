-- Prove2me | solution 1 for GlobalTheory.KTypeCompare.weight_integral
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T03:18:13.729583+00:00
-- url     : https://prove2.me/submissions/fca0ce63-9367-4d24-bf15-84c386e26ef2

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UpqRep
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_JetGauges_HarishChandraParameters
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_JetHarmonics_IsWtOnIffOfTorus

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Finset
noncomputable section
open GlobalTheory GlobalTheory.KTypeCompare
open GlobalTheory.IndefiniteRowSideFullHecke
variable {n : ℕ}
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
namespace GlobalTheory.KTypeCompare
theorem _root_.solution {σ : Matrix (Fin n) (Fin n) ℂ → H →L[ℂ] H} {ω : Fin n → ℝ} {v : H}
    (h : HarishChandraRootData.IsWeightVector σ ω v) (a : Fin n) : ∃ m : ℤ, ω a = m := by
  obtain ⟨hv0, hv⟩ := h
  have hw : ∀ θ, σ (HarishChandraRootData.torus θ) v = HarishChandraRootData.wtChar ω θ • v := hv
  obtain ⟨θ₁, hθ₁⟩ : ∃ θ₁ : Fin n → ℝ, θ₁ = Pi.single a (2 * Real.pi) := ⟨_, rfl⟩
  have htor : HarishChandraRootData.torus θ₁ = HarishChandraRootData.torus 0 := by
    unfold HarishChandraRootData.torus
    congr 1
    funext b
    by_cases hb : b = a
    · rw [hb, hθ₁, Pi.single_eq_same, Pi.zero_apply, Complex.ofReal_zero, mul_zero,
        Complex.exp_zero, ← Complex.exp_two_pi_mul_I]
      congr 1
      push_cast
      ring
    · simp [hθ₁, Pi.single_eq_of_ne hb]
  have h1 := hw θ₁
  rw [htor, hw 0] at h1
  have h0 : HarishChandraRootData.wtChar ω 0 = 1 := by simp [HarishChandraRootData.wtChar]
  rw [h0, one_smul] at h1
  have hc : HarishChandraRootData.wtChar ω θ₁ = 1 := by
    have hz : (HarishChandraRootData.wtChar ω θ₁ - 1) • v = 0 := by
      rw [sub_smul, ← h1, one_smul, sub_self]
    rcases smul_eq_zero.mp hz with hz | hz
    · exact sub_eq_zero.mp hz
    · exact absurd hz hv0
  unfold HarishChandraRootData.wtChar at hc
  obtain ⟨m, hm⟩ := Complex.exp_eq_one_iff.mp hc
  refine ⟨m, ?_⟩
  have hsum : (∑ b, ω b * θ₁ b) = ω a * (2 * Real.pi) := by
    simp [hθ₁, Pi.single_apply]
  rw [hsum] at hm
  have hpi : (2 * Real.pi * Complex.I : ℂ) ≠ 0 := by simp [Real.pi_ne_zero]
  have hc' : ((ω a : ℝ) : ℂ) = ((m : ℝ) : ℂ) := by
    apply mul_right_cancel₀ hpi
    push_cast at hm ⊢
    linear_combination hm
  exact_mod_cast hc'
end GlobalTheory.KTypeCompare
