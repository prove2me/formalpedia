-- Prove2me | solution 1 for GlobalTheory.LipschitzTR.summable_lhsTerm_ideal
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T19:35:09.362864+00:00
-- url     : https://prove2.me/submissions/2790182d-5c5a-4906-a2eb-52e3bdfeeba5

import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_RembApply
import Definitions.Def_Formalism_LatticeTheta_Statement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_SummableLipschitzLatticeNormPowSummand
import Theorems.Thm_GlobalTheory_LipschitzTR_LhsSum_exists_lower_norm
import Theorems.Thm_GlobalTheory_LipschitzTR_LhsSum_exists_lower_one_add
import Theorems.Thm_GlobalTheory_LipschitzTR_LhsSum_floor_bound
import Theorems.Thm_GlobalTheory_LipschitzTR_LhsSum_summable_prod_wt
import Theorems.Thm_GlobalTheory_IndefiniteRowSideFullHecke_TraceDualDifferent_card_realEmb
import Theorems.Thm_GlobalTheory_LipschitzTR_remb_apply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.LipschitzTR.remb_apply



set_option autoImplicit false
open NumberField nonZeroDivisors MeasureTheory GlobalTheory.LipschitzTR GlobalTheory.IndefiniteRowSideFullHecke.TraceDualDifferent
open scoped FourierTransform RealInnerProductSpace
noncomputable section
open GlobalTheory.LipschitzTR.LhsSum
namespace GlobalTheory.LipschitzTR
theorem _root_.solution :
    ∀ (F : Type) [Field F] [NumberField F] [IsTotallyReal F] (M : FractionalIdeal (𝓞 F)⁰ F), M ≠ 0 →
      ∀ (k : ℕ), 2 ≤ k → ∀ (z : (F →+* ℝ) → ℂ), (∀ τ, (z τ).im ≠ 0) →
        Summable (fun a : (M : Set F) => lhsTerm k z a) := by
  intro F _ _ _ M _ k hk z hz
  classical
  obtain ⟨ν, hν0, hν⟩ := exists_lower_norm M
  have hcard : 0 < Fintype.card (F →+* ℝ) := by
    rw [card_realEmb]; exact Module.finrank_pos
  set s : ℝ := min 1 (ν / 2) with hs
  have hs0 : 0 < s := lt_min one_pos (by positivity)
  have hs1 : s ≤ 1 := min_le_left _ _
  have hsν : s ^ Fintype.card (F →+* ℝ) < ν :=
    lt_of_le_of_lt (pow_le_of_le_one hs0.le hs1 hcard.ne') (lt_of_le_of_lt (min_le_right _ _) (by linarith))
  let N : ↥(M : Set F) → ((F →+* ℝ) → ℤ) := fun a τ => ⌊τ (a : F) / s⌋
  have hN : Function.Injective N := by
    intro a b hab
    by_contra hne
    have hne' : (a : F) - b ≠ 0 := sub_ne_zero.2 (fun h => hne (Subtype.ext h))
    have hmem : (a : F) - b ∈ M := (M : Submodule (𝓞 F) F).sub_mem a.2 b.2
    have h1 := hν _ hmem hne'
    have h2 : |∏ τ : F →+* ℝ, τ ((a : F) - b)| ≤ s ^ Fintype.card (F →+* ℝ) := by
      rw [Finset.abs_prod, ← Finset.card_univ, ← Finset.prod_const]
      refine Finset.prod_le_prod (fun _ _ => abs_nonneg _) (fun τ _ => ?_)
      have hf := Int.abs_sub_lt_one_of_floor_eq_floor (congrFun hab τ)
      rw [← sub_div, abs_div, abs_of_pos hs0, div_lt_one hs0] at hf
      rw [map_sub]; exact hf.le
    linarith
  have hc : ∀ τ : F →+* ℝ, ∃ c : ℝ, 0 < c ∧ ∀ t : ℝ, c * (1 + |t|) ≤ ‖z τ + (t : ℂ)‖ :=
    fun τ => exists_lower_one_add (z τ) (hz τ)
  choose c hc0 hc using hc
  set C : ℝ := ∏ τ : F →+* ℝ, ((c τ * (s / 2)) ^ k)⁻¹ with hC
  refine Summable.of_norm_bounded (g := fun a => C * ∏ τ, wt (N a τ))
    (((summable_prod_wt (F →+* ℝ)).comp_injective hN).mul_left C) (fun a => ?_)
  simp only [lhsTerm, zpow_neg, zpow_natCast, ← Finset.prod_pow, ← Finset.prod_inv_distrib, norm_prod, norm_inv, norm_pow]
  rw [hC, ← Finset.prod_mul_distrib]
  refine Finset.prod_le_prod (fun _ _ => by positivity) (fun τ _ => ?_)
  have hD : 0 < c τ * (s / 2) := by have := hc0 τ; positivity
  have hfl := floor_bound hs0 hs1 (τ (a : F))
  have he : c τ * (s / 2) * (1 + |((N a τ : ℤ) : ℝ)|) ≤ ‖z τ + ((τ (a : F) : ℝ) : ℂ)‖ := by
    calc c τ * (s / 2) * (1 + |((N a τ : ℤ) : ℝ)|) = c τ * (s / 2 * (1 + |((N a τ : ℤ) : ℝ)|)) := by ring
      _ ≤ c τ * (1 + |τ (a : F)|) := mul_le_mul_of_nonneg_left hfl (hc0 τ).le
      _ ≤ _ := hc τ _
  have hone : (1 : ℝ) ≤ 1 + |((N a τ : ℤ) : ℝ)| := by linarith [abs_nonneg ((N a τ : ℤ) : ℝ)]
  rw [wt, ← mul_inv]
  apply inv_anti₀ (by positivity)
  calc (c τ * (s / 2)) ^ k * (1 + |((N a τ : ℤ) : ℝ)|) ^ 2
      ≤ (c τ * (s / 2)) ^ k * (1 + |((N a τ : ℤ) : ℝ)|) ^ k :=
        mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hone hk) (by positivity)
    _ = (c τ * (s / 2) * (1 + |((N a τ : ℤ) : ℝ)|)) ^ k := by rw [mul_pow (c τ * (s / 2))]
    _ ≤ _ := pow_le_pow_left₀ (by positivity) he k
end GlobalTheory.LipschitzTR
