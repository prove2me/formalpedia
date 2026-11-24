-- Prove2me | solution 1 for GlobalTheory.HeckeTwo.summable_latSum
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T19:50:10.513799+00:00
-- url     : https://prove2.me/submissions/4b8c810f-89d5-41e0-9af8-1f0c4e794ad2

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_DivisorBase_OmegaFactorization
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_KFacDifferentiable
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_SummableLipschitzLatticeNormPowSummand
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_SummableHeckeWeightTwoLatticeSum
import Theorems.Thm_GlobalTheory_HeckeTwo_norm_phi_le
import Theorems.Thm_GlobalTheory_IndefiniteRowSideFullHecke_OmegaFactorization_latM_eq_dual
import Theorems.Thm_GlobalTheory_LipschitzTR_remb_apply
import Theorems.Thm_GlobalTheory_LipschitzTR_summable_lhsTerm_ideal
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.LipschitzTR.remb_apply



set_option autoImplicit false
open NumberField Complex
open scoped nonZeroDivisors
open GlobalTheory GlobalTheory.HeckeTwo
open GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization
namespace GlobalTheory.HeckeTwo
theorem _root_.solution (F : Type) [Field F] [NumberField F] [NumberField.IsTotallyReal F] (𝔞 : Frac F) (σ : ℂ)
    (hσ : 0 < σ.re) (z : Emb F → ℂ) (hz : z ∈ upperHalf F) (b : F) (hb : b ≠ 0) :
    Summable (fun a : {a : F // a ∈ latM 𝔞} =>
      ∏ τ : Emb F, phi σ (((τ a.1 : ℝ) : ℂ) + ((τ b : ℝ) : ℂ) * z τ)) := by
  classical
  have hM : latM 𝔞 ≠ 0 := by
    rw [latM_eq_dual]
    exact FractionalIdeal.dual_ne_zero ℤ ℚ (Units.ne_zero 𝔞)
  set z' : Emb F → ℂ := fun τ => ((τ b : ℝ) : ℂ) * z τ with hz'
  have hc : ∀ τ : Emb F, 0 < |τ b * (z τ).im| := fun τ =>
    abs_pos.2 (mul_ne_zero ((map_ne_zero τ).2 hb) (hz τ).ne')
  have him : ∀ τ : Emb F, (z' τ).im ≠ 0 := fun τ => by
    have := hc τ
    simp only [hz', Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, zero_mul, add_zero]
    exact abs_pos.1 this
  have hs := GlobalTheory.LipschitzTR.summable_lhsTerm_ideal F (latM 𝔞) hM 2 le_rfl z' him
  have hs' : Summable (fun a : {a : F // a ∈ latM 𝔞} => GlobalTheory.IndefiniteRowSideFullHecke.TraceDualDifferent.lhsTerm 2 z' a.1) := hs
  set C : ℝ := ∏ τ : Emb F, |τ b * (z τ).im| ^ (-2 * σ.re) with hC
  refine Summable.of_norm_bounded ((summable_norm_iff.2 hs').mul_left C) fun a => ?_
  have hl : GlobalTheory.IndefiniteRowSideFullHecke.TraceDualDifferent.lhsTerm 2 z' a.1 =
      ∏ τ : Emb F, (((τ a.1 : ℝ) : ℂ) + ((τ b : ℝ) : ℂ) * z τ)⁻¹ ^ 2 := by
    unfold GlobalTheory.IndefiniteRowSideFullHecke.TraceDualDifferent.lhsTerm
    rw [zpow_neg, zpow_natCast, ← Finset.prod_pow, ← Finset.prod_inv_distrib]
    refine Finset.prod_congr rfl fun τ _ => ?_
    rw [hz', inv_pow, add_comm]
  rw [hl, norm_prod, norm_prod, hC, ← Finset.prod_mul_distrib]
  refine Finset.prod_le_prod (fun _ _ => norm_nonneg _) fun τ _ => ?_
  rw [mul_comm (|τ b * (z τ).im| ^ (-2 * σ.re))]
  refine norm_phi_le σ _ hσ _ (hc τ) (le_of_eq ?_)
  simp
end GlobalTheory.HeckeTwo
