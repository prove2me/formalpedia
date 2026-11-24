-- Prove2me | solution 1 for GlobalTheory.HeckeTwo.SumGood.norm_iteratedFDeriv_wirtWord
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T17:57:39.38712+00:00
-- url     : https://prove2.me/submissions/abd9eace-5ce1-4a71-bbb5-8cd8b377bb5d

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_DivisorBase_OmegaFactorization
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_Divisors__PartialZetaFunctionalEquation_ee0156e8c041b1a2
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_KFacDifferentiable
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_IsSmoothHolomorphicInSigmaFamilyAdd
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_HeckeWeightTwoIsGoodOfTsum
import Theorems.Thm_GlobalTheory_HeckeTwo_SumGood_wirt_eq_clm
import Theorems.Thm_GlobalTheory_HeckeTwo_GoodAdd_wirtWord_contDiffOn
import Theorems.Thm_GlobalTheory_IndefiniteRowSideFullHecke_OmegaFactorization_wirtWord_cons
import Theorems.Thm_GlobalTheory_IndefiniteRowSideFullHecke_OmegaFactorization_wirtWord_nil


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField Complex
open scoped nonZeroDivisors ContDiff
open GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization GlobalTheory.HeckeTwo
noncomputable section
open GlobalTheory GlobalTheory.HeckeTwo GlobalTheory.HeckeTwo.SumGood
variable {Φ : Type} [Fintype Φ] {ι : Type}
namespace GlobalTheory.HeckeTwo.SumGood
theorem _root_.solution {U : Set (Φ → ℂ)} (hU : IsOpen U) (w : List (Φ × Bool)) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ h : (Φ → ℂ) → ℂ, ContDiffOn ℝ ∞ h U → ∀ k : ℕ, ∀ z ∈ U,
      ‖iteratedFDeriv ℝ k (wirtWord w h) z‖ ≤ C * ‖iteratedFDeriv ℝ (k + w.length) h z‖ := by
  induction w with
  | nil => exact ⟨1, zero_le_one, fun h _ k z _ => by simp [wirtWord_nil]⟩
  | cons a w ih =>
    obtain ⟨C, hC0, hC⟩ := ih
    obtain ⟨Λ, hΛ⟩ := wirt_eq_clm a.1 a.2
    refine ⟨‖Λ‖ * C, mul_nonneg (norm_nonneg _) hC0, fun h hh k z hz => ?_⟩
    have e : wirtWord (a :: w) h = Λ ∘ fderiv ℝ (wirtWord w h) := by
      rw [wirtWord_cons]; funext y; exact hΛ _ y
    have hs : ContDiffOn ℝ ∞ (wirtWord w h) U := GoodAdd.wirtWord_contDiffOn hU w hh
    have hd : ContDiffAt ℝ ∞ (fderiv ℝ (wirtWord w h)) z :=
      (hs.fderiv_of_isOpen hU (by simp)).contDiffAt (hU.mem_nhds hz)
    rw [e]
    calc ‖iteratedFDeriv ℝ k (Λ ∘ fderiv ℝ (wirtWord w h)) z‖
        ≤ ‖Λ‖ * ‖iteratedFDeriv ℝ k (fderiv ℝ (wirtWord w h)) z‖ :=
          Λ.norm_iteratedFDeriv_comp_left hd (by exact_mod_cast le_top)
      _ = ‖Λ‖ * ‖iteratedFDeriv ℝ (k + 1) (wirtWord w h) z‖ := by rw [norm_iteratedFDeriv_fderiv]
      _ ≤ ‖Λ‖ * (C * ‖iteratedFDeriv ℝ (k + 1 + w.length) h z‖) :=
          mul_le_mul_of_nonneg_left (hC h hh (k + 1) z hz) (norm_nonneg _)
      _ = ‖Λ‖ * C * ‖iteratedFDeriv ℝ (k + (a :: w).length) h z‖ := by
          rw [List.length_cons, show k + 1 + w.length = k + (w.length + 1) by ring]; ring
end GlobalTheory.HeckeTwo.SumGood
