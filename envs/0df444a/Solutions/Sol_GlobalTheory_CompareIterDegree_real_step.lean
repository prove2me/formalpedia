-- Prove2me | solution 1 for GlobalTheory.CompareIterDegree.real_step
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T04:23:45.201148+00:00
-- url     : https://prove2.me/submissions/0c0989fe-0d66-4926-b85e-fcb56a408276

import Mathlib
import Definitions.Def_Formalism_FlagUnipotentLattices_UnipotentStabiliserCharacterisation
import Definitions.Def_Formalism_FormalDegreeBessel_FormalDegreeRatio_DSFdeg
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_JetGauges_DegreeProportionalWords
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_JetHarmonics_GapSubsetOfSetBoundIntegral
import Theorems.Thm_GlobalTheory_CompareIterDegree_fac_nonneg
import Theorems.Thm_GlobalTheory_CompareIterDegree_fdeg_ratio
import Theorems.Thm_GlobalTheory_CompareIterDegree_sub_single
import Theorems.Thm_GlobalTheory_CompareIterDegree_inj_of_gapTwo
import Theorems.Thm_GlobalTheory_CompareIterDegree_inj_add_of_gapTwo
import Theorems.Thm_GlobalTheory_CompareIterDegree_round_gap
import Theorems.Thm_GlobalTheory_CompareIterDegree_fac_le

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset
open scoped ENNReal
noncomputable section
open GlobalTheory GlobalTheory.CompareIterDegree
open Formalism.QuantumDeterminants Formalism.HermitianLatticeCounting.ExpansionTerms GlobalTheory.IndefiniteRowSideFullHecke.DegreeProportionalWords
namespace GlobalTheory.CompareIterDegree
theorem _root_.solution (h : DegStepBound) {n : ℕ} {μ : Fin n → ℝ} (hg : GapTwo μ) (s : Fin n) (t : ℝ)
    (ht : t = 1 ∨ t = -1) :
    1 / (n : ℝ) ≤ fdegHC (μ + Pi.single s t) / fdegHC μ ∧ fdegHC (μ + Pi.single s t) / fdegHC μ ≤ n := by
  have ht1 : |t| ≤ 1 := by rcases ht with rfl | rfl <;> simp
  rw [fdeg_ratio μ s t ht1 fun a b hab => le_trans one_le_two (hg a b hab)]
  have main : ∀ g : ℝ → ℤ, Monotone g → (∀ x, g (x + 2) = g x + 2) → g 0 = 0 →
      ((∀ x, t * g x ≤ t * x) → ∏ c ∈ univ.erase s, (μ s + t - μ c) / (μ s - μ c) ≤ n) ∧
      ((∀ x, t * x ≤ t * g x) → 1 / (n : ℝ) ≤ ∏ c ∈ univ.erase s, (μ s + t - μ c) / (μ s - μ c)) := by
    intro g hm h2 h0
    obtain ⟨hg', hsg⟩ := round_gap hg s g hm h2 h0
    have hb : 1 / (n : ℝ) ≤ ∏ c ∈ univ.erase s, ((g (μ s - μ c) : ℝ) + t) / g (μ s - μ c) ∧
        ∏ c ∈ univ.erase s, ((g (μ s - μ c) : ℝ) + t) / g (μ s - μ c) ≤ n := by
      have hinj : Function.Injective ((fun c => -(g (μ s - μ c) : ℝ)) + Pi.single s t) :=
        inj_add_of_gapTwo hg' fun a b => by
          simp only [Pi.single_apply]; split_ifs <;> simp [ht1]
      have := h n _ s (inj_of_gapTwo hg') fun a b =>
        ⟨-g (μ s - μ a) - -g (μ s - μ b), by push_cast; rfl⟩
      rcases ht with rfl | rfl
      · simpa [h0, add_comm] using this.1 hinj
      · rw [sub_single] at this
        simpa [h0, add_comm, sub_eq_add_neg] using this.2 hinj
    have hn1 : ∀ c ∈ univ.erase s, 0 ≤ (μ s + t - μ c) / (μ s - μ c) := fun c hc => by
      rw [add_sub_right_comm]
      exact fac_nonneg (le_trans one_le_two (hg s c (ne_of_mem_erase hc).symm)) ht1
    have hn2 : ∀ c ∈ univ.erase s, 0 ≤ ((g (μ s - μ c) : ℝ) + t) / g (μ s - μ c) := fun c hc => by
      have := hg' s c (ne_of_mem_erase hc).symm
      simp only [sub_self, h0, Int.cast_zero, neg_zero, zero_sub, neg_neg] at this
      exact fac_nonneg (le_trans one_le_two this) ht1
    refine ⟨fun hx => le_trans (prod_le_prod hn1 fun c hc => ?_) hb.2,
      fun hx => le_trans hb.1 (prod_le_prod hn2 fun c hc => ?_)⟩
    · rw [add_sub_right_comm]
      exact fac_le (hsg c (ne_of_mem_erase hc)) (hx _)
    · rw [add_sub_right_comm]
      exact fac_le (by rw [mul_comm]; exact hsg c (ne_of_mem_erase hc)) (hx _)
  have hf := main (fun x => ⌊x⌋) Int.floor_mono (fun x => Int.floor_add_ofNat x 2) Int.floor_zero
  have hc := main (fun x => ⌈x⌉) Int.ceil_mono (fun x => Int.ceil_add_ofNat x 2) Int.ceil_zero
  rcases ht with rfl | rfl
  · exact ⟨hc.2 fun x => by simpa using Int.le_ceil x, hf.1 fun x => by simpa using Int.floor_le x⟩
  · exact ⟨hf.2 fun x => by simpa using Int.floor_le x, hc.1 fun x => by simpa using Int.le_ceil x⟩
end GlobalTheory.CompareIterDegree
