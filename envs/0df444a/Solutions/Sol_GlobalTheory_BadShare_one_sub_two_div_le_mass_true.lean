-- Prove2me | solution 1 for GlobalTheory.BadShare.one_sub_two_div_le_mass_true
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T04:20:06.686691+00:00
-- url     : https://prove2.me/submissions/3356cf56-5756-473b-bcb7-c7f95b9236a5

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_SamePartIffOfNeZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_MemMonicSquarefreeUnitConstPolysIffMonicSquarefrStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_CardMonicSquarefreeUnitConstPolysGeStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_SquarefreeLabelTorusCardBoundsAndMulStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_OneSubTwoDivLeSquarefreeLabelMass
import Theorems.Thm_GlobalTheory_T_card_monicSquarefreeUnitConstPolys_ge
import Theorems.Thm_GlobalTheory_T_mem_monicSquarefreeUnitConstPolys_iff_monic_squarefree
import Theorems.Thm_GlobalTheory_T_squarefreeLabelTorusCard_bounds_and_mul


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Polynomial Classical GlobalTheory.BadShare
open GlobalTheory GlobalTheory.BadShare
namespace GlobalTheory.BadShare
theorem _root_.solution :
    ∀ (g : ℕ) [Fact g.Prime], ∀ N : ℕ, 1 - 2 / (g : ℝ) ≤ mass g N fun _ => True := by
  intro g hg N
  have hg0 : (0 : ℝ) < g := by exact_mod_cast hg.out.pos
  have hpow : (0 : ℝ) < (g : ℝ) ^ N := pow_pos hg0 N
  have hterm : ∀ f ∈ sqSet g N, ((g : ℝ) ^ N)⁻¹ ≤ ((torusCard g f : ℝ))⁻¹ := by
    intro f hf
    obtain ⟨h1, h2, -⟩ := (GlobalTheory.T.squarefreeLabelTorusCard_bounds_and_mul g).1 N f hf
    have h1' : (0 : ℝ) < (torusCard g f : ℝ) := by exact_mod_cast h1
    have h2' : (torusCard g f : ℝ) ≤ (g : ℝ) ^ N := by exact_mod_cast h2
    exact inv_anti₀ h1' h2'
  have hsum : ((sqSet g N).card : ℝ) * ((g : ℝ) ^ N)⁻¹ ≤ mass g N fun _ => True := by
    have h := Finset.card_nsmul_le_sum (sqSet g N) (fun f => ((torusCard g f : ℝ))⁻¹) _ hterm
    rw [nsmul_eq_mul] at h
    unfold mass
    simpa only [Finset.filter_true] using h
  refine le_trans ?_ hsum
  rcases Nat.eq_zero_or_pos N with rfl | hN
  · have h1 : (1 : (ZMod g)[X]) ∈ sqSet g 0 :=
      (GlobalTheory.T.mem_monicSquarefreeUnitConstPolys_iff_monic_squarefree g 0 1).2 ⟨monic_one, natDegree_one, squarefree_one, by simp⟩
    have hc : (1 : ℝ) ≤ ((sqSet g 0).card : ℝ) := by
      exact_mod_cast Finset.card_pos.2 ⟨_, h1⟩
    have : (0 : ℝ) ≤ 2 / (g : ℝ) := by positivity
    simp only [pow_zero, inv_one, mul_one]
    linarith
  · have hc := GlobalTheory.T.card_monicSquarefreeUnitConstPolys_ge g N hN
    obtain ⟨M, rfl⟩ : ∃ M, N = M + 1 := ⟨N - 1, by omega⟩
    rw [Nat.add_sub_cancel] at hc
    have he : 1 - 2 / (g : ℝ) = ((g : ℝ) ^ (M + 1) - 2 * (g : ℝ) ^ M) * ((g : ℝ) ^ (M + 1))⁻¹ := by
      field_simp
      ring
    rw [he]
    exact mul_le_mul_of_nonneg_right hc (inv_nonneg.2 hpow.le)
end GlobalTheory.BadShare
