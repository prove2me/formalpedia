-- Prove2me | solution 1 for GlobalTheory.SmoothForms.PermWord.permWord
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T21:31:05.460093+00:00
-- url     : https://prove2.me/submissions/d9a38b2b-0256-42a7-93a4-d26ad3b827de

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HeightProofs_IsLieDataCircle
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HeightProofs_PermutationWordGelfandPolynomialModShorter
import Theorems.Thm_GlobalTheory_SmoothForms_PermWord_shorter_le_filt
import Theorems.Thm_GlobalTheory_SmoothForms_PermWord_symb_sub
import Theorems.Thm_GlobalTheory_SmoothForms_PermWord_sum_mem_symb
import Theorems.Thm_GlobalTheory_SmoothForms_PermWord_wordMap_permMat
import Theorems.Thm_GlobalTheory_SmoothForms_PermWord_exists_symb

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.SmoothForms NumberField Matrix
open scoped ContDiff Topology
noncomputable section
open GlobalTheory GlobalTheory.SmoothForms GlobalTheory.SmoothForms.PermWord
namespace GlobalTheory.SmoothForms.PermWord
theorem _root_.solution : ∀ (A : Type) [Ring A] [Algebra ℂ A] (n : ℕ) (E : Fin n → Fin n → A), Formalism.REAL.GlRel E → ∀ (d : ℕ) (π : Equiv.Perm (Fin d)), ∃ c ∈ Algebra.adjoin ℂ (Set.range (gelfA E)), wordMap E d (permMat n d π) - c ∈ filt E d := by
  intro A _ _ n E hE d π
  obtain ⟨c, hc, h⟩ := exists_symb E d π
  refine ⟨c, hc, shorter_le_filt E d ?_⟩
  have h2 := symb_sub hE (sum_mem_symb E (fun (K : Fin d → Fin n) a => K (π a)) fun K => K)
  have h1 := symb_sub hE h
  have h3 := sub_mem h2 h1
  rw [sub_sub_sub_cancel_right] at h3
  rw [wordMap_permMat]
  exact h3
end GlobalTheory.SmoothForms.PermWord
