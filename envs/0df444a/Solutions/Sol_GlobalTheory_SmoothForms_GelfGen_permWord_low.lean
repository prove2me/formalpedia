-- Prove2me | solution 1 for GlobalTheory.SmoothForms.GelfGen.permWord_low
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T23:01:26.639819+00:00
-- url     : https://prove2.me/submissions/3c25a153-4e69-4ed8-a471-f2b071db1b94

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HeightProofs_PolarConjTranspose
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HeightProofs_PermutationWordGelfandPolynomialModShorter
import Definitions.Def_Formalism_LatticeRigidity_HeightMinimum_PowFinrankEqZeroOfTracePow
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_GelfAMemAdjoinLow
import Theorems.Thm_GlobalTheory_SmoothForms_GelfGen_exists_symb_low
import Theorems.Thm_GlobalTheory_SmoothForms_PermWord_shorter_le_filt
import Theorems.Thm_GlobalTheory_SmoothForms_PermWord_sum_mem_symb
import Theorems.Thm_GlobalTheory_SmoothForms_PermWord_symb_sub
import Theorems.Thm_GlobalTheory_SmoothForms_PermWord_wordMap_permMat


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.SmoothForms
noncomputable section
open GlobalTheory.SmoothForms.PermWord
open GlobalTheory GlobalTheory.SmoothForms GlobalTheory.SmoothForms.GelfGen
variable {A : Type} [Ring A] [Algebra ℂ A] {n : ℕ}
namespace GlobalTheory.SmoothForms.GelfGen
theorem _root_.solution {E : Fin n → Fin n → A} (hE : Formalism.REAL.GlRel E) (d : ℕ) (π : Equiv.Perm (Fin d)) :
    ∃ c ∈ Algebra.adjoin ℂ (Set.range fun k : Fin n => gelfA E k.val),
      wordMap E d (permMat n d π) - c ∈ filt E d := by
  obtain ⟨c, hc, h⟩ := exists_symb_low E d π
  refine ⟨c, hc, shorter_le_filt E d ?_⟩
  have h2 := symb_sub hE (sum_mem_symb E (fun (K : Fin d → Fin n) a => K (π a)) fun K => K)
  have h1 := symb_sub hE h
  have h3 := sub_mem h2 h1
  rw [sub_sub_sub_cancel_right] at h3
  rw [wordMap_permMat]
  exact h3
end GlobalTheory.SmoothForms.GelfGen
