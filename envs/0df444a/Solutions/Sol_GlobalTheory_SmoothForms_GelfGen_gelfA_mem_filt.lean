-- Prove2me | solution 1 for GlobalTheory.SmoothForms.GelfGen.gelfA_mem_filt
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T22:32:57.859058+00:00
-- url     : https://prove2.me/submissions/c6a9bb4c-131c-421b-83d9-88ede39af351

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HeightProofs_PolarConjTranspose
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HeightProofs_PermutationWordGelfandPolynomialModShorter
import Definitions.Def_Formalism_LatticeRigidity_HeightMinimum_PowFinrankEqZeroOfTracePow
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_GelfAMemAdjoinLow
import Theorems.Thm_GlobalTheory_SmoothForms_PermWord_shorter_le_filt
import Theorems.Thm_GlobalTheory_SmoothForms_PermWord_wd_mem_shorter
import Theorems.Thm_GlobalTheory_SmoothForms_PermWord_wd_ofFn


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
theorem _root_.solution (E : Fin n → Fin n → A) (m : ℕ) : gelfA E m ∈ filt E (m + 2) := by
  refine shorter_le_filt E _ (Submodule.sum_mem _ fun idx _ => ?_)
  rw [← wd_ofFn E (fun a : Fin (m + 1) => idx a) fun a => idx (a + 1)]
  exact wd_mem_shorter E (by simp)
end GlobalTheory.SmoothForms.GelfGen
