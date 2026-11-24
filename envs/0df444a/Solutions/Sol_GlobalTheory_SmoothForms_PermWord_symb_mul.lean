-- Prove2me | solution 1 for GlobalTheory.SmoothForms.PermWord.symb_mul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T21:05:40.667289+00:00
-- url     : https://prove2.me/submissions/c9648cc9-3a8e-49f5-8cf0-c83f27df4902

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HeightProofs_IsLieDataCircle
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HeightProofs_PermutationWordGelfandPolynomialModShorter
import Theorems.Thm_GlobalTheory_SmoothForms_PermWord_wd_append

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
variable {A : Type} [Ring A] [Algebra ℂ A] {n : ℕ}
namespace GlobalTheory.SmoothForms.PermWord
theorem _root_.solution (E : Fin n → Fin n → A) {a b : ℕ} {x y} (hx : x ∈ symb E a) (hy : y ∈ symb E b) :
    x * y ∈ symb E (a + b) := by
  have := Submodule.mul_mem_mul hx hy
  rw [symb, symb, Submodule.span_mul_span] at this
  refine Submodule.span_mono ?_ this
  rintro _ ⟨_, ⟨l, rfl, rfl⟩, _, ⟨l', rfl, rfl⟩, rfl⟩
  exact ⟨l ++ l', by simp, by simp [wd_append]⟩
end GlobalTheory.SmoothForms.PermWord
