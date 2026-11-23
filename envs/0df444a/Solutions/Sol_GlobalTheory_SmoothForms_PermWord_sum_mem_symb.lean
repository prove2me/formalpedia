-- Prove2me | solution 1 for GlobalTheory.SmoothForms.PermWord.sum_mem_symb
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T07:53:00.772739+00:00
-- url     : https://prove2.me/submissions/a0df0178-bcb6-4652-a6fd-c8c8acdc6f42

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HeightProofs_IsLieDataCircle
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HeightProofs_PermutationWordGelfandPolynomialModShorter
import Theorems.Thm_GlobalTheory_SmoothForms_PermWord_wd_ofFn

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
theorem _root_.solution (E : Fin n → Fin n → A) {d : ℕ} {ι : Type} [Fintype ι] (I K : ι → Fin d → Fin n) :
    (∑ i, (List.ofFn fun a => gen n (I i a) (K i a)).prod, ∑ i, (List.ofFn fun a => E (I i a) (K i a)).prod) ∈
      symb E d := by
  rw [prod_mk_sum]
  refine Submodule.sum_mem _ fun i _ => Submodule.subset_span ⟨List.ofFn fun a => (I i a, K i a), by simp, ?_⟩
  rw [wd_ofFn, wd_ofFn]
end GlobalTheory.SmoothForms.PermWord
