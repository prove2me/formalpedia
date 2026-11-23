-- Prove2me | solution 1 for GlobalTheory.SmoothForms.PermWord.wd_mem_shorter
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T07:47:16.707939+00:00
-- url     : https://prove2.me/submissions/ecc6db0e-2d0c-4235-b698-a23cc09976f8

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HeightProofs_IsLieDataCircle
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HeightProofs_PermutationWordGelfandPolynomialModShorter

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
theorem _root_.solution (E : Fin n → Fin n → A) {d : ℕ} {l : List (Fin n × Fin n)} (h : l.length < d) :
    wd E l ∈ shorter E d := Submodule.subset_span ⟨l, h, rfl⟩
end GlobalTheory.SmoothForms.PermWord
