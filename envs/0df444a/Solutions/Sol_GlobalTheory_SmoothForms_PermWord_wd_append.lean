-- Prove2me | solution 1 for GlobalTheory.SmoothForms.PermWord.wd_append
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T20:51:58.836192+00:00
-- url     : https://prove2.me/submissions/d005775b-9072-4387-8763-1d19b9b775a7

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
theorem _root_.solution {B : Type} [Ring B] (E : Fin n → Fin n → B) (l l' : List (Fin n × Fin n)) :
    wd E (l ++ l') = wd E l * wd E l' := by simp [wd]
end GlobalTheory.SmoothForms.PermWord
