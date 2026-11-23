-- Prove2me | solution 1 for GlobalTheory.SmoothForms.PermWord.wd_cons
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T04:06:12.2016+00:00
-- url     : https://prove2.me/submissions/aa8958da-7ca0-44b5-a628-0ee083816ad7

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
theorem _root_.solution {B : Type} [Ring B] (E : Fin n → Fin n → B) (z) (l : List (Fin n × Fin n)) :
    wd E (z :: l) = E z.1 z.2 * wd E l := by simp [wd]
end GlobalTheory.SmoothForms.PermWord
