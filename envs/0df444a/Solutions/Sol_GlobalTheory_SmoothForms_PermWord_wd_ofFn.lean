-- Prove2me | solution 1 for GlobalTheory.SmoothForms.PermWord.wd_ofFn
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T07:47:17.148376+00:00
-- url     : https://prove2.me/submissions/0a9235b3-f913-44a6-9887-b97a3832c6f5

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
theorem _root_.solution {B : Type} [Ring B] (E : Fin n → Fin n → B) {d : ℕ} (I K : Fin d → Fin n) :
    wd E (List.ofFn fun a => (I a, K a)) = (List.ofFn fun a => E (I a) (K a)).prod := by
  simp [wd, List.map_ofFn, Function.comp_def]
end GlobalTheory.SmoothForms.PermWord
