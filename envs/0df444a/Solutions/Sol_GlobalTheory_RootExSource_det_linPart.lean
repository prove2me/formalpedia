-- Prove2me | solution 1 for GlobalTheory.RootExSource.det_linPart
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T20:20:42.246268+00:00
-- url     : https://prove2.me/submissions/74ff2ab7-f267-45ba-aa19-a034764fad49

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_SimpleSum
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_UnipotentRadicalBasic
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_LinearChangeOfVariablesLocalFieldMatrix
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_SecondCountableLocal
import Theorems.Thm_GlobalTheory_RootExSource_det_eq_one_of_unip

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.RootEx
noncomputable section
open GlobalTheory GlobalTheory.RootExSource
variable {k : Type} [Field k] {n n' : Type} [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n']
  {c p : ℕ}
open Classical
namespace GlobalTheory.RootExSource
theorem _root_.solution {g : GL (n' ⊕ Fin (c + 1)) k} (hg : InN p g) : (linPart n p g).det = 1 := by
  rw [← det_transpose]
  refine det_eq_one_of_unip (fun a => lev p a.1.2) _ fun a b hab => ?_
  rcases a with ⟨⟨r, s⟩, ha⟩
  rcases b with ⟨⟨r', s'⟩, hb⟩
  simp only [linPart, transpose_apply, of_apply]
  rw [hg _ _ hab]
  by_cases h1 : r = r' <;> by_cases h2 : s = s' <;> simp [Matrix.one_apply, h1, h2]
end GlobalTheory.RootExSource
