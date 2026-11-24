-- Prove2me | solution 1 for GlobalTheory.LLocal.analyticOrderNatAt_comp_const_add
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T18:37:33.72808+00:00
-- url     : https://prove2.me/submissions/e1c33319-d4e4-4744-b34d-7b3a76b4d6cd

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_DifferentiableAtMellinSummatory
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_TsumOneDivRpowLe
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_NormOneSubConjMul
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_LogDerivDirichletLFunctionLocalZeroSum

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Complex DirichletCharacter ArithmeticFunction MeasureTheory
open GlobalTheory GlobalTheory.LLocal
namespace GlobalTheory.LLocal
theorem _root_.solution (g : ℂ → ℂ) (c w : ℂ) :
    analyticOrderNatAt (fun z => g (c + z)) w = analyticOrderNatAt g (c + w) := by
  unfold analyticOrderNatAt
  congr 1
  have h := analyticOrderAt_comp_of_deriv_ne_zero (f := g) (g := fun z : ℂ => c + z) (z₀ := w)
    (by fun_prop) (by simp)
  exact h
end GlobalTheory.LLocal
