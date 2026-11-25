-- Prove2me | solution 1 for GlobalTheory.HermFrame.posDef_gradedGram
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T17:46:29.168257+00:00
-- url     : https://prove2.me/submissions/1c4e2a60-0bbe-4f73-8b0a-59b7c2e7e9d8

import Mathlib
import Definitions.Def_ReciprocityTheory_AnalyticForms_MaIntEmpty
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ThetaMetrics_EventuallyDifferentiableAtOfContDiffAtTwo
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_LeTwoMulOfForallScale
import Theorems.Thm_GlobalTheory_HermFrame_posDef_quotGram

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Complex ComplexConjugate
open scoped ComplexOrder MatrixOrder
noncomputable section
open GlobalTheory GlobalTheory.HermFrame
variable {m n l : Type*} [Fintype m] [Fintype n] [Fintype l]
variable {N : ℕ}
namespace GlobalTheory.HermFrame
theorem _root_.solution {H : Matrix (Fin N) (Fin N) ℂ} (h : H.PosDef) (i : Fin N) :
    (gradedGram H i).PosDef := by
  refine posDef_quotGram (h.submatrix ?_)
  rintro (a | a) (b | b) hab
  · exact congrArg _ (Fin.castLE_injective i.2.le hab)
  · exact absurd (congrArg Fin.val hab) a.2.ne
  · exact absurd (congrArg Fin.val hab) b.2.ne'
  · rfl
end GlobalTheory.HermFrame
