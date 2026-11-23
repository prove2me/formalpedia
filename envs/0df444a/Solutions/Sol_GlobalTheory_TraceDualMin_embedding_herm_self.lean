-- Prove2me | solution 1 for GlobalTheory.TraceDualMin.embedding_herm_self
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T13:13:48.333784+00:00
-- url     : https://prove2.me/submissions/ae21bbcc-ac7b-40f9-bb2b-fb8d9dad5751

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_FundamentalDomainPointBound
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_FinrankMulDiscrRpowLeSumSqOfMemTraceDual
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CuspFormEvaluations_EmbeddingHermSelf
import Theorems.Thm_GlobalTheory_TraceDualMin_herm_one_eq

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField ReciprocityTheory.ChartRestriction.G.FD
open scoped nonZeroDivisors
open GlobalTheory
variable {E : Type} [Field E] [NumberField E] [IsCMField E]
open GlobalTheory.TraceDualMin
namespace GlobalTheory.TraceDualMin
theorem _root_.solution {n : ℕ} (σ : E →+* ℂ) (x : Fin n → E) :
    σ (herm 1 x x) = ((∑ k, ‖σ (x k)‖ ^ 2 : ℝ) : ℂ) := by
  simp [herm_one_eq, cc, IsCMField.complexEmbedding_complexConj, Complex.mul_conj']
end GlobalTheory.TraceDualMin
