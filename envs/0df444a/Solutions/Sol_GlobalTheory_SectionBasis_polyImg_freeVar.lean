-- Prove2me | solution 1 for GlobalTheory.SectionBasis.polyImg_freeVar
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T03:12:38.682115+00:00
-- url     : https://prove2.me/submissions/1521c9b8-99f1-4392-860b-f038c52926d5

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TorusHaarMeasure_PolyImgSuccAbove
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TorusHaarMeasure_ExistsDvdOfAlgebraic
import Theorems.Thm_GlobalTheory_GenericSection_polyImg_same
import Theorems.Thm_GlobalTheory_GenericSection_polyImg_succAbove


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.SectionBasis
open MvPolynomial ReciprocityTheory.ChartRestriction.G.T0 GlobalTheory.GenericSection
open scoped TensorProduct
variable {K Ω K' : Type} [Field K] [Field Ω] [Algebra K Ω] [Field K'] [Algebra K K'] {D N : ℕ}
namespace GlobalTheory.SectionBasis
theorem _root_.solution (j0 : Fin (N + 1)) (x : Fin N → Ω) (s : SVar D N) :
    polyImg j0 x (freeVar j0 s) = X s := by
  rcases s with ⟨⟨⟩⟩ | ⟨i, k⟩
  · show polyImg j0 x (0, j0) = _
    rw [polyImg_same, if_pos rfl]
  · exact polyImg_succAbove j0 x i k
end GlobalTheory.SectionBasis
