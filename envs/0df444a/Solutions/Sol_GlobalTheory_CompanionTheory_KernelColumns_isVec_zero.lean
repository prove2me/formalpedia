-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.KernelColumns.isVec_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T12:56:17.054799+00:00
-- url     : https://prove2.me/submissions/b488232e-eff8-4f30-bfa8-d8f4b806be91

import Mathlib
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_ArchimedeanBaseChange_ArchimedeanBaseChangeProof_ThetaCellCovers_VecClose
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_VecNormOfVecClose
import Theorems.Thm_GlobalTheory_CompanionTheory_KernelColumns_ker_zero

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MeasureTheory
open scoped ENNReal Pointwise
open PositivityTheory.Rg.BcB.E1
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.KernelColumns
namespace GlobalTheory.CompanionTheory.KernelColumns
theorem _root_.solution (X : Ctx) {ι : Type} [Fintype ι] (y : X.G) (j : ι) :
    X.IsVec (0 : Matrix ι ι (X.G → ℂ)) y j (0 : X.Hs ι) := by
  intro l
  have h : (((0 : X.Hs ι) l : Lp ℂ 2 X.ν) : X.G → ℂ) =ᵐ[X.ν] 0 := Lp.coeFn_zero ℂ 2 X.ν
  refine h.trans (Filter.Eventually.of_forall fun z => ?_)
  exact (ker_zero X z y).symm
end GlobalTheory.CompanionTheory.KernelColumns
