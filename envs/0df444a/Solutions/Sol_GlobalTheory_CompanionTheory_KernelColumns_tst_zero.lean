-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.KernelColumns.tst_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T12:40:54.608824+00:00
-- url     : https://prove2.me/submissions/bafcd083-e9bc-413e-bf2f-8fd6369048c5

import Mathlib
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_ArchimedeanBaseChange_ArchimedeanBaseChangeProof_ThetaCellCovers_VecClose
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_VecNormOfVecClose

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
theorem _root_.solution (X : Ctx) : Tst (0 : X.G → ℂ) :=
  ⟨continuous_const, HasCompactSupport.zero⟩
end GlobalTheory.CompanionTheory.KernelColumns
