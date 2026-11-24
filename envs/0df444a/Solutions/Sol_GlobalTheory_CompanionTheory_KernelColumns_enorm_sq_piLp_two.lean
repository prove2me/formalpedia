-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.KernelColumns.enorm_sq_piLp_two
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T12:41:01.13352+00:00
-- url     : https://prove2.me/submissions/2d169832-0cd2-4350-a007-ef62c2545a2f

import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_ArchimedeanBaseChange_ArchimedeanBaseChangeProof_ThetaCellCovers_VecClose
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_VecCloseOfKerBasicColSq

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open PositivityTheory.Rg.BcB.E1
noncomputable section
open MeasureTheory
open scoped ENNReal Pointwise
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.KernelColumns
namespace GlobalTheory.CompanionTheory.KernelColumns
theorem _root_.solution {ι : Type*} [Fintype ι] {E : ι → Type*}
    [∀ i, NormedAddCommGroup (E i)] (f : PiLp 2 E) :
    ‖f‖ₑ ^ 2 = ∑ l, ‖f l‖ₑ ^ 2 := by
  have h : ‖f‖₊ ^ 2 = ∑ l, ‖f l‖₊ ^ 2 := by
    apply NNReal.coe_injective
    push_cast
    simpa using PiLp.norm_sq_eq_of_L2 E f
  simp only [enorm_eq_nnnorm]
  exact_mod_cast congrArg (fun t : NNReal => (t : ℝ≥0∞)) h
end GlobalTheory.CompanionTheory.KernelColumns
