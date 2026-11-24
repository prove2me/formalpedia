-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.KernelColumns.exists_bound
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T12:40:25.541186+00:00
-- url     : https://prove2.me/submissions/6211368c-c25f-40e4-a16d-c4dff31e1b85

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
theorem _root_.solution (X : Ctx) {ι : Type} [Fintype ι] (Φ : Matrix ι ι (X.G → ℂ))
    (hΦ : ∀ i j, Tst (Φ i j)) : ∃ ε : ℝ, ∀ l j z, ‖Φ l j z‖ ≤ ε := by
  have h : ∀ i j, ∃ B : ℝ, ∀ z, ‖Φ i j z‖ ≤ B := fun i j => by
    obtain ⟨B, hB⟩ := ((hΦ i j).1.norm).bddAbove_range_of_hasCompactSupport (hΦ i j).2.norm
    exact ⟨B, fun z => hB ⟨z, rfl⟩⟩
  choose B hB using h
  have hB0 : ∀ i j, 0 ≤ B i j := fun i j => (norm_nonneg _).trans (hB i j 1)
  refine ⟨∑ i, ∑ j, B i j, fun l j z => (hB l j z).trans ?_⟩
  calc B l j ≤ ∑ j, B l j :=
        Finset.single_le_sum (f := fun j => B l j) (fun j _ => hB0 l j) (Finset.mem_univ j)
    _ ≤ ∑ i, ∑ j, B i j :=
        Finset.single_le_sum (f := fun i => ∑ j, B i j)
          (fun i _ => Finset.sum_nonneg fun j _ => hB0 i j) (Finset.mem_univ l)
end GlobalTheory.CompanionTheory.KernelColumns
