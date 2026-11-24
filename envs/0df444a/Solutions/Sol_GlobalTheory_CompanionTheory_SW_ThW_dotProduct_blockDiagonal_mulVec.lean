-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.SW.ThW.dotProduct_blockDiagonal_mulVec
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T13:35:12.596946+00:00
-- url     : https://prove2.me/submissions/0d7faf56-e6fc-49af-8a74-464efdc3ab6e

import Mathlib
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_SumRhoEqTrace
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_SiegelMatrixSymmetricPosdefImag

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain MeasureTheory Matrix Topology GlobalTheory.CompanionTheory.SW.Core GlobalTheory.CompanionTheory.SW.ThW
open scoped ENNReal NNReal MatrixGroups Kronecker
noncomputable section
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.SW GlobalTheory.CompanionTheory.SW.ThW
namespace GlobalTheory.CompanionTheory.SW.ThW
theorem _root_.solution {R ι W : Type} [CommSemiring R] [Fintype ι] [DecidableEq ι]
    [Fintype W] [DecidableEq W] (f : W → Matrix ι ι R) (y : ι × W → R) :
    y ⬝ᵥ (blockDiagonal f *ᵥ y) = ∑ w, (fun i => y (i, w)) ⬝ᵥ (f w *ᵥ fun i => y (i, w)) := by
  simp only [dotProduct, mulVec]
  rw [Fintype.sum_prod_type_right]
  refine Finset.sum_congr rfl fun w _ => Finset.sum_congr rfl fun i _ => ?_
  congr 1
  rw [Fintype.sum_prod_type_right, Finset.sum_eq_single w]
  · simp [blockDiagonal_apply]
  · intro v _ hv
    refine Finset.sum_eq_zero fun j _ => ?_
    simp [blockDiagonal_apply, hv.symm]
  · simp
end GlobalTheory.CompanionTheory.SW.ThW
