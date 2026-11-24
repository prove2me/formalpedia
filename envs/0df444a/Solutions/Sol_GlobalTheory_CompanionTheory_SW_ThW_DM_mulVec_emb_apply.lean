-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.SW.ThW.DM_mulVec_emb_apply
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T13:33:39.531975+00:00
-- url     : https://prove2.me/submissions/2010a84b-d394-470f-945a-e49a6cef720e

import Mathlib
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_SumRhoEqTrace
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_AdelicCharacterExponentialFormula

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.SW GlobalTheory.CompanionTheory.SW.ThW
open NumberField IsDedekindDomain MeasureTheory Matrix Topology GlobalTheory.CompanionTheory.SW.Core
open scoped ENNReal NNReal MatrixGroups Kronecker
namespace GlobalTheory.CompanionTheory.SW.ThW
theorem _root_.solution {F : Type} [Field F] [NumberField F] {ι : Type} [Fintype ι]
    [DecidableEq ι] [DecidableEq (InfinitePlace F)] (B : Matrix ι ι F)
    (ρ : InfinitePlace F → (F →+* ℝ)) (y : ι → F) (i : ι) (w : InfinitePlace F) :
    (DM B ρ *ᵥ emb ρ y) (i, w) = ρ w ((B *ᵥ y) i) := by
  have h : ρ w ((B *ᵥ y) i) = ∑ j, ρ w (B i j) * ρ w (y j) := by
    simp [mulVec, dotProduct, map_sum, map_mul]
  rw [h]
  simp only [mulVec, dotProduct, DM, emb, Fintype.sum_prod_type_right, blockDiagonal_apply]
  rw [Finset.sum_eq_single w]
  · simp
  · intro v _ hv
    simp [Ne.symm hv]
  · simp
end GlobalTheory.CompanionTheory.SW.ThW
