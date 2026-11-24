-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.KernelBasic.ker_adj
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T12:40:54.877991+00:00
-- url     : https://prove2.me/submissions/e08a0d8d-f7f7-48a5-9181-bb00701ad225

import Mathlib
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_ArchimedeanBaseChange_ArchimedeanBaseChangeProof_ThetaCellCovers_KernelL2RowsColumns
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_FiniteOfCompact
import Theorems.Thm_GlobalTheory_CompanionTheory_KernelBasic_support_finite

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MeasureTheory PositivityTheory.Rg.BcB.E1
open scoped ENNReal Pointwise
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.KernelBasic
namespace GlobalTheory.CompanionTheory.KernelBasic
theorem _root_.solution (X : Ctx) {φ : X.G → ℂ} (hφ : HasCompactSupport φ) (x y : X.G) :
    ker X.Γ (adj φ) x y = starRingEnd ℂ (ker X.Γ φ y x) := by
  unfold ker
  rw [map_finsum _ (support_finite X hφ y x), ← finsum_comp_equiv (Equiv.inv X.Γ)]
  refine finsum_congr fun δ => ?_
  simp only [adj, Equiv.inv_apply, Subgroup.coe_inv]
  congr 2
  group
end GlobalTheory.CompanionTheory.KernelBasic
