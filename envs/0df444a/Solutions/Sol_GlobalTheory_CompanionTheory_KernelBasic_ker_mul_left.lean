-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.KernelBasic.ker_mul_left
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T12:40:56.443215+00:00
-- url     : https://prove2.me/submissions/919c9193-aece-49fc-93f4-943547d8fd5a

import Mathlib
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_ArchimedeanBaseChange_ArchimedeanBaseChangeProof_ThetaCellCovers_KernelL2RowsColumns
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_FiniteOfCompact

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
theorem _root_.solution (X : Ctx) (φ : X.G → ℂ) {γ : X.G} (hγ : γ ∈ X.Γ) (x y : X.G) :
    ker X.Γ φ (γ * x) y = ker X.Γ φ x y := by
  unfold ker
  rw [← finsum_comp_equiv (Equiv.mulLeft (⟨γ, hγ⟩ : X.Γ))]
  refine finsum_congr fun δ => ?_
  congr 1
  simp only [Equiv.coe_mulLeft, Subgroup.coe_mul]
  group
end GlobalTheory.CompanionTheory.KernelBasic
