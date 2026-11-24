-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.KernelBasic.ker_mul_right
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T12:40:57.423397+00:00
-- url     : https://prove2.me/submissions/e5c0f167-1a17-4058-abaa-3d53052e2b82

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
    ker X.Γ φ x (γ * y) = ker X.Γ φ x y := by
  unfold ker
  rw [← finsum_comp_equiv (Equiv.mulRight (⟨γ, hγ⟩ : X.Γ)⁻¹)]
  refine finsum_congr fun δ => ?_
  congr 1
  simp only [Equiv.coe_mulRight, Subgroup.coe_mul, Subgroup.coe_inv]
  group
end GlobalTheory.CompanionTheory.KernelBasic
