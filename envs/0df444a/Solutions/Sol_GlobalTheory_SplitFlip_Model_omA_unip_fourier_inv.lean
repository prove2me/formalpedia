-- Prove2me | solution 1 for GlobalTheory.SplitFlip.Model.omA_unip_fourier_inv
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T18:12:28.214819+00:00
-- url     : https://prove2.me/submissions/c5b5539a-f84f-419d-b334-b78892f97bda

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_RankEqCardIffExistsFrameMatrixFirstColumnBlock
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_OmAUnipFourierInv
import Theorems.Thm_GlobalTheory_SplitFlip_Model_omA_unip_fourier

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory ValuativeRel Matrix
open scoped NNReal ENNReal Pointwise
noncomputable section
open GlobalTheory GlobalTheory.SplitFlip GlobalTheory.SplitFlip.Model
open GlobalTheory.SplitWeil GlobalTheory.SplitWeil.Model GlobalTheory.SplitFlip
variable {k : Type*} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
variable {A D₁ D₂ : Type*} [Fintype A] [DecidableEq A] [Fintype D₁] [DecidableEq D₁] [Fintype D₂] [DecidableEq D₂]
variable [MeasurableSpace k] [BorelSpace k]
namespace GlobalTheory.SplitFlip.Model
theorem _root_.solution (ψ : AddChar k Circle) (m : Measure k) (ν β : kˣ →* ℂˣ) (b : Matrix D₁ D₂ k)
    (Φ : Matrix A (D₁ ⊕ D₂) k → ℂ) :
    omA ν β 1 (unip b) (fourierInt ψ⁻¹ m (Assignment.one.block D₁ D₂) Φ) =
      fourierInt ψ⁻¹ m (Assignment.one.block D₁ D₂)
        fun T => (ψ (trace (T.toCols₁ * b * T.toCols₂ᵀ)) : ℂ) * Φ T := by
  rw [omA_unip_fourier]
  simp [AddChar.inv_apply]
end GlobalTheory.SplitFlip.Model
