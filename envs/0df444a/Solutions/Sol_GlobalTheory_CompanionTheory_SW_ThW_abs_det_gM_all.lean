-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.SW.ThW.abs_det_gM_all
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T14:12:31.449996+00:00
-- url     : https://prove2.me/submissions/775090a2-6af2-47b2-a34d-ac4088cae1f7

import Mathlib
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_SumRhoEqTrace
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_LatticeMatrixDeterminantFormula
import Theorems.Thm_GlobalTheory_CompanionTheory_SW_ThW_abs_det_gM

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
open scoped ENNReal NNReal MatrixGroups Kronecker nonZeroDivisors
variable {F : Type} [Field F] [NumberField F] {ι : Type} [Fintype ι] [DecidableEq ι]
  [DecidableEq (InfinitePlace F)]
namespace GlobalTheory.CompanionTheory.SW.ThW
theorem _root_.solution : ∀ (F : Type) [Field F] [NumberField F] (ι : Type) [Fintype ι] [DecidableEq ι]
    [DecidableEq (InfinitePlace F)] (ρ : InfinitePlace F → (F →+* ℝ)), IsTotallyReal F →
    (∀ w x, ((ρ w x : ℝ) : ℂ) = w.embedding x) →
    ∀ (b : Module.Basis (InfinitePlace F) ℤ (𝓞 F)) (N : ℕ),
    |(gM (ι := ι) ρ (fun v => b v) N).det| =
      ((N : ℝ) ^ Module.finrank ℚ F * Real.sqrt |(discr F : ℝ)|) ^ Fintype.card ι :=
  fun _ _ _ _ _ _ _ _ hT hρ b N => abs_det_gM hT hρ b N
end GlobalTheory.CompanionTheory.SW.ThW
