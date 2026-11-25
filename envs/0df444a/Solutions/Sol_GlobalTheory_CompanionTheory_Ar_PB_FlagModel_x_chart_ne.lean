-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.Ar.PB.FlagModel.x_chart_ne
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T09:02:55.068589+00:00
-- url     : https://prove2.me/submissions/8ccdeb24-5469-4011-bfce-d70742c21523

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Statements_MetricStatements_AgreementIffGuarded
import Definitions.Def_Development_AutomorphicSpectrum_Definitions_MetricPeriods_GenericBlockMatrixIsBlockDiag

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.PB
open ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo MvPolynomial Matrix
open GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder
variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]
attribute [instance] FlagModel.fieldΩ FlagModel.charΩ FlagModel.alg
open GlobalTheory.CompanionTheory.Ar.PB.FlagModel
variable {Φ : Type} [Field Φ] {y : (Σ k, ι k) → Φ} {Ψ : Type} {N j : ℕ} (M : FlagModel y Ψ N j)
namespace GlobalTheory.CompanionTheory.Ar.PB.FlagModel
theorem _root_.solution {F : FrameData ι Ψ N M.Ω M.blk} {Q : Ideal (MRing (baseIdx ι M.blk))} (hQ : mCoordIdeal M.x ≤ Q)
    (hF : M.GoodAt F Q) (k : NonPluckerBlocks M.blk) : M.x ⟨k, F.c k⟩ ≠ 0 := fun h => hF.1 k (hQ (by
  show mConeMap M.x (X ⟨k, F.c k⟩) = 0
  rw [mConeMap, aeval_X, h, map_zero, zero_mul]))
end GlobalTheory.CompanionTheory.Ar.PB.FlagModel
