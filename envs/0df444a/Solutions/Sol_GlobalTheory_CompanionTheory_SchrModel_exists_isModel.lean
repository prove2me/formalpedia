-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.SchrModel.exists_isModel
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T17:34:59.17734+00:00
-- url     : https://prove2.me/submissions/465238e3-7b45-4b13-abdb-5f2aac83d421

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Definitions_MembershipCriteria_GoodChar
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_MembershipProofs_GoodCharIsLocallyConstant
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_MembershipProofs_LocallyCompactOfGoodChar
import Theorems.Thm_GlobalTheory_CompanionTheory_SchrModel_isModel_sys

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MeasureTheory GlobalTheory.WeilM GlobalTheory.CompanionTheory.VacLoc GlobalTheory.CompanionTheory.SchrLaw
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.SchrModel
variable {R : Type} [CommRing R] [TopologicalSpace R] [IsTopologicalRing R]
variable [T2Space R] [Invertible (2 : R)] {W : Type} [AddCommGroup W] [Module R W] {B : W → W → R} {κ : Type} [Fintype κ]
namespace GlobalTheory.CompanionTheory.SchrModel
theorem _root_.solution {ψ : AddChar R ℂ} {O : Subring R} {u : Rˣ} (h : GoodChar ψ O u) (d : Darboux B κ)
    (μ : @Measure (κ → R) (borel _)) (hμ : @Measure.IsAddHaarMeasure _ _ _ (borel _) μ) :
    ∃ S : GlobalTheory.CompanionTheory.FinHeis.Sys W (SB (κ → R)), IsModel ψ d μ S := by
  exact ⟨sys h d μ hμ, isModel_sys h d μ hμ⟩
end GlobalTheory.CompanionTheory.SchrModel
