-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.SchrModel.isModel_sys
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T17:05:10.587693+00:00
-- url     : https://prove2.me/submissions/20cd3d34-b99d-4cc4-aeef-ac579f0d0dda

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Definitions_MembershipCriteria_GoodChar
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_MembershipProofs_GoodCharIsLocallyConstant
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_MembershipProofs_LocallyCompactOfGoodChar

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
    IsModel ψ d μ (sys h d μ hμ) := by
  show (∀ w φ, _) ∧ (∀ φ φ', _) ∧ ∀ w w', _
  exact ⟨fun w φ => rfl, fun φ φ' => rfl, fun w w' => rfl⟩
end GlobalTheory.CompanionTheory.SchrModel
