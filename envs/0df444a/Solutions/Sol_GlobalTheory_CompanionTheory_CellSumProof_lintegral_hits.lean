-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.CellSumProof.lintegral_hits
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T12:22:52.713382+00:00
-- url     : https://prove2.me/submissions/a47d1db5-98d0-4ef1-afa7-ad4d192073c8

import Mathlib
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_ArchimedeanBaseChange_ArchimedeanBaseChangeProof_ThetaCellCovers_KernelL2RowsColumns
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_CellSumOfCntBasic

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory
open scoped ENNReal Pointwise
open PositivityTheory.Rg.BcB.E1
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.CellSumProof
namespace GlobalTheory.CompanionTheory.CellSumProof
theorem _root_.solution (X : Ctx) {S : Set X.G} (hS : MeasurableSet S) :
    ∫⁻ x, hits X S x ∂X.ν = X.μ S := by
  haveI : MeasurableConstSMul X.Γ X.G := ⟨fun γ => measurable_const_mul (γ : X.G)⟩
  haveI : SMulInvariantMeasure X.Γ X.G X.μ := ⟨fun γ s _ => measure_preimage_mul _ γ.1 s⟩
  have hm : ∀ γ : X.Γ, AEMeasurable (fun x : X.G => S.indicator (1 : X.G → ℝ≥0∞) ((γ : X.G) * x)) X.ν :=
    fun γ => ((measurable_one.indicator hS).comp (measurable_const_mul (γ : X.G))).aemeasurable
  have h1 : ∫⁻ x, hits X S x ∂X.ν
      = ∑' γ : X.Γ, ∫⁻ x in X.F, S.indicator (1 : X.G → ℝ≥0∞) ((γ : X.G) * x) ∂X.μ := by
    unfold hits
    exact lintegral_tsum hm
  have h2 := X.fd.lintegral_eq_tsum'' (S.indicator (1 : X.G → ℝ≥0∞))
  rw [h1]
  have h3 : ∫⁻ x, S.indicator (1 : X.G → ℝ≥0∞) x ∂X.μ = X.μ S := lintegral_indicator_one hS
  rw [← h3, h2]
  rfl
end GlobalTheory.CompanionTheory.CellSumProof
