-- Prove2me | solution 1 for GlobalTheory.FlagTransport.map_restrict_withDensity
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T15:09:50.002058+00:00
-- url     : https://prove2.me/submissions/3f9b2290-5e4d-499e-acb9-74cfc12d5703

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_HaarChart
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_LintegralTransportHermitianFrameChartMeasure

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField MeasureTheory ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.L2DbarEstimates GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHaarVolume GlobalTheory.FlagQuotHaar
open scoped ENNReal
open scoped Matrix
open GlobalTheory GlobalTheory.FlagTransport
noncomputable section
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}
  {E' : Type} [Field E'] [NumberField E'] [IsCMField E']
variable (X : Data E r) (X' : Data E' r) (e : X.Ψ ≃ X'.Ψ)
namespace GlobalTheory.FlagTransport
theorem _root_.solution {α β : Type*} [MeasurableSpace α] [MeasurableSpace β] {μ : Measure α}
    {ν : Measure β} (S : α ≃ᵐ β) (hS : MeasurePreserving S μ ν) {Ω : Set α} {Ω' : Set β}
    (hΩ : S ⁻¹' Ω' = Ω) {d : α → ℝ≥0∞} {d' : β → ℝ≥0∞} (hd : ∀ x, d' (S x) = d x) :
    Measure.map S ((μ.restrict Ω).withDensity d) = (ν.restrict Ω').withDensity d' := by
  ext A hA
  rw [S.map_apply, withDensity_apply _ hA, withDensity_apply _ (S.measurable hA), ← hS.map_eq,
    S.restrict_map, S.restrict_map, lintegral_map_equiv, hΩ]
  simp_rw [hd]
end GlobalTheory.FlagTransport
