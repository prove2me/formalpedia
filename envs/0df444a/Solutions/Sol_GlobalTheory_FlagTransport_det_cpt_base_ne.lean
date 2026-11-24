-- Prove2me | solution 1 for GlobalTheory.FlagTransport.det_cpt_base_ne
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T15:09:46.59797+00:00
-- url     : https://prove2.me/submissions/02ec4082-c8ed-4fbf-bda1-36fbd87a7737

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
theorem _root_.solution {F : Type} [Field F] [NumberField F] [IsCMField F] (Y : Data F r) (z : V (nd Y)) (τ : Y.Ψ) :
    (mat (cpt Y (baseFr Y) z) τ).det ≠ 0 ↔ (mat (nmat Y z) τ).det ≠ 0 := by
  have h1 : mat (cpt Y (baseFr Y) z) τ = mat (baseFr Y) τ * mat (nmat Y z) τ := rfl
  have hB : (mat (baseFr Y) τ).det ≠ 0 := (Y.signature τ).choose_spec.1
  rw [h1, Matrix.det_mul, mul_ne_zero_iff]
  exact ⟨fun h => h.2, fun h => ⟨hB, h⟩⟩
end GlobalTheory.FlagTransport
