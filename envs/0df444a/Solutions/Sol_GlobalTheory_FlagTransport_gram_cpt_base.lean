-- Prove2me | solution 1 for GlobalTheory.FlagTransport.gram_cpt_base
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T17:57:23.612341+00:00
-- url     : https://prove2.me/submissions/bebfd836-b61b-4fc0-84fa-5289b90b865a

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_HaarChart
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_LintegralTransportHermitianFrameChartMeasure
import Theorems.Thm_GlobalTheory_FlagTransport_gram_mul_right
import Theorems.Thm_GlobalTheory_IndefiniteRowSideFullHecke_UnitaryHaarVolume_baseFr_mem


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
    gram τ.1 Y.Gm (mat (cpt Y (baseFr Y) z) τ) =
      (mat (nmat Y z) τ)ᵀ * sgnMat r Y.p0 * (mat (nmat Y z) τ).map (starRingEnd ℂ) := by
  have h1 : mat (cpt Y (baseFr Y) z) τ = mat (baseFr Y) τ * mat (nmat Y z) τ := rfl
  rw [h1, gram_mul_right, baseFr_mem Y τ]
end GlobalTheory.FlagTransport
