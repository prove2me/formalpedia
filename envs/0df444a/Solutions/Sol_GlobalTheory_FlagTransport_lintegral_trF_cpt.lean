-- Prove2me | solution 1 for GlobalTheory.FlagTransport.lintegral_trF_cpt
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T17:42:31.310389+00:00
-- url     : https://prove2.me/submissions/e0748321-b3ed-4e16-97d1-a663ee633822

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_HaarChart
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_LintegralTransportHermitianFrameChartMeasure
import Theorems.Thm_GlobalTheory_FlagTransport_trF_cpt
import Theorems.Thm_GlobalTheory_FlagTransport_map_muF

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
namespace GlobalTheory.FlagTransport
theorem _root_.solution : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} {E' : Type} [Field E']
    [NumberField E'] [IsCMField E'] (X : Data E r) (X' : Data E' r) (e : X.Ψ ≃ X'.Ψ), X.p0 = X'.p0 →
    ∀ (φ : Frame X'.Ψ r → ℝ≥0∞), Measurable φ →
      ∫⁻ z, φ (trF X X' e (cpt X (baseFr X) z)) ∂muF X (baseFr X) =
        ∫⁻ z, φ (cpt X' (baseFr X') z) ∂muF X' (baseFr X') := by
  intro E _ _ _ r E' _ _ _ X X' e hp φ _
  rw [← map_muF e hp, lintegral_map_equiv]
  simp_rw [trF_cpt]
  rfl
end GlobalTheory.FlagTransport
