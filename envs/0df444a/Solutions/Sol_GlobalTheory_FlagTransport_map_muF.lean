-- Prove2me | solution 1 for GlobalTheory.FlagTransport.map_muF
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T19:12:05.401715+00:00
-- url     : https://prove2.me/submissions/72e4bc56-e06e-4e56-a4ec-b426941a6e54

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_HaarChart
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_LintegralTransportHermitianFrameChartMeasure
import Theorems.Thm_GlobalTheory_FlagTransport_coordIso_mp
import Theorems.Thm_GlobalTheory_FlagTransport_map_restrict_withDensity
import Theorems.Thm_GlobalTheory_FlagTransport_mem_dom_coordIso
import Theorems.Thm_GlobalTheory_FlagTransport_densF_coordIso

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
variable {X X'}
namespace GlobalTheory.FlagTransport
theorem _root_.solution (hp : X.p0 = X'.p0) :
    Measure.map (coordIso X X' e).toHomeomorph.toMeasurableEquiv (muF X (baseFr X)) = muF X' (baseFr X') := by
  unfold muF
  refine map_restrict_withDensity _ (coordIso_mp X X' e) ?_ ?_
  · ext z
    exact mem_dom_coordIso e hp z
  · intro z
    exact congrArg ENNReal.ofReal (densF_coordIso e hp z)
end GlobalTheory.FlagTransport
