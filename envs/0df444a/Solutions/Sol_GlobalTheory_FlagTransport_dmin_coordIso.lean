-- Prove2me | solution 1 for GlobalTheory.FlagTransport.dmin_coordIso
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T18:12:41.835265+00:00
-- url     : https://prove2.me/submissions/e212064f-b635-4d1a-b6ae-417a85ed3016

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_HaarChart
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_LintegralTransportHermitianFrameChartMeasure
import Theorems.Thm_GlobalTheory_FlagTransport_nmat_coordIso
import Theorems.Thm_GlobalTheory_FlagTransport_gram_cpt_base

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
theorem _root_.solution (hp : X.p0 = X'.p0) (z : V (nd X)) (τ' : X'.Ψ) (i : Fin (r + 1)) :
    dmin X'.Gm (cpt X' (baseFr X') (coordIso X X' e z)) τ' i = dmin X.Gm (cpt X (baseFr X) z) (e.symm τ') i := by
  have h2 : mat (nmat X' (coordIso X X' e z)) τ' = mat (nmat X z) (e.symm τ') := by
    unfold mat; rw [nmat_coordIso]
  unfold dmin
  rw [gram_cpt_base, gram_cpt_base, h2, hp]
end GlobalTheory.FlagTransport
