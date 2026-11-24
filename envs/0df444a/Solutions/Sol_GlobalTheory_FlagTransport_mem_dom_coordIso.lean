-- Prove2me | solution 1 for GlobalTheory.FlagTransport.mem_dom_coordIso
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T18:33:44.949687+00:00
-- url     : https://prove2.me/submissions/1c10bb5a-10fa-4e77-b1b9-08f9a00f1b05

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_HaarChart
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_LintegralTransportHermitianFrameChartMeasure
import Theorems.Thm_GlobalTheory_FlagTransport_nmat_coordIso
import Theorems.Thm_GlobalTheory_FlagTransport_dmin_coordIso
import Theorems.Thm_GlobalTheory_FlagTransport_det_cpt_base_ne

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
theorem _root_.solution (hp : X.p0 = X'.p0) (z : V (nd X)) :
    cpt X' (baseFr X') (coordIso X X' e z) ∈ X'.dom ↔ cpt X (baseFr X) z ∈ X.dom := by
  show (∀ τ' : X'.Ψ, _ ∧ _) ↔ (∀ τ : X.Ψ, _ ∧ _)
  refine Iff.trans ?_ e.symm.forall_congr_right
  refine forall_congr' fun τ' => ?_
  have h2 : mat (nmat X' (coordIso X X' e z)) τ' = mat (nmat X z) (e.symm τ') := by
    unfold mat; rw [nmat_coordIso]
  rw [det_cpt_base_ne, det_cpt_base_ne, h2, hp]
  simp only [dmin_coordIso e hp]
end GlobalTheory.FlagTransport
