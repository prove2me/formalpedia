-- Prove2me | solution 1 for GlobalTheory.FlagTransport.idxEquiv_symm_equivFin
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T15:09:49.299798+00:00
-- url     : https://prove2.me/submissions/506e92a8-969a-49c4-b03e-7665a2f7b30d

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
theorem _root_.solution (τ' : X'.Ψ) (p : {p : Fin r × Fin r // p.2 < p.1}) :
    (idxEquiv X X' e).symm (Fintype.equivFin (Ent X') (τ', p)) = Fintype.equivFin (Ent X) (e.symm τ', p) := by
  show Fintype.equivFin (Ent X) ((entEquiv X X' e).symm
    ((Fintype.equivFin (Ent X')).symm (Fintype.equivFin (Ent X') (τ', p)))) = _
  rw [Equiv.symm_apply_apply]
  rfl
end GlobalTheory.FlagTransport
