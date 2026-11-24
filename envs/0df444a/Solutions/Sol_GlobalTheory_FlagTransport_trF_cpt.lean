-- Prove2me | solution 1 for GlobalTheory.FlagTransport.trF_cpt
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T15:45:28.083988+00:00
-- url     : https://prove2.me/submissions/6399423a-230e-4d88-a6e4-8a8c1af2c31f

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_HaarChart
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_LintegralTransportHermitianFrameChartMeasure
import Theorems.Thm_GlobalTheory_FlagTransport_nmat_coordIso

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
theorem _root_.solution (z : V (nd X)) :
    trF X X' e (cpt X (baseFr X) z) = cpt X' (baseFr X') (coordIso X X' e z) := by
  funext τ'
  have hB : IsUnit (mat (baseFr X) (e.symm τ')).det :=
    isUnit_iff_ne_zero.2 (X.signature (e.symm τ')).choose_spec.1
  have h1 : mat (cpt X (baseFr X) z) (e.symm τ') =
      mat (baseFr X) (e.symm τ') * mat (nmat X z) (e.symm τ') := rfl
  have h2 : mat (nmat X' (coordIso X X' e z)) τ' = mat (nmat X z) (e.symm τ') := by
    unfold mat; rw [nmat_coordIso]
  show (mat (baseFr X') τ' * (mat (baseFr X) (e.symm τ'))⁻¹ * mat (cpt X (baseFr X) z) (e.symm τ') :
      Matrix (Fin r) (Fin r) ℂ) = (mat (baseFr X') τ' * mat (nmat X' (coordIso X X' e z)) τ' : Matrix (Fin r) (Fin r) ℂ)
  rw [h1, h2, Matrix.mul_assoc, Matrix.nonsing_inv_mul_cancel_left _ _ hB]
end GlobalTheory.FlagTransport
