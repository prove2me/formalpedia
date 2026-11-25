-- Prove2me | solution 1 for GlobalTheory.IndefiniteRowSideFullHecke.FlagSectionAction.zAct_rmul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T02:51:37.94468+00:00
-- url     : https://prove2.me/submissions/5d027a33-6e42-4b35-a85d-0801f5f817b6

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_RdOrbIntOfLatZ
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_UnifDom
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_FourierCoefficientDomain
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_FderivIntegralApplyOfHolomorphicOfDominated
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_ExistenceTori_CoefMemFlagSec

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.IndefiniteRowSideFullHecke GlobalTheory.IndefiniteRowSideFullHecke.FlagSectionAction
open NumberField MeasureTheory ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj Formalism.L2.Pj.FJ
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r ρ : ℕ}
namespace GlobalTheory.IndefiniteRowSideFullHecke.FlagSectionAction
theorem _root_.solution (X : Data E r) (cu : FJ.CuspFD X ρ) (t : Fin (nZ X ρ) → ℝ) (x b : Frame X.Ψ r) :
    zAct X cu t (rmul x b) = rmul (zAct X cu t x) b := by
  funext τ
  exact (Matrix.mul_assoc _ (mat x τ) (mat b τ)).symm
end GlobalTheory.IndefiniteRowSideFullHecke.FlagSectionAction
