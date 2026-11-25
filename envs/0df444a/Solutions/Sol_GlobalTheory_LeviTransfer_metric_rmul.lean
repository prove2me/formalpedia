-- Prove2me | solution 1 for GlobalTheory.LeviTransfer.metric_rmul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T03:33:55.545555+00:00
-- url     : https://prove2.me/submissions/b28c486d-2f5b-4143-9e8b-94b3019448b9

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_WeightFunctionOnFrames
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_LUStatementPf
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_OrthoStatementPf
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_InterpStatementPfH
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_RhGradFPfA
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TorusHaarMeasure_BorelDiagNeZero
import Theorems.Thm_GlobalTheory_LeviTransfer_borel_char_ne_zero
import Theorems.Thm_GlobalTheory_LeviTransfer_normFactor_pos
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Ck_normSq
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Smooth_normSq


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.L2DbarEstimates MeasureTheory Topology
open scoped ContDiff ENNReal Matrix
open GlobalTheory GlobalTheory.LeviTransfer
variable {E : Type} [Field E] [NumberField E] [IsCMField E]
namespace GlobalTheory.LeviTransfer
theorem _root_.solution (h : NfacRmulStatement (E := E)) {r : ℕ} (X : Data E r) (la : Wt X.Ψ r)
    {x b : Frame X.Ψ r} (hx : x ∈ X.dom) (hb : b ∈ Bor X.Ψ r) :
    phla X la (rmul x b) = phla X la x + Real.log (Complex.normSq (bchar la b)) := by
  have h1 := normFactor_pos X la hx
  have h2 : 0 < ‖bchar la b‖ := norm_pos_iff.2 (borel_char_ne_zero hb la)
  unfold phla
  rw [h r X la x hx b hb, Real.log_mul (inv_pos.2 h2).ne' h1.ne', Real.log_inv,
    Complex.normSq_eq_norm_sq, Real.log_pow]
  push_cast
  ring
end GlobalTheory.LeviTransfer
