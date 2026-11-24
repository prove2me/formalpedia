-- Prove2me | solution 1 for GlobalTheory.ThK.Dbl.LD.cont_toGL
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T21:28:52.203511+00:00
-- url     : https://prove2.me/submissions/eedca1a5-d6ac-427e-b7cb-10c5b6177d4a

import Mathlib
import Definitions.Def_Development_WeilBound_ThetaLifts_LatticeBasics_LocDistB
import Definitions.Def_Development_WeilBound_ThetaLifts_LatticeBasics_LocDistD
import Definitions.Def_Development_WeilBound_ThetaLifts_LatticeBasics_LocDistE
import Theorems.Thm_GlobalTheory_ThK_Dbl_LD_toGL_val

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Filter Topology GlobalTheory.WeilM Matrix
open GlobalTheory GlobalTheory.ThK GlobalTheory.ThK.Dbl GlobalTheory.ThK.Dbl.LD
variable {k : Type} [Field k] [TopologicalSpace k] [IsTopologicalRing k] [ContinuousInv₀ k] [T2Space k] {d : ℕ}
namespace GlobalTheory.ThK.Dbl.LD
theorem _root_.solution : ContinuousOn (toGL (k := k) (d := d)) {X | X.det ≠ 0} := by
  rw [continuousOn_iff_continuous_restrict, Units.continuous_iff]
  refine ⟨continuous_subtype_val.congr fun X => (toGL_val X.2).symm, ?_⟩
  have : ContinuousOn (fun X : Matrix (Fin d) (Fin d) k => X⁻¹) {X | X.det ≠ 0} := fun X hX =>
    (continuousAt_matrix_inv X (by rw [Ring.inverse_eq_inv']; exact continuousAt_inv₀ hX)).continuousWithinAt
  refine this.restrict.congr fun X => ?_
  rw [coe_units_inv]
  exact congrArg _ (toGL_val X.2).symm
end GlobalTheory.ThK.Dbl.LD
