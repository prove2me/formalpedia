-- Prove2me | solution 1 for GlobalTheory.NablaExpConj.Dof_expS
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T00:38:57.709254+00:00
-- url     : https://prove2.me/submissions/6f24c275-3eb0-44f8-be1b-fcbdc799a577

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_ConnectionKillsSeries
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_FormalExpMulFormalExpNeg
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_RingsOfIntegers_ExpSNegMulExpS
import Theorems.Thm_GlobalTheory_FormalCalc_pderiv_formalExp


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open MvPowerSeries ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.TB
open GlobalTheory GlobalTheory.NablaExpConj
variable {R : Type} [CommRing R] {d : ℕ} {O : Type} [CommRing O] [StarRing O]
variable (k : Type) [CommRing k] [Algebra ℚ k] [Algebra R k]
namespace GlobalTheory.NablaExpConj
theorem _root_.solution (F : Fin d → PS k 2 d) (u : Fin d → k) {g : PS k 1 d}
    (hg : constantCoeff g = 0) : Dof F u (FB.expS k g) = FB.expS k g * Dof F u g := by
  have e : ∀ i, pderiv k i (FB.expS k g) = FB.expS k g * pderiv k i g :=
    FormalCalc.pderiv_formalExp hg
  unfold Dof
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [e]
  ring
end GlobalTheory.NablaExpConj
