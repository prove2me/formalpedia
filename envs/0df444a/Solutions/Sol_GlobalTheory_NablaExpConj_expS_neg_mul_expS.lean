-- Prove2me | solution 1 for GlobalTheory.NablaExpConj.expS_neg_mul_expS
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T00:43:45.699716+00:00
-- url     : https://prove2.me/submissions/bfddbf62-6e69-41ff-9a44-d3f032853981

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_ConnectionKillsSeries
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_FormalExpMulFormalExpNeg
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_RingsOfIntegers_ExpSNegMulExpS
import Theorems.Thm_GlobalTheory_FormalCalc_formalExp_mul_formalExp_neg


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
theorem _root_.solution {n : ℕ} {g : PS k n d} (hg : constantCoeff g = 0) :
    FB.expS k (-g) * FB.expS k g = 1 := by
  rw [mul_comm]
  exact FormalCalc.formalExp_mul_formalExp_neg hg
end GlobalTheory.NablaExpConj
