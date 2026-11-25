-- Prove2me | solution 1 for GlobalTheory.NablaExpConj.Dx_liftX
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T01:00:57.051557+00:00
-- url     : https://prove2.me/submissions/0f00552b-647c-4bbc-9c22-986681bdd16b

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_ConnectionKillsSeries
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_FormalExpMulFormalExpNeg
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_RingsOfIntegers_ExpSNegMulExpS
import Theorems.Thm_GlobalTheory_NablaExpConj_liftX_mul
import Theorems.Thm_GlobalTheory_NablaExpConj_liftX_sum
import Theorems.Thm_GlobalTheory_NablaExpConj_pderiv_inl_liftX
import Theorems.Thm_GlobalTheory_FormalCalc_formalExp_zero
import Theorems.Thm_GlobalTheory_FormalCalc_formalLog_one
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.FormalCalc.formalExp_zero
attribute [local simp] GlobalTheory.FormalCalc.formalLog_one



set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open MvPowerSeries ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.TB
open GlobalTheory GlobalTheory.NablaExpConj
variable {R : Type} [CommRing R] {d : ℕ} {O : Type} [CommRing O] [StarRing O]
variable (k : Type) [CommRing k] [Algebra ℚ k] [Algebra R k]
omit [Algebra ℚ k]
namespace GlobalTheory.NablaExpConj
theorem _root_.solution (B : FB R d O) (u : Fin d → k) (f : PS k 1 d) :
    Dx k B u (liftX k f) = liftX k (Dof (B.FK k) u f) := by
  simp only [Dx, Dof, pderiv_inl_liftX, liftX_sum, liftX_mul]
end GlobalTheory.NablaExpConj
