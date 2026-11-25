-- Prove2me | solution 1 for GlobalTheory.NablaExpConj.Dx_mul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T00:40:53.712344+00:00
-- url     : https://prove2.me/submissions/a0b7b694-d431-44d3-8910-8ad8624b0c4c

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_ConnectionKillsSeries
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_FormalExpMulFormalExpNeg
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_RingsOfIntegers_ExpSNegMulExpS
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
theorem _root_.solution (B : FB R d O) (u : Fin d → k) (f G : AA k d) :
    Dx k B u (f * G) = Dx k B u f * G + f * Dx k B u G := by
  simp only [Dx, Derivation.leibniz, smul_eq_mul, Finset.sum_mul, Finset.mul_sum,
    ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun t _ => by ring
end GlobalTheory.NablaExpConj
