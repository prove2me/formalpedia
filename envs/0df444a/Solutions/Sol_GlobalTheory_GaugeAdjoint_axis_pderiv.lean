-- Prove2me | solution 1 for GlobalTheory.GaugeAdjoint.axis_pderiv
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T17:59:59.698578+00:00
-- url     : https://prove2.me/submissions/62b7f8ee-2b29-4fab-b141-2ae829e64f37

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_ConnectionKillsSeries
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_RingsOfIntegers_IntAASubstOfHasSubst
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_FormalExpMulFormalExpNeg
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_RingsOfIntegers_ConstantCoeffEv
import Theorems.Thm_GlobalTheory_GaugeAdjoint_const_pt
import Theorems.Thm_GlobalTheory_GaugeAdjoint_ev_origin
import Theorems.Thm_GlobalTheory_GaugeAdjoint_ev_ev_one
import Theorems.Thm_GlobalTheory_GaugeAdjoint_const_axis
import Theorems.Thm_GlobalTheory_GaugeAdjoint_axis_pt_one
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
open MvPowerSeries ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.TB
open GlobalTheory GlobalTheory.GaugeAdjoint
open GlobalTheory.FormalCalc GlobalTheory.IntSeries
variable {k : Type} [CommRing k] {d m n p : ℕ}
namespace GlobalTheory.GaugeAdjoint
theorem _root_.solution (φ : PS k 1 d) (i : Fin d) :
    ev (n := 1) ![pt k d 0, 0] (ev (n := 2) ![pt k d 1] (pderiv k ((0 : Fin 1), i) φ)) =
      C (coeff (Finsupp.single ((0 : Fin 1), i) 1) φ) := by
  rw [ev_ev_one (fun i => const_pt 1 i) const_axis, axis_pt_one, ev_origin]
  congr 1
  rw [← coeff_zero_eq_constantCoeff_apply, coeff_pderiv]
  simp
end GlobalTheory.GaugeAdjoint
