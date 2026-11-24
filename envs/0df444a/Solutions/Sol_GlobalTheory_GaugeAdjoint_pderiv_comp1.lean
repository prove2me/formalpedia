-- Prove2me | solution 1 for GlobalTheory.GaugeAdjoint.pderiv_comp1
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T17:43:33.704555+00:00
-- url     : https://prove2.me/submissions/6b6af029-bc74-4335-b414-e4d615901632

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_ConnectionKillsSeries
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_RingsOfIntegers_IntAASubstOfHasSubst
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_FormalExpMulFormalExpNeg
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_RingsOfIntegers_ConstantCoeffEv
import Theorems.Thm_GlobalTheory_GaugeAdjoint_pderiv_ev
import Theorems.Thm_GlobalTheory_GaugeAdjoint_const_pt
import Theorems.Thm_GlobalTheory_GaugeAdjoint_const_one
import Theorems.Thm_GlobalTheory_GaugeAdjoint_pderiv_pt
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
theorem _root_.solution (φ : Pt k 1 d) (j j' : Fin n) (i l : Fin d) :
    pderiv k (j, i) (comp1 φ (pt k d j') l) =
      if j' = j then ev ![pt k d j'] (pderiv k ((0 : Fin 1), i) (φ l)) else 0 := by
  show pderiv k (j, i) (ev ![pt k d j'] (φ l)) = _
  rw [pderiv_ev (const_one (fun i => const_pt j' i))]
  by_cases hj : j' = j
  · subst hj
    simp [pderiv_pt]
  · simp [pderiv_pt, hj]
end GlobalTheory.GaugeAdjoint
