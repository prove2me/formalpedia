-- Prove2me | solution 1 for GlobalTheory.GaugeAdjoint.pderiv_right
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T17:59:48.581621+00:00
-- url     : https://prove2.me/submissions/1204d519-fdb0-457e-b597-e3a6b9cbaacf

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_ConnectionKillsSeries
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_RingsOfIntegers_IntAASubstOfHasSubst
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_FormalExpMulFormalExpNeg
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_RingsOfIntegers_ConstantCoeffEv
import Theorems.Thm_GlobalTheory_GaugeAdjoint_pderiv_ev
import Theorems.Thm_GlobalTheory_GaugeAdjoint_const_pt
import Theorems.Thm_GlobalTheory_GaugeAdjoint_const_two
import Theorems.Thm_GlobalTheory_GaugeAdjoint_const_comp1
import Theorems.Thm_GlobalTheory_GaugeAdjoint_pderiv_pt
import Theorems.Thm_GlobalTheory_GaugeAdjoint_pderiv_comp1
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
theorem _root_.solution {φ : Pt k 1 d} (hφ : ∀ i, constantCoeff (φ i) = 0) (f : PS k 2 d)
    (i : Fin d) :
    pderiv k ((1 : Fin 2), i) (ev (n := 2) ![pt k d 0, comp1 φ (pt k d 1)] f) =
      ∑ j, ev (n := 2) ![pt k d 0, comp1 φ (pt k d 1)] (pderiv k ((1 : Fin 2), j) f) *
        ev (n := 2) ![pt k d 1] (pderiv k ((0 : Fin 1), i) (φ j)) := by
  rw [pderiv_ev (const_two (fun i => const_pt 0 i) (const_comp1 hφ (fun i => const_pt 1 i)))]
  simp [Fin.sum_univ_two, pderiv_comp1, pderiv_pt]
end GlobalTheory.GaugeAdjoint
