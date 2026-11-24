-- Prove2me | solution 1 for GlobalTheory.FormalCalc.coeff_law_fst
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T15:09:42.694017+00:00
-- url     : https://prove2.me/submissions/6fd7420f-13ee-48ec-a85c-234c80ae9139

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_ConnectionKillsSeries
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_NatCastMulCoeffOfPderivEq
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_RingsOfIntegers_CoeffSingleLawAdd
import Theorems.Thm_GlobalTheory_FormalCalc_coeff_single_ev_two
import Theorems.Thm_GlobalTheory_FormalCalc_coeff_single_X
import Theorems.Thm_GlobalTheory_FormalCalc_constantCoeff_pt
import Theorems.Thm_GlobalTheory_FormalCalc_coeff_law_snd

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
open MvPowerSeries ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.TB
open GlobalTheory GlobalTheory.FormalCalc
variable {R : Type} [CommRing R] {d : ℕ}
namespace GlobalTheory.FormalCalc
theorem _root_.solution (G : FGLaw R d) (i l : Fin d) :
    coeff (Finsupp.single ((0 : Fin 2), l) 1) (G.F i) = if l = i then 1 else 0 := by
  have hc := congrArg (coeff (Finsupp.single ((0 : Fin 2), l) 1)) (G.comm i)
  rw [coeff_single_ev_two (n := 2) (pt R d 1) (pt R d 0) (fun m => constantCoeff_pt 1 m)
    (fun m => constantCoeff_pt 0 m)] at hc
  rw [← hc]
  simp [pt, coeff_single_X, coeff_law_snd, mul_boole, Finset.sum_ite_eq, Finset.sum_ite_eq']
end GlobalTheory.FormalCalc
