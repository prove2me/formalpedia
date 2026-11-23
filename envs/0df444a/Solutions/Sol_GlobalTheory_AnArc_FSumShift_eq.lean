-- Prove2me | solution 1 for GlobalTheory.AnArc.FSumShift_eq
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T16:33:58.514548+00:00
-- url     : https://prove2.me/submissions/486b3706-9578-4827-899b-e01012d93067

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ArchimedeanThetaValues_DegeneratingToriPeriodMapEqBaseOfYEqZero
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ArchimedeanThetaValues_CoeffFSumDerivEqFderiv
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaShiftProofs_FormalThetaSumShiftPeriodDiv
import Theorems.Thm_GlobalTheory_AnArc_term_add_P0_div
import Theorems.Thm_GlobalTheory_AnArc_coeff_FSum
import Theorems.Thm_GlobalTheory_AnArc_coeff_FSumShift


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (hermForm eTwoPi)
open GlobalTheory.AnArc
variable {O : Type} [CommRing O] [StarRing O] (A : AnArc O)
variable (k : ℕ) [NeZero k]
namespace GlobalTheory.AnArc
theorem _root_.solution (la : A.La) {α : A.X} {m : ℤ} (hm : A.be la.y α = k * m) (th : (Fin A.gB → ℂ) → ℂ) (v : A.V) :
    A.FSumShift k α th la v =
      HahnSeries.single m (Complex.exp (A.lin la v)) * A.FSum k (α + la.y) (A.shift k la α th) v := by
  ext n
  rw [coeff_FSumShift, hm, Int.mul_ediv_cancel_left _ (NeZero.ne (k : ℤ))]
  conv_rhs => rw [← sub_add_cancel n m, HahnSeries.coeff_single_mul_add, coeff_FSum, Finset.mul_sum]
  exact Finset.sum_congr rfl fun μ _ => A.term_add_P0_div k la α th μ v
end GlobalTheory.AnArc
