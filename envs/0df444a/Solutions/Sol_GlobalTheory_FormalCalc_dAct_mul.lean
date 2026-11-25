-- Prove2me | solution 1 for GlobalTheory.FormalCalc.dAct_mul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T00:16:29.460205+00:00
-- url     : https://prove2.me/submissions/c7755801-aa78-4b19-b87b-804d8d32f1ca

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_ConnectionKillsSeries
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_RingsOfIntegers_CoeffSingleLawAdd
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_RingsOfIntegers_BetaHSumSmulRight
import Theorems.Thm_GlobalTheory_FormalCalc_coeff_single_subst


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
variable {R : Type} [CommRing R] {d : ℕ} {O : Type} [CommRing O] [StarRing O]
  (k : Type) [CommRing k] [Algebra R k]
namespace GlobalTheory.FormalCalc
theorem _root_.solution (B : FB R d O) (a b : O) : dAct k B (a * b) = dAct k B a * dAct k B b := by
  ext i j
  simp only [dAct, FB.actK, coeff_map, Matrix.mul_apply]
  rw [B.A.mul_act]
  unfold comp1 ev
  rw [coeff_single_subst, Fintype.sum_prod_type, Fin.sum_univ_one, map_sum]
  · refine Finset.sum_congr rfl fun l _ => ?_
    rw [map_mul]
    rfl
  · rintro ⟨s, l⟩
    fin_cases s
    exact B.A.const b l
end GlobalTheory.FormalCalc
