-- Prove2me | solution 1 for GlobalTheory.FormalCalc.dAct_add_and_one
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T00:10:01.38866+00:00
-- url     : https://prove2.me/submissions/b9339bed-cb37-4741-a2f0-30a5fbb5101a

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_ConnectionKillsSeries
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_NatCastMulCoeffOfPderivEq
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_RingsOfIntegers_CoeffSingleLawAdd
import Theorems.Thm_GlobalTheory_FormalCalc_coeff_single_X
import Theorems.Thm_GlobalTheory_FormalCalc_coeff_single_law_add

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
theorem _root_.solution : ∀ (R : Type) [CommRing R] (d : ℕ) (O : Type) [CommRing O] [StarRing O]
    (k : Type) [CommRing k] [Algebra ℚ k] [Algebra R k] (B : FB R d O),
    (∀ a b : O, dAct k B (a + b) = dAct k B a + dAct k B b) ∧ dAct k B 1 = 1 := by
  intro R _ d O _ _ k _ _ _ B
  constructor
  · intro a b
    ext i j
    rw [Matrix.add_apply]
    unfold dAct FB.actK
    rw [B.A.add_act]
    simp only [coeff_map]
    rw [coeff_single_law_add B.G (B.A.act a) (B.A.act b) (B.A.const a) (B.A.const b), map_add]
  · ext i j
    unfold dAct FB.actK
    simp only [B.A.one_act, coeff_map, Matrix.one_apply, pt, coeff_single_X, Prod.mk.injEq, true_and]
    rcases eq_or_ne i j with rfl | h
    · simp
    · simp [h, Ne.symm h]
end GlobalTheory.FormalCalc
