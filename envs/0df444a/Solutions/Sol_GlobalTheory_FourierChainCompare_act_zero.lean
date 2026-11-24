-- Prove2me | solution 1 for GlobalTheory.FourierChainCompare.act_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T19:10:22.973352+00:00
-- url     : https://prove2.me/submissions/76475e93-9b6e-4a97-902a-f8c39ba0810b

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_FourierCoeffIntSt
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_JetGauges_PerfectPairings
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_RingsOfIntegers_FormalGroupLawCompMulNZero
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ThetaMetrics_EqZeroOrSingleOfDegreeLtTwo
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_JetHarmonics_AddCharMemValuationSubring
import Theorems.Thm_GlobalTheory_FormalCalc_formalExp_zero
import Theorems.Thm_GlobalTheory_FormalCalc_formalLog_one
import Theorems.Thm_GlobalTheory_FormalMulN_dLin_add
import Theorems.Thm_GlobalTheory_FormalSeries_eq_of_forall_le_order_sub
import Theorems.Thm_GlobalTheory_FormalSeries_jacobian_X
import Theorems.Thm_GlobalTheory_FormalSeries_jacobian_apply
import Theorems.Thm_GlobalTheory_FormalSeries_le_order_subst_sub_subst
import Theorems.Thm_GlobalTheory_FormalSeries_two_le_order_iff
import Theorems.Thm_GlobalTheory_GaugeAdjoint_const_one
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.FormalCalc.formalExp_zero
attribute [local simp] GlobalTheory.FormalCalc.formalLog_one
attribute [local simp] GlobalTheory.FormalSeries.jacobian_X
attribute [local simp] GlobalTheory.FormalSeries.jacobian_apply



set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open MvPowerSeries ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.TB GlobalTheory.IndefiniteRowSideFullHecke.PerfectPairings
open GlobalTheory GlobalTheory.FourierChainCompare
variable {R : Type} [CommRing R] {d : ℕ}
namespace GlobalTheory.FourierChainCompare
theorem _root_.solution {O : Type} [CommRing O] {G : FGLaw R d} (A : OAct O G) : A.act 0 = 0 := by
  have hc := A.const 0
  have h1 : A.act 0 = G.add (A.act 0) (A.act 0) := by rw [← A.add_act, add_zero]
  have h2 : A.act 0 = comp1 (A.act 0) (A.act 0) := by rw [← A.mul_act, mul_zero]
  have h3 : dLin (A.act 0) = 0 := by
    have := GlobalTheory.FormalMulN.dLin_add G hc hc
    rw [← h1] at this
    exact left_eq_add.mp this
  have h4 : ∀ i, 2 ≤ (A.act 0 i).order := fun i =>
    GlobalTheory.FormalSeries.two_le_order_iff.mpr ⟨hc i, fun j => by
      obtain ⟨j0, j⟩ := j
      obtain rfl : j0 = 0 := Subsingleton.elim _ _
      exact congrFun (congrFun h3 i) j⟩
  have h5 : ∀ (k : ℕ) i, (k : ℕ∞) ≤ (A.act 0 i).order := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      intro i
      have := GlobalTheory.FormalSeries.le_order_subst_sub_subst
        (a := fun p : Fin 1 × Fin d => (![A.act 0] : Fin 1 → Pt R 1 d) p.1 p.2) (b := 0) (k := k)
        (fun p => GlobalTheory.GaugeAdjoint.const_one hc p.1 p.2) (by simp)
        (fun p => by simpa using ih p.2) (h4 i)
      rw [subst_zero_of_constantCoeff_zero (hc i), sub_zero] at this
      rw [congrFun h2 i]
      exact this
  funext i
  exact GlobalTheory.FormalSeries.eq_of_forall_le_order_sub fun k => by simpa using h5 k i
end GlobalTheory.FourierChainCompare
