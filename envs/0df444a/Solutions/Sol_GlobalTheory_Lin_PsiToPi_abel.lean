-- Prove2me | solution 1 for GlobalTheory.Lin.PsiToPi.abel
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T19:00:43.255053+00:00
-- url     : https://prove2.me/submissions/efb00cb5-3602-4e1a-92a4-94187a4b2eab

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_GlobalTwisting_ZerosDisc
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_PrimeCountRelativeErrorOfPsiRelativeError
import Theorems.Thm_GlobalTheory_Lin_PsiToPi_contOn_w
import Theorems.Thm_GlobalTheory_Lin_PsiToPi_cnt_eq

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Complex DirichletCharacter ArithmeticFunction MeasureTheory Filter Topology GlobalTheory.Lin
open scoped Classical
open GlobalTheory GlobalTheory.Lin GlobalTheory.Lin.PsiToPi
open Formalism.HermitianLattices.GL2PrimeSums (Li Emain)
namespace GlobalTheory.Lin.PsiToPi
theorem _root_.solution (P : ℕ → Prop) {Y X : ℝ} (hY : 1 < Y) (hYX : Y ≤ X) :
    cnt P X - cnt P Y = (∑ k ∈ Finset.Icc 0 ⌊X⌋₊, wt P k) / Real.log X - (∑ k ∈ Finset.Icc 0 ⌊Y⌋₊, wt P k) / Real.log Y +
      ∫ t in Y..X, 1 / (t * Real.log t ^ 2) * ∑ k ∈ Finset.Icc 0 ⌊t⌋₊, wt P k := by
  have hd : ∀ t ∈ Set.Icc Y X, HasDerivAt (fun t : ℝ => 1 / Real.log t) (-(1 / (t * Real.log t ^ 2))) t := by
    intro t ht
    have h1 : 1 < t := lt_of_lt_of_le hY ht.1
    have hl := Real.log_pos h1
    refine HasDerivAt.congr_deriv (f := fun t : ℝ => 1 / Real.log t)
      ((hasDerivAt_const t (1 : ℝ)).div (Real.hasDerivAt_log (by linarith : t ≠ 0)) hl.ne') ?_
    field_simp; ring
  have hint : IntegrableOn (deriv fun t : ℝ => 1 / Real.log t) (Set.Icc Y X) :=
    ((contOn_w hY).neg.congr fun t ht => (hd t ht).deriv).integrableOn_Icc
  have h := sum_mul_eq_sub_sub_integral_mul (wt P) (f := fun t : ℝ => 1 / Real.log t) (by linarith) hYX
    (fun t ht => (hd t ht).differentiableAt) hint
  rw [cnt_eq, cnt_eq, ← Finset.sum_Ioc_consecutive _ (Nat.zero_le ⌊Y⌋₊) (Nat.floor_le_floor hYX),
    add_sub_cancel_left, h, intervalIntegral.integral_of_le hYX, sub_eq_add_neg _ (∫ t in _, _), ← integral_neg]
  congr 1
  · ring
  · refine setIntegral_congr_fun measurableSet_Ioc fun t ht => ?_
    rw [(hd t (Set.Ioc_subset_Icc_self ht)).deriv]; ring
end GlobalTheory.Lin.PsiToPi
