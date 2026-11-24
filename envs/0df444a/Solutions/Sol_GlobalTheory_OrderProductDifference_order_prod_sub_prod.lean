-- Prove2me | solution 1 for GlobalTheory.OrderProductDifference.order_prod_sub_prod
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T19:19:55.095955+00:00
-- url     : https://prove2.me/submissions/aaed57fa-a929-4e25-8222-86c2b9883801

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_OrderProdSubProd

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.OrderProductDifference
open MvPowerSeries
namespace GlobalTheory.OrderProductDifference
theorem _root_.solution {R τ ι : Type} [CommRing R] (s : Finset ι)
    (a b : ι → MvPowerSeries τ R) (k : ι → ℕ)
    (ha : ∀ i ∈ s, ((k i : ℕ) : ℕ∞) ≤ MvPowerSeries.order (a i))
    (hb : ∀ i ∈ s, ((k i : ℕ) : ℕ∞) ≤ MvPowerSeries.order (b i))
    (hab : ∀ i ∈ s, ((k i : ℕ) : ℕ∞) + (1 : ℕ∞) ≤ MvPowerSeries.order (a i - b i)) :
    ∑ i ∈ s, ((k i : ℕ) : ℕ∞) + (1 : ℕ∞) ≤ MvPowerSeries.order (∏ i ∈ s, a i - ∏ i ∈ s, b i) := by
  classical
  revert ha hb hab
  induction s using Finset.induction_on with
  | empty => intro _ _ _; simp
  | @insert j s hj ih =>
    intro ha hb hab
    have ih' := ih (fun i hi => ha i (Finset.mem_insert_of_mem hi))
      (fun i hi => hb i (Finset.mem_insert_of_mem hi))
      (fun i hi => hab i (Finset.mem_insert_of_mem hi))
    have key : ∏ i ∈ insert j s, a i - ∏ i ∈ insert j s, b i
        = a j * (∏ i ∈ s, a i - ∏ i ∈ s, b i) + (a j - b j) * ∏ i ∈ s, b i := by
      rw [Finset.prod_insert hj, Finset.prod_insert hj]; ring
    have hbs : ∑ i ∈ s, ((k i : ℕ) : ℕ∞) ≤ MvPowerSeries.order (∏ i ∈ s, b i) :=
      le_trans (Finset.sum_le_sum fun i hi => hb i (Finset.mem_insert_of_mem hi))
        (MvPowerSeries.le_order_prod _ _)
    rw [key, Finset.sum_insert hj]
    refine le_trans ?_ MvPowerSeries.min_order_le_add
    refine le_min ?_ ?_
    · calc ((k j : ℕ) : ℕ∞) + ∑ i ∈ s, ((k i : ℕ) : ℕ∞) + 1
          = (k j : ℕ∞) + (∑ i ∈ s, ((k i : ℕ) : ℕ∞) + 1) := by rw [add_assoc]
        _ ≤ MvPowerSeries.order (a j) + MvPowerSeries.order (∏ i ∈ s, a i - ∏ i ∈ s, b i) :=
          add_le_add (ha j (Finset.mem_insert_self _ _)) ih'
        _ ≤ _ := MvPowerSeries.le_order_mul
    · calc ((k j : ℕ) : ℕ∞) + ∑ i ∈ s, ((k i : ℕ) : ℕ∞) + 1
          = ((k j : ℕ∞) + 1) + ∑ i ∈ s, ((k i : ℕ) : ℕ∞) := by rw [add_right_comm]
        _ ≤ MvPowerSeries.order (a j - b j) + MvPowerSeries.order (∏ i ∈ s, b i) :=
          add_le_add (hab j (Finset.mem_insert_self _ _)) hbs
        _ ≤ _ := MvPowerSeries.le_order_mul
end GlobalTheory.OrderProductDifference
