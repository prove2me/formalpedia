-- Prove2me | solution 1 for GlobalTheory.WittIntegrality.key
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T22:28:15.248667+00:00
-- url     : https://prove2.me/submissions/73135d9a-9f99-4546-ac55-c7e5630c5b87

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_WittMatrixCoeffMemOfFrobenius
import Theorems.Thm_GlobalTheory_WittIntegrality_teich_mem
import Theorems.Thm_GlobalTheory_WittIntegrality_frob_mem
import Theorems.Thm_GlobalTheory_WittIntegrality_mem_of_mul_p_mem
import Theorems.Thm_GlobalTheory_WittIntegrality_tail_coeff
import Theorems.Thm_GlobalTheory_WittIntegrality_decomp
import Theorems.Thm_GlobalTheory_WittIntegrality_key0

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped PowerSeries Pointwise
open GlobalTheory
open GlobalTheory.WittIntegrality
open WittVector
variable {C : Type} [Field C] (A : ValuationSubring C)
variable (p : ℕ) [hp : Fact p.Prime]
variable {p}
variable [CharP C p]
variable [PerfectRing C p]
namespace GlobalTheory.WittIntegrality
theorem _root_.solution {n : Type} [Fintype n] (Y : Matrix n n (WittVector p C)) (hY : ∀ i j, Y i j ∈ S A p) :
    ∀ (k : ℕ) (Z B : Matrix n n (WittVector p C)), (∀ i j, B i j ∈ S A p) →
    (∀ i j, frobenius (Z i j) = ∑ a, Y i a * Z a j + B i j) →
    ∀ i j, (Z i j).coeff k ∈ A := by
  intro k
  induction k with
  | zero => exact fun Z B hB h => key0 A Y Z B hY hB h
  | succ k ih =>
    intro Z B hB h
    have h0 := key0 A Y Z B hY hB h
    let U : Matrix n n (WittVector p C) := fun i j => tail (Z i j)
    let D : Matrix n n (WittVector p C) :=
      fun i j => frobenius (U i j) - ∑ a, Y i a * U a j
    have hD : ∀ i j, D i j * p = ∑ a, Y i a * teichmuller p ((Z a j).coeff 0) + B i j
        - frobenius (teichmuller p ((Z i j).coeff 0)) := by
      intro i j
      have e1 : frobenius (Z i j) = frobenius (teichmuller p ((Z i j).coeff 0))
          + frobenius (U i j) * p := by
        conv_lhs => rw [decomp (Z i j)]
        rw [map_add, map_mul, map_natCast]
      have e2 : ∑ a, Y i a * Z a j = ∑ a, Y i a * teichmuller p ((Z a j).coeff 0)
          + (∑ a, Y i a * U a j) * p := by
        rw [Finset.sum_mul, ← Finset.sum_add_distrib]
        refine Finset.sum_congr rfl fun a _ => ?_
        conv_lhs => rw [decomp (Z a j)]
        ring
      have e4 := h i j
      rw [e1, e2] at e4
      simp only [D]
      linear_combination e4
    have hDm : ∀ i j, D i j ∈ S A p := by
      intro i j
      refine mem_of_mul_p_mem A ?_
      rw [hD]
      exact Subring.sub_mem _ (Subring.add_mem _ (Subring.sum_mem _ fun a _ =>
        Subring.mul_mem _ (hY i a) (teich_mem A (h0 a j))) (hB i j))
        (frob_mem A (teich_mem A (h0 i j)))
    have hU := ih U D hDm (fun i j => by simp only [D]; ring)
    intro i j
    rw [tail_coeff]
    exact pow_mem (hU i j) _
end GlobalTheory.WittIntegrality
