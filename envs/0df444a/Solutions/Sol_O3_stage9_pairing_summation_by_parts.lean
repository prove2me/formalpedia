-- Prove2me | solution 1 for O3.stage9_pairing_summation_by_parts
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T14:28:57.099832+00:00
-- url     : https://prove2.me/submissions/3dc1887d-dc2a-40b7-a172-fa4b14f28e7a

import Definitions.Def_O3_Foundation
import Definitions.Def_O3_Stage2RouteC
import Definitions.Def_O3_Stage2RouteD
import Definitions.Def_O3_Stage9Telescoping
import Theorems.Thm_O3_pairing_finset_sum_left
import Theorems.Thm_O3_stage9WeightedGradient_succ
import Theorems.Thm_O3_Stage2RouteD_dualityMap_zero
import Theorems.Thm_O3_Stage2RouteD_pairing_add_left
import Theorems.Thm_O3_Stage2RouteD_pairing_add_right
import Theorems.Thm_O3_Stage2RouteD_pairing_smul_left
import Theorems.Thm_O3_lpNorm_neg
import Theorems.Thm_O3_lpNorm_zero
import Theorems.Thm_O3_lpPower_neg
import Theorems.Thm_O3_lpPower_zero
import Theorems.Thm_O3_pairing_neg_left
import Theorems.Thm_O3_pairing_neg_right
attribute [local simp] O3.Stage2RouteD.dualityMap_zero
attribute [local simp] O3.lpNorm_neg
attribute [local simp] O3.lpNorm_zero
attribute [local simp] O3.lpPower_neg
attribute [local simp] O3.lpPower_zero
attribute [local simp] O3.pairing_neg_left
attribute [local simp] O3.pairing_neg_right



set_option autoImplicit true
open scoped BigOperators
open O3
namespace O3
theorem _root_.solution {d : ℕ}
    (delta : ℕ → ℝ) (g v : ℕ → Vec d) : ∀ n,
    (∑ i ∈ Finset.range n,
        delta i * pairing (g i) (v n - v i)) =
      ∑ k ∈ Finset.range n,
        pairing (stage9WeightedGradient delta g (k + 1))
          (v (k + 1) - v k) := by
  intro n
  induction n with
  | zero => simp
  | succ n ih =>
      rw [Finset.sum_range_succ, Finset.sum_range_succ]
      have hshift :
          (∑ i ∈ Finset.range n,
              delta i * pairing (g i) (v (n + 1) - v i)) =
            (∑ i ∈ Finset.range n,
              delta i * pairing (g i) (v n - v i)) +
              pairing (stage9WeightedGradient delta g n)
                (v (n + 1) - v n) := by
        calc
          (∑ i ∈ Finset.range n,
              delta i * pairing (g i) (v (n + 1) - v i)) =
              ∑ i ∈ Finset.range n,
                (delta i * pairing (g i) (v n - v i) +
                  pairing (delta i • g i) (v (n + 1) - v n)) := by
                    apply Finset.sum_congr rfl
                    intro i _
                    have hvec : v (n + 1) - v i =
                        (v n - v i) + (v (n + 1) - v n) := by
                      funext j
                      simp only [Pi.sub_apply, Pi.add_apply]
                      ring
                    rw [hvec, Stage2RouteD.pairing_add_right,
                      Stage2RouteD.pairing_smul_left]
                    ring
          _ = (∑ i ∈ Finset.range n,
                delta i * pairing (g i) (v n - v i)) +
              ∑ i ∈ Finset.range n,
                pairing (delta i • g i) (v (n + 1) - v n) := by
                  rw [Finset.sum_add_distrib]
          _ = _ := by
            rw [← pairing_finset_sum_left]
            rfl
      rw [hshift, ih, stage9WeightedGradient_succ]
      rw [Stage2RouteD.pairing_add_left,
        Stage2RouteD.pairing_smul_left]
      ring
end O3
