-- Prove2me | solution 1 for N4Code.Psi_real
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T10:05:10.605592+00:00
-- url     : https://prove2.me/submissions/780a6137-ebfd-4bf8-96a6-eed633926cf5

import Definitions.Def_N4Code_Comparison
import Mathlib.Tactic.FieldSimp
import Definitions.Def_N4Code_Compare

set_option autoImplicit true
open N4Code
namespace N4Code
theorem _root_.solution {n : ℕ} (C : Code n) (t : Fin n) (d : ℕ) (hd : 1 ≤ d) :
    (∑ i ∈ Finset.Icc 1 d, ((alpha3 C t i : ℝ) - (alpha5 C t (i - 1) : ℝ))) =
      Psi C t d := by
  have hre : (∑ i ∈ Finset.Icc 1 d, (alpha5 C t (i - 1) : ℝ)) =
      ∑ j ∈ Finset.Icc 0 (d - 1), (alpha5 C t j : ℝ) := by
    refine Finset.sum_bij (fun i _ => i - 1) ?_ ?_ ?_ ?_
    · intro i hi
      simp [Finset.mem_Icc] at hi ⊢
      omega
    · intro a ha b hb hab
      have ha1 : 1 ≤ a := (Finset.mem_Icc.mp ha).1
      have hb1 : 1 ≤ b := (Finset.mem_Icc.mp hb).1
      omega
    · intro j hj
      refine ⟨j + 1, ?_, ?_⟩
      · simp [Finset.mem_Icc] at hj ⊢
        omega
      · omega
    · intro i hi
      rfl
  unfold Psi
  rw [Int.cast_sub, Int.cast_sum, Int.cast_sum]
  rw [Finset.sum_sub_distrib, hre]
  norm_num
end N4Code
