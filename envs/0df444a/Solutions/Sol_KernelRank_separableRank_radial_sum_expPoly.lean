-- Prove2me | solution 1 for KernelRank.separableRank_radial_sum_expPoly
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T02:46:18.844863+00:00
-- url     : https://prove2.me/submissions/3ea722ec-e979-4713-a981-43c0b305f9b9

import Definitions.Def_KernelRankLean_ComplexRank
import Definitions.Def_KernelRankLean_MultiComplexRank
import Theorems.Thm_KernelRank_separableRank_sum_expPoly
import Theorems.Thm_KernelRank_separableRank_radial_eq_hankel


set_option autoImplicit true
open Complex Polynomial NNReal
open KernelRank
namespace KernelRank
theorem _root_.solution {d : ℕ} (hd : 2 ≤ d) {ι : Type*} [Fintype ι]
    {rate : ι → ℂ} (hinj : Function.Injective rate) (P : ι → ℂ[X]) (hP : ∀ i, P i ≠ 0) :
    separableRank (fun x : Fin d → ℝ => ∑ i, expPoly (P i) (rate i) (∑ j, x j ^ 2)) =
      (∑ i, ((d - 1) * (P i).natDegree + 1) : ℕ) := by
  rw [separableRank_radial_eq_hankel d (fun t => ∑ i, expPoly (P i) (rate i) t),
    separableRank_sum_expPoly hd hinj P hP]
end KernelRank
