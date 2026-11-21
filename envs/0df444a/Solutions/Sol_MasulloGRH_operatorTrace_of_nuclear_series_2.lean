-- Prove2me | solution 2 for MasulloGRH.operatorTrace_of_nuclear_series
-- status  : ACCEPTED   (prove)
-- author  : @dga471
-- created : 2026-11-21T02:05:13.424178+00:00
-- url     : https://prove2.me/submissions/8529fd2a-758a-414f-9df9-7988229d13d1

import Definitions.Def_MasulloGRH_HilbertNuclear

open MasulloGRH

set_option maxHeartbeats 800000

theorem solution {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (T : H →L[ℂ] H) (x y : ℕ → H) (hs : Summable (fun m => ‖x m‖ * ‖y m‖))
    (hxy : ∀ u : H, HasSum (fun m => inner ℂ (x m) u • y m) (T u)) :
    operatorTrace T = ∑' m, inner ℂ (x m) (y m) := by
  classical
  let b := chosenHilbertBasis H
  let c (m : ℕ) (i : (exists_hilbertBasis ℂ H).choose) :=
    inner ℂ (x m) (b i) * inner ℂ (b i) (y m)
  have bound (m : ℕ) (s : Finset _) : ∑ i ∈ s, ‖c m i‖ ≤ ‖x m‖ * ‖y m‖ := by
    simp only [c, norm_mul, norm_inner_symm (x m)]
    apply (Real.sum_mul_le_sqrt_mul_sqrt s _ _).trans
    apply mul_le_mul _ _ (Real.sqrt_nonneg _) (norm_nonneg _)
    · simpa using Real.sqrt_le_sqrt (b.orthonormal.sum_inner_products_le (s := s) (x m))
    · simpa using Real.sqrt_le_sqrt (b.orthonormal.sum_inner_products_le (s := s) (y m))
  have ha : Summable (fun p : ℕ × _ => ‖c p.1 p.2‖) := by
    apply (summable_prod_of_nonneg (fun _ => norm_nonneg _)).mpr
    refine ⟨fun m => summable_of_sum_le (fun _ => norm_nonneg _) (bound m), ?_⟩
    exact hs.of_nonneg_of_le (fun _ => tsum_nonneg fun _ => norm_nonneg _)
      (fun m => Real.tsum_le_of_sum_le (fun _ => norm_nonneg _) (bound m))
  have habs : Summable (fun p : ℕ × _ => c p.1 p.2) := ha.of_norm
  calc
    operatorTrace T = ∑' i, ∑' m, c m i := by
      apply tsum_congr
      intro i
      have h := (hxy (b i)).mapL (innerSL ℂ (b i))
      simpa [c, inner_smul_right] using h.tsum_eq.symm
    _ = ∑' m, ∑' i, c m i := habs.tsum_comm
    _ = ∑' m, inner ℂ (x m) (y m) := tsum_congr fun m => b.tsum_inner_mul_inner _ _
