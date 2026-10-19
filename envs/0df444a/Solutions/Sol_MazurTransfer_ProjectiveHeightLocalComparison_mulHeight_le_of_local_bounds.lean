-- Prove2me | solution 1 for MazurTransfer.ProjectiveHeightLocalComparison.mulHeight_le_of_local_bounds
-- status  : ACCEPTED   (prove)
-- author  : @Vas
-- created : 2026-10-17T01:18:03.951767+00:00
-- url     : https://prove2.me/submissions/bcc7a9af-8269-4359-87a5-d6398d4bb85a

/- Copyright (c) 2026 Vas and contributors. Released under Apache-2.0.
Adapted from Mathlib.NumberTheory.Height.MvPolynomial,
Height.mulHeight_linearMap_apply_le, Michael Stoll (2026), Apache-2.0,
exact Mathlib pin 0df444a360eaa60ab8c11dca51a86af692955474.
Design boundary: globalize multiplicative local bounds with a fixed
archimedean factor and no nonarchimedean factor. Named downstream consumer:
the actual monic theta norm equations and section-value height growth. -/
import Mathlib
open Height Height.AdmissibleAbsValues Multiset
universe vK vI vB vT

theorem solution {K : Type vK} {ι : Type vI} {κ : Type vB} {τ : Type vT}
    [Field K] [AdmissibleAbsValues K] [Finite ι] [Finite κ] [Finite τ]
    (u : ι → K) (b : κ → K) (t : τ → K)
    (hu : u ≠ 0) (hb : b ≠ 0) (ht : t ≠ 0) (C : ℝ) (hC : 1 ≤ C)
    (ha : ∀ v ∈ archAbsVal (K := K),
      ⨆ j, v (t j) ≤ C * (⨆ k, v (b k)) * ⨆ i, v (u i))
    (hn : ∀ v : nonarchAbsVal (K := K),
      ⨆ j, v.val (t j) ≤ (⨆ k, v.val (b k)) * ⨆ i, v.val (u i)) :
    mulHeight t ≤ C ^ totalWeight K * mulHeight b * mulHeight u := by
  rw [mulHeight_eq ht, mulHeight_eq hb, mulHeight_eq hu, mul_mul_mul_comm,
    ← mul_assoc, ← mul_assoc, mul_assoc (_ * _ * _)]
  gcongr
  · exact finprod_nonneg fun v => Real.iSup_nonneg_of_nonnegHomClass v.val _
  · exact mul_nonneg (mul_nonneg (pow_nonneg (zero_le_one.trans hC) _)
      (prod_map_nonneg fun v _ => Real.iSup_nonneg_of_nonnegHomClass v _))
      (prod_map_nonneg fun v _ => Real.iSup_nonneg_of_nonnegHomClass v _)
  · rw [mul_assoc, ← prod_map_mul, ← prod_replicate, totalWeight, ← map_const', ← prod_map_mul]
    refine prod_map_le_prod_map₀ _ _ (fun v _ => Real.iSup_nonneg_of_nonnegHomClass v _) fun v hv => ?_
    rw [mul_comm (iSup _), ← mul_assoc]
    exact ha v hv
  · rw [← finprod_mul_distrib (by fun_prop) (by fun_prop)]
    refine finprod_le_finprod (by fun_prop)
      (fun v => Real.iSup_nonneg_of_nonnegHomClass v.val _) (by fun_prop) fun v => ?_
    exact hn v
#print axioms solution
