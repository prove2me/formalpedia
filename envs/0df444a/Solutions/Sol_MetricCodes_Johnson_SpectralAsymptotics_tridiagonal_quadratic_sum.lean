-- Prove2me | solution 1 for MetricCodes.Johnson.SpectralAsymptotics.tridiagonal_quadratic_sum
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:31.72047+00:00
-- url     : https://prove2.me/submissions/cdb7c64b-a8fa-4cb4-9f29-29c8d4922908

import Definitions.Def_SpherePacking
import Definitions.Def_MetricCodes
import Theorems.Thm_MetricCodes_Hamming_tridiagonal_quadratic_sum

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
open MetricCodes
open MetricCodes.Johnson
open MetricCodes.Johnson.SpectralAsymptotics
noncomputable section
set_option autoImplicit false
open Filter Topology
open scoped BigOperators Topology
open MetricCodes.Johnson.Asymptotics
namespace MetricCodes.Johnson.SpectralAsymptotics
theorem _root_.solution
    (d : ℕ) (b c v : ℕ → ℝ) :
    (∑ i ∈ Finset.range (d + 1),
      ∑ j ∈ Finset.range (d + 1),
        (if i = j then b i
          else if i + 1 = j then c i
          else if j + 1 = i then c j else 0) * v j * v i) =
      (∑ i ∈ Finset.range (d + 1), b i * v i ^ 2) +
        2 * ∑ i ∈ Finset.range d, c i * v i * v (i + 1) := by
  have hpoint (i j : ℕ) :
      (if i = j then b i
        else if i + 1 = j then c i
        else if j + 1 = i then c j else 0) * v j * v i =
      (if i = j then b i * v i ^ 2 else 0) +
        (if i + 1 = j then c i
          else if j + 1 = i then c j else 0) * v j * v i := by
    by_cases hij : i = j
    · subst j
      simp
      ring
    · simp [hij]
  calc
    (∑ i ∈ Finset.range (d + 1),
      ∑ j ∈ Finset.range (d + 1),
        (if i = j then b i
          else if i + 1 = j then c i
          else if j + 1 = i then c j else 0) * v j * v i) =
      ∑ i ∈ Finset.range (d + 1),
        ∑ j ∈ Finset.range (d + 1),
          ((if i = j then b i * v i ^ 2 else 0) +
            (if i + 1 = j then c i
              else if j + 1 = i then c j else 0) * v j * v i) := by
        apply Finset.sum_congr rfl
        intro i hi
        apply Finset.sum_congr rfl
        intro j hj
        exact hpoint i j
    _ =
      (∑ i ∈ Finset.range (d + 1),
        ∑ j ∈ Finset.range (d + 1),
          if i = j then b i * v i ^ 2 else 0) +
      (∑ i ∈ Finset.range (d + 1),
        ∑ j ∈ Finset.range (d + 1),
          (if i + 1 = j then c i
            else if j + 1 = i then c j else 0) * v j * v i) := by
        simp_rw [Finset.sum_add_distrib]
    _ = _ := by
      rw [MetricCodes.Hamming.tridiagonal_quadratic_sum]
      congr 1
      apply Finset.sum_congr rfl
      intro i hi
      simp [Finset.mem_range.mp hi]
end MetricCodes.Johnson.SpectralAsymptotics
