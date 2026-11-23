-- Prove2me | solution 1 for Kyprianou.Ch02.cadlagNNRealDiscontinuitiesCountableV1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-23T19:32:14.486096+00:00
-- url     : https://prove2.me/submissions/eff2dd94-62ee-447c-baca-9a11f011829f

import Mathlib
import Theorems.Thm_Kyprianou_ProofPreparation_finite_large_jumps_of_nnreal_cadlag

open Filter Set Topology
open scoped NNReal ENNReal
set_option autoImplicit false

/-- Every càdlàg real path on nonnegative time has countably many discontinuities. -/
theorem solution
    (f : ℝ≥0 → ℝ)
    (hright : ∀ t : ℝ≥0, ContinuousWithinAt f (Set.Ici t) t)
    (hleft : ∀ t : ℝ≥0, 0 < t →
      ∃ l : ℝ, Tendsto f (nhdsWithin t (Set.Iio t)) (nhds l)) :
    Set.Countable {t : ℝ≥0 | ¬ ContinuousAt f t} := by
  let jump (n k : ℕ) : Set ℝ≥0 :=
    {u | 0 < u ∧ u ≤ (n : ℝ≥0) ∧
      ∃ l : ℝ, Tendsto f (𝓝[<] u) (𝓝 l) ∧
        1 / (((k + 1 : ℕ) : ℝ)) < |f u - l|}
  have hfinite : ∀ n k, (jump n k).Finite := by
    intro n k
    exact Kyprianou.ProofPreparation.finite_large_jumps_of_nnreal_cadlag
      f hright hleft n (1 / (((k + 1 : ℕ) : ℝ))) (by positivity)
  have hcount : (⋃ n : ℕ, ⋃ k : ℕ, jump n k).Countable := by
    exact Set.countable_iUnion (fun n =>
      Set.countable_iUnion (fun k => (hfinite n k).countable))
  apply hcount.mono
  intro t ht
  have ht0 : t ≠ 0 := by
    intro he
    subst t
    apply ht
    have hzero := hright (0 : ℝ≥0)
    have hset : Set.Ici (0 : ℝ≥0) = Set.univ := by
      ext s
      simp
    rw [hset] at hzero
    simpa only [continuousWithinAt_univ] using hzero
  have htpos : (0 : ℝ≥0) < t := pos_iff_ne_zero.mpr ht0
  obtain ⟨l, hl⟩ := hleft t htpos
  have hneq : f t ≠ l := by
    intro he
    apply ht
    have hlt : Tendsto f (𝓝[<] t) (𝓝 (f t)) := by
      simpa [he] using hl
    change Tendsto f (𝓝 t) (𝓝 (f t))
    rw [← nhdsLT_sup_nhdsGE]
    exact hlt.sup (hright t)
  obtain ⟨n, hn⟩ := exists_nat_gt t
  have hpos : 0 < |f t - l| :=
    abs_pos.mpr (sub_ne_zero.mpr hneq)
  obtain ⟨k, hk⟩ := exists_nat_one_div_lt hpos
  change t ∈ ⋃ n : ℕ, ⋃ k : ℕ, jump n k
  simp only [Set.mem_iUnion]
  refine ⟨n, k, htpos, hn.le, l, hl, ?_⟩
  simpa only [Nat.cast_add, Nat.cast_one] using hk
