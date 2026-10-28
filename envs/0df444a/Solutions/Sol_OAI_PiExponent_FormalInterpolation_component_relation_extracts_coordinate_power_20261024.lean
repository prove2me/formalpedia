-- Prove2me | solution 1 for OAI.PiExponent.FormalInterpolation.component_relation_extracts_coordinate_power_20261024
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-24T15:29:29.710091+00:00
-- url     : https://prove2.me/submissions/0c2f513b-2a12-4678-8e36-910893db1b3c

import Mathlib.Data.Complex.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Data.Rat.Defs
import Mathlib.RingTheory.MvPolynomial.WeightedHomogeneous
import Theorems.Thm_OAI_PiExponent_FormalInterpolation_positive_relation_extracts_coordinate_power_20261024
import Theorems.Thm_OAI_PiExponent_FormalInterpolation_constant_relation_extracts_coordinate_power_20261024
open scoped BigOperators

theorem solution
    {d : Nat} (w : Fin d → Rat)
    (hw : ∀ j, 0 < (w j : Real))
    (I : Ideal (MvPolynomial (Fin d) Complex))
    (hcomp : ∀ p ∈ I, ∀ r : Rat,
      MvPolynomial.weightedHomogeneousComponent
        (fun j => (w j : Rat)) r p ∈ I)
    (i : Fin d)
    (hrel : ∃ (N : Nat) (c : Fin (N + 1) → Complex),
      (∃ k, c k ≠ 0) ∧
      (∑ k : Fin (N + 1),
        MvPolynomial.C (c k) * MvPolynomial.X i ^ (k : Nat)) ∈ I) :
    ∃ n : Nat, 0 < n ∧ MvPolynomial.X i ^ n ∈ I := by
  classical
  obtain ⟨N, c, ⟨hnz, hmem⟩⟩ := hrel
  by_cases hpos : ∃ k : Fin (N + 1), k.val ≠ 0 ∧ c k ≠ 0
  · exact OAI.PiExponent.FormalInterpolation.positive_relation_extracts_coordinate_power_20261024
      w hw I hcomp i N c hpos hmem
  · have hc0 : c 0 ≠ 0 := by
      obtain ⟨k, hk⟩ := hnz
      by_contra hzero
      apply hpos
      have hkpos : k.val ≠ 0 := by
        intro hval
        have hk0 : k = 0 := Fin.ext hval
        subst k
        exact hk hzero
      exact ⟨k, hkpos, hk⟩
    have hvanish : ∀ k : Fin (N + 1), k.val ≠ 0 → c k = 0 := by
      intro k hk
      by_contra hne
      exact hpos ⟨k, hk, hne⟩
    exact OAI.PiExponent.FormalInterpolation.constant_relation_extracts_coordinate_power_20261024
      i I N c hc0 hvanish hmem
