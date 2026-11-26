-- Prove2me | solution 1 for Kyprianou.Ch05.finitePartitionIntegralError
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-26T18:50:48.765404+00:00
-- url     : https://prove2.me/submissions/33d27f5e-84a7-4f6e-93f4-7ebaa18c9ff7

import Mathlib
import Definitions.Def_Kyprianou_Ch05_RenewalMeasure
import Theorems.Thm_Kyprianou_Ch05_finiteMeasureCellIntegralError
open MeasureTheory Filter Set
open scoped NNReal ENNReal
set_option autoImplicit false
open Kyprianou.Ch05

/-- Sum the cell error estimates over the finite-support partition. -/
theorem solution
    (V : Measure Real) (T : Set Real) (S : Nat → Set Real)
    (hT : V T ≠ ⊤)
    (hU : (⋃ k, S k) = T)
    (hD : Pairwise (Function.onFun Disjoint S))
    (hM : ∀ k, MeasurableSet (S k))
    (hN : ∃ N : Nat, ∀ k : Nat, N ≤ k → S k = ∅)
    (f : Real → Real) (hf : IntegrableOn f T V)
    (c e : Nat → Real)
    (ha : ∀ k z, z ∈ S k → |f z-c k| ≤ e k) :
    |(∫ z in T, f z ∂V) - (∑' k : Nat, c k * (V (S k)).toReal)| ≤
      ∑' k : Nat, e k * (V (S k)).toReal := by
  obtain ⟨N,hN⟩ := hN
  let I := fun k : Nat => ∫ z in S k, f z ∂V
  let C := fun k : Nat => c k * (V (S k)).toReal
  let E := fun k : Nat => e k * (V (S k)).toReal
  have hi : ∫ z in T, f z ∂V = ∑' k, I k := by
    rw [← hU] at hf ⊢
    exact integral_iUnion hM hD hf
  have hz (k : Nat) (hk : k ∉ Finset.range N) : I k = 0 ∧ C k = 0 ∧ E k = 0 := by
    have he := hN k (Nat.le_of_not_lt (fun h => hk (Finset.mem_range.mpr h)))
    simp [I,C,E,he]
  have hsub (k : Nat) : S k ⊆ T := by
    rw [← hU]
    exact subset_iUnion S k
  have herr (k : Nat) : |I k-C k| ≤ E k :=
    finiteMeasureCellIntegralError V (S k) (hM k)
      (ne_top_of_le_ne_top hT (measure_mono (hsub k))) f (hf.mono_set (hsub k))
      (c k) (e k) (ha k)
  change |(∫ z in T, f z ∂V)-(∑' k, C k)| ≤ ∑' k, E k
  rw [hi, tsum_eq_sum (s := Finset.range N) (fun k hk => (hz k hk).1),
    tsum_eq_sum (s := Finset.range N) (fun k hk => (hz k hk).2.1),
    tsum_eq_sum (s := Finset.range N) (fun k hk => (hz k hk).2.2),
    ← Finset.sum_sub_distrib]
  exact (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum (fun k _ => herr k))
