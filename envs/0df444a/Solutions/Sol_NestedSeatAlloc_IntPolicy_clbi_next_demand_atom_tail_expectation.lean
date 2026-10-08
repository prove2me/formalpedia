-- Prove2me | solution 1 for NestedSeatAlloc.IntPolicy.clbi_next_demand_atom_tail_expectation
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-08T10:20:24.034609+00:00
-- url     : https://prove2.me/submissions/b985c221-5cda-4046-b5c5-61469b7f9ea1

import Mathlib
import Definitions.Def_NestedSeatAlloc_IntPolicy_Model
import Theorems.Thm_NestedSeatAlloc_IntPolicy_revenue_succ_eq_atom_tail_pointwise
import Theorems.Thm_NestedSeatAlloc_IntPolicy_integral_expRevenue_mul_next_event_indicator
import Theorems.Thm_revenue_joint_measurable
import Theorems.Thm_revenue_abs_bound
import Theorems.Thm_clbi_integrable_affine_revenue_event
import Theorems.Thm_clbi_integral_affine_revenue_event
import Theorems.Thm_clbi_integrable_sum_range
import Theorems.Thm_clbi_integral_sum_range
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true
open MeasureTheory ProbabilityTheory NestedSeatAlloc.IntPolicy

theorem solution {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (X : ℕ → Ω → ℝ) (f : ℕ → ℝ) (hM : IsSeatModel P X f)
    (hint : ∀ i ω, ∃ n : ℕ, X i ω = n) (k n : ℕ) (hk : 0 < k)
    (p : ℕ → ℕ) (s : ℝ)
    (hs : s ∈ Set.Icc ((p k : ℝ) + n) ((p k : ℝ) + n + 1)) :
    expRevenue P X f (fun j => (p j : ℝ)) (k + 1) s =
      (∑ i ∈ Finset.range (n + 1),
        P.real {ω | X (k + 1) ω = (i : ℝ)} *
          ((i : ℝ) * f (k + 1) +
            expRevenue P X f (fun j => (p j : ℝ)) k (s - i))) +
      P.real {ω | (n : ℝ) < X (k + 1) ω} *
        ((s - (p k : ℝ)) * f (k + 1) +
          expRevenue P X f (fun j => (p j : ℝ)) k (p k : ℝ)) := by
  classical
  let q : ℕ → ℝ := fun j => (p j : ℝ)
  have hq : ∀ i, 0 ≤ q i := fun i => Nat.cast_nonneg (p i)
  let Atom : ℕ → Ω → ℝ := fun i ω =>
    if X (k + 1) ω = (i : ℝ) then
      (i : ℝ) * f (k + 1) + revenue f q (fun i => X i ω) k (s - i)
    else 0
  let Tail : Ω → ℝ := fun ω =>
    if (n : ℝ) < X (k + 1) ω then
      (s - q k) * f (k + 1) + revenue f q (fun i => X i ω) k (q k)
    else 0
  have hshift : ∀ i : ℕ, i ≤ n → 0 ≤ s - i := by
    intro i hi
    have hn : (i : ℝ) ≤ n := by exact_mod_cast hi
    have hpk : 0 ≤ (p k : ℝ) := Nat.cast_nonneg _
    linarith [hs.1, hn, hpk]
  have hAtomInt : ∀ i ≤ n, Integrable (Atom i) P := by
    intro i hi
    let E : Set ℝ := {(i : ℝ)}
    have hE : MeasurableSet E := measurableSet_singleton _
    have hEq : Atom i = fun ω =>
        ((i : ℝ) * f (k + 1) + revenue f q (fun i => X i ω) k (s - i)) *
          (if X (k + 1) ω ∈ E then (1 : ℝ) else 0) := by
      funext ω
      by_cases hω : X (k + 1) ω = (i : ℝ) <;> simp [Atom, E, hω]
    rw [hEq]
    exact clbi_integrable_affine_revenue_event P X f q hM k (s - i)
      ((i : ℝ) * f (k + 1)) (hshift i hi) hq E hE
  have hTailInt : Integrable Tail P := by
    let E : Set ℝ := Set.Ioi (n : ℝ)
    have hE : MeasurableSet E := measurableSet_Ioi
    have hEq : Tail = fun ω =>
        ((s - q k) * f (k + 1) + revenue f q (fun i => X i ω) k (q k)) *
          (if X (k + 1) ω ∈ E then (1 : ℝ) else 0) := by
      funext ω
      by_cases hω : (n : ℝ) < X (k + 1) ω <;>
        simp [Tail, E, Set.mem_Ioi, hω]
    rw [hEq]
    exact clbi_integrable_affine_revenue_event P X f q hM k (q k)
      ((s - q k) * f (k + 1)) (hq k) hq E hE
  have hSumInt : Integrable
      (fun ω => ∑ i ∈ Finset.range (n + 1), Atom i ω) P :=
    clbi_integrable_sum_range P Atom n hAtomInt
  have hPartition : ∀ ω,
      revenue f q (fun i => X i ω) (k + 1) s =
        (∑ i ∈ Finset.range (n + 1), Atom i ω) + Tail ω := by
    intro ω
    have h := revenue_succ_eq_atom_tail_pointwise X f hint k n hk p s hs ω
    simpa [Atom, Tail, q] using h
  have hAtomFormula : ∀ i ≤ n,
      ∫ ω, Atom i ω ∂P =
        P.real {ω | X (k + 1) ω = (i : ℝ)} *
          ((i : ℝ) * f (k + 1) + expRevenue P X f q k (s - i)) := by
    intro i hi
    let E : Set ℝ := {(i : ℝ)}
    have hE : MeasurableSet E := measurableSet_singleton _
    have hEq : Atom i = fun ω =>
        ((i : ℝ) * f (k + 1) + revenue f q (fun i => X i ω) k (s - i)) *
          (if X (k + 1) ω ∈ E then (1 : ℝ) else 0) := by
      funext ω
      by_cases hω : X (k + 1) ω = (i : ℝ) <;> simp [Atom, E, hω]
    have hPre : X (k + 1) ⁻¹' E = {ω | X (k + 1) ω = (i : ℝ)} := by
      ext ω
      simp [E]
    rw [hEq, clbi_integral_affine_revenue_event P X f q hM k (s - i)
      ((i : ℝ) * f (k + 1)) (hshift i hi) hq E hE, hPre]
    ring
  have hTailFormula :
      ∫ ω, Tail ω ∂P =
        P.real {ω | (n : ℝ) < X (k + 1) ω} *
          ((s - q k) * f (k + 1) + expRevenue P X f q k (q k)) := by
    let E : Set ℝ := Set.Ioi (n : ℝ)
    have hE : MeasurableSet E := measurableSet_Ioi
    have hEq : Tail = fun ω =>
        ((s - q k) * f (k + 1) + revenue f q (fun i => X i ω) k (q k)) *
          (if X (k + 1) ω ∈ E then (1 : ℝ) else 0) := by
      funext ω
      by_cases hω : (n : ℝ) < X (k + 1) ω <;>
        simp [Tail, E, Set.mem_Ioi, hω]
    have hPre : X (k + 1) ⁻¹' E = {ω | (n : ℝ) < X (k + 1) ω} := by
      ext ω
      simp [E, Set.mem_Ioi]
    rw [hEq, clbi_integral_affine_revenue_event P X f q hM k (q k)
      ((s - q k) * f (k + 1)) (hq k) hq E hE, hPre]
    ring
  letI : IsProbabilityMeasure P := hM.isProb
  calc
    expRevenue P X f q (k + 1) s =
        ∫ ω, revenue f q (fun i => X i ω) (k + 1) s ∂P := rfl
    _ = ∫ ω, (∑ i ∈ Finset.range (n + 1), Atom i ω) + Tail ω ∂P := by
      apply integral_congr_ae
      filter_upwards [] with ω
      exact hPartition ω
    _ = (∫ ω, (∑ i ∈ Finset.range (n + 1), Atom i ω) ∂P) +
        ∫ ω, Tail ω ∂P := integral_add hSumInt hTailInt
    _ = (∑ i ∈ Finset.range (n + 1), ∫ ω, Atom i ω ∂P) +
        ∫ ω, Tail ω ∂P := by
      rw [clbi_integral_sum_range P Atom n hAtomInt]
    _ = (∑ i ∈ Finset.range (n + 1),
          P.real {ω | X (k + 1) ω = (i : ℝ)} *
            ((i : ℝ) * f (k + 1) + expRevenue P X f q k (s - i))) +
        P.real {ω | (n : ℝ) < X (k + 1) ω} *
          ((s - q k) * f (k + 1) + expRevenue P X f q k (q k)) := by
      congr 1
      · apply Finset.sum_congr rfl
        intro i hi
        have hi' : i < n + 1 := Finset.mem_range.mp hi
        exact hAtomFormula i (by omega)
    _ = _ := by simpa [q]
