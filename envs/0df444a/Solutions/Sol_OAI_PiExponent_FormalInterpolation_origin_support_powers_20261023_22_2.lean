-- Prove2me | solution 2 for OAI.PiExponent.FormalInterpolation.origin_support_powers_20261023_22
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-23T18:40:01.277717+00:00
-- url     : https://prove2.me/submissions/08484c3a-aa31-4d68-9331-43d0f92ef199

import Mathlib
import Mathlib.Algebra.MvPolynomial.Eval
import Mathlib.Data.Complex.Basic
import Mathlib.RingTheory.Ideal.Operations
import Mathlib.RingTheory.MvPolynomial.WeightedHomogeneous

section

open MvPolynomial

namespace PiL34

theorem log_floor {m : ℕ} (v0 : ℝ) (hv0 : 0 < v0) {H : Real} (hH : 0 < H) :
    Real.log ((((⌊H⌋₊ + 1) ^ (2 * m) * (⌊H / v0⌋₊ + 1) : Nat) : Real)) ≤
      Real.log ((H + 1) ^ (2 * m) * (H / v0 + 1)) := by
  have h1 : (⌊H⌋₊ : ℝ) ≤ H := Nat.floor_le hH.le
  have h2 : (⌊H / v0⌋₊ : ℝ) ≤ H / v0 := Nat.floor_le (div_nonneg hH.le hv0.le)
  apply Real.log_le_log
  · push_cast; positivity
  · push_cast
    apply mul_le_mul (pow_le_pow_left₀ (by positivity) (by linarith) _) (by linarith) (by positivity)
      (by positivity)

theorem origin_powers {d m : Nat} (q : Fin m → MvPolynomial (Fin d) Complex)
    (hzero : ∀ x : Fin d → Complex,
      (∀ j : Fin m, MvPolynomial.eval x (q j) = 0) →
      ∀ i : Fin d, x i = 0) :
    (∀ i : Fin d, ∃ N : Nat,
      0 < N ∧ (MvPolynomial.X i) ^ N ∈ Ideal.span (Set.range q)) := by
  intro i
  set I := Ideal.span (Set.range q)
  have hmem : (X i : MvPolynomial (Fin d) ℂ) ∈ vanishingIdeal ℂ (zeroLocus ℂ I) := by
    rw [mem_vanishingIdeal_iff]
    intro x hx
    rw [mem_zeroLocus_iff] at hx
    have := hzero x (fun j => by
      have := hx (q j) (Ideal.subset_span ⟨j, rfl⟩)
      simpa [MvPolynomial.aeval_eq_eval] using this) i
    simp [this]
  rw [vanishingIdeal_zeroLocus_eq_radical] at hmem
  obtain ⟨n, hn⟩ := hmem
  refine ⟨n + 1, Nat.succ_pos n, ?_⟩
  rw [pow_succ]
  exact Ideal.mul_mem_right _ _ hn

theorem finite_witness {d : Nat} (I : Ideal (MvPolynomial (Fin d) Complex))
    (w : Fin d → Rat) (s D : Nat)
    (hpoint : ∀ x : Fin d → Complex,
      (∃ i : Fin d, x i ≠ 0) →
      ∃ g : MvPolynomial (Fin d) Complex,
        g ∈ I ^ s ∧
        (∀ a ∈ g.support,
          ∑ k, (w k : Real) * (a k : Real) ≤ (D : Real)) ∧
        MvPolynomial.eval x
          (MvPolynomial.weightedHomogeneousComponent
            (fun k => (w k : ℚ)) (D : ℚ) g) ≠ 0) :
    ∃ m : Nat, ∃ g : Fin m → MvPolynomial (Fin d) Complex,
      (∀ j, g j ∈ I ^ s) ∧
      (∀ j, ∀ a ∈ (g j).support,
        ∑ k, (w k : Real) * (a k : Real) ≤ (D : Real)) ∧
      ∀ x : Fin d → Complex,
        (∀ j : Fin m,
          MvPolynomial.eval x
            (MvPolynomial.weightedHomogeneousComponent
              (fun k => (w k : ℚ)) (D : ℚ) (g j)) = 0) →
        ∀ i : Fin d, x i = 0 := by
  classical
  set G : Set (MvPolynomial (Fin d) ℂ) := {g | g ∈ I ^ s ∧
      ∀ a ∈ g.support, ∑ k, (w k : Real) * (a k : Real) ≤ (D : Real)}
  set top : MvPolynomial (Fin d) ℂ → MvPolynomial (Fin d) ℂ := fun g =>
    MvPolynomial.weightedHomogeneousComponent (R := ℂ) (fun k => (w k : ℚ)) (D : ℚ) g
  have hfg : (Ideal.span (top '' G)).FG := (isNoetherianRing_iff.1 inferInstance).noetherian _
  obtain ⟨S, hSsub, hSspan⟩ := (Submodule.fg_span_iff_fg_span_finset_subset _).1 hfg
  -- choose a preimage in G for each element of S
  have hpre : ∀ t : S, ∃ g ∈ G, top g = t := fun t => hSsub t.2
  choose gg hgG hgt using hpre
  refine ⟨Fintype.card S, fun j => gg ((Fintype.equivFin S).symm j),
    fun j => (hgG _).1, fun j => (hgG _).2, ?_⟩
  intro x hx
  by_contra hne
  push_neg at hne
  obtain ⟨g, hgI, hgD, hgx⟩ := hpoint x hne
  apply hgx
  -- top g lies in the span of S, all of whose elements vanish at x
  have hmem : top g ∈ Ideal.span (S : Set (MvPolynomial (Fin d) ℂ)) := by
    change top g ∈ Submodule.span (MvPolynomial (Fin d) ℂ) (S : Set (MvPolynomial (Fin d) ℂ))
    rw [← hSspan]; exact Ideal.subset_span ⟨g, ⟨hgI, hgD⟩, rfl⟩
  have hvan : ∀ p ∈ Ideal.span (S : Set (MvPolynomial (Fin d) ℂ)), MvPolynomial.eval x p = 0 := by
    intro p hp
    refine Submodule.span_induction ?_ ?_ ?_ ?_ hp
    · intro t ht
      have := hx ((Fintype.equivFin S) ⟨t, ht⟩)
      simp only [Equiv.symm_apply_apply] at this
      have e := hgt ⟨t, ht⟩
      simp only at e
      rw [← e]
      exact this
    · simp
    · intro a b _ _ ha hb; simp [ha, hb]
    · intro a b _ hb; simp [hb]
  exact hvan _ hmem

end PiL34

end



theorem solution
    {d m : Nat} (q : Fin m → MvPolynomial (Fin d) Complex)
    (hzero : ∀ x : Fin d → Complex,
      (∀ j : Fin m, MvPolynomial.eval x (q j) = 0) →
      ∀ i : Fin d, x i = 0) :
    (∀ i : Fin d, ∃ N : Nat,
      0 < N ∧ (MvPolynomial.X i) ^ N ∈ Ideal.span (Set.range q)) := by
  apply PiL34.origin_powers <;> assumption
